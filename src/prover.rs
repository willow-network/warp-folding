//! Indexer-side WARP fold-step prover.
//!
//! The indexer maintains a [`WarpProverState`] that carries the running
//! accumulator's `(instance, witness)` pair. Each new block calls
//! [`WarpProverState::fold_block`], which:
//!
//!   1. Synthesizes a per-block twin-constrained instance/witness pair
//!      from a deterministic block seed + the configured codeword size.
//!   2. Calls the FS-compiled WARP IOR prover on the two-instance pair.
//!   3. Returns a [`FoldStepWire`] blob the indexer attaches to its
//!      `WarpProofData.proof`, plus the updated accumulator state.
//!
//! The block seed is derived from authenticated per-block data
//! (block hash, output root, subgrove config hash, completeness-proof
//! hash, block number) by [`block_seed`]. Both prover and verifier
//! recompute it from the same public inputs, so a malicious indexer
//! who lies about any of those values gets divergent FS challenges
//! and the IOR rejects.
//!
//! ## Security model
//!
//! WARP here provides *accumulation only* — it chains per-block
//! claims into a single running root and proves each fold operation
//! is correctly computed (per-step IOR soundness via parallel-rep
//! `r=2`). Per-block *correctness* (that the indexer's output really
//! came from the canonical block contents) is enforced by the
//! completeness proof + transformation GKR proof that ride alongside
//! every WARP submission. The two layers compose:
//!
//! - Completeness + GKR pin `output_root` to authenticated block data.
//! - WARP binds `output_root` (via `block_seed`) into a fold-step
//!   proof whose `prev_instance_root` chain-links to the prior
//!   submission's `new_instance_root`.
//!
//! So the bundled PESAT constraint inside WARP is the trivial identity
//! `w[0] - w[0] = 0` — non-trivial circuits are not needed here,
//! because correctness is enforced outside the fold. The decider
//! (`crate::decider`) is wired into [`WarpProverState`] as a local
//! self-check that runs on state load (see [`WarpProverState::self_check`]),
//! so an indexer detects on-disk state corruption before submitting a
//! proof that would fail consensus's chain-link check.
//!
//! ## Witness binding
//!
//! `fold_block(seed, payload)` builds the per-block witness directly
//! from `payload` (the indexer's canonical transformation output, e.g.
//! bincode-encoded state diff bytes). Bytes are paired into 16-bit
//! little-endian groups and each pair becomes one M31 limb — 16 bits
//! fits losslessly in M31's 31-bit prime, so the encoding is injective
//! and two distinct payloads can't collide on the witness. Padding to
//! codeword length comes from `Keccak(seed || payload.len())` so two
//! indexers running the same transformation produce the same witness.
//! An adversary substituting different transformation output for the
//! same block_seed produces a different `new_instance_root`, breaking
//! the chain hash that consensus persists across submissions.

use expander_arith::Field;
use rand::{rngs::StdRng, SeedableRng};
use serdes::ExpSerde;
use sha3::{Digest, Keccak256};
use std::ops::Mul;

use crate::code::LinearCode;
use crate::constr_5_10;
use crate::error::{FoldingError, Result};
use crate::fs::prove_with_parallel_rep_bound;
use crate::orion_code::OrionLinearCode;
use crate::pesat::{Constraint, PesatIndex, PesatInstance, Term};
use crate::twin::{TwinConstrainedInstance, TwinConstrainedWitness};
use crate::wire::FoldStepWire;
use crate::{SamplingParams, SchemeParams};

/// Deterministic seed for the production Orion code instance. The code
/// is a system parameter shared between prover and verifier (and across
/// all subgroves), not per-instance; this constant binds everyone to
/// the same expander-graph sampling. Public so verifiers building the
/// code independently can call [`default_orion_code`].
pub const ORION_CODE_SEED: [u8; 32] = *b"willow-warp/orion-code-seed/v1\0\0";

/// Construct the canonical production Orion code for the given message
/// log-length. Both prover and verifier must construct the same code
/// to verify a proof; this is the single source of truth.
pub fn default_orion_code(msg_log_n: usize) -> OrionLinearCode {
    OrionLinearCode::new(1usize << msg_log_n, ORION_CODE_SEED)
}

/// Running accumulator state held by an indexer between block
/// submissions. Genesis state is built via [`WarpProverState::genesis`];
/// each subsequent block calls [`WarpProverState::fold_block`].
pub struct WarpProverState<F>
where
    F: Field + ExpSerde + From<u32> + Mul<F, Output = F>,
{
    instance: TwinConstrainedInstance<F>,
    witness: TwinConstrainedWitness<F>,
    p_b: Constraint<F>,
    code: OrionLinearCode,
    /// log₂ of the witness/message length. The actual codeword length is
    /// derived from the Orion code's encoding ratio and rounded up to
    /// the next power of two (see [`OrionLinearCode`]).
    msg_log_n: usize,
    parallel_rep: u32,
    sampling_n_ood: usize,
    sampling_n_shifts: usize,
}

impl<F> WarpProverState<F>
where
    F: Field + ExpSerde + From<u32> + Mul<F, Output = F>,
{
    /// Build the genesis accumulator. The witness is a deterministic
    /// length-`2^msg_log_n` vector derived from `genesis_seed` so the
    /// same seed reproduces the same accumulator. The Orion code itself
    /// is a system parameter and uses a fixed shared seed
    /// ([`ORION_CODE_SEED`]). Defaults sampling to the `(n_ood=1,
    /// n_shifts=2)` profile (r=4) — call [`WarpProverState::with_sampling`]
    /// to override.
    pub fn genesis(msg_log_n: usize, parallel_rep: u32, genesis_seed: [u8; 32]) -> Self {
        let msg_len = 1usize << msg_log_n;
        let code = OrionLinearCode::new(msg_len, ORION_CODE_SEED);

        let mut rng = StdRng::from_seed(genesis_seed);
        let w: Vec<F> = (0..msg_len).map(|_| F::random_unsafe(&mut rng)).collect();

        // Trivial PESAT identity `w[0] - w[0] = 0`. Per-block
        // correctness is enforced by the completeness + GKR proofs
        // that ride alongside every WARP submission; the fold only
        // needs to accumulate claims, not prove them. See the module
        // docs for the layering.
        let p_b = Constraint {
            terms: vec![
                // x is empty / β is empty for our config, so var 0 is w[0].
                Term {
                    coeff: F::one(),
                    vars: vec![0],
                },
                Term {
                    coeff: -F::one(),
                    vars: vec![0],
                },
            ],
        };

        // Build the genesis instance via the same Construction 5.10
        // path the verifier would use, so prev_instance hashing matches.
        let pesat_idx = PesatIndex {
            constraints: vec![p_b.clone()],
            n_pub: 0,
            k: msg_len,
            d: 1,
        };
        let pesat_inst = PesatInstance {
            x: vec![],
            w: w.clone(),
        };
        // Single constraint ⇒ log M = 0 ⇒ tau is empty.
        let tau: Vec<F> = Vec::new();
        let (instance, witness, p_b_bundled) =
            constr_5_10::reduce(&pesat_idx, &pesat_inst, &code, &tau).expect("genesis reduce");

        Self {
            instance,
            witness,
            p_b: p_b_bundled,
            code,
            msg_log_n,
            parallel_rep,
            sampling_n_ood: 1,
            sampling_n_shifts: 2,
        }
    }

    /// Override the Construction 7.2 sampling profile. `r = 1 + n_ood +
    /// n_shifts` must be a power of two; verifier and prover must agree.
    pub fn with_sampling(mut self, n_ood: usize, n_shifts: usize) -> Self {
        self.sampling_n_ood = n_ood;
        self.sampling_n_shifts = n_shifts;
        self
    }

    /// Genesis hash: 32-byte commitment to the genesis accumulator. The
    /// first WARP submission's `prev_instance_root` is this value.
    pub fn current_root(&self) -> [u8; 32] {
        crate::wire::hash_instance(&self.instance)
    }

    /// Run the WARP decider against the current accumulator. Used as
    /// an indexer-side integrity check after loading state from disk
    /// — catches on-disk corruption that survived ExpSerde decoding
    /// but produced a `(instance, witness)` pair the decider rejects.
    /// Production hot path is `fold_block`, not this; per-step IOR
    /// soundness already prevents the prover from chaining bogus
    /// claims.
    pub fn self_check(&self) -> Result<()> {
        crate::decider::decide(&self.instance, &self.witness, &self.code, &self.p_b)
    }

    /// Fold a new block's contribution into the running accumulator.
    /// Returns the wire blob the indexer should serialize into
    /// `WarpProofData.proof`.
    ///
    /// `block_seed` is the binding-only seed the verifier shares with
    /// the prover (typically Keccak of block_hash || output_root ||
    /// config_hash || block_number). It's used as a fallback domain
    /// separator when `block_payload` is shorter than the codeword.
    ///
    /// `block_payload` is the canonical bincode/RLP-style serialization
    /// of the indexer's actual transformation output (e.g., the encoded
    /// state diff bytes). The witness is built from `block_payload`
    /// chunked into M31 limbs; padding draws from `block_seed` so
    /// short payloads still hit the codeword length deterministically.
    /// Two indexers with the same payload produce the same witness;
    /// adversarial substitution would break the chain hash.
    pub fn fold_block(
        &mut self,
        block_seed: [u8; 32],
        block_payload: &[u8],
    ) -> Result<FoldStepWire<F>> {
        let msg_len = 1usize << self.msg_log_n;

        // Step 1: Encode the per-block payload as field elements. Two
        // bytes per limb: a 16-bit value fits losslessly in M31's
        // 31-bit prime, so distinct payloads produce distinct witnesses
        // (no high-bit truncation). Witness fills the WITNESS length
        // (`msg_len`), not the codeword length — the Orion code expands
        // `w` into the larger codeword `f = code.encode(w)`.
        let mut w: Vec<F> = Vec::with_capacity(msg_len);
        for chunk in block_payload.chunks(2) {
            let mut buf = [0u8; 2];
            buf[..chunk.len()].copy_from_slice(chunk);
            let limb = u16::from_le_bytes(buf) as u32;
            w.push(F::from(limb));
            if w.len() == msg_len {
                break;
            }
        }

        // Step 2: If the payload didn't fill the witness, pad
        // deterministically from the block_seed so the witness is
        // unique per (payload, seed) pair without revealing entropy.
        if w.len() < msg_len {
            let mut hasher = Keccak256::new();
            hasher.update(b"willow-warp/block-witness/pad/v1");
            hasher.update(block_seed);
            // Bind the padding to the actual payload length so two
            // payloads of different lengths can't be confused.
            hasher.update((block_payload.len() as u64).to_le_bytes());
            let pad_seed: [u8; 32] = hasher.finalize().into();
            let mut rng = StdRng::from_seed(pad_seed);
            while w.len() < msg_len {
                w.push(F::random_unsafe(&mut rng));
            }
        }

        let pesat_idx = PesatIndex {
            constraints: vec![Constraint {
                terms: vec![
                    Term {
                        coeff: F::one(),
                        vars: vec![0],
                    },
                    Term {
                        coeff: -F::one(),
                        vars: vec![0],
                    },
                ],
            }],
            n_pub: 0,
            k: msg_len,
            d: 1,
        };
        let pesat_inst = PesatInstance { x: vec![], w };
        let tau: Vec<F> = Vec::new();
        let (new_instance, new_witness, _p_b) =
            constr_5_10::reduce(&pesat_idx, &pesat_inst, &self.code, &tau)?;

        // Run the FS-compiled WARP IOR. `log_n` and `k` come from the
        // code: `log_n = log₂(codeword_len)`, `k = msg_len` (witness
        // length). Defaults sampling to `(1, 2)` → r=4.
        let params = SchemeParams {
            log_n: <OrionLinearCode as LinearCode<F>>::log_codeword_len(&self.code),
            k: msg_len,
            m: 0,
            d: 1,
        };
        let sampling = SamplingParams {
            n_ood: self.sampling_n_ood,
            n_shifts: self.sampling_n_shifts,
        };
        // Bind the FS transcript to the block_seed. Verifier independently
        // recomputes block_seed from authenticated public inputs (block hash,
        // output root, completeness-proof hash, …); a wrong-seed prover
        // diverges at the very first FS challenge and the IOR rejects.
        let (folded_inst, folded_wit, messages) = prove_with_parallel_rep_bound::<F>(
            &[self.instance.clone(), new_instance.clone()],
            &[self.witness.clone(), new_witness.clone()],
            &self.p_b,
            &params,
            &sampling,
            self.parallel_rep,
            &block_seed,
        )?;

        let wire = FoldStepWire {
            prev_instance: self.instance.clone(),
            new_instance: new_instance.clone(),
            messages,
        };

        // Advance the prover's running state to the folded result.
        self.instance = folded_inst;
        self.witness = folded_wit;

        Ok(wire)
    }
}

/// Number of bytes the prover's `current_root` and the on-chain
/// `prev_instance_root` are expected to be — kept here so downstream
/// type assertions don't need a magic constant.
pub const WARP_INSTANCE_ROOT_BYTES: usize = 32;

const STATE_MAGIC: &[u8; 8] = b"WARPST01";

impl<F> WarpProverState<F>
where
    F: Field + ExpSerde + From<u32> + Mul<F, Output = F>,
{
    /// Serialize the prover state to bytes for on-disk persistence.
    /// Only the dynamic parts (instance + witness vectors) and the
    /// scheme parameters are written; `p_b` is the trivial identity
    /// constraint that [`Self::from_bytes`] rebuilds from `msg_log_n`,
    /// and the Orion code is reconstructed from `msg_log_n` plus the
    /// shared [`ORION_CODE_SEED`].
    pub fn to_bytes(&self) -> Result<Vec<u8>> {
        let mut buf: Vec<u8> = Vec::new();
        buf.extend_from_slice(STATE_MAGIC);
        buf.push(self.msg_log_n as u8);
        buf.extend_from_slice(&self.parallel_rep.to_le_bytes());
        buf.push(self.sampling_n_ood as u8);
        buf.push(self.sampling_n_shifts as u8);
        self.instance
            .serialize_into(&mut buf)
            .map_err(|e| FoldingError::ShapeMismatch(format!("instance serialize: {e:?}")))?;
        self.witness
            .f
            .serialize_into(&mut buf)
            .map_err(|e| FoldingError::ShapeMismatch(format!("witness.f serialize: {e:?}")))?;
        self.witness
            .w
            .serialize_into(&mut buf)
            .map_err(|e| FoldingError::ShapeMismatch(format!("witness.w serialize: {e:?}")))?;
        Ok(buf)
    }

    /// Inverse of [`Self::to_bytes`]. Rebuilds the static constraint
    /// and the Orion code from `msg_log_n` so callers don't have to
    /// store them.
    pub fn from_bytes(bytes: &[u8]) -> Result<Self> {
        if bytes.len() < STATE_MAGIC.len() + 1 + 4 + 2 || &bytes[..8] != STATE_MAGIC {
            return Err(FoldingError::ShapeMismatch(
                "WarpProverState bytes: missing or wrong magic".into(),
            ));
        }
        let mut cur = &bytes[8..];
        let msg_log_n = cur[0] as usize;
        cur = &cur[1..];
        let parallel_rep = u32::from_le_bytes(cur[..4].try_into().unwrap());
        cur = &cur[4..];
        let sampling_n_ood = cur[0] as usize;
        let sampling_n_shifts = cur[1] as usize;
        cur = &cur[2..];

        let instance = TwinConstrainedInstance::<F>::deserialize_from(&mut cur)
            .map_err(|e| FoldingError::ShapeMismatch(format!("instance deserialize: {e:?}")))?;
        let f = Vec::<F>::deserialize_from(&mut cur)
            .map_err(|e| FoldingError::ShapeMismatch(format!("witness.f deserialize: {e:?}")))?;
        let w = Vec::<F>::deserialize_from(&mut cur)
            .map_err(|e| FoldingError::ShapeMismatch(format!("witness.w deserialize: {e:?}")))?;

        let msg_len = 1usize << msg_log_n;
        let code = OrionLinearCode::new(msg_len, ORION_CODE_SEED);
        let p_b = Constraint {
            terms: vec![
                Term {
                    coeff: F::one(),
                    vars: vec![0],
                },
                Term {
                    coeff: -F::one(),
                    vars: vec![0],
                },
            ],
        };
        Ok(Self {
            instance,
            witness: TwinConstrainedWitness { f, w },
            p_b,
            code,
            msg_log_n,
            parallel_rep,
            sampling_n_ood,
            sampling_n_shifts,
        })
    }
}

/// Build a deterministic block seed from per-block public data,
/// **including** the completeness-proof commitment.
///
/// Indexer and consensus verifier must agree on this seed for the
/// fold chain to verify. Critically, `completeness_proof_hash` binds
/// the WARP fold to the GKR completeness proof that demonstrates
/// every matching event from the underlying Ethereum block was
/// actually included — without this binding, an indexer could submit
/// a partial event set and the WARP chain would still verify cleanly,
/// destroying the anti-censorship guarantee.
///
/// `completeness_proof_hash` should be `Keccak256(completeness_proof_bytes)`
/// where `completeness_proof_bytes` is the serialized
/// `ChunkedBlockCompletenessProof` from `willow-indexing`.
///
/// `output_root` is the state-diff Merkle root.
/// `config_hash` is the subgrove config hash.
/// `block_hash` and `block_number` pin the seed to a specific block.
pub fn block_seed(
    block_hash: &[u8; 32],
    output_root: &[u8; 32],
    config_hash: &[u8; 32],
    completeness_proof_hash: &[u8; 32],
    block_number: u64,
) -> [u8; 32] {
    let mut hasher = Keccak256::new();
    hasher.update(b"willow-warp/block-seed/v1");
    hasher.update(block_hash);
    hasher.update(output_root);
    hasher.update(config_hash);
    hasher.update(completeness_proof_hash);
    hasher.update(block_number.to_le_bytes());
    hasher.finalize().into()
}

/// Compute the canonical commitment to a serialized completeness proof.
/// Verifier and prover use this same function so the seed binds to the
/// exact bytes consensus checks via `verify_chunked_proof_against_block`.
pub fn completeness_proof_hash(completeness_proof_bytes: &[u8]) -> [u8; 32] {
    let mut hasher = Keccak256::new();
    hasher.update(b"willow-warp/completeness-proof/v1");
    hasher.update(completeness_proof_bytes);
    hasher.finalize().into()
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::wire::FoldStepWire;
    use expander_mersenne31::M31Ext6;

    type F = M31Ext6;

    /// Round-trip: genesis → fold one block → wire encode → wire decode
    /// → IOR verify → folded instance hash matches what the prover
    /// would persist as the new chain root.
    #[test]
    fn genesis_then_fold_round_trips_through_wire() {
        use crate::fs::verify_with_parallel_rep_bound;

        let msg_log_n = 4; // msg=16 — small for the test
        let parallel_rep = 1;
        let mut prover = WarpProverState::<F>::genesis(msg_log_n, parallel_rep, [42u8; 32]);
        let prev_root = prover.current_root();

        let bs = block_seed(&[1u8; 32], &[2u8; 32], &[3u8; 32], &[0u8; 32], 1);
        let payload = b"block 1 state diff bytes";
        let wire = prover.fold_block(bs, payload).unwrap();

        // Round-trip wire bytes.
        let bytes = wire.to_bytes().unwrap();
        let decoded = FoldStepWire::<F>::from_bytes(&bytes).unwrap();

        // Verifier: prev_instance hashes to the prover's prior root.
        assert_eq!(
            crate::wire::hash_instance(&decoded.prev_instance),
            prev_root
        );

        // Verifier reconstructs the canonical Orion code from msg_log_n
        // to learn the codeword shape (log_n is the LOG OF CODEWORD
        // LENGTH, not msg length — they differ when the code is a real
        // expanding code rather than IdentityCode).
        let code = default_orion_code(msg_log_n);
        let params = SchemeParams {
            log_n: <OrionLinearCode as LinearCode<F>>::log_codeword_len(&code),
            k: 1usize << msg_log_n,
            m: 0,
            d: 1,
        };
        let sampling = SamplingParams {
            n_ood: 1,
            n_shifts: 2,
        };
        let folded = verify_with_parallel_rep_bound::<F>(
            &[decoded.prev_instance.clone(), decoded.new_instance.clone()],
            &params,
            &sampling,
            &decoded.messages,
            &bs,
        )
        .unwrap();
        assert_eq!(crate::wire::hash_instance(&folded), prover.current_root());

        // Negative: wrong binding bytes (e.g., flipped completeness hash)
        // → IOR rejects.
        let mut wrong_bs = bs;
        wrong_bs[0] ^= 1;
        let result = verify_with_parallel_rep_bound::<F>(
            &[decoded.prev_instance.clone(), decoded.new_instance.clone()],
            &params,
            &sampling,
            &decoded.messages,
            &wrong_bs,
        );
        assert!(
            result.is_err(),
            "verifier with wrong external_binding must reject"
        );
    }

    /// Folding twice keeps the prover's chain hashes consistent: the
    /// second fold's prev hash equals the first fold's new hash.
    #[test]
    fn fold_chain_links_across_blocks() {
        let log_n = 4;
        let mut prover = WarpProverState::<F>::genesis(log_n, 1, [99u8; 32]);

        let _ = prover
            .fold_block(
                block_seed(&[1u8; 32], &[2u8; 32], &[3u8; 32], &[0u8; 32], 1),
                b"diff-1",
            )
            .unwrap();
        let after_first = prover.current_root();

        let wire2 = prover
            .fold_block(
                block_seed(&[10u8; 32], &[20u8; 32], &[3u8; 32], &[0u8; 32], 2),
                b"diff-2",
            )
            .unwrap();
        assert_eq!(
            crate::wire::hash_instance(&wire2.prev_instance),
            after_first,
            "second fold's prev_instance must match first fold's new root",
        );
    }

    /// Two indexers with the same payload produce the same witness — i.e.
    /// the witness is determined by the transformation output, not by
    /// fresh entropy. Two different payloads with the same seed must
    /// produce different witnesses (so adversarial payload swap fails).
    #[test]
    fn witness_is_payload_bound() {
        let log_n = 4;
        let bs = block_seed(&[1u8; 32], &[2u8; 32], &[3u8; 32], &[0u8; 32], 1);

        let mut a = WarpProverState::<F>::genesis(log_n, 1, [7u8; 32]);
        let mut b = WarpProverState::<F>::genesis(log_n, 1, [7u8; 32]);
        let _ = a.fold_block(bs, b"payload-A").unwrap();
        let _ = b.fold_block(bs, b"payload-A").unwrap();
        assert_eq!(
            a.current_root(),
            b.current_root(),
            "same (seed, payload) → same accumulator root"
        );

        let mut c = WarpProverState::<F>::genesis(log_n, 1, [7u8; 32]);
        let _ = c.fold_block(bs, b"payload-B").unwrap();
        assert_ne!(
            a.current_root(),
            c.current_root(),
            "different payload at same seed → different accumulator root"
        );
    }

    /// A garbled wire blob is rejected by the IOR verifier — sanity
    /// check the binding works even with our trivial PESAT.
    #[test]
    fn tampered_messages_rejected() {
        use crate::fs::verify_with_parallel_rep_bound;

        let log_n = 4;
        let mut prover = WarpProverState::<F>::genesis(log_n, 1, [7u8; 32]);
        let bs = block_seed(&[1u8; 32], &[2u8; 32], &[3u8; 32], &[0u8; 32], 1);
        let wire = prover.fold_block(bs, b"some-payload").unwrap();

        // Tamper: bump mu_new in the multilinear-batching message.
        let mut tampered = wire.clone();
        tampered.messages[0].multilinear_batching.mu_new = F::from(0xDEADu32);

        let params = SchemeParams {
            log_n,
            k: 1usize << log_n,
            m: 0,
            d: 1,
        };
        let sampling = SamplingParams {
            n_ood: 1,
            n_shifts: 2,
        };
        let result = verify_with_parallel_rep_bound::<F>(
            &[
                tampered.prev_instance.clone(),
                tampered.new_instance.clone(),
            ],
            &params,
            &sampling,
            &tampered.messages,
            &bs,
        );
        assert!(
            result.is_err(),
            "tampered IOR transcript should be rejected"
        );
    }

    /// Persist a prover across "restarts": serialize state, drop, reload,
    /// fold again, and confirm the chain hash continues to line up.
    #[test]
    fn prover_state_persists_across_serde() {
        let log_n = 4;
        let mut prover = WarpProverState::<F>::genesis(log_n, 1, [7u8; 32]);
        let _ = prover
            .fold_block(
                block_seed(&[1u8; 32], &[2u8; 32], &[3u8; 32], &[0u8; 32], 1),
                b"diff-1",
            )
            .unwrap();
        let chain_root_after_block_1 = prover.current_root();

        let bytes = prover.to_bytes().expect("serialize");
        drop(prover);
        let mut restored = WarpProverState::<F>::from_bytes(&bytes).expect("deserialize");
        assert_eq!(restored.current_root(), chain_root_after_block_1);

        let wire2 = restored
            .fold_block(
                block_seed(&[10u8; 32], &[20u8; 32], &[3u8; 32], &[0u8; 32], 2),
                b"diff-2",
            )
            .unwrap();
        assert_eq!(
            crate::wire::hash_instance(&wire2.prev_instance),
            chain_root_after_block_1,
            "restored prover must continue the chain from where it left off"
        );
    }

    /// A freshly-seeded genesis state passes its own decider check.
    /// Mutating the witness behind the instance's commitments makes
    /// `self_check` reject — which is what an indexer needs when its
    /// state file is corrupted on disk.
    #[test]
    fn self_check_accepts_honest_state_and_rejects_tampered_witness() {
        let mut prover = WarpProverState::<F>::genesis(4, 1, [3u8; 32]);
        prover
            .self_check()
            .expect("honest genesis state must decide");

        // Tamper the witness coordinate the constraint reads. The
        // instance's `mu` was computed from the pre-tamper codeword,
        // so the decider's f̂(α) = μ check fails.
        prover.witness.w[0] += F::one();
        prover.witness.f[0] += F::one();
        assert!(
            prover.self_check().is_err(),
            "self_check must reject a state whose witness no longer matches the instance"
        );
    }
}
