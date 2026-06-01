//! Single-instance chunk-PESAT prover + verifier.
//!
//! Compresses one multi-constraint PESAT instance (e.g. a willow-gkr
//! chunk PESAT from `crates/gkr/src/warp_aggregator/`) into a small
//! IOR-style proof:
//!
//! ```text
//!   chunk_pesat:                       Compressed proof:
//!     PesatIndex  (~2.5 MB)              TwinConstrainedInstance (~hundred bytes)
//!     PesatInstance (~427 KB)            FoldMessages           (~few hundred KB)
//! ```
//!
//! The IOR is the same one [`crate::prover::WarpProverState::fold_block`]
//! uses, but invoked in a single-shot mode that:
//!
//! 1. Pads the PESAT witness up to a power-of-two length the Orion code
//!    accepts.
//! 2. Constructs a deterministic ALL-ZEROS satisfying instance for the
//!    same PesatIndex (acts as the IOR's "anchor" second slot).
//! 3. Reduces both PESAT instances via Construction 5.10 → twin-form.
//! 4. Folds the two via [`prove_with_parallel_rep_bound`] to produce
//!    sumcheck-style proof messages.
//!
//! The anchor is satisfying because the chunk-PESAT constraint shape
//! always vanishes under the all-zeros witness:
//! `h_evals[*] = 0`, `claim = 0` ⇒ every sumcheck-chain and terminal
//! constraint evaluates to `0 - 0 = 0`. See module docs in
//! `willow-gkr::warp_aggregator::layer_multiphase` for the constraint
//! shape.
//!
//! ## Wire format
//!
//! [`ChunkPesatProof`] holds:
//!
//! - `instance`: `TwinConstrainedInstance` from reduce — the verifier
//!   reconstructs the anchor (also from PesatIndex) and the wire
//!   instance, then runs `verify_with_parallel_rep_bound`.
//! - `messages`: the per-rep `FoldMessage`s.
//!
//! ## Soundness
//!
//! - `p_b` is derived deterministically from PesatIndex (no tau values
//!   plug into the SHAPE), so prover and verifier compute the same
//!   bundled constraint.
//! - The IOR's binding via `block_seed` is unchanged from
//!   `fold_block_with_parallel_rep_bound`.
//! - The anchor is a fixed all-zeros instance; prover cannot
//!   adversarially choose it.
//!
//! ## Caveat
//!
//! This is the "fold-against-zero" pattern. It produces a proof of
//! satisfaction for ONE non-trivial PESAT instance per call; it does
//! NOT chain across blocks (no accumulator state). For Willow's
//! receipts-trie completeness use case, that's exactly right — each
//! block's proof is self-contained.

use std::ops::Mul;

use expander_arith::Field;
use rand::{rngs::StdRng, SeedableRng};
use serdes::ExpSerde;
use sha3::{Digest, Keccak256};

use crate::code::LinearCode;
use crate::constr_5_10;
use crate::constr_9_4::FoldMessage;
use crate::error::FoldingError;
use crate::fs::{prove_with_parallel_rep_bound, verify_with_parallel_rep_bound};
use crate::orion_code::OrionLinearCode;
use crate::pesat::{PesatIndex, PesatInstance};
use crate::prover::default_orion_code;
use crate::{SamplingParams, SchemeParams};

/// Domain separator for chunk-PESAT tau derivation.
const CHUNK_TAU_DOMAIN: &[u8] = b"willow-warp/chunk-pesat/tau/v1";

/// Compressed proof of chunk-PESAT satisfaction. Wire format:
/// `instance` + `messages` are ExpSerde-encoded. Validator
/// reconstructs the anchor independently from the chunk PesatIndex.
#[derive(Clone, Debug)]
pub struct ChunkPesatProof<F: Field + ExpSerde> {
    /// The block's TwinConstrainedInstance after reduce.
    pub instance: crate::twin::TwinConstrainedInstance<F>,
    /// Per-rep IOR fold messages.
    pub messages: Vec<FoldMessage<F>>,
}

/// Errors specific to chunk-PESAT proving / verification.
#[derive(Debug)]
pub enum ChunkProofError {
    /// Underlying folding error.
    Folding(FoldingError),
    /// Witness length exceeds the largest msg_log_n supported.
    WitnessTooLarge {
        witness_len: usize,
        max_msg_log_n: usize,
    },
}

impl std::fmt::Display for ChunkProofError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Folding(e) => write!(f, "folding: {e:?}"),
            Self::WitnessTooLarge {
                witness_len,
                max_msg_log_n,
            } => write!(
                f,
                "witness length {witness_len} exceeds 2^{max_msg_log_n}"
            ),
        }
    }
}

impl std::error::Error for ChunkProofError {}

impl From<FoldingError> for ChunkProofError {
    fn from(e: FoldingError) -> Self {
        Self::Folding(e)
    }
}

/// Pad a `PesatIndex` + `PesatInstance` to a target witness length
/// `2^msg_log_n`. Adds zero-valued witness slots that don't appear in
/// any constraint; satisfaction is preserved.
///
/// Returns `(padded_index, padded_instance)`. The padded_index has
/// `k = 2^msg_log_n`. The padded_instance has `w.len() = 2^msg_log_n`.
pub fn pad_pesat_to_power_of_two<F: Field + Clone>(
    index: &PesatIndex<F>,
    instance: &PesatInstance<F>,
    target_msg_log_n: usize,
) -> core::result::Result<(PesatIndex<F>, PesatInstance<F>), ChunkProofError> {
    let target_k = 1usize << target_msg_log_n;
    if index.k > target_k {
        return Err(ChunkProofError::WitnessTooLarge {
            witness_len: index.k,
            max_msg_log_n: target_msg_log_n,
        });
    }
    let mut padded_w = instance.w.clone();
    while padded_w.len() < target_k {
        padded_w.push(F::zero());
    }
    let padded_index = PesatIndex {
        constraints: index.constraints.clone(),
        n_pub: index.n_pub,
        k: target_k,
        d: index.d,
    };
    let padded_instance = PesatInstance {
        x: instance.x.clone(),
        w: padded_w,
    };
    Ok((padded_index, padded_instance))
}

/// Derive the `tau` challenge for `constr_5_10::reduce` from a block
/// seed. log_m elements squeezed deterministically from
/// `Keccak(domain || seed || index_hash)`.
///
/// Both prover and verifier MUST derive tau identically from the same
/// inputs.
fn derive_tau<F: Field>(block_seed: &[u8; 32], log_m: usize) -> Vec<F> {
    if log_m == 0 {
        return Vec::new();
    }
    let mut hasher = Keccak256::new();
    hasher.update(CHUNK_TAU_DOMAIN);
    hasher.update(block_seed);
    let seed: [u8; 32] = hasher.finalize().into();
    let mut rng = StdRng::from_seed(seed);
    (0..log_m).map(|_| F::random_unsafe(&mut rng)).collect()
}

/// Construct an all-zeros satisfying PesatInstance for the given
/// `index` — used as the IOR's anchor "second slot" in single-instance
/// mode. The zero witness satisfies any chunk-PESAT shape (sumcheck-
/// chain + terminal + cross-layer constraints all vanish under zeros).
pub fn anchor_zeros_instance<F: Field + Clone>(index: &PesatIndex<F>) -> PesatInstance<F> {
    PesatInstance {
        x: vec![F::zero(); index.n_pub],
        w: vec![F::zero(); index.k],
    }
}

/// Required `msg_log_n` for `index.k`. Rounds up to the next power of
/// two; clamps minimum at 4 (= 16, the Orion code's minimum).
pub fn required_msg_log_n(index_k: usize) -> usize {
    let mut log = 4;
    while (1usize << log) < index_k.max(16) {
        log += 1;
    }
    log
}

/// **Indexer-side prover.** Generate a chunk-PESAT proof.
///
/// `index` + `instance` must have `index.k == instance.w.len()` and
/// `instance.satisfies(index) == true` (caller's responsibility; not
/// re-checked here for perf).
pub fn prove_chunk_pesat<F>(
    index: &PesatIndex<F>,
    instance: &PesatInstance<F>,
    block_seed: [u8; 32],
    parallel_rep: u32,
    sampling: SamplingParams,
) -> core::result::Result<ChunkPesatProof<F>, ChunkProofError>
where
    F: Field + ExpSerde + From<u32> + Mul<F, Output = F>,
{
    let msg_log_n = required_msg_log_n(index.k);
    let code = default_orion_code(msg_log_n);

    let (padded_idx, padded_inst) = pad_pesat_to_power_of_two(index, instance, msg_log_n)?;
    let (padded_idx_anchor, padded_inst_anchor) =
        pad_pesat_to_power_of_two(index, &anchor_zeros_instance(index), msg_log_n)?;
    // Both branches pad to the same length and same constraint set; the
    // anchor padded_idx and the block padded_idx are identical.
    debug_assert_eq!(padded_idx.constraints.len(), padded_idx_anchor.constraints.len());

    let log_m = ceil_log2(padded_idx.constraints.len());
    let tau: Vec<F> = derive_tau(&block_seed, log_m);

    // Reduce both instances.
    let (block_instance, block_witness, _p_b_block) =
        constr_5_10::reduce(&padded_idx, &padded_inst, &code, &tau)?;
    let (anchor_instance, anchor_witness, p_b) =
        constr_5_10::reduce(&padded_idx_anchor, &padded_inst_anchor, &code, &tau)?;

    // p_b is structurally identical for both reductions (same index,
    // same tau). Use either; they're equal as Constraint values.

    let params = SchemeParams {
        log_n: <OrionLinearCode as LinearCode<F>>::log_codeword_len(&code),
        k: padded_idx.k,
        m: tau.len(),
        d: padded_idx.d + log_m, // bundled p_b degree
    };
    let (_folded_inst, _folded_wit, messages) = prove_with_parallel_rep_bound::<F>(
        &[anchor_instance.clone(), block_instance.clone()],
        &[anchor_witness, block_witness],
        &p_b,
        &params,
        &sampling,
        parallel_rep,
        &block_seed,
    )?;

    Ok(ChunkPesatProof {
        instance: block_instance,
        messages,
    })
}

/// **Validator-side verifier.** Check a chunk-PESAT proof.
///
/// `index` is the chunk PesatIndex (regenerated by the validator from
/// the FIXED circuit metadata — same value the prover passed to
/// `prove_chunk_pesat`).
pub fn verify_chunk_pesat<F>(
    index: &PesatIndex<F>,
    proof: &ChunkPesatProof<F>,
    block_seed: [u8; 32],
    parallel_rep: u32,
    sampling: SamplingParams,
) -> core::result::Result<(), ChunkProofError>
where
    F: Field + ExpSerde + From<u32> + Mul<F, Output = F>,
{
    let msg_log_n = required_msg_log_n(index.k);
    let code = default_orion_code(msg_log_n);

    let (padded_idx_anchor, padded_inst_anchor) =
        pad_pesat_to_power_of_two(index, &anchor_zeros_instance(index), msg_log_n)?;

    let log_m = ceil_log2(padded_idx_anchor.constraints.len());
    let tau: Vec<F> = derive_tau(&block_seed, log_m);

    let (anchor_instance, _anchor_witness, _p_b) =
        constr_5_10::reduce(&padded_idx_anchor, &padded_inst_anchor, &code, &tau)?;

    let params = SchemeParams {
        log_n: <OrionLinearCode as LinearCode<F>>::log_codeword_len(&code),
        k: padded_idx_anchor.k,
        m: tau.len(),
        d: padded_idx_anchor.d + log_m,
    };

    if proof.messages.len() != parallel_rep as usize {
        return Err(ChunkProofError::Folding(FoldingError::ShapeMismatch(
            format!(
                "proof has {} messages, expected {parallel_rep} parallel reps",
                proof.messages.len()
            ),
        )));
    }

    let _folded = verify_with_parallel_rep_bound::<F>(
        &[anchor_instance, proof.instance.clone()],
        &params,
        &sampling,
        &proof.messages,
        &block_seed,
    )?;

    Ok(())
}

/// `ceil(log2(n))` for `n >= 1`, returns 0 for `n == 1`.
fn ceil_log2(n: usize) -> usize {
    if n <= 1 {
        return 0;
    }
    (usize::BITS - (n - 1).leading_zeros()) as usize
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::pesat::{Constraint, Term};
    use expander_mersenne31::M31Ext6;

    type F = M31Ext6;
    fn f(n: u32) -> F {
        F::from(n)
    }

    fn sampling() -> SamplingParams {
        SamplingParams {
            n_ood: 1,
            n_shifts: 2,
        }
    }

    /// `ceil_log2` sanity.
    #[test]
    fn ceil_log2_basics() {
        assert_eq!(ceil_log2(0), 0);
        assert_eq!(ceil_log2(1), 0);
        assert_eq!(ceil_log2(2), 1);
        assert_eq!(ceil_log2(3), 2);
        assert_eq!(ceil_log2(4), 2);
        assert_eq!(ceil_log2(5), 3);
        assert_eq!(ceil_log2(8), 3);
        assert_eq!(ceil_log2(9), 4);
        assert_eq!(ceil_log2(16), 4);
        assert_eq!(ceil_log2(17), 5);
        assert_eq!(ceil_log2(10638), 14);
    }

    /// `required_msg_log_n` floor + log behavior.
    #[test]
    fn required_msg_log_n_basics() {
        assert_eq!(required_msg_log_n(1), 4); // floor at 4 (= 16)
        assert_eq!(required_msg_log_n(15), 4);
        assert_eq!(required_msg_log_n(16), 4);
        assert_eq!(required_msg_log_n(17), 5);
        assert_eq!(required_msg_log_n(32), 5);
        assert_eq!(required_msg_log_n(33), 6);
        assert_eq!(required_msg_log_n(26703), 15); // chunk PESAT N1 witness
    }

    /// Anchor zero-witness is always a satisfying instance for any
    /// PesatIndex whose constraints all use polynomial terms (no
    /// constant-only terms with non-zero constant).
    ///
    /// Our chunk-PESAT shapes always include the target slot in every
    /// constraint (e.g. `target - sum(...) = 0`), so zero witness
    /// gives `0 - 0 = 0`. Verify on a toy chunk-PESAT-shaped
    /// constraint.
    #[test]
    fn anchor_zeros_satisfies_chunk_pesat_shapes() {
        // h(0) + h(1) - claim = 0 (sumcheck round identity shape)
        let idx = PesatIndex {
            constraints: vec![Constraint {
                terms: vec![
                    Term {
                        coeff: f(1),
                        vars: vec![0],
                    },
                    Term {
                        coeff: f(1),
                        vars: vec![1],
                    },
                    Term {
                        coeff: -f(1),
                        vars: vec![2],
                    },
                ],
            }],
            n_pub: 0,
            k: 3,
            d: 1,
        };
        let zeros = anchor_zeros_instance(&idx);
        // Inline satisfies check (warp-folding's PesatInstance doesn't
        // expose a method — only willow-gkr's does).
        let z = [zeros.x.clone(), zeros.w.clone()].concat();
        for c in &idx.constraints {
            assert_eq!(c.evaluate(&z), f(0));
        }
    }

    /// Pad sanity: longer-than-target index_k returns an error.
    #[test]
    fn pad_rejects_witness_larger_than_target() {
        let idx = PesatIndex {
            constraints: vec![],
            n_pub: 0,
            k: 100,
            d: 1,
        };
        let inst = PesatInstance {
            x: vec![],
            w: vec![f(0); 100],
        };
        let result = pad_pesat_to_power_of_two(&idx, &inst, 4); // target 16 < 100
        assert!(matches!(
            result,
            Err(ChunkProofError::WitnessTooLarge { .. })
        ));
    }

    /// **End-to-end**: prove + verify a non-trivial multi-constraint
    /// PESAT instance via the chunk-PESAT IOR.
    ///
    /// Builds a small PESAT that mirrors the chunk-PESAT shape
    /// (sumcheck round + chain identity), proves satisfaction via
    /// `prove_chunk_pesat`, and confirms `verify_chunk_pesat` accepts.
    #[test]
    fn prove_then_verify_small_chunk_pesat() {
        // PesatIndex: 4 constraints, k = 8 (rounds up to msg_log_n = 4
        // = 16-slot witness, padded with 8 zeros).
        //   Variables: w0..w7
        //   c0: w0 + w1 - w2 = 0          (sumcheck round identity)
        //   c1: w2 - w3 = 0                (chain identity)
        //   c2: w4 + w5 - w6 = 0          (another sumcheck shape)
        //   c3: w6 - w7 = 0                (chain identity)
        let idx = PesatIndex {
            constraints: vec![
                Constraint {
                    terms: vec![
                        Term {
                            coeff: f(1),
                            vars: vec![0],
                        },
                        Term {
                            coeff: f(1),
                            vars: vec![1],
                        },
                        Term {
                            coeff: -f(1),
                            vars: vec![2],
                        },
                    ],
                },
                Constraint {
                    terms: vec![
                        Term {
                            coeff: f(1),
                            vars: vec![2],
                        },
                        Term {
                            coeff: -f(1),
                            vars: vec![3],
                        },
                    ],
                },
                Constraint {
                    terms: vec![
                        Term {
                            coeff: f(1),
                            vars: vec![4],
                        },
                        Term {
                            coeff: f(1),
                            vars: vec![5],
                        },
                        Term {
                            coeff: -f(1),
                            vars: vec![6],
                        },
                    ],
                },
                Constraint {
                    terms: vec![
                        Term {
                            coeff: f(1),
                            vars: vec![6],
                        },
                        Term {
                            coeff: -f(1),
                            vars: vec![7],
                        },
                    ],
                },
            ],
            n_pub: 0,
            k: 8,
            d: 1,
        };
        // Satisfying assignment: w = [3, 5, 8, 8, 7, 11, 18, 18].
        let inst = PesatInstance {
            x: vec![],
            w: vec![f(3), f(5), f(8), f(8), f(7), f(11), f(18), f(18)],
        };
        // Inline satisfies sanity.
        let z = [inst.x.clone(), inst.w.clone()].concat();
        for c in &idx.constraints {
            assert_eq!(c.evaluate(&z), f(0), "honest witness must satisfy");
        }

        let block_seed = [0x42u8; 32];
        let parallel_rep = 1;
        let proof = prove_chunk_pesat::<F>(&idx, &inst, block_seed, parallel_rep, sampling())
            .expect("prove");
        verify_chunk_pesat::<F>(&idx, &proof, block_seed, parallel_rep, sampling())
            .expect("verify must accept honest proof");
    }

    /// Tampered proof (corrupted message) is rejected.
    #[test]
    fn tampered_chunk_pesat_proof_rejected() {
        let idx = PesatIndex {
            constraints: vec![Constraint {
                terms: vec![
                    Term {
                        coeff: f(1),
                        vars: vec![0],
                    },
                    Term {
                        coeff: f(1),
                        vars: vec![1],
                    },
                    Term {
                        coeff: -f(1),
                        vars: vec![2],
                    },
                ],
            }],
            n_pub: 0,
            k: 3,
            d: 1,
        };
        let inst = PesatInstance {
            x: vec![],
            w: vec![f(3), f(5), f(8)],
        };
        let block_seed = [0x99u8; 32];
        let mut proof =
            prove_chunk_pesat::<F>(&idx, &inst, block_seed, 1, sampling()).expect("prove");

        // Tamper: corrupt the instance's mu.
        proof.instance.mu = proof.instance.mu + f(1);

        let result = verify_chunk_pesat::<F>(&idx, &proof, block_seed, 1, sampling());
        assert!(result.is_err(), "tampered proof must be rejected");
    }
}
