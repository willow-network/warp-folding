//! Wire format for transporting WARP fold-step proofs across the
//! Willow consensus boundary.
//!
//! The IOR types ([`FoldMessage`], [`TwinConstrainedInstance`]) carry
//! `ExpSerde` derives, so they round-trip through bytes individually.
//! `FoldStepWire` bundles everything a verifier needs into a single
//! length-prefixed blob: the prior accumulator instance, the new
//! contribution from this submission, and the parallel-rep messages.
//!
//! The verifier reconstructs the two-instance pair from
//! `(prev_instance, new_instance)`, calls `fs::verify_with_parallel_rep`
//! on `messages`, hashes the resulting folded instance, and compares
//! against the next-state root carried in `WarpProofData.public_inputs`.

use expander_arith::Field;
use serdes::ExpSerde;

use crate::constr_9_4::FoldMessage;
use crate::error::{FoldingError, Result};
use crate::twin::TwinConstrainedInstance;

/// All the data the verifier needs to check one WARP fold-step
/// submission. Wire-encoded via `expander-serdes`.
#[derive(Clone, Debug, ExpSerde)]
pub struct FoldStepWire<F: Field + ExpSerde> {
    /// Accumulator instance the prover claims to have folded *into*.
    /// Hashed and compared against the per-subgrove stored
    /// `prev_instance_root` so the chain doesn't fork.
    pub prev_instance: TwinConstrainedInstance<F>,
    /// New contribution derived from the just-indexed block. The
    /// verifier reconstructs this independently from the submission's
    /// public inputs (block_range, output_root, …) and checks it
    /// matches what the prover sent.
    pub new_instance: TwinConstrainedInstance<F>,
    /// Parallel-rep IOR messages, one per repetition. Length must
    /// match the subgrove's parallel_rep parameter.
    pub messages: Vec<FoldMessage<F>>,
}

impl<F: Field + ExpSerde> FoldStepWire<F> {
    /// Encode the wire blob.
    pub fn to_bytes(&self) -> Result<Vec<u8>> {
        let mut buf = Vec::new();
        self.serialize_into(&mut buf)
            .map_err(|e| FoldingError::ShapeMismatch(format!("FoldStepWire serialize: {e:?}")))?;
        Ok(buf)
    }

    /// Decode a wire blob.
    pub fn from_bytes(bytes: &[u8]) -> Result<Self> {
        Self::deserialize_from(bytes)
            .map_err(|e| FoldingError::ShapeMismatch(format!("FoldStepWire deserialize: {e:?}")))
    }
}

/// Hash a `TwinConstrainedInstance` to a 32-byte commitment usable as a
/// chain-of-fold-steps root. Domain-separated Keccak over the ExpSerde
/// bytes — matches how the rest of WARP commits to the codeword/Merkle.
pub fn hash_instance<F: Field + ExpSerde>(instance: &TwinConstrainedInstance<F>) -> [u8; 32] {
    use sha3::{Digest, Keccak256};
    let mut buf = Vec::new();
    instance
        .serialize_into(&mut buf)
        .expect("ExpSerde Vec write cannot fail");
    let mut hasher = Keccak256::new();
    hasher.update(b"willow-warp/instance/v1");
    hasher.update(&buf);
    hasher.finalize().into()
}

#[cfg(test)]
mod tests {
    use super::*;
    use expander_mersenne31::M31Ext6;

    type F = M31Ext6;

    #[test]
    fn fold_step_wire_round_trips() {
        // Build a tiny well-formed fold-step blob and confirm
        // bytes → struct → bytes is stable.
        let inst = TwinConstrainedInstance::<F> {
            alpha: vec![F::from(1u32), F::from(2u32)],
            mu: F::from(3u32),
            beta: vec![F::from(4u32)],
            eta: F::from(5u32),
            merkle_root: [7u8; 32],
        };
        let wire = FoldStepWire {
            prev_instance: inst.clone(),
            new_instance: inst.clone(),
            messages: vec![],
        };
        let bytes = wire.to_bytes().unwrap();
        let decoded = FoldStepWire::<F>::from_bytes(&bytes).unwrap();
        assert_eq!(decoded.prev_instance.alpha, wire.prev_instance.alpha);
        assert_eq!(decoded.prev_instance.mu, wire.prev_instance.mu);
        assert_eq!(
            decoded.new_instance.merkle_root,
            wire.new_instance.merkle_root
        );
        assert!(decoded.messages.is_empty());
    }

    #[test]
    fn hash_instance_is_deterministic_and_distinguishing() {
        let a = TwinConstrainedInstance::<F> {
            alpha: vec![F::from(1u32)],
            mu: F::from(1u32),
            beta: vec![],
            eta: F::from(0u32),
            merkle_root: [0u8; 32],
        };
        let mut b = a.clone();
        b.mu = F::from(99u32);
        assert_eq!(hash_instance(&a), hash_instance(&a));
        assert_ne!(hash_instance(&a), hash_instance(&b));
    }
}
