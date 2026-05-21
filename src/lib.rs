//! warp-folding — WARP accumulation over M31Ext3 + Orion.
//!
//! Implements the accumulation scheme from Bünz, Chiesa, Fenzi, Wang,
//! "Linear-Time Accumulation Schemes" (eprint 2025/753, TCC 2025),
//! instantiated over the Polyhedra Expander M31 stack with
//! parallel-repetition r=2 for 128-bit soundness over M31Ext3.
//!
//! The production code path uses [`OrionLinearCode`] (vendored from
//! Polyhedra Expander; Xie–Zhang–Song 2022 with Druk–Ishai-14 distance
//! analysis). [`IdentityCode`] and [`SpielmanCode`] are kept for unit-
//! testing and as historical benchmark stubs respectively.

pub mod code;
pub mod constr_5_10;
pub mod constr_6_3;
pub mod constr_7_2;
pub mod constr_8_2;
pub mod constr_9_4;
#[cfg(feature = "cuda")]
pub mod cuda_kernels;
pub mod decider;
pub mod error;
pub mod fs;
pub mod merkle;
pub mod orion_code;
pub mod pesat;
pub mod prover;
pub mod transcript;
pub mod twin;
pub mod univariate;
pub mod wire;

#[doc(hidden)]
pub use code::SpielmanCode;
pub use code::{IdentityCode, LinearCode};
pub use constr_6_3::{prove_ell_2, verify_ell_2, SchemeParams, TwinPseudoBatchingMsg};
pub use constr_7_2::{BatchedEvalClaims, CodewordBatchingChallenges, CodewordBatchingMsg};
pub use constr_8_2::{MultilinearBatchingMsg, SumcheckRoundMsg};
pub use constr_9_4::{FoldChallenges, FoldMessage};
pub use error::{FoldingError, Result};
pub use fs::{
    prove_with_parallel_rep, prove_with_parallel_rep_bound, prove_with_transcript,
    verify_with_parallel_rep, verify_with_parallel_rep_bound, verify_with_transcript,
    SamplingParams,
};
pub use merkle::{verify_path, Digest32, MerklePath, MerkleTree};
pub use orion_code::{OrionLinearCode, ORION_CODE_PARAMETER_INSTANCE};
pub use pesat::{Constraint, PesatIndex, PesatInstance, Term};
pub use prover::{
    block_seed, completeness_proof_hash, default_orion_code, WarpProverState, ORION_CODE_SEED,
    WARP_INSTANCE_ROOT_BYTES,
};
pub use transcript::Transcript;
pub use twin::{
    build_eq_evals, eq_scalar, mle_eval, mle_eval_with_eq, BundledConstraint,
    TwinConstrainedInstance, TwinConstrainedWitness,
};
pub use univariate::UnivariatePoly;
pub use wire::{hash_instance, FoldStepWire};

/// Re-export the WARP field downstream crates verify against, so they
/// don't need to declare a separate `expander-mersenne31` dependency
/// just to spell out `M31Ext3` in a verifier path.
pub use expander_mersenne31::M31Ext3;
