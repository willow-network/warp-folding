//! WARP Construction 7.2 — Codeword batching IOR.
//!
//! Takes the output of Construction 6.3 (a single twin-constrained
//! instance + its codeword `f`) and produces a batched multi-point
//! evaluation claim by sampling `s` out-of-domain points and `t`
//! in-domain shift-query positions. The output feeds Construction 8.2,
//! which collapses all `r = 1 + s + t` evaluation claims back to a
//! single `f̂(α) = μ` claim.
//!
//! Phase 2 note: the full scheme inserts a Merkle commitment to `f`
//! before OOD sampling so that `f` is bound before the prover sees
//! challenges. We defer that to step 8 (BCS + Fiat-Shamir wiring) —
//! here, `f` is passed in the clear between prover and verifier, and
//! the soundness of the multi-point setup is guaranteed by the
//! subsequent Construction 8.2 sumcheck. Adding the Merkle layer does
//! not change the IOR-level math of 7.2, only the RO/transcript
//! wrapping.

use expander_arith::Field;

use crate::error::Result;
use crate::twin::{mle_eval, TwinConstrainedInstance, TwinConstrainedWitness};

/// Output of Construction 7.2: a list of `r = 1 + s + t`
/// multilinear-evaluation claims about `f̂`, plus the verifier's
/// batching challenge `ξ ∈ F^{log r}` and the Merkle root that
/// commits the codeword being claimed against.
#[derive(Clone, Debug, PartialEq, Eq, serdes::ExpSerde)]
pub struct BatchedEvalClaims<F: Field + serdes::ExpSerde> {
    pub zetas: Vec<Vec<F>>,
    pub nus: Vec<F>,
    pub xi: Vec<F>,
    pub beta: Vec<F>,
    pub eta: F,
    /// Merkle root committing to the codeword. Set by the prover in
    /// `prove`, propagated to the next IOR (8.2) so the final twin-
    /// constrained instance carries it forward.
    pub merkle_root: crate::merkle::Digest32,
}

/// Prover's Construction 7.2 message: codeword Merkle root, OOD evals,
/// shift-query values, and Merkle paths authenticating each shift-
/// query value against the root.
#[derive(Clone, Debug, PartialEq, Eq, serdes::ExpSerde)]
pub struct CodewordBatchingMsg<F: Field + serdes::ExpSerde> {
    /// Merkle root committing to the codeword `f`. Sent before the
    /// verifier samples OOD points and shift queries.
    pub merkle_root: crate::merkle::Digest32,
    pub ood_evals: Vec<F>,
    pub shift_values: Vec<F>,
    /// One Merkle path per shift-query position.
    pub shift_paths: Vec<crate::merkle::MerklePath>,
}

/// Verifier-side challenges for Construction 7.2. These would be
/// squeezed from the transcript under Fiat-Shamir; for the Phase 2
/// IOR-level interface they are passed in.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CodewordBatchingChallenges<F: Field> {
    /// `s` OOD sample points, each in F^{log n}.
    pub ood_points: Vec<Vec<F>>,
    /// `t` in-domain shift-query positions in `[0, n)`.
    pub shift_queries: Vec<usize>,
    /// Batching challenge `ξ ∈ F^{log r}`.
    pub xi: Vec<F>,
}

/// Run Construction 7.2 as prover.
pub fn prove<F: Field + serdes::ExpSerde>(
    instance: &TwinConstrainedInstance<F>,
    witness: &TwinConstrainedWitness<F>,
    challenges: &CodewordBatchingChallenges<F>,
) -> Result<(BatchedEvalClaims<F>, CodewordBatchingMsg<F>)> {
    let log_n = instance.alpha.len();

    let ood_evals: Vec<F> = challenges
        .ood_points
        .iter()
        .map(|z| mle_eval(&witness.f, z))
        .collect();
    let shift_values: Vec<F> = challenges
        .shift_queries
        .iter()
        .map(|&idx| witness.f[idx])
        .collect();

    // Build Merkle tree over the codeword and open at each shift query
    // position. The verifier checks each path against the resulting
    // root, which is propagated into BatchedEvalClaims.
    let tree = crate::merkle::MerkleTree::build(&witness.f);
    let merkle_root = tree.root();
    let shift_paths: Vec<crate::merkle::MerklePath> = challenges
        .shift_queries
        .iter()
        .map(|&idx| tree.open(idx))
        .collect();

    let claims = assemble_claims(
        instance,
        &challenges.ood_points,
        &challenges.shift_queries,
        &challenges.xi,
        &ood_evals,
        &shift_values,
        log_n,
        merkle_root,
    );

    Ok((
        claims,
        CodewordBatchingMsg {
            merkle_root,
            ood_evals,
            shift_values,
            shift_paths,
        },
    ))
}

/// Run Construction 7.2 as verifier. In Phase 2 the verifier accepts
/// the prover's OOD/shift values on faith — Construction 8.2 will bind
/// them via the batching sumcheck. Once the Merkle layer lands in
/// step 8, the shift values will additionally be checked against the
/// commitment's openings.
pub fn verify<F: Field + serdes::ExpSerde>(
    instance: &TwinConstrainedInstance<F>,
    challenges: &CodewordBatchingChallenges<F>,
    msg: &CodewordBatchingMsg<F>,
) -> Result<BatchedEvalClaims<F>> {
    let merkle_root = msg.merkle_root;
    use crate::error::FoldingError;

    if msg.ood_evals.len() != challenges.ood_points.len() {
        return Err(FoldingError::ShapeMismatch(format!(
            "ood_evals.len() = {}, expected s = {}",
            msg.ood_evals.len(),
            challenges.ood_points.len()
        )));
    }
    if msg.shift_values.len() != challenges.shift_queries.len() {
        return Err(FoldingError::ShapeMismatch(format!(
            "shift_values.len() = {}, expected t = {}",
            msg.shift_values.len(),
            challenges.shift_queries.len()
        )));
    }
    if msg.shift_paths.len() != challenges.shift_queries.len() {
        return Err(FoldingError::ShapeMismatch(format!(
            "shift_paths.len() = {}, expected t = {}",
            msg.shift_paths.len(),
            challenges.shift_queries.len()
        )));
    }
    let log_n = instance.alpha.len();
    let n = 1usize << log_n;

    // Authenticate every shift-query value against the codeword's
    // Merkle root. Without this check, a cheating prover could
    // declare arbitrary `shift_values` and the sumcheck batching in
    // 8.2 wouldn't catch it (the values are just accepted on faith).
    for ((leaf, path), &idx) in msg
        .shift_values
        .iter()
        .zip(msg.shift_paths.iter())
        .zip(challenges.shift_queries.iter())
    {
        if !crate::merkle::verify_path(&merkle_root, leaf, idx, n, path) {
            return Err(FoldingError::ShapeMismatch(format!(
                "Merkle path verification failed for shift query at index {idx}"
            )));
        }
    }

    let r = 1 + challenges.ood_points.len() + challenges.shift_queries.len();
    let expected_log_r = log2_exact(r)
        .ok_or_else(|| FoldingError::ShapeMismatch(format!("r = {r} must be a power of two")))?;
    if challenges.xi.len() != expected_log_r {
        return Err(FoldingError::ShapeMismatch(format!(
            "xi.len() = {}, expected log r = {}",
            challenges.xi.len(),
            expected_log_r
        )));
    }

    Ok(assemble_claims(
        instance,
        &challenges.ood_points,
        &challenges.shift_queries,
        &challenges.xi,
        &msg.ood_evals,
        &msg.shift_values,
        log_n,
        merkle_root,
    ))
}

#[allow(clippy::too_many_arguments)]
fn assemble_claims<F: Field>(
    instance: &TwinConstrainedInstance<F>,
    ood_points: &[Vec<F>],
    shift_queries: &[usize],
    xi: &[F],
    ood_evals: &[F],
    shift_values: &[F],
    log_n: usize,
    merkle_root: crate::merkle::Digest32,
) -> BatchedEvalClaims<F> {
    let mut zetas = Vec::with_capacity(1 + ood_points.len() + shift_queries.len());
    zetas.push(instance.alpha.clone());
    for zeta in ood_points {
        zetas.push(zeta.clone());
    }
    for &idx in shift_queries {
        zetas.push(index_to_boolean_vector::<F>(idx, log_n));
    }

    let mut nus = Vec::with_capacity(zetas.len());
    nus.push(instance.mu);
    nus.extend_from_slice(ood_evals);
    nus.extend_from_slice(shift_values);

    BatchedEvalClaims {
        zetas,
        nus,
        xi: xi.to_vec(),
        beta: instance.beta.clone(),
        eta: instance.eta,
        merkle_root,
    }
}

fn index_to_boolean_vector<F: Field>(mut idx: usize, nbits: usize) -> Vec<F> {
    let mut out = Vec::with_capacity(nbits);
    for _ in 0..nbits {
        out.push(if idx & 1 == 1 { F::one() } else { F::zero() });
        idx >>= 1;
    }
    out
}

fn log2_exact(n: usize) -> Option<usize> {
    if n.is_power_of_two() {
        Some(n.trailing_zeros() as usize)
    } else {
        None
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{BundledConstraint, Term};
    use expander_mersenne31::M31Ext6;

    type F = M31Ext6;
    fn f(n: u32) -> F {
        F::from(n)
    }

    /// A small twin-constrained instance (log n = 2) reused across tests.
    fn toy_instance() -> (TwinConstrainedInstance<F>, TwinConstrainedWitness<F>) {
        let p_b = BundledConstraint {
            terms: vec![Term {
                coeff: f(1),
                vars: vec![0, 1],
            }],
        };
        let wit = TwinConstrainedWitness {
            f: vec![f(2), f(4), f(6), f(8)],
            w: vec![f(5)],
        };
        let inst = TwinConstrainedInstance::from_honest(vec![f(0), f(1)], vec![f(3)], &p_b, &wit);
        (inst, wit)
    }

    #[test]
    fn round_trip_s1_t2_accepts() {
        // r = 1 + 1 + 2 = 4 → log r = 2, so xi has length 2.
        let (inst, wit) = toy_instance();
        let challenges = CodewordBatchingChallenges {
            ood_points: vec![vec![f(13), f(17)]],
            shift_queries: vec![0, 2],
            xi: vec![f(19), f(23)],
        };

        let (prover_claims, msg) = prove(&inst, &wit, &challenges).unwrap();
        let verifier_claims = verify(&inst, &challenges, &msg).unwrap();
        assert_eq!(prover_claims, verifier_claims);
    }

    #[test]
    fn claims_contain_alpha_first() {
        let (inst, wit) = toy_instance();
        let challenges = CodewordBatchingChallenges {
            ood_points: vec![vec![f(7), f(11)]],
            shift_queries: vec![1, 3],
            xi: vec![f(19), f(23)],
        };
        let (claims, _) = prove(&inst, &wit, &challenges).unwrap();
        assert_eq!(claims.zetas[0], inst.alpha);
        assert_eq!(claims.nus[0], inst.mu);
    }

    #[test]
    fn shift_values_match_codeword() {
        let (inst, wit) = toy_instance();
        let challenges = CodewordBatchingChallenges {
            ood_points: vec![vec![f(1), f(2)]],
            shift_queries: vec![0, 1, 2, 3],
            xi: vec![f(0), f(0), f(0)], // r = 6 — this is not a power of two and should fail validation
        };
        // r = 6 not a power of two → verifier should reject.
        let (_, msg) = prove(&inst, &wit, &challenges).unwrap();
        assert!(verify(&inst, &challenges, &msg).is_err());
    }

    #[test]
    fn shift_values_equal_codeword_indices() {
        let (inst, wit) = toy_instance();
        let challenges = CodewordBatchingChallenges {
            ood_points: vec![vec![f(1), f(2)]],
            shift_queries: vec![0, 3],
            xi: vec![f(0), f(0)],
        };
        let (claims, msg) = prove(&inst, &wit, &challenges).unwrap();
        assert_eq!(msg.shift_values, vec![wit.f[0], wit.f[3]]);
        assert_eq!(claims.nus[2], wit.f[0]); // index 2 = first shift query
        assert_eq!(claims.nus[3], wit.f[3]);
    }

    #[test]
    fn ood_evals_match_mle_of_codeword() {
        let (inst, wit) = toy_instance();
        let challenges = CodewordBatchingChallenges {
            ood_points: vec![vec![f(7), f(11)], vec![f(13), f(17)]],
            shift_queries: vec![0], // r = 1 + 2 + 1 = 4, log r = 2
            xi: vec![f(19), f(23)],
        };
        let (claims, msg) = prove(&inst, &wit, &challenges).unwrap();
        assert_eq!(msg.ood_evals.len(), 2);
        assert_eq!(
            msg.ood_evals[0],
            mle_eval(&wit.f, &challenges.ood_points[0])
        );
        assert_eq!(
            msg.ood_evals[1],
            mle_eval(&wit.f, &challenges.ood_points[1])
        );
        assert_eq!(claims.nus[1], msg.ood_evals[0]);
        assert_eq!(claims.nus[2], msg.ood_evals[1]);
    }

    #[test]
    fn beta_and_eta_carry_through() {
        let (inst, wit) = toy_instance();
        let challenges = CodewordBatchingChallenges {
            ood_points: vec![vec![f(7), f(11)]],
            shift_queries: vec![0, 2],
            xi: vec![f(19), f(23)],
        };
        let (claims, _) = prove(&inst, &wit, &challenges).unwrap();
        assert_eq!(claims.beta, inst.beta);
        assert_eq!(claims.eta, inst.eta);
    }

    #[test]
    fn shape_mismatch_on_truncated_msg() {
        let (inst, wit) = toy_instance();
        let challenges = CodewordBatchingChallenges {
            ood_points: vec![vec![f(7), f(11)]],
            shift_queries: vec![0, 2],
            xi: vec![f(19), f(23)],
        };
        let (_, mut msg) = prove(&inst, &wit, &challenges).unwrap();
        msg.ood_evals.pop();
        assert!(verify(&inst, &challenges, &msg).is_err());
    }

    #[test]
    fn index_to_boolean_vector_roundtrip() {
        for idx in 0..8 {
            let bits = index_to_boolean_vector::<F>(idx, 3);
            let recovered: usize = bits
                .iter()
                .enumerate()
                .map(|(i, b)| if *b == f(1) { 1 << i } else { 0 })
                .sum();
            assert_eq!(recovered, idx);
        }
    }
}
