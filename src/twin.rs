//! Twin-constrained code relation (WARP Definition 5.7).
//!
//! The relation accumulated by WARP. An instance claims that a
//! codeword `u ∈ C` simultaneously satisfies a multilinear-evaluation
//! constraint `û(α) = μ` and a "bundled" polynomial constraint
//! `P_b(β, C⁻¹(u)) = η` on its preimage witness.
//!
//! Type generics:
//! - `W` is the witness/codeword field (e.g., `M31Ext3` for the
//!   bench fast-path, or the same as `C` for the single-field paths
//!   covered by tests).
//! - `C` is the challenge field, with `C: Field + Mul<W, Output=C>`.
//!   In particular `α, μ, β, η, γ, τ, ω, …` all live in `C`.
//!
//! For the single-field case (`W = C`), `Mul<W, Output=C>` reduces to
//! `Mul<Self, Output=Self>` which is already part of `Field`, so the
//! existing tests work unchanged.

use std::ops::Mul;

use expander_arith::Field;

use crate::Constraint;

/// The instance part of a twin-constrained relation element. All
/// coordinates live in the challenge field `C`. A Merkle root binds
/// the codeword `f`; the verifier uses it to authenticate shift-query
/// openings in Construction 7.2 and the decider re-hashes the
/// committed codeword to verify consistency.
#[derive(Clone, Debug, PartialEq, Eq, serdes::ExpSerde)]
pub struct TwinConstrainedInstance<C: Field + serdes::ExpSerde> {
    /// Evaluation point for the codeword's MLE. `α ∈ C^{log n}`.
    pub alpha: Vec<C>,
    /// Claimed `û(α) = μ`.
    pub mu: C,
    /// Evaluation point for the bundled PESAT constraint. `β ∈ C^m`.
    pub beta: Vec<C>,
    /// Claimed `P_b(β, w) = η` where `w = C⁻¹(u)`.
    pub eta: C,
    /// Keccak-256 Merkle root committing to the codeword `f`.
    /// Set by Construction 5.10 (initial commit) and re-set after
    /// every fold by Construction 7.2 (re-commit folded codeword).
    pub merkle_root: crate::merkle::Digest32,
}

/// The witness part: the codeword and its preimage witness, both in
/// the witness field `W`. After a fold step the resulting witness is
/// `TwinConstrainedWitness<C>` (since fold combines elements via a
/// `C`-typed challenge `γ`).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct TwinConstrainedWitness<W: Field> {
    pub f: Vec<W>,
    pub w: Vec<W>,
}

/// The "bundled" PESAT constraint polynomial `P_b(β, w)`. Stored over
/// `C` because the bundling combines per-PESAT-constraint coefficients
/// with `eq(τ, ·)` factors, where `τ ∈ C^{log M}`. Polynomial
/// evaluation produces a `C` scalar.
pub type BundledConstraint<C> = Constraint<C>;

impl<C: Field> TwinConstrainedInstance<C> {
    /// Build a twin-constrained instance from its prover-side witness,
    /// computing `(μ, η)` honestly and committing to the codeword via
    /// BLAKE3-Merkle. Used by tests and by Construction 5.10 to seed
    /// the first accumulator.
    pub fn from_honest<W>(
        alpha: Vec<C>,
        beta: Vec<C>,
        p_b: &BundledConstraint<C>,
        witness: &TwinConstrainedWitness<W>,
    ) -> Self
    where
        W: Field + serdes::ExpSerde,
        C: Mul<W, Output = C> + From<W>,
    {
        let mu = mle_eval(&witness.f, &alpha);
        let z: Vec<C> = beta
            .iter()
            .copied()
            .chain(witness.w.iter().map(|wi| C::from(*wi)))
            .collect();
        let eta = p_b.evaluate(&z);
        let merkle_root = crate::merkle::MerkleTree::build(&witness.f).root();
        Self {
            alpha,
            mu,
            beta,
            eta,
            merkle_root,
        }
    }
}

/// Evaluate the multilinear extension of `f ∈ W^{2^ν}` at point
/// `r ∈ C^ν`. Cross-field by design: each inner-product term is
/// `eq(r, b) ∈ C` times `f[b] ∈ W`, summed in `C`.
pub fn mle_eval<W, C>(f: &[W], r: &[C]) -> C
where
    W: Field,
    C: Field + Mul<W, Output = C>,
{
    assert!(f.len().is_power_of_two(), "f must have power-of-two length");
    let nu = f.len().trailing_zeros() as usize;
    assert_eq!(r.len(), nu, "r must have length log₂(f.len())");

    let eq = build_eq_evals(r);
    mle_eval_with_eq(f, &eq)
}

/// Cross-field MLE eval given a precomputed `eq(r, ·)` table over `C`.
/// Reusable when evaluating multiple `W`-typed polynomials at the same
/// `C`-typed point — saves rebuilding the eq vector.
pub fn mle_eval_with_eq<W, C>(f: &[W], eq: &[C]) -> C
where
    W: Field,
    C: Field + Mul<W, Output = C>,
{
    debug_assert_eq!(f.len(), eq.len());
    f.iter()
        .zip(eq.iter())
        .fold(C::zero(), |acc, (fi, ei)| acc + *ei * *fi)
}

/// Build the vector `eq(r, b)` for `b ∈ {0,1}^{|r|}`, indexed in
/// little-endian order (`b = Σ bit_i · 2^i`). All arithmetic is in
/// `C` since `r ∈ C^ν`.
pub fn build_eq_evals<C: Field>(r: &[C]) -> Vec<C> {
    let mut evals = vec![C::zero(); 1 << r.len()];
    evals[0] = C::one();
    let mut cur_len = 1;
    for ri in r {
        for j in 0..cur_len {
            let product = evals[j] * *ri;
            evals[j + cur_len] = product;
            evals[j] -= product;
        }
        cur_len <<= 1;
    }
    evals
}

/// Scalar `eq(a, b) = Π_i (a_i·b_i + (1−a_i)(1−b_i))` over a single
/// field. Used for the `eq*(α_new) · μ_new` final-claim factor in
/// Construction 8.2.
pub fn eq_scalar<F: Field>(a: &[F], b: &[F]) -> F {
    assert_eq!(a.len(), b.len());
    a.iter()
        .zip(b.iter())
        .map(|(ai, bi)| *ai * *bi + (F::one() - *ai) * (F::one() - *bi))
        .fold(F::one(), |acc, t| acc * t)
}

#[cfg(test)]
mod tests {
    use super::*;
    use expander_mersenne31::M31Ext6;

    type F = M31Ext6;
    fn f(n: u32) -> F {
        F::from(n)
    }

    #[test]
    fn mle_eval_recovers_hypercube_values() {
        // f over {0,1}^2: indexed as [f(00), f(10), f(01), f(11)]
        //                                f=3,   f=5,   f=7,   f=11
        let vals = vec![f(3), f(5), f(7), f(11)];
        assert_eq!(mle_eval::<F, F>(&vals, &[f(0), f(0)]), f(3));
        assert_eq!(mle_eval::<F, F>(&vals, &[f(1), f(0)]), f(5));
        assert_eq!(mle_eval::<F, F>(&vals, &[f(0), f(1)]), f(7));
        assert_eq!(mle_eval::<F, F>(&vals, &[f(1), f(1)]), f(11));
    }

    #[test]
    fn mle_eval_at_midpoint_linear_combination() {
        // At (1/2, 1/2), MLE equals the average of all hypercube values.
        let vals = vec![f(3), f(5), f(7), f(11)];
        let half = f(2).inv().unwrap();
        let expected = (f(3) + f(5) + f(7) + f(11)) * f(4).inv().unwrap();
        assert_eq!(mle_eval::<F, F>(&vals, &[half, half]), expected);
    }

    #[test]
    fn eq_scalar_basic_cases() {
        // eq(a, a) = 1 for any a ∈ {0,1}^n
        assert_eq!(
            eq_scalar::<F>(&[f(0), f(1), f(1)], &[f(0), f(1), f(1)]),
            f(1)
        );
        // eq(a, b) = 0 when a, b differ on a Boolean coord
        assert_eq!(eq_scalar::<F>(&[f(0)], &[f(1)]), f(0));
    }

    #[test]
    fn from_honest_computes_mu_and_eta() {
        let p_b = BundledConstraint {
            terms: vec![crate::Term {
                coeff: f(1),
                vars: vec![0, 1], // β₀, w₀
            }],
        };
        let f_code = vec![f(2), f(4), f(6), f(8)];
        let w = vec![f(5)];
        let alpha = vec![f(0), f(1)]; // MLE at (0, 1) → index b=(0,1) → f_code[2] = 6
        let beta = vec![f(3)];

        let inst: TwinConstrainedInstance<F> = TwinConstrainedInstance::from_honest::<F>(
            alpha.clone(),
            beta.clone(),
            &p_b,
            &TwinConstrainedWitness { f: f_code, w },
        );
        assert_eq!(inst.alpha, alpha);
        assert_eq!(inst.beta, beta);
        assert_eq!(inst.mu, f(6));
        assert_eq!(inst.eta, f(3) * f(5));
    }

    #[test]
    fn dual_field_mle_eval_matches_single_field() {
        // Sanity: when the codeword is W = M31Ext3 lifted to C = M31Ext6
        // via `From<W>`, the cross-field MLE eval gives the same result
        // as a same-field eval after lifting. Confirms semantics.
        use expander_mersenne31::M31Ext3;
        let f_w: Vec<M31Ext3> = (1u32..=8).map(M31Ext3::from).collect();
        let r: Vec<M31Ext6> = (10u32..=12).map(M31Ext6::from).collect();
        let cross = mle_eval::<M31Ext3, M31Ext6>(&f_w, &r);
        let f_c: Vec<M31Ext6> = f_w.iter().map(|x| M31Ext6::from(*x)).collect();
        let same = mle_eval::<M31Ext6, M31Ext6>(&f_c, &r);
        assert_eq!(cross, same);
    }
}
