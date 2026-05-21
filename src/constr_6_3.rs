//! WARP Construction 6.3 — Twin pseudo-batching IOR.
//!
//! Reduces ℓ twin-constrained instances of relation `R_C` to one,
//! via a log-ℓ-round outer sumcheck. This Phase 2 implementation
//! covers ℓ = 2 (one sumcheck round), which is sufficient for
//! pairwise historical-sync folding. Higher arities work identically
//! with log-ℓ rounds; the single-round case is just enough to prove
//! the end-to-end protocol.
//!
//! The sumcheck equation reduced is
//! `Σ_{I∈{0,1}} eq(τ,I) · Ĝ(F̂(I), ŵ(I), Â(I), B̂(I)) = σ⁽¹⁾`
//! where `Ĝ(F, W, A, B) = mle(F)(A) + ω·P_b(B, W)` and
//! `σ⁽¹⁾ = (1−τ)(μ₀ + ω·η₀) + τ(μ₁ + ω·η₁)`.
//!
//! Soundness is the MCA-proximity-gap argument of WARP §6.2 plus
//! standard polynomial-identity-lemma sumcheck soundness. Field-size
//! constraints are inherited from `warp-over-m31.md §4`.

use expander_arith::Field;

use crate::error::{FoldingError, Result};
use crate::twin::{mle_eval, BundledConstraint, TwinConstrainedInstance, TwinConstrainedWitness};
use crate::univariate::UnivariatePoly;

/// Prover's per-round message for Construction 6.3 at ℓ = 2.
#[derive(Clone, Debug, serdes::ExpSerde)]
pub struct TwinPseudoBatchingMsg<F: Field + serdes::ExpSerde> {
    /// Round polynomial ĥ(X), evaluations at X = 0, 1, …, degree.
    pub h: UnivariatePoly<F>,
    /// Prover-claimed MLE evaluation of the folded codeword at α_new.
    pub mu_new: F,
    /// Prover-claimed bundled-constraint value at (β_new, w_new).
    pub eta_new: F,
}

/// Fixed-per-scheme geometry used by both prover and verifier.
#[derive(Clone, Debug)]
pub struct SchemeParams {
    /// log₂(codeword length `n`).
    pub log_n: usize,
    /// Preimage-witness length `k`.
    pub k: usize,
    /// `m = log M + κ` — the β-coordinate count.
    pub m: usize,
    /// Total degree of the bundled constraint polynomial `P_b`.
    pub d: usize,
}

impl SchemeParams {
    /// Degree of the per-round sumcheck polynomial ĥ(X). See module
    /// docs: `1 + max(log n + 1, d)`.
    pub fn h_degree(&self) -> usize {
        1 + usize::max(self.log_n + 1, self.d)
    }
}

/// Run Construction 6.3 as prover on ℓ = 2 inputs.
///
/// Returns the folded instance/witness plus the sumcheck message the
/// verifier needs to check consistency.
pub fn prove_ell_2<F: Field>(
    instances: &[TwinConstrainedInstance<F>; 2],
    witnesses: &[TwinConstrainedWitness<F>; 2],
    p_b: &BundledConstraint<F>,
    params: &SchemeParams,
    tau: F,
    omega: F,
    gamma: F,
) -> Result<(
    TwinConstrainedInstance<F>,
    TwinConstrainedWitness<F>,
    TwinPseudoBatchingMsg<F>,
)> {
    validate_shapes(instances, witnesses, params)?;

    let degree = params.h_degree();
    let mut h_evals = Vec::with_capacity(degree + 1);
    for i in 0..=degree {
        let x = F::from(i as u32);
        h_evals.push(evaluate_h(instances, witnesses, p_b, params, tau, omega, x));
    }
    let h = UnivariatePoly { evals: h_evals };

    let (folded_inst, folded_wit) = fold_at(instances, witnesses, p_b, gamma);
    let msg = TwinPseudoBatchingMsg {
        h,
        mu_new: folded_inst.mu,
        eta_new: folded_inst.eta,
    };

    Ok((folded_inst, folded_wit, msg))
}

/// Run Construction 6.3 as verifier on ℓ = 2 inputs.
pub fn verify_ell_2<F: Field>(
    instances: &[TwinConstrainedInstance<F>; 2],
    params: &SchemeParams,
    tau: F,
    omega: F,
    gamma: F,
    msg: &TwinPseudoBatchingMsg<F>,
) -> Result<TwinConstrainedInstance<F>> {
    let expected_degree = params.h_degree();
    if msg.h.degree() != expected_degree {
        return Err(FoldingError::DegreeExceeded {
            expected: expected_degree,
            actual: msg.h.degree(),
        });
    }

    let sigma_1 = (F::one() - tau) * (instances[0].mu + omega * instances[0].eta)
        + tau * (instances[1].mu + omega * instances[1].eta);
    let h_at_0 = msg.h.eval_at_0();
    let h_at_1 = msg.h.eval_at_1();
    if h_at_0 + h_at_1 != sigma_1 {
        return Err(FoldingError::ShapeMismatch(
            "round polynomial ĥ fails ĥ(0) + ĥ(1) = σ⁽¹⁾".into(),
        ));
    }

    let eq_tau_gamma = tau * gamma + (F::one() - tau) * (F::one() - gamma);
    let expected_h_at_gamma = eq_tau_gamma * (msg.mu_new + omega * msg.eta_new);
    let actual_h_at_gamma = msg.h.evaluate(gamma);
    if actual_h_at_gamma != expected_h_at_gamma {
        return Err(FoldingError::ShapeMismatch(
            "round polynomial ĥ fails consistency ĥ(γ) = eq(τ,γ)·(μ_new + ω·η_new)".into(),
        ));
    }

    let alpha_new = linear_interp(&instances[0].alpha, &instances[1].alpha, gamma);
    let beta_new = linear_interp(&instances[0].beta, &instances[1].beta, gamma);
    // 6.3's verifier doesn't have witness access; the codeword's new
    // Merkle root is set by Construction 7.2 when it commits to the
    // folded codeword. Placeholder zero root here.
    Ok(TwinConstrainedInstance {
        alpha: alpha_new,
        mu: msg.mu_new,
        beta: beta_new,
        eta: msg.eta_new,
        merkle_root: [0u8; 32],
    })
}

/// Compute ĥ(X) at a single X value, by expanding the summand
/// definition: `eq(τ, X) · [mle(F̂(X))(Â(X)) + ω · P_b(B̂(X), ŵ(X))]`.
pub(crate) fn evaluate_h<F: Field>(
    instances: &[TwinConstrainedInstance<F>; 2],
    witnesses: &[TwinConstrainedWitness<F>; 2],
    p_b: &BundledConstraint<F>,
    _params: &SchemeParams,
    tau: F,
    omega: F,
    x: F,
) -> F {
    let w_x = linear_interp(&witnesses[0].w, &witnesses[1].w, x);
    let a_x = linear_interp(&instances[0].alpha, &instances[1].alpha, x);
    let b_x = linear_interp(&instances[0].beta, &instances[1].beta, x);

    // Use MLE linearity to skip allocating f_x = (1−x)f₀ + x·f₁ —
    // mle((1−x)f₀ + x·f₁, a_x) = (1−x)·mle(f₀, a_x) + x·mle(f₁, a_x),
    // and both inner sums share the same `eq(a_x, ·)` table.
    use crate::twin::{build_eq_evals, mle_eval_with_eq};
    let eq_at_ax = build_eq_evals(&a_x);
    let mle_f0 = mle_eval_with_eq(&witnesses[0].f, &eq_at_ax);
    let mle_f1 = mle_eval_with_eq(&witnesses[1].f, &eq_at_ax);
    let mle_f_at_a = (F::one() - x) * mle_f0 + x * mle_f1;

    let p_b_val = {
        let z: Vec<F> = b_x.iter().chain(w_x.iter()).copied().collect();
        p_b.evaluate(&z)
    };
    let g = mle_f_at_a + omega * p_b_val;

    let eq_tau_x = tau * x + (F::one() - tau) * (F::one() - x);
    eq_tau_x * g
}

/// Fold two instances/witnesses at point γ via linear interpolation.
pub(crate) fn fold_at<F: Field>(
    instances: &[TwinConstrainedInstance<F>; 2],
    witnesses: &[TwinConstrainedWitness<F>; 2],
    p_b: &BundledConstraint<F>,
    gamma: F,
) -> (TwinConstrainedInstance<F>, TwinConstrainedWitness<F>) {
    let f_new = linear_interp(&witnesses[0].f, &witnesses[1].f, gamma);
    let w_new = linear_interp(&witnesses[0].w, &witnesses[1].w, gamma);
    let alpha_new = linear_interp(&instances[0].alpha, &instances[1].alpha, gamma);
    let beta_new = linear_interp(&instances[0].beta, &instances[1].beta, gamma);

    let mu_new = mle_eval(&f_new, &alpha_new);
    let eta_new = {
        let z: Vec<F> = beta_new.iter().chain(w_new.iter()).copied().collect();
        p_b.evaluate(&z)
    };

    (
        TwinConstrainedInstance {
            alpha: alpha_new,
            mu: mu_new,
            beta: beta_new,
            eta: eta_new,
            // Placeholder; the real root is set by Construction 7.2
            // when it builds the Merkle tree over the folded codeword.
            merkle_root: [0u8; 32],
        },
        TwinConstrainedWitness { f: f_new, w: w_new },
    )
}

/// `(1 − t) · v0 + t · v1`, element-wise.
fn linear_interp<F: Field>(v0: &[F], v1: &[F], t: F) -> Vec<F> {
    assert_eq!(v0.len(), v1.len());
    v0.iter()
        .zip(v1.iter())
        .map(|(a, b)| (F::one() - t) * *a + t * *b)
        .collect()
}

fn validate_shapes<F: Field>(
    instances: &[TwinConstrainedInstance<F>; 2],
    witnesses: &[TwinConstrainedWitness<F>; 2],
    params: &SchemeParams,
) -> Result<()> {
    let n = 1usize << params.log_n;
    for i in 0..2 {
        if instances[i].alpha.len() != params.log_n {
            return Err(FoldingError::ShapeMismatch(format!(
                "instance {i}: |α| = {}, expected log_n = {}",
                instances[i].alpha.len(),
                params.log_n
            )));
        }
        if instances[i].beta.len() != params.m {
            return Err(FoldingError::ShapeMismatch(format!(
                "instance {i}: |β| = {}, expected m = {}",
                instances[i].beta.len(),
                params.m
            )));
        }
        if witnesses[i].f.len() != n {
            return Err(FoldingError::CodewordLengthMismatch {
                n,
                got: witnesses[i].f.len(),
            });
        }
        if witnesses[i].w.len() != params.k {
            return Err(FoldingError::ShapeMismatch(format!(
                "witness {i}: |w| = {}, expected k = {}",
                witnesses[i].w.len(),
                params.k
            )));
        }
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::Term;
    use expander_mersenne31::M31Ext6;
    use rand::SeedableRng;
    use rand_chacha::ChaCha20Rng;

    type F = M31Ext6;
    fn f(n: u32) -> F {
        F::from(n)
    }

    /// Build two honestly-constructed twin-constrained instances
    /// sharing a bundled constraint `P_b(β₀, w₀) = β₀ · w₀` and
    /// return them with their witnesses.
    fn two_toy_instances() -> (
        [TwinConstrainedInstance<F>; 2],
        [TwinConstrainedWitness<F>; 2],
        BundledConstraint<F>,
        SchemeParams,
    ) {
        let p_b = BundledConstraint {
            terms: vec![Term {
                coeff: f(1),
                vars: vec![0, 1],
            }],
        };
        let params = SchemeParams {
            log_n: 2, // n = 4
            k: 1,
            m: 1,
            d: 2,
        };

        let wit_0 = TwinConstrainedWitness {
            f: vec![f(2), f(4), f(6), f(8)],
            w: vec![f(5)],
        };
        let inst_0 =
            TwinConstrainedInstance::from_honest(vec![f(0), f(1)], vec![f(3)], &p_b, &wit_0);

        let wit_1 = TwinConstrainedWitness {
            f: vec![f(1), f(3), f(9), f(27)],
            w: vec![f(11)],
        };
        let inst_1 =
            TwinConstrainedInstance::from_honest(vec![f(1), f(0)], vec![f(7)], &p_b, &wit_1);

        ([inst_0, inst_1], [wit_0, wit_1], p_b, params)
    }

    #[test]
    fn honest_round_trip_accepts() {
        let (instances, witnesses, p_b, params) = two_toy_instances();
        let tau = f(13);
        let omega = f(17);
        let gamma = f(23);

        let (folded_inst, folded_wit, msg) =
            prove_ell_2(&instances, &witnesses, &p_b, &params, tau, omega, gamma).unwrap();

        let verified_inst = verify_ell_2(&instances, &params, tau, omega, gamma, &msg).unwrap();

        assert_eq!(folded_inst, verified_inst);

        // Sanity: the folded witness is consistent with the folded
        // instance — μ = mle(f)(α), η = P_b(β, w).
        let expected_mu = mle_eval(&folded_wit.f, &folded_inst.alpha);
        let z: Vec<F> = folded_inst
            .beta
            .iter()
            .chain(folded_wit.w.iter())
            .copied()
            .collect();
        let expected_eta = p_b.evaluate(&z);
        assert_eq!(folded_inst.mu, expected_mu);
        assert_eq!(folded_inst.eta, expected_eta);
    }

    #[test]
    fn cheating_mu_rejected() {
        let (instances, witnesses, p_b, params) = two_toy_instances();
        let tau = f(13);
        let omega = f(17);
        let gamma = f(23);

        let (_, _, mut msg) =
            prove_ell_2(&instances, &witnesses, &p_b, &params, tau, omega, gamma).unwrap();

        msg.mu_new += f(1); // flip the claimed MLE evaluation
        assert!(verify_ell_2(&instances, &params, tau, omega, gamma, &msg).is_err());
    }

    #[test]
    fn cheating_eta_rejected() {
        let (instances, witnesses, p_b, params) = two_toy_instances();
        let tau = f(13);
        let omega = f(17);
        let gamma = f(23);

        let (_, _, mut msg) =
            prove_ell_2(&instances, &witnesses, &p_b, &params, tau, omega, gamma).unwrap();

        msg.eta_new += f(1);
        assert!(verify_ell_2(&instances, &params, tau, omega, gamma, &msg).is_err());
    }

    #[test]
    fn tampered_round_polynomial_rejected() {
        let (instances, witnesses, p_b, params) = two_toy_instances();
        let tau = f(13);
        let omega = f(17);
        let gamma = f(23);

        let (_, _, mut msg) =
            prove_ell_2(&instances, &witnesses, &p_b, &params, tau, omega, gamma).unwrap();

        msg.h.evals[0] += f(1);
        assert!(verify_ell_2(&instances, &params, tau, omega, gamma, &msg).is_err());
    }

    #[test]
    fn round_trip_random_challenges() {
        let mut rng = ChaCha20Rng::seed_from_u64(0xfee1_d00d);
        let (instances, witnesses, p_b, params) = two_toy_instances();
        for _ in 0..10 {
            let tau = F::random_unsafe(&mut rng);
            let omega = F::random_unsafe(&mut rng);
            let gamma = F::random_unsafe(&mut rng);

            let (folded_inst, _, msg) =
                prove_ell_2(&instances, &witnesses, &p_b, &params, tau, omega, gamma).unwrap();
            let verified_inst = verify_ell_2(&instances, &params, tau, omega, gamma, &msg).unwrap();
            assert_eq!(folded_inst, verified_inst);
        }
    }

    #[test]
    fn non_satisfying_first_instance_rejected() {
        // If μ_0 doesn't match mle(f_0)(α_0), the sumcheck's σ⁽¹⁾
        // won't match ĥ(0)+ĥ(1) and verification should fail.
        let (mut instances, witnesses, p_b, params) = two_toy_instances();
        let tau = f(13);
        let omega = f(17);
        let gamma = f(23);

        instances[0].mu += f(1); // corrupt the first instance's claim

        // Prover happens to still produce a message (it runs the
        // formula with the corrupted instance), but the verifier's
        // σ⁽¹⁾ is computed from the same corrupted instances so the
        // consistency at γ is what catches this — verifier rejects.
        let (_, _, msg) =
            prove_ell_2(&instances, &witnesses, &p_b, &params, tau, omega, gamma).unwrap();
        assert!(verify_ell_2(&instances, &params, tau, omega, gamma, &msg).is_err());
    }
}
