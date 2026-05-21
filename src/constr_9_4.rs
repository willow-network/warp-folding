//! WARP Construction 9.4 — full `R_C^ℓ → R_C` fold step.
//!
//! Composes Constructions 6.3 (twin pseudo-batching), 7.2 (codeword
//! batching with OOD + shift queries), and 8.2 (multilinear-constraint
//! batching sumcheck) into a single IOR that takes `ℓ` twin-
//! constrained instances and produces one. At ℓ = 2 this is the
//! atomic fold step for Willow's historical-sync accumulation.
//!
//! The challenges — (τ, ω, γ) for 6.3, (ood_points, shift_queries, ξ)
//! for 7.2, and (α_new) for 8.2 — are passed in explicitly. Step 8 of
//! the Phase 2 plan wires them to a Fiat-Shamir transcript so they
//! become derived from the accumulator state.

use expander_arith::Field;

use crate::constr_6_3::{self, SchemeParams, TwinPseudoBatchingMsg};
use crate::constr_7_2::{self, CodewordBatchingChallenges, CodewordBatchingMsg};
use crate::constr_8_2::{self, MultilinearBatchingMsg};
use crate::error::Result;
use crate::twin::{BundledConstraint, TwinConstrainedInstance, TwinConstrainedWitness};

/// All IOR messages bundled for a single fold step at ℓ = 2.
#[derive(Clone, Debug, serdes::ExpSerde)]
pub struct FoldMessage<F: Field + serdes::ExpSerde> {
    pub twin_pseudo_batching: TwinPseudoBatchingMsg<F>,
    pub codeword_batching: CodewordBatchingMsg<F>,
    pub multilinear_batching: MultilinearBatchingMsg<F>,
}

/// All verifier challenges for a single fold step at ℓ = 2.
#[derive(Clone, Debug)]
pub struct FoldChallenges<F: Field> {
    /// Construction 6.3 outer-sumcheck challenges.
    pub tau: F,
    pub omega: F,
    pub gamma: F,
    /// Construction 7.2 OOD + shift-query + batching challenges.
    pub codeword_batching: CodewordBatchingChallenges<F>,
    /// Construction 8.2 per-round sumcheck challenges.
    pub alpha_new: Vec<F>,
}

pub fn prove<F: Field>(
    instances: &[TwinConstrainedInstance<F>; 2],
    witnesses: &[TwinConstrainedWitness<F>; 2],
    p_b: &BundledConstraint<F>,
    params: &SchemeParams,
    challenges: &FoldChallenges<F>,
) -> Result<(
    TwinConstrainedInstance<F>,
    TwinConstrainedWitness<F>,
    FoldMessage<F>,
)> {
    let (pseudo_inst, pseudo_wit, msg_6_3) = constr_6_3::prove_ell_2(
        instances,
        witnesses,
        p_b,
        params,
        challenges.tau,
        challenges.omega,
        challenges.gamma,
    )?;

    let (batched_claims, msg_7_2) =
        constr_7_2::prove(&pseudo_inst, &pseudo_wit, &challenges.codeword_batching)?;

    let (final_inst, msg_8_2) =
        constr_8_2::prove(&batched_claims, &pseudo_wit.f, &challenges.alpha_new)?;

    let msg = FoldMessage {
        twin_pseudo_batching: msg_6_3,
        codeword_batching: msg_7_2,
        multilinear_batching: msg_8_2,
    };
    Ok((final_inst, pseudo_wit, msg))
}

pub fn verify<F: Field>(
    instances: &[TwinConstrainedInstance<F>; 2],
    params: &SchemeParams,
    challenges: &FoldChallenges<F>,
    msg: &FoldMessage<F>,
) -> Result<TwinConstrainedInstance<F>> {
    let pseudo_inst = constr_6_3::verify_ell_2(
        instances,
        params,
        challenges.tau,
        challenges.omega,
        challenges.gamma,
        &msg.twin_pseudo_batching,
    )?;

    let batched_claims = constr_7_2::verify(
        &pseudo_inst,
        &challenges.codeword_batching,
        &msg.codeword_batching,
    )?;

    let final_inst = constr_8_2::verify(
        &batched_claims,
        &challenges.alpha_new,
        &msg.multilinear_batching,
    )?;

    Ok(final_inst)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{mle_eval, BundledConstraint, Term};
    use expander_mersenne31::M31Ext6;
    use rand::SeedableRng;
    use rand_chacha::ChaCha20Rng;

    type F = M31Ext6;
    fn f(n: u32) -> F {
        F::from(n)
    }

    fn setup() -> (
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
            log_n: 2,
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

    fn challenges(rng: &mut ChaCha20Rng) -> FoldChallenges<F> {
        FoldChallenges {
            tau: F::random_unsafe(&mut *rng),
            omega: F::random_unsafe(&mut *rng),
            gamma: F::random_unsafe(&mut *rng),
            codeword_batching: CodewordBatchingChallenges {
                ood_points: vec![vec![
                    F::random_unsafe(&mut *rng),
                    F::random_unsafe(&mut *rng),
                ]],
                shift_queries: vec![0, 2],
                xi: vec![F::random_unsafe(&mut *rng), F::random_unsafe(&mut *rng)],
            },
            alpha_new: vec![F::random_unsafe(&mut *rng), F::random_unsafe(&mut *rng)],
        }
    }

    #[test]
    fn composed_round_trip_accepts() {
        let mut rng = ChaCha20Rng::seed_from_u64(1);
        let (instances, witnesses, p_b, params) = setup();
        let ch = challenges(&mut rng);

        let (folded_inst, folded_wit, msg) =
            prove(&instances, &witnesses, &p_b, &params, &ch).unwrap();
        let verified_inst = verify(&instances, &params, &ch, &msg).unwrap();

        assert_eq!(folded_inst, verified_inst);

        // Sanity: the final (α, μ) is consistent with the folded
        // witness codeword.
        let expected_mu = mle_eval(&folded_wit.f, &folded_inst.alpha);
        assert_eq!(folded_inst.mu, expected_mu);
    }

    #[test]
    fn folded_instance_is_valid_twin_constrained() {
        let mut rng = ChaCha20Rng::seed_from_u64(2);
        let (instances, witnesses, p_b, params) = setup();
        let ch = challenges(&mut rng);

        let (folded_inst, folded_wit, _) =
            prove(&instances, &witnesses, &p_b, &params, &ch).unwrap();

        // μ = mle(f)(α) (directly tested)
        assert_eq!(folded_inst.mu, mle_eval(&folded_wit.f, &folded_inst.alpha));
        // η = P_b(β, w) (this is the twin-constrained invariant)
        let z: Vec<F> = folded_inst
            .beta
            .iter()
            .chain(folded_wit.w.iter())
            .copied()
            .collect();
        assert_eq!(folded_inst.eta, p_b.evaluate(&z));
    }

    #[test]
    fn tampered_6_3_message_rejected() {
        let mut rng = ChaCha20Rng::seed_from_u64(3);
        let (instances, witnesses, p_b, params) = setup();
        let ch = challenges(&mut rng);
        let (_, _, mut msg) = prove(&instances, &witnesses, &p_b, &params, &ch).unwrap();
        msg.twin_pseudo_batching.mu_new += f(1);
        assert!(verify(&instances, &params, &ch, &msg).is_err());
    }

    #[test]
    fn tampered_7_2_message_rejected() {
        let mut rng = ChaCha20Rng::seed_from_u64(4);
        let (instances, witnesses, p_b, params) = setup();
        let ch = challenges(&mut rng);
        let (_, _, mut msg) = prove(&instances, &witnesses, &p_b, &params, &ch).unwrap();
        msg.codeword_batching.shift_values[0] += f(1);
        // Tampering the shift value doesn't fail 7.2's verifier (which
        // accepts prover-declared values in Phase 2), but the ν change
        // cascades into 8.2's initial σ⁽²⁾, which breaks the sumcheck.
        assert!(verify(&instances, &params, &ch, &msg).is_err());
    }

    #[test]
    fn tampered_8_2_message_rejected() {
        let mut rng = ChaCha20Rng::seed_from_u64(5);
        let (instances, witnesses, p_b, params) = setup();
        let ch = challenges(&mut rng);
        let (_, _, mut msg) = prove(&instances, &witnesses, &p_b, &params, &ch).unwrap();
        msg.multilinear_batching.mu_new += f(1);
        assert!(verify(&instances, &params, &ch, &msg).is_err());
    }

    #[test]
    fn many_random_folds_accept() {
        let mut rng = ChaCha20Rng::seed_from_u64(0xdeadbeef);
        let (instances, witnesses, p_b, params) = setup();
        for _ in 0..20 {
            let ch = challenges(&mut rng);
            let (folded_inst, _, msg) = prove(&instances, &witnesses, &p_b, &params, &ch).unwrap();
            let verified_inst = verify(&instances, &params, &ch, &msg).unwrap();
            assert_eq!(folded_inst, verified_inst);
        }
    }
}
