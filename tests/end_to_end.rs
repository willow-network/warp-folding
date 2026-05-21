//! Phase 2 end-to-end test: two PESAT instances → Construction 5.10
//! reduction → Construction 9.4 fold → decider acceptance.
//!
//! This is the Phase 2 success criterion described in
//! `docs/research/warp-over-m31.md §6.4`. Success = the full pipeline
//! round-trips: prover produces a fold, verifier accepts each IOR
//! message, decider accepts the terminal accumulator.

use expander_arith::Field;
use expander_mersenne31::M31Ext6;
use rand::SeedableRng;
use rand_chacha::ChaCha20Rng;

use warp_folding::{
    code::IdentityCode,
    constr_5_10,
    constr_7_2::CodewordBatchingChallenges,
    constr_9_4::{self, FoldChallenges},
    decider,
    fs::SamplingParams,
    pesat::{Constraint, PesatIndex, PesatInstance, Term},
    prove_with_parallel_rep, prove_with_transcript, verify_with_parallel_rep,
    verify_with_transcript, SchemeParams,
};

type F = M31Ext6;
fn f(n: u32) -> F {
    F::from(n)
}

/// M = 2 constraints over n_pub = 2 public + k = 4 witness:
///   p̂_1(x, w) = w0 + w1 − x0       (linear, degree 1)
///   p̂_2(x, w) = w2·w3 − x1         (degree 2)
fn make_index() -> PesatIndex<F> {
    let c1 = Constraint {
        terms: vec![
            Term {
                coeff: f(1),
                vars: vec![2],
            },
            Term {
                coeff: f(1),
                vars: vec![3],
            },
            Term {
                coeff: -f(1),
                vars: vec![0],
            },
        ],
    };
    let c2 = Constraint {
        terms: vec![
            Term {
                coeff: f(1),
                vars: vec![4, 5],
            },
            Term {
                coeff: -f(1),
                vars: vec![1],
            },
        ],
    };
    PesatIndex {
        constraints: vec![c1, c2],
        n_pub: 2,
        k: 4,
        d: 2,
    }
}

fn random_challenges(rng: &mut ChaCha20Rng) -> FoldChallenges<F> {
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
fn phase_2_success_criterion() {
    // Two satisfying PESAT instances.
    let idx = make_index();
    let pesat_0 = PesatInstance {
        x: vec![f(3), f(15)],
        w: vec![f(1), f(2), f(3), f(5)],
    };
    let pesat_1 = PesatInstance {
        x: vec![f(7), f(77)],
        w: vec![f(3), f(4), f(7), f(11)],
    };
    pesat_0.check(&idx).unwrap();
    pesat_1.check(&idx).unwrap();

    let code = IdentityCode::new(4); // k = n = 4, log_n = 2

    // Each instance generates its own zero-check τ in 5.10. Under
    // full Fiat-Shamir these would be squeezed from the per-instance
    // transcript; in Phase 2 we fix them.
    let tau_0 = vec![f(7)];
    let tau_1 = vec![f(11)];
    let (twin_0, wit_0, p_b_0) = constr_5_10::reduce(&idx, &pesat_0, &code, &tau_0).unwrap();
    let (twin_1, wit_1, p_b_1) = constr_5_10::reduce(&idx, &pesat_1, &code, &tau_1).unwrap();

    // Sanity: the two 5.10 outputs share the same P_b structure (P_b
    // depends only on the PESAT *index*, not the τ), so we can fold
    // them with a single P_b.
    assert_eq!(p_b_0, p_b_1);
    let p_b = p_b_0;

    // SchemeParams must match the 5.10 output shapes.
    let params = SchemeParams {
        log_n: 2,
        k: 4,
        m: idx.n_pub + tau_0.len(), // n_pub + log M
        d: p_b.degree(),
    };

    // Each 5.10 output must be decider-valid on its own.
    decider::decide(&twin_0, &wit_0, &code, &p_b).unwrap();
    decider::decide(&twin_1, &wit_1, &code, &p_b).unwrap();

    // Fold them via Construction 9.4.
    let mut rng = ChaCha20Rng::seed_from_u64(0xfacade);
    let challenges = random_challenges(&mut rng);
    let (folded_inst, folded_wit, msg) = constr_9_4::prove(
        &[twin_0.clone(), twin_1.clone()],
        &[wit_0, wit_1],
        &p_b,
        &params,
        &challenges,
    )
    .unwrap();

    // Verifier round-trip.
    let verified_inst = constr_9_4::verify(&[twin_0, twin_1], &params, &challenges, &msg).unwrap();
    assert_eq!(folded_inst, verified_inst);

    // The folded accumulator passes the decider.
    decider::decide(&folded_inst, &folded_wit, &code, &p_b).unwrap();
}

#[test]
fn phase_2_success_criterion_many_random_challenges() {
    let idx = make_index();
    let pesat_0 = PesatInstance {
        x: vec![f(3), f(15)],
        w: vec![f(1), f(2), f(3), f(5)],
    };
    let pesat_1 = PesatInstance {
        x: vec![f(7), f(77)],
        w: vec![f(3), f(4), f(7), f(11)],
    };

    let code = IdentityCode::new(4);
    let tau_0 = vec![f(7)];
    let tau_1 = vec![f(11)];
    let (twin_0, wit_0, p_b) = constr_5_10::reduce(&idx, &pesat_0, &code, &tau_0).unwrap();
    let (twin_1, wit_1, _) = constr_5_10::reduce(&idx, &pesat_1, &code, &tau_1).unwrap();

    let params = SchemeParams {
        log_n: 2,
        k: 4,
        m: idx.n_pub + 1,
        d: p_b.degree(),
    };

    let mut rng = ChaCha20Rng::seed_from_u64(0x1234_5678);
    for i in 0..30 {
        let challenges = random_challenges(&mut rng);
        let (folded_inst, folded_wit, msg) = constr_9_4::prove(
            &[twin_0.clone(), twin_1.clone()],
            &[wit_0.clone(), wit_1.clone()],
            &p_b,
            &params,
            &challenges,
        )
        .unwrap_or_else(|e| panic!("prove failed on iter {i}: {e:?}"));

        let verified_inst = constr_9_4::verify(
            &[twin_0.clone(), twin_1.clone()],
            &params,
            &challenges,
            &msg,
        )
        .unwrap_or_else(|e| panic!("verify failed on iter {i}: {e:?}"));
        assert_eq!(folded_inst, verified_inst);

        decider::decide(&folded_inst, &folded_wit, &code, &p_b)
            .unwrap_or_else(|e| panic!("decider failed on iter {i}: {e:?}"));
    }
}

#[test]
fn fold_of_folds_via_fs() {
    // Three satisfying PESAT instances. Fold (0, 1) → A using FS,
    // then fold (A, 2) → B using FS. The decider must accept B.
    let idx = make_index();
    let pesats = [
        PesatInstance {
            x: vec![f(3), f(15)],
            w: vec![f(1), f(2), f(3), f(5)],
        },
        PesatInstance {
            x: vec![f(7), f(77)],
            w: vec![f(3), f(4), f(7), f(11)],
        },
        PesatInstance {
            x: vec![f(8), f(91)],
            w: vec![f(5), f(3), f(7), f(13)],
        },
    ];
    for p in &pesats {
        p.check(&idx).unwrap();
    }

    let code = IdentityCode::new(4);
    let taus = [vec![f(7)], vec![f(11)], vec![f(13)]];
    let mut twins: Vec<_> = Vec::new();
    let mut wits: Vec<_> = Vec::new();
    let mut p_b_opt = None;
    for (p, tau) in pesats.iter().zip(taus.iter()) {
        let (t, w, p_b) = constr_5_10::reduce(&idx, p, &code, tau).unwrap();
        twins.push(t);
        wits.push(w);
        p_b_opt = Some(p_b);
    }
    let p_b = p_b_opt.unwrap();
    let params = SchemeParams {
        log_n: 2,
        k: 4,
        m: idx.n_pub + 1,
        d: p_b.degree(),
    };
    let sampling = SamplingParams {
        n_ood: 1,
        n_shifts: 2,
    };

    // First fold: (0, 1) → A.
    let (twin_a, wit_a, msg_a) = prove_with_transcript(
        &[twins[0].clone(), twins[1].clone()],
        &[wits[0].clone(), wits[1].clone()],
        &p_b,
        &params,
        &sampling,
    )
    .unwrap();
    let verified_a = verify_with_transcript(
        &[twins[0].clone(), twins[1].clone()],
        &params,
        &sampling,
        &msg_a,
    )
    .unwrap();
    assert_eq!(twin_a, verified_a);
    decider::decide(&twin_a, &wit_a, &code, &p_b).unwrap();

    // Second fold: (A, 2) → B. The output of the first fold is shape-
    // identical to a freshly-reduced twin-constrained instance, so it
    // can directly feed the next fold.
    let (twin_b, wit_b, msg_b) = prove_with_transcript(
        &[twin_a.clone(), twins[2].clone()],
        &[wit_a, wits[2].clone()],
        &p_b,
        &params,
        &sampling,
    )
    .unwrap();
    let verified_b =
        verify_with_transcript(&[twin_a, twins[2].clone()], &params, &sampling, &msg_b).unwrap();
    assert_eq!(twin_b, verified_b);
    decider::decide(&twin_b, &wit_b, &code, &p_b).unwrap();
}

#[test]
fn parallel_rep_round_trip() {
    // Parallel rep r=2: prover sends 2 messages, verifier checks both,
    // they agree on the folded instance.
    let idx = make_index();
    let pesat_0 = PesatInstance {
        x: vec![f(3), f(15)],
        w: vec![f(1), f(2), f(3), f(5)],
    };
    let pesat_1 = PesatInstance {
        x: vec![f(7), f(77)],
        w: vec![f(3), f(4), f(7), f(11)],
    };
    let code = IdentityCode::new(4);
    let tau_0 = vec![f(7)];
    let tau_1 = vec![f(11)];
    let (twin_0, wit_0, p_b) = constr_5_10::reduce(&idx, &pesat_0, &code, &tau_0).unwrap();
    let (twin_1, wit_1, _) = constr_5_10::reduce(&idx, &pesat_1, &code, &tau_1).unwrap();
    let params = SchemeParams {
        log_n: 2,
        k: 4,
        m: idx.n_pub + 1,
        d: p_b.degree(),
    };
    let sampling = SamplingParams {
        n_ood: 1,
        n_shifts: 2,
    };

    let (folded_inst, folded_wit, msgs) = prove_with_parallel_rep(
        &[twin_0.clone(), twin_1.clone()],
        &[wit_0, wit_1],
        &p_b,
        &params,
        &sampling,
        2,
    )
    .unwrap();
    assert_eq!(msgs.len(), 2);

    let verified = verify_with_parallel_rep(&[twin_0, twin_1], &params, &sampling, &msgs).unwrap();
    assert_eq!(folded_inst, verified);
    decider::decide(&folded_inst, &folded_wit, &code, &p_b).unwrap();
}

#[test]
fn parallel_rep_tampered_one_msg_rejected() {
    let idx = make_index();
    let pesat_0 = PesatInstance {
        x: vec![f(3), f(15)],
        w: vec![f(1), f(2), f(3), f(5)],
    };
    let pesat_1 = PesatInstance {
        x: vec![f(7), f(77)],
        w: vec![f(3), f(4), f(7), f(11)],
    };
    let code = IdentityCode::new(4);
    let tau = vec![f(7)];
    let (twin_0, wit_0, p_b) = constr_5_10::reduce(&idx, &pesat_0, &code, &tau).unwrap();
    let (twin_1, wit_1, _) = constr_5_10::reduce(&idx, &pesat_1, &code, &tau).unwrap();
    let params = SchemeParams {
        log_n: 2,
        k: 4,
        m: idx.n_pub + 1,
        d: p_b.degree(),
    };
    let sampling = SamplingParams {
        n_ood: 1,
        n_shifts: 2,
    };

    let (_, _, mut msgs) = prove_with_parallel_rep(
        &[twin_0.clone(), twin_1.clone()],
        &[wit_0, wit_1],
        &p_b,
        &params,
        &sampling,
        2,
    )
    .unwrap();
    msgs[1].twin_pseudo_batching.mu_new += f(1);
    assert!(verify_with_parallel_rep(&[twin_0, twin_1], &params, &sampling, &msgs).is_err());
}

#[test]
fn non_satisfying_pesat_rejected_by_decider() {
    let idx = make_index();
    // Deliberately violating p̂_2: w2·w3 ≠ x1.
    let bad = PesatInstance {
        x: vec![f(3), f(15)],
        w: vec![f(1), f(2), f(99), f(5)], // w2·w3 = 495 ≠ 15
    };

    let code = IdentityCode::new(4);
    let tau = vec![f(7)];
    let (twin, wit, p_b) = constr_5_10::reduce(&idx, &bad, &code, &tau).unwrap();

    // 5.10 reduction itself doesn't verify PESAT satisfiability, so it
    // happily produces an accumulator. The decider catches the lie.
    assert!(decider::decide(&twin, &wit, &code, &p_b).is_err());
}
