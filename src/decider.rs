//! WARP decider `D_ACC` (Construction 10.4 Step 3 "Decider").
//!
//! Given a terminal twin-constrained accumulator `(acc.x, acc.w)`,
//! accept iff:
//!   1. `f = C(w)` — the codeword really does encode `w`.
//!   2. Merkle root of `f` matches `instance.merkle_root`.
//!   3. `f̂(α) = μ` — the MLE claim holds.
//!   4. `P_b(β, w) = η` — the bundled-constraint claim holds.
//!
//! ## Where this runs in the Willow pipeline
//!
//! The decider is *not* part of consensus's per-block verification — at
//! chain-tip we rely on per-step IOR soundness plus chain-link
//! continuity, which is cheap (no witness on chain) and matches the
//! recursive structure of WARP.
//!
//! Indexer-side, [`WarpProverState::self_check`](crate::WarpProverState::self_check)
//! wraps this function. It runs once at state-load so an indexer
//! detects on-disk state corruption locally — before submitting a
//! proof that would fail consensus's chain-link check and produce an
//! opaque rejection. A future on-chain settlement transaction
//! (indexer ships the accumulator witness; consensus runs `decide`)
//! would close the recursion formally; the algebraic check below is
//! the kernel that path would call.

use expander_arith::Field;
use serdes::ExpSerde;

use crate::code::LinearCode;
use crate::error::{FoldingError, Result};
use crate::merkle::MerkleTree;
use crate::twin::{mle_eval, BundledConstraint, TwinConstrainedInstance, TwinConstrainedWitness};

pub fn decide<F: Field + ExpSerde, C: LinearCode<F>>(
    instance: &TwinConstrainedInstance<F>,
    witness: &TwinConstrainedWitness<F>,
    code: &C,
    p_b: &BundledConstraint<F>,
) -> Result<()> {
    let expected_f = code.encode(&witness.w);
    if expected_f != witness.f {
        return Err(FoldingError::ShapeMismatch(
            "decider: witness codeword f ≠ C(w)".into(),
        ));
    }

    // Verify the committed Merkle root matches a fresh re-build over
    // the witness codeword.
    let recomputed_root = MerkleTree::build(&witness.f).root();
    if recomputed_root != instance.merkle_root {
        return Err(FoldingError::ShapeMismatch(
            "decider: Merkle root does not match re-hashed codeword".into(),
        ));
    }

    let actual_mu = mle_eval(&witness.f, &instance.alpha);
    if actual_mu != instance.mu {
        return Err(FoldingError::ShapeMismatch("decider: f̂(α) ≠ μ".into()));
    }

    let z: Vec<F> = instance
        .beta
        .iter()
        .chain(witness.w.iter())
        .copied()
        .collect();
    let actual_eta = p_b.evaluate(&z);
    if actual_eta != instance.eta {
        return Err(FoldingError::ShapeMismatch("decider: P_b(β, w) ≠ η".into()));
    }

    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::code::IdentityCode;
    use crate::constr_5_10;
    use crate::pesat::{Constraint, PesatIndex, PesatInstance, Term};
    use expander_mersenne31::M31Ext6;

    type F = M31Ext6;
    fn f(n: u32) -> F {
        F::from(n)
    }

    fn toy_index() -> PesatIndex<F> {
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

    fn satisfying_instance() -> PesatInstance<F> {
        PesatInstance {
            x: vec![f(3), f(15)],
            w: vec![f(1), f(2), f(3), f(5)],
        }
    }

    #[test]
    fn initial_accumulator_decides() {
        let idx = toy_index();
        let inst = satisfying_instance();
        let code = IdentityCode::new(4);
        let tau = vec![f(7)];
        let (twin_inst, twin_wit, p_b) = constr_5_10::reduce(&idx, &inst, &code, &tau).unwrap();

        decide(&twin_inst, &twin_wit, &code, &p_b).unwrap();
    }

    #[test]
    fn corrupted_codeword_rejected() {
        let idx = toy_index();
        let inst = satisfying_instance();
        let code = IdentityCode::new(4);
        let tau = vec![f(7)];
        let (twin_inst, mut twin_wit, p_b) = constr_5_10::reduce(&idx, &inst, &code, &tau).unwrap();

        twin_wit.f[0] += f(1);
        assert!(decide(&twin_inst, &twin_wit, &code, &p_b).is_err());
    }

    #[test]
    fn corrupted_mu_rejected() {
        let idx = toy_index();
        let inst = satisfying_instance();
        let code = IdentityCode::new(4);
        let tau = vec![f(7)];
        let (mut twin_inst, twin_wit, p_b) = constr_5_10::reduce(&idx, &inst, &code, &tau).unwrap();

        twin_inst.mu += f(1);
        assert!(decide(&twin_inst, &twin_wit, &code, &p_b).is_err());
    }

    #[test]
    fn corrupted_eta_rejected() {
        let idx = toy_index();
        let inst = satisfying_instance();
        let code = IdentityCode::new(4);
        let tau = vec![f(7)];
        let (mut twin_inst, twin_wit, p_b) = constr_5_10::reduce(&idx, &inst, &code, &tau).unwrap();

        twin_inst.eta += f(1);
        assert!(decide(&twin_inst, &twin_wit, &code, &p_b).is_err());
    }

    #[test]
    fn corrupted_merkle_root_rejected() {
        // Even if (μ, η, codeword) all match, a wrong Merkle root
        // means the on-chain commitment doesn't bind the codeword
        // and the decider rejects.
        let idx = toy_index();
        let inst = satisfying_instance();
        let code = IdentityCode::new(4);
        let tau = vec![f(7)];
        let (mut twin_inst, twin_wit, p_b) = constr_5_10::reduce(&idx, &inst, &code, &tau).unwrap();

        twin_inst.merkle_root[0] ^= 1;
        assert!(decide(&twin_inst, &twin_wit, &code, &p_b).is_err());
    }

    #[test]
    fn non_satisfying_pesat_rejected() {
        // If the prover lies about the witness (fails PESAT), then even
        // with honest η = 0, the decider catches it because P_b(β, w) ≠ 0.
        let idx = toy_index();
        let bad = PesatInstance {
            x: vec![f(3), f(15)],
            w: vec![f(1), f(2), f(99), f(5)],
        };
        let code = IdentityCode::new(4);
        let tau = vec![f(7)];

        // reduce() doesn't know the PESAT is unsat — it happily produces
        // the accumulator. The decider catches the constraint violation.
        let (twin_inst, twin_wit, p_b) = constr_5_10::reduce(&idx, &bad, &code, &tau).unwrap();
        assert!(decide(&twin_inst, &twin_wit, &code, &p_b).is_err());
    }
}
