//! WARP Construction 5.10 — PESAT → twin-constrained reduction.
//!
//! Bootstraps a fresh PESAT instance into the twin-constrained
//! accumulator shape that Construction 9.4 consumes. The protocol:
//!
//! 1. Encode the witness: `f := C(w)` ∈ F^n.
//! 2. Set `α := 0^{log n}` and `μ := f̂(α)`. (For α all-zero, `μ = f[0]`.)
//! 3. Squeeze zero-check randomness `τ ∈ F^{log M}`.
//! 4. Set `β := (x, τ)` ∈ F^m where `m = n_pub + log M`.
//! 5. Set `η := 0` (the prover claims every constraint vanishes).
//!
//! The induced bundled polynomial is
//! `P_b(β, w) = Σ_{j ∈ [M]} eq(bin(j), τ) · p̂_j(x, w)`.
//! For satisfying `(x, w)`, each `p̂_j(x, w) = 0`, so `P_b(β, w) = 0`
//! — matching `η = 0`.

use expander_arith::Field;

use crate::code::LinearCode;
use crate::error::{FoldingError, Result};
use crate::pesat::{Constraint, PesatIndex, PesatInstance, Term};
use crate::twin::{mle_eval, BundledConstraint, TwinConstrainedInstance, TwinConstrainedWitness};

/// Number of PESAT constraints the bundled-P_b machinery can handle.
/// Must be a power of two for the `log₂(M)` zero-check batching.
pub fn validate_constraint_count(index: &PesatIndex<impl Field>) -> Result<usize> {
    let m = index.m();
    if !m.is_power_of_two() {
        return Err(FoldingError::ShapeMismatch(format!(
            "PESAT constraint count M = {m} must be a power of two"
        )));
    }
    Ok(m.trailing_zeros() as usize)
}

/// Build `P_b(β_full, w) = Σ_j eq(bin(j), τ) · p̂_j(x, w)` expressed as
/// a `Constraint<F>` over the concatenated variable vector
/// `z = (x, τ, w)` of length `n_pub + log M + k = m + k`.
///
/// Variable indexing in the resulting constraint:
///   z[0..n_pub]                → x
///   z[n_pub..n_pub+log M]      → τ (folded into β)
///   z[n_pub+log M..]           → w
///
/// Each PESAT term `coeff · ∏ z_i` where `z_i` is in (x, w) gets
/// re-indexed to the new layout and multiplied by the eq-coefficient
/// `eq(bin(j), τ)`. Since `eq` factors into linear monomials in τ
/// coordinates, the resulting `Constraint` has degree
/// `PESAT_degree + log M`.
pub fn bundled_constraint<F: Field>(index: &PesatIndex<F>) -> Result<BundledConstraint<F>> {
    let log_m = validate_constraint_count(index)?;
    let n_pub = index.n_pub;

    let mut bundled = Constraint::default();
    for (j, c) in index.constraints.iter().enumerate() {
        let eq_factor_terms = eq_bin_term_factors::<F>(j, log_m, n_pub);
        for t in &c.terms {
            let reindexed_vars: Vec<usize> = t
                .vars
                .iter()
                .map(|&v| {
                    if v < n_pub {
                        v
                    } else {
                        // PESAT variable v in [n_pub, n_pub+k) → witness. In the
                        // new z-layout the witness lives after τ, offset by log M.
                        v + log_m
                    }
                })
                .collect();

            // Multiply (coeff · ∏ z_{reindexed_vars}) by every term of the
            // eq(bin(j), τ) product expansion.
            for (eq_coeff, eq_vars) in &eq_factor_terms {
                let mut vars = reindexed_vars.clone();
                vars.extend(eq_vars.iter().copied());
                bundled.terms.push(Term {
                    coeff: t.coeff * *eq_coeff,
                    vars,
                });
            }
        }
    }
    Ok(bundled)
}

/// Expand `eq(bin(j), τ) = Π_ℓ (bin(j)_ℓ · τ_ℓ + (1 − bin(j)_ℓ)(1 − τ_ℓ))`
/// into an explicit list of (coefficient, τ-variable-indices) monomials
/// in `Constraint<F>` form. The τ coordinates are indexed `[n_pub,
/// n_pub+log M)` in the bundled constraint's z-vector.
fn eq_bin_term_factors<F: Field>(j: usize, log_m: usize, n_pub: usize) -> Vec<(F, Vec<usize>)> {
    // Start with a single term: coefficient 1, no variables.
    let mut terms: Vec<(F, Vec<usize>)> = vec![(F::one(), Vec::new())];

    for ell in 0..log_m {
        let bit = (j >> ell) & 1;
        // Factor is (bit · τ_ell + (1 − bit)(1 − τ_ell))
        //         = if bit == 1: τ_ell
        //           if bit == 0: 1 − τ_ell
        let mut new_terms = Vec::with_capacity(terms.len() * 2);
        for (coeff, vars) in &terms {
            if bit == 1 {
                let mut v = vars.clone();
                v.push(n_pub + ell);
                new_terms.push((*coeff, v));
            } else {
                // (1 − τ_ell) · existing = existing − τ_ell · existing
                new_terms.push((*coeff, vars.clone()));
                let mut v = vars.clone();
                v.push(n_pub + ell);
                new_terms.push((-*coeff, v));
            }
        }
        terms = new_terms;
    }
    terms
}

/// Run Construction 5.10: map a PESAT instance into an initial
/// twin-constrained accumulator.
pub fn reduce<F: Field + serdes::ExpSerde, C: LinearCode<F>>(
    index: &PesatIndex<F>,
    instance: &PesatInstance<F>,
    code: &C,
    tau: &[F],
) -> Result<(
    TwinConstrainedInstance<F>,
    TwinConstrainedWitness<F>,
    BundledConstraint<F>,
)> {
    let log_m = validate_constraint_count(index)?;
    if tau.len() != log_m {
        return Err(FoldingError::ShapeMismatch(format!(
            "tau.len() = {}, expected log M = {log_m}",
            tau.len()
        )));
    }
    if instance.x.len() != index.n_pub {
        return Err(FoldingError::ShapeMismatch(format!(
            "x.len() = {}, expected n_pub = {}",
            instance.x.len(),
            index.n_pub
        )));
    }
    if instance.w.len() != index.k {
        return Err(FoldingError::ShapeMismatch(format!(
            "w.len() = {}, expected k = {}",
            instance.w.len(),
            index.k
        )));
    }
    if code.message_len() != index.k {
        return Err(FoldingError::ShapeMismatch(format!(
            "code message length {} ≠ PESAT k = {}",
            code.message_len(),
            index.k
        )));
    }

    let f = code.encode(&instance.w);
    let log_n = code.log_codeword_len();
    let alpha = vec![F::zero(); log_n];
    let mu = mle_eval(&f, &alpha);

    let mut beta = Vec::with_capacity(index.n_pub + log_m);
    beta.extend_from_slice(&instance.x);
    beta.extend_from_slice(tau);
    let eta = F::zero();

    let p_b = bundled_constraint(index)?;
    let merkle_root = crate::merkle::MerkleTree::build(&f).root();

    Ok((
        TwinConstrainedInstance {
            alpha,
            mu,
            beta,
            eta,
            merkle_root,
        },
        TwinConstrainedWitness {
            f,
            w: instance.w.clone(),
        },
        p_b,
    ))
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::code::IdentityCode;
    use expander_mersenne31::M31Ext6;

    type F = M31Ext6;
    fn f(n: u32) -> F {
        F::from(n)
    }

    /// M = 2 constraints over n_pub = 2 public + k = 4 witness:
    ///   p̂_1(x, w) = w0 + w1 − x0
    ///   p̂_2(x, w) = w2·w3 − x1
    fn toy_index() -> PesatIndex<F> {
        let c1 = Constraint {
            terms: vec![
                Term {
                    coeff: f(1),
                    vars: vec![2],
                }, // w0 — index n_pub+0 = 2
                Term {
                    coeff: f(1),
                    vars: vec![3],
                }, // w1
                Term {
                    coeff: -f(1),
                    vars: vec![0],
                }, // x0
            ],
        };
        let c2 = Constraint {
            terms: vec![
                Term {
                    coeff: f(1),
                    vars: vec![4, 5],
                }, // w2·w3
                Term {
                    coeff: -f(1),
                    vars: vec![1],
                }, // x1
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
        // x0 = w0 + w1 = 3; x1 = w2·w3 = 15; w = (1, 2, 3, 5).
        PesatInstance {
            x: vec![f(3), f(15)],
            w: vec![f(1), f(2), f(3), f(5)],
        }
    }

    #[test]
    fn satisfying_pesat_checks() {
        let idx = toy_index();
        let inst = satisfying_instance();
        inst.check(&idx).unwrap();
    }

    #[test]
    fn bundled_constraint_vanishes_on_satisfying_instance() {
        let idx = toy_index();
        let inst = satisfying_instance();
        let p_b = bundled_constraint(&idx).unwrap();

        // z = (x, τ, w) — any τ should give P_b(β, w) = 0 when PESAT holds.
        for tau_val in [f(7), f(11), f(13)] {
            let z = vec![
                inst.x[0], inst.x[1], tau_val, inst.w[0], inst.w[1], inst.w[2], inst.w[3],
            ];
            let val = p_b.evaluate(&z);
            assert_eq!(val, f(0), "P_b should vanish, got {val:?} at τ={tau_val:?}");
        }
    }

    #[test]
    fn bundled_constraint_nonzero_on_nonsatisfying_instance() {
        let idx = toy_index();
        let bad = PesatInstance {
            x: vec![f(3), f(15)],
            w: vec![f(1), f(2), f(99), f(5)], // w2 wrong → p̂_2 != 0
        };
        let p_b = bundled_constraint(&idx).unwrap();
        let tau_val = f(7);
        let z = vec![
            bad.x[0], bad.x[1], tau_val, bad.w[0], bad.w[1], bad.w[2], bad.w[3],
        ];
        assert_ne!(p_b.evaluate(&z), f(0));
    }

    #[test]
    fn reduce_produces_twin_constrained_instance() {
        let idx = toy_index();
        let inst = satisfying_instance();
        let code = IdentityCode::new(4);
        let tau = vec![f(7)];

        let (twin_inst, twin_wit, p_b) = reduce(&idx, &inst, &code, &tau).unwrap();

        assert_eq!(twin_inst.alpha, vec![f(0), f(0)]);
        assert_eq!(twin_inst.beta, vec![f(3), f(15), f(7)]);
        assert_eq!(twin_inst.eta, f(0));

        // μ = f̂(0) = f[0] = w[0] (identity code) = 1
        assert_eq!(twin_inst.mu, f(1));

        // Twin-constrained invariant: η = P_b(β, w)
        let z: Vec<F> = twin_inst
            .beta
            .iter()
            .chain(twin_wit.w.iter())
            .copied()
            .collect();
        assert_eq!(twin_inst.eta, p_b.evaluate(&z));
    }

    #[test]
    fn reduce_rejects_wrong_tau_length() {
        let idx = toy_index();
        let inst = satisfying_instance();
        let code = IdentityCode::new(4);
        let tau = vec![f(7), f(11)]; // too long: log M = 1 here
        assert!(reduce(&idx, &inst, &code, &tau).is_err());
    }

    #[test]
    fn reduce_rejects_code_mismatch() {
        let idx = toy_index();
        let inst = satisfying_instance();
        let code = IdentityCode::new(8); // too big
        let tau = vec![f(7)];
        assert!(reduce(&idx, &inst, &code, &tau).is_err());
    }
}
