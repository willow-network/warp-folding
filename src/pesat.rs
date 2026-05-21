use expander_arith::Field;

use crate::error::{FoldingError, Result};

/// A term c · ∏_{i ∈ vars} z_i in the polynomial p̂_j.
///
/// `vars` is a list of variable indices into the concatenated
/// (x, w) ∈ F^N vector; repeated indices mean higher power.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Term<F: Field> {
    pub coeff: F,
    pub vars: Vec<usize>,
}

impl<F: Field> Term<F> {
    pub fn degree(&self) -> usize {
        self.vars.len()
    }

    pub fn evaluate(&self, z: &[F]) -> F {
        let mut acc = self.coeff;
        for &i in &self.vars {
            acc *= z[i];
        }
        acc
    }
}

/// One constraint polynomial p̂_j, as a sum of terms.
#[derive(Clone, Debug, PartialEq, Eq, Default)]
pub struct Constraint<F: Field> {
    pub terms: Vec<Term<F>>,
}

impl<F: Field> Constraint<F> {
    pub fn degree(&self) -> usize {
        self.terms.iter().map(Term::degree).max().unwrap_or(0)
    }

    pub fn evaluate(&self, z: &[F]) -> F {
        let mut acc = F::zero();
        for t in &self.terms {
            acc += t.evaluate(z);
        }
        acc
    }
}

/// PESAT index i = (p̂, M, N, k).
///
/// Matches WARP Definition 5.2. The constraint polynomials share a
/// single global degree bound `d`; `N = n_pub + k` is the total
/// variable count.
#[derive(Clone, Debug)]
pub struct PesatIndex<F: Field> {
    pub constraints: Vec<Constraint<F>>,
    pub n_pub: usize,
    pub k: usize,
    pub d: usize,
}

impl<F: Field> PesatIndex<F> {
    pub fn n_total(&self) -> usize {
        self.n_pub + self.k
    }

    pub fn m(&self) -> usize {
        self.constraints.len()
    }

    pub fn validate(&self) -> Result<()> {
        for (idx, c) in self.constraints.iter().enumerate() {
            if c.degree() > self.d {
                return Err(FoldingError::DegreeExceeded {
                    expected: self.d,
                    actual: c.degree(),
                });
            }
            for t in &c.terms {
                for &v in &t.vars {
                    if v >= self.n_total() {
                        return Err(FoldingError::ShapeMismatch(format!(
                            "constraint {idx} references variable {v}, but N = {}",
                            self.n_total()
                        )));
                    }
                }
            }
        }
        Ok(())
    }
}

/// Instance-witness pair. `x.len() = n_pub`, `w.len() = k`.
#[derive(Clone, Debug)]
pub struct PesatInstance<F: Field> {
    pub x: Vec<F>,
    pub w: Vec<F>,
}

impl<F: Field> PesatInstance<F> {
    /// Concatenate (x, w) into a single z ∈ F^N.
    pub fn z(&self) -> Vec<F> {
        let mut z = Vec::with_capacity(self.x.len() + self.w.len());
        z.extend_from_slice(&self.x);
        z.extend_from_slice(&self.w);
        z
    }

    /// Direct PESAT satisfiability check, for prover-side sanity
    /// and test fixtures. Returns Ok(()) iff every p̂_j(x, w) = 0.
    pub fn check(&self, idx: &PesatIndex<F>) -> Result<()> {
        if self.x.len() != idx.n_pub {
            return Err(FoldingError::ShapeMismatch(format!(
                "x.len() = {}, expected n_pub = {}",
                self.x.len(),
                idx.n_pub
            )));
        }
        if self.w.len() != idx.k {
            return Err(FoldingError::ShapeMismatch(format!(
                "w.len() = {}, expected k = {}",
                self.w.len(),
                idx.k
            )));
        }
        let z = self.z();
        for (j, c) in idx.constraints.iter().enumerate() {
            let v = c.evaluate(&z);
            if !v.is_zero() {
                return Err(FoldingError::ConstraintNonZero {
                    idx: j,
                    value: format!("{v:?}"),
                });
            }
        }
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use expander_mersenne31::M31Ext6;

    type F = M31Ext6;

    fn f(n: u32) -> F {
        F::from(n)
    }

    /// Single constraint encoding y = x1·x2 + x3 over variables
    /// (x1, x2, x3, y) with n_pub = 3, k = 1.
    fn toy_index() -> PesatIndex<F> {
        // p̂(x1, x2, x3, y) = x1·x2 + x3 − y
        let c = Constraint {
            terms: vec![
                Term {
                    coeff: f(1),
                    vars: vec![0, 1],
                },
                Term {
                    coeff: f(1),
                    vars: vec![2],
                },
                Term {
                    coeff: -f(1),
                    vars: vec![3],
                },
            ],
        };
        PesatIndex {
            constraints: vec![c],
            n_pub: 3,
            k: 1,
            d: 2,
        }
    }

    #[test]
    fn toy_index_validates() {
        toy_index().validate().unwrap();
    }

    #[test]
    fn satisfying_instance_checks() {
        let idx = toy_index();
        let inst = PesatInstance {
            x: vec![f(3), f(4), f(5)],
            w: vec![f(17)],
        };
        inst.check(&idx).unwrap();
    }

    #[test]
    fn nonsatisfying_instance_rejected() {
        let idx = toy_index();
        let inst = PesatInstance {
            x: vec![f(3), f(4), f(5)],
            w: vec![f(99)],
        };
        assert!(matches!(
            inst.check(&idx),
            Err(FoldingError::ConstraintNonZero { idx: 0, .. })
        ));
    }

    #[test]
    fn shape_mismatch_rejected() {
        let idx = toy_index();
        let inst = PesatInstance {
            x: vec![f(3), f(4)],
            w: vec![f(17)],
        };
        assert!(matches!(
            inst.check(&idx),
            Err(FoldingError::ShapeMismatch(_))
        ));
    }

    #[test]
    fn degree_bound_enforced() {
        let bad = PesatIndex {
            constraints: vec![Constraint {
                terms: vec![Term {
                    coeff: f(1),
                    vars: vec![0, 0, 0],
                }],
            }],
            n_pub: 1,
            k: 0,
            d: 2,
        };
        assert!(matches!(
            bad.validate(),
            Err(FoldingError::DegreeExceeded {
                expected: 2,
                actual: 3
            })
        ));
    }
}
