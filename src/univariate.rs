//! Small univariate-polynomial helper used to represent the per-round
//! sumcheck message. Stored as evaluations at `0, 1, …, degree` so
//! `eval(0) + eval(1)` is a direct lookup and Lagrange interpolation
//! at an arbitrary point is O(degree).

use expander_arith::Field;
use serdes::ExpSerde;

/// A univariate polynomial represented by its evaluations at
/// `X = 0, 1, …, degree`.
#[derive(Clone, Debug, PartialEq, Eq, ExpSerde)]
pub struct UnivariatePoly<F: Field + ExpSerde> {
    pub evals: Vec<F>,
}

impl<F: Field> UnivariatePoly<F> {
    pub fn degree(&self) -> usize {
        self.evals.len().saturating_sub(1)
    }

    pub fn eval_at_0(&self) -> F {
        self.evals[0]
    }

    pub fn eval_at_1(&self) -> F {
        self.evals[1]
    }

    /// Lagrange-interpolate and evaluate at an arbitrary point.
    ///
    /// L_i(x) = ∏_{j ≠ i} (x − j) / (i − j), summed with evals[i].
    /// O(degree²) — acceptable for the small degrees we use.
    pub fn evaluate(&self, x: F) -> F {
        let n = self.evals.len();
        if n == 0 {
            return F::zero();
        }
        let mut result = F::zero();
        for i in 0..n {
            let mut num = F::one();
            let mut den = F::one();
            for j in 0..n {
                if i == j {
                    continue;
                }
                num *= x - F::from(j as u32);
                den *= F::from(i as u32) - F::from(j as u32);
            }
            result += self.evals[i] * num * den.inv().unwrap();
        }
        result
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

    #[test]
    fn degree_zero_constant() {
        let p = UnivariatePoly { evals: vec![f(7)] };
        assert_eq!(p.degree(), 0);
        assert_eq!(p.evaluate(f(0)), f(7));
        assert_eq!(p.evaluate(f(5)), f(7));
    }

    #[test]
    fn linear_through_known_points() {
        // p(x) = 3 + 2x: p(0) = 3, p(1) = 5, p(2) = 7
        let p = UnivariatePoly {
            evals: vec![f(3), f(5)],
        };
        assert_eq!(p.evaluate(f(0)), f(3));
        assert_eq!(p.evaluate(f(1)), f(5));
        assert_eq!(p.evaluate(f(2)), f(7));
        assert_eq!(p.evaluate(f(10)), f(23));
    }

    #[test]
    fn quadratic_interpolates_correctly() {
        // p(x) = x² + x + 1: p(0)=1, p(1)=3, p(2)=7
        let p = UnivariatePoly {
            evals: vec![f(1), f(3), f(7)],
        };
        // p(3) = 9+3+1 = 13
        assert_eq!(p.evaluate(f(3)), f(13));
        // p(4) = 16+4+1 = 21
        assert_eq!(p.evaluate(f(4)), f(21));
    }
}
