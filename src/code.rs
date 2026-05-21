//! Linear-code abstraction.
//!
//! WARP works over any linear code admitting mutual correlated
//! agreement. We expose the encoding side of the API: `encode(w) →
//! C(w) ∈ F^n` (codeword length `n` is power-of-two for MLE
//! compatibility).
//!
//! Two implementations:
//! - `IdentityCode` — `n = k`, used for IOR-level correctness tests
//!   where encoding cost should be negligible.
//! - `SpielmanCode` — Spielman-style expander code with two cascaded
//!   sparse-matrix multiplications. Encoder is `O(k · degree)` field
//!   ops; the codeword `c = (w, G₁·w, G₂·G₁·w)` is zero-padded to
//!   the next power of two for MLE compatibility. Used for Phase 3
//!   benchmarks and as a realistic stand-in for the Orion paper's
//!   tuned-parameter code (which would also need its expander-graph
//!   sampling certified for distance — out of scope for benchmarks).

use expander_arith::Field;
use rand::{Rng, RngCore, SeedableRng};
use rand_chacha::ChaCha20Rng;

pub trait LinearCode<F: Field> {
    /// Message length `k`.
    fn message_len(&self) -> usize;
    /// Codeword length `n`. Must be a power of 2.
    fn codeword_len(&self) -> usize;
    /// `log₂(codeword_len)`.
    fn log_codeword_len(&self) -> usize {
        self.codeword_len().trailing_zeros() as usize
    }
    /// Encode a length-`k` message into a length-`n` codeword.
    fn encode(&self, message: &[F]) -> Vec<F>;
}

/// Trivial linear code `C(w) = w`. Requires `k = n` where `n` is a
/// power of two.
#[derive(Clone, Debug)]
pub struct IdentityCode {
    pub k: usize,
}

impl IdentityCode {
    pub fn new(k: usize) -> Self {
        assert!(
            k.is_power_of_two(),
            "IdentityCode requires power-of-two length"
        );
        Self { k }
    }
}

impl<F: Field> LinearCode<F> for IdentityCode {
    fn message_len(&self) -> usize {
        self.k
    }
    fn codeword_len(&self) -> usize {
        self.k
    }
    fn encode(&self, message: &[F]) -> Vec<F> {
        assert_eq!(message.len(), self.k);
        message.to_vec()
    }
}

/// One stage of a Spielman-style expander multiplication: a sparse
/// `out_len × in_len` random matrix where each output row is a linear
/// combination of `degree` inputs at random positions with random
/// non-zero weights. Stored as the per-output `(input_index, weight)`
/// pairs so multiplication is `O(out_len · degree)`.
#[derive(Clone, Debug)]
struct ExpanderStage<F: Field> {
    in_len: usize,
    /// For each output row: a list of (input_idx, weight) with
    /// length `degree`. Output count is `rows.len()`.
    rows: Vec<Vec<(usize, F)>>,
}

impl<F: Field> ExpanderStage<F> {
    fn new(in_len: usize, out_len: usize, degree: usize, rng: &mut impl RngCore) -> Self {
        let degree = degree.min(in_len);
        assert!(degree > 0);
        let mut rows = Vec::with_capacity(out_len);
        for _ in 0..out_len {
            let mut row = Vec::with_capacity(degree);
            // Sample `degree` distinct input indices via Fisher-Yates-style
            // partial shuffle. For our parameter regimes (degree ≪ in_len)
            // simple rejection is adequate.
            let mut taken = vec![false; in_len];
            let mut count = 0;
            while count < degree {
                let idx = rng.gen_range(0..in_len);
                if !taken[idx] {
                    taken[idx] = true;
                    let mut weight = F::random_unsafe(&mut *rng);
                    while weight.is_zero() {
                        weight = F::random_unsafe(&mut *rng);
                    }
                    row.push((idx, weight));
                    count += 1;
                }
            }
            rows.push(row);
        }
        Self { in_len, rows }
    }

    fn multiply(&self, input: &[F]) -> Vec<F> {
        assert_eq!(input.len(), self.in_len);
        // Each output row is an independent dot product over `degree`
        // sparse positions. Parallelize when output size is large
        // enough to amortize rayon overhead.
        const PAR_THRESHOLD: usize = 1024;
        if self.rows.len() >= PAR_THRESHOLD {
            use rayon::prelude::*;
            self.rows
                .par_iter()
                .map(|row| {
                    let mut acc = F::zero();
                    for &(idx, w) in row {
                        acc += input[idx] * w;
                    }
                    acc
                })
                .collect()
        } else {
            self.rows
                .iter()
                .map(|row| {
                    let mut acc = F::zero();
                    for &(idx, w) in row {
                        acc += input[idx] * w;
                    }
                    acc
                })
                .collect()
        }
    }
}

/// Two-cascade Spielman-style code:
/// `c = (w, G₁·w, G₂·G₁·w)` then zero-padded to the next power of two.
///
/// `α₁ = α₂ = 0.5` means each cascade halves the dimension; combined
/// pre-pad codeword length is `k + k/2 + k/4 = 1.75k`; padded length
/// is `2k` for k a power of two. Per-row degree `degree = 6` mirrors
/// Orion's tuned `g = 6` parameter.
///
/// Soundness disclaimer: the random expander-graph sampling here is
/// not certified for any specific distance bound — it's structurally
/// the right shape for benchmarks. Production deployment would adopt
/// Orion's tuned parameters + their expander-graph testing algorithm
/// (or a different code with a proof) and re-derive the MCA constant.
#[derive(Clone, Debug)]
pub struct SpielmanCode<F: Field> {
    msg_len: usize,
    raw_codeword_len: usize,
    padded_codeword_len: usize,
    g1: ExpanderStage<F>,
    g2: ExpanderStage<F>,
}

impl<F: Field> SpielmanCode<F> {
    pub const DEFAULT_DEGREE: usize = 6;

    /// Build a fresh code instance for messages of length `msg_len`
    /// (must be a power of two ≥ 4) using a deterministic seed. Two
    /// SpielmanCodes built with the same seed are byte-identical.
    pub fn new(msg_len: usize, seed: u64) -> Self {
        Self::new_with_degree(msg_len, seed, Self::DEFAULT_DEGREE)
    }

    pub fn new_with_degree(msg_len: usize, seed: u64, degree: usize) -> Self {
        assert!(
            msg_len.is_power_of_two() && msg_len >= 4,
            "SpielmanCode requires power-of-two msg_len ≥ 4 (got {msg_len})"
        );
        let mut rng = ChaCha20Rng::seed_from_u64(seed);
        let half = msg_len / 2;
        let quarter = msg_len / 4;
        let g1 = ExpanderStage::new(msg_len, half, degree, &mut rng);
        let g2 = ExpanderStage::new(half, quarter, degree, &mut rng);
        let raw_codeword_len = msg_len + half + quarter;
        let padded_codeword_len = raw_codeword_len.next_power_of_two();
        Self {
            msg_len,
            raw_codeword_len,
            padded_codeword_len,
            g1,
            g2,
        }
    }

    pub fn raw_codeword_len(&self) -> usize {
        self.raw_codeword_len
    }
}

impl<F: Field> LinearCode<F> for SpielmanCode<F> {
    fn message_len(&self) -> usize {
        self.msg_len
    }
    fn codeword_len(&self) -> usize {
        self.padded_codeword_len
    }
    fn encode(&self, message: &[F]) -> Vec<F> {
        assert_eq!(message.len(), self.msg_len);
        let mid = self.g1.multiply(message);
        let tail = self.g2.multiply(&mid);
        let mut out = Vec::with_capacity(self.padded_codeword_len);
        out.extend_from_slice(message);
        out.extend_from_slice(&mid);
        out.extend_from_slice(&tail);
        out.resize(self.padded_codeword_len, F::zero());
        out
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
    fn identity_code_linearity() {
        let code = IdentityCode::new(4);
        let a = [f(1), f(2), f(3), f(4)];
        let b = [f(5), f(6), f(7), f(8)];
        let combined: Vec<F> = a.iter().zip(b.iter()).map(|(x, y)| *x + *y).collect();
        assert_eq!(
            <IdentityCode as LinearCode<F>>::encode(&code, &combined),
            a.iter()
                .zip(b.iter())
                .map(|(x, y)| *x + *y)
                .collect::<Vec<_>>()
        );
    }

    #[test]
    fn spielman_code_is_linear() {
        let code: SpielmanCode<F> = SpielmanCode::new(16, 0x123);
        let a: Vec<F> = (0..16).map(|i| f((i + 1) as u32)).collect();
        let b: Vec<F> = (0..16).map(|i| f((100 + i) as u32)).collect();
        let combined: Vec<F> = a.iter().zip(b.iter()).map(|(x, y)| *x + *y).collect();

        let enc_a = code.encode(&a);
        let enc_b = code.encode(&b);
        let enc_combined = code.encode(&combined);

        let summed: Vec<F> = enc_a
            .iter()
            .zip(enc_b.iter())
            .map(|(x, y)| *x + *y)
            .collect();
        assert_eq!(enc_combined, summed);
    }

    #[test]
    fn spielman_code_is_deterministic_per_seed() {
        let c1: SpielmanCode<F> = SpielmanCode::new(16, 0xabcd);
        let c2: SpielmanCode<F> = SpielmanCode::new(16, 0xabcd);
        let msg: Vec<F> = (0..16).map(|i| f(i as u32)).collect();
        assert_eq!(c1.encode(&msg), c2.encode(&msg));
    }

    #[test]
    fn spielman_code_codeword_length_is_power_of_two() {
        for k in [4usize, 8, 16, 32, 64, 256, 1024] {
            let code: SpielmanCode<F> = SpielmanCode::new(k, 0);
            assert!(code.codeword_len().is_power_of_two());
            assert!(code.codeword_len() >= code.raw_codeword_len());
        }
    }

    #[test]
    fn spielman_codeword_starts_with_message() {
        // The systematic prefix means c[0..k] = w. Useful for tests
        // that need the witness recoverable from the codeword.
        let code: SpielmanCode<F> = SpielmanCode::new(8, 0xfeed);
        let msg: Vec<F> = (0..8).map(|i| f((i + 1) as u32)).collect();
        let cw = code.encode(&msg);
        assert_eq!(&cw[..8], &msg[..]);
    }
}
