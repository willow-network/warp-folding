//! Minimal Fiat-Shamir transcript for the WARP fold.
//!
//! A simple Keccak-256 sponge: absorb arbitrary bytes, squeeze field
//! elements / indices via SHA3-256 of (state || counter). Subsequent
//! absorbs after a squeeze fold the squeezed output into the state, so
//! the next challenge depends on every prior absorb and squeeze.
//!
//! This is the byte-level transcript layer. The full BCS compilation
//! adds Merkle commitments and matches Willow's existing Keccak-Merkle
//! convention. For Phase 2 polish, the transcript alone is enough to
//! make the fold non-interactive.

use expander_arith::Field;
use serdes::ExpSerde;
use sha3::{Digest, Sha3_256};

#[derive(Clone, Debug)]
pub struct Transcript {
    state: Sha3_256,
}

impl Transcript {
    pub fn new(label: &[u8]) -> Self {
        let mut state = Sha3_256::new();
        state.update(label);
        Self { state }
    }

    pub fn absorb_bytes(&mut self, bytes: &[u8]) {
        self.state.update(bytes);
    }

    pub fn absorb_usize(&mut self, n: usize) {
        self.state.update((n as u64).to_le_bytes());
    }

    pub fn absorb_field<F: Field + ExpSerde>(&mut self, x: &F) {
        let mut buf = Vec::new();
        x.serialize_into(&mut buf).expect("ExpSerde Vec write");
        self.state.update(&buf);
    }

    pub fn absorb_field_vec<F: Field + ExpSerde>(&mut self, xs: &[F]) {
        self.absorb_usize(xs.len());
        for x in xs {
            self.absorb_field(x);
        }
    }

    /// Derive `n` bytes by hashing `state || counter` for monotone
    /// counter values. Folds the squeezed output back into the state
    /// so subsequent absorbs and squeezes remain bound.
    pub fn squeeze_bytes(&mut self, n: usize) -> Vec<u8> {
        let mut out = Vec::with_capacity(n);
        let mut counter: u64 = 0;
        while out.len() < n {
            let mut h = self.state.clone();
            h.update(b"squeeze");
            h.update(counter.to_le_bytes());
            let digest = h.finalize();
            let take = (n - out.len()).min(32);
            out.extend_from_slice(&digest[..take]);
            counter += 1;
        }
        // Bind the squeeze into state for subsequent operations.
        self.state.update(b"after-squeeze");
        self.state.update(&out);
        out
    }

    pub fn squeeze_field<F: Field>(&mut self) -> F {
        let bytes_needed = F::SIZE.max(32);
        let raw = self.squeeze_bytes(bytes_needed);
        F::from_uniform_bytes(&raw)
    }

    pub fn squeeze_field_vec<F: Field>(&mut self, n: usize) -> Vec<F> {
        (0..n).map(|_| self.squeeze_field::<F>()).collect()
    }

    /// Sample a uniform index in `[0, bound)` from 8 squeeze bytes.
    /// For `bound < 2^32` the modular bias is ≤ `2^-32`, cryptographically
    /// negligible at our security parameters.
    pub fn squeeze_index(&mut self, bound: usize) -> usize {
        assert!(bound > 0);
        let raw = self.squeeze_bytes(8);
        let v = u64::from_le_bytes(raw[..8].try_into().unwrap()) as usize;
        v % bound
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use expander_mersenne31::M31Ext6;

    type F = M31Ext6;

    #[test]
    fn determinism_same_label_same_output() {
        let mut t1 = Transcript::new(b"willow-folding/test");
        let mut t2 = Transcript::new(b"willow-folding/test");
        t1.absorb_bytes(b"some-data");
        t2.absorb_bytes(b"some-data");
        let f1: F = t1.squeeze_field();
        let f2: F = t2.squeeze_field();
        assert_eq!(f1, f2);
    }

    #[test]
    fn absorb_diverges_output() {
        let mut t1 = Transcript::new(b"label");
        let mut t2 = Transcript::new(b"label");
        t1.absorb_bytes(b"branch-a");
        t2.absorb_bytes(b"branch-b");
        let f1: F = t1.squeeze_field();
        let f2: F = t2.squeeze_field();
        assert_ne!(f1, f2);
    }

    #[test]
    fn sequential_squeezes_diverge() {
        let mut t = Transcript::new(b"label");
        let f1: F = t.squeeze_field();
        let f2: F = t.squeeze_field();
        assert_ne!(f1, f2);
    }

    #[test]
    fn label_diverges_output() {
        let mut t1 = Transcript::new(b"label-a");
        let mut t2 = Transcript::new(b"label-b");
        let f1: F = t1.squeeze_field();
        let f2: F = t2.squeeze_field();
        assert_ne!(f1, f2);
    }

    #[test]
    fn squeeze_index_bounded() {
        let mut t = Transcript::new(b"idx-test");
        for _ in 0..100 {
            let i = t.squeeze_index(16);
            assert!(i < 16);
        }
    }
}
