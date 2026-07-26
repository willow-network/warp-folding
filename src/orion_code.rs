//! Orion linear code from Xie–Zhang–Song 2022 (`https://eprint.iacr.org/2022/1010`).
//!
//! This file is vendored from Polyhedra Expander
//! (`https://github.com/PolyhedraZK/Expander`, **AGPL-3.0**) at
//! `poly_commit/src/orion/linear_code.rs`. Earlier revisions of this header
//! described the upstream as MIT/Apache-2.0, which was incorrect — upstream
//! Expander is AGPL-3.0 and carries no separate license under `poly_commit/`.
//! This crate is AGPL-3.0-only for that reason. The original carries the
//! soundness analysis (Druk–Ishai-14 distance-by-induction with the
//! `ORION_CODE_PARAMETER_INSTANCE` parameters from Section 5 of the
//! Orion paper). We import it as the certified production replacement
//! for the `SpielmanCode` benchmark stub in `code.rs`.
//!
//! The thin [`OrionLinearCode`] wrapper at the bottom adapts the
//! Expander API surface to our crate's [`crate::code::LinearCode`]
//! trait. Everything above the marker is a verbatim copy with only the
//! local-module reference re-pointed and the upstream `arith` rename
//! adjusted to our `expander_arith` dependency name.

use std::cmp;

use expander_arith::Field;
use itertools::{chain, izip};
use rand::seq::index;
use serdes::ExpSerde;
use thiserror::Error;

#[derive(Debug, Error)]
pub enum OrionPCSError {
    #[error("Orion PCS linear code parameter unmatch error")]
    ParameterUnmatchError,
}

pub type OrionResult<T> = std::result::Result<T, OrionPCSError>;

// ===========================================================================
// Vendored verbatim from Expander `poly_commit/src/orion/linear_code.rs`
// ===========================================================================

/*
 * IMPLEMENTATIONS FOR ORION EXPANDER GRAPH
 */

pub type DirectedEdge = usize;

pub type DirectedNeighboring = Vec<DirectedEdge>;

#[derive(Clone, Debug, Default, ExpSerde)]
pub struct OrionExpanderGraph {
    // L R vertices size book keeping:
    // keep track of message length (l), and "compressed" code length (r)
    pub l_vertices_size: usize,
    pub r_vertices_size: usize,

    // neighboring stands for all (weighted) connected vertices of a vertex.
    // In this context, the neighborings stands for the neighborings
    // of vertices in R set of the bipariate graph, which explains why it has
    // size of l_vertices_size, while each neighboring reserved r_vertices_size
    // capacity.
    pub neighborings: Vec<DirectedNeighboring>,
}

impl OrionExpanderGraph {
    pub fn new(
        l_vertices_size: usize,
        r_vertices_size: usize,
        expanding_degree: usize,
        mut rng: impl rand::RngCore,
    ) -> Self {
        let mut neighborings: Vec<DirectedNeighboring> =
            vec![Vec::with_capacity(l_vertices_size); r_vertices_size];

        (0..l_vertices_size).for_each(|l_index| {
            let random_r_vertices = index::sample(&mut rng, r_vertices_size, expanding_degree);

            random_r_vertices
                .iter()
                .for_each(|r_index| neighborings[r_index].push(l_index))
        });

        Self {
            neighborings,
            l_vertices_size,
            r_vertices_size,
        }
    }

    #[inline(always)]
    pub fn expander_mul<F: Field>(
        &self,
        l_vertices: &[F],
        r_vertices: &mut [F],
    ) -> OrionResult<()> {
        if l_vertices.len() != self.l_vertices_size || r_vertices.len() != self.r_vertices_size {
            return Err(OrionPCSError::ParameterUnmatchError);
        }

        izip!(r_vertices, &self.neighborings).for_each(|(ri, ni)| {
            *ri = ni.iter().map(|&edge_i| l_vertices[edge_i]).sum();
        });

        Ok(())
    }
}

/*
 * IMPLEMENTATIONS FOR ORION CODE FROM EXPANDER GRAPH
 */

#[derive(Debug, Clone, Copy, PartialEq)]
pub struct OrionCodeParameter {
    // parameter for graph g0, that maps n -> (\alpha_g0 n)
    // \alpha_g0 should be ranging in (0, 1)
    pub alpha_g0: f64,
    pub degree_g0: usize,

    // parameter regarding graph generation for the code:
    // stopping condition when message is too short for the recursive code
    // in the next round.
    pub length_threshold_g0s: usize,

    // parameter for graph g1, let the message in the middle has length L,
    // then the graph g1 maps L -> (\alpha_g1 L)
    pub alpha_g1: f64,
    pub degree_g1: usize,

    // code's relateive distance
    pub hamming_weight: f64,
}

// NOTE: This instance of code derives from Orion paper Section 5.
pub const ORION_CODE_PARAMETER_INSTANCE: OrionCodeParameter = OrionCodeParameter {
    alpha_g0: 0.33,
    degree_g0: 6,

    length_threshold_g0s: 12,

    alpha_g1: 0.337,
    degree_g1: 6,

    hamming_weight: 0.055,
};

#[allow(clippy::doc_lazy_continuation)]
/// ACKNOWLEDGEMENT: on alphabet being F2 binary case, we appreciate the help from
/// - Section 18 in essential coding theory
///   <https://cse.buffalo.edu/faculty/atri/courses/coding-theory/book/web-coding-book.pdf>
///
/// - Notes from coding theory
///   <https://www.cs.cmu.edu/~venkatg/teaching/codingtheory/notes/notes8.pdf>
///
/// - Druk-Ishai 2014
///   <https://dl.acm.org/doi/10.1145/2554797.2554815>

#[derive(Clone, Debug, Default, ExpSerde)]
pub struct OrionExpanderGraphPositioned {
    pub graph: OrionExpanderGraph,

    pub input_starts: usize,
    pub output_starts: usize,
    pub output_ends: usize,
}

impl OrionExpanderGraphPositioned {
    #[inline(always)]
    pub fn new(
        input_starts: usize,
        output_starts: usize,
        output_ends: usize,
        expanding_degree: usize,
        mut rng: impl rand::RngCore,
    ) -> Self {
        Self {
            graph: OrionExpanderGraph::new(
                output_starts - input_starts,
                output_ends - output_starts + 1,
                expanding_degree,
                &mut rng,
            ),
            input_starts,
            output_starts,
            output_ends,
        }
    }

    #[inline(always)]
    pub fn expander_mul<F: Field>(&self, buffer: &mut [F], scratch: &mut [F]) -> OrionResult<()> {
        let input_ref = &buffer[self.input_starts..self.output_starts];
        let output_ref = &mut scratch[self.output_starts..self.output_ends + 1];

        self.graph.expander_mul(input_ref, output_ref)?;
        buffer[self.output_starts..self.output_ends + 1].copy_from_slice(output_ref);

        Ok(())
    }
}

// NOTE: The OrionCode here is representing an instance of Spielman code
// (Spielman96), that relies on 2 lists of expander graphs serving as
// error reduction code, and thus the linear error correction code derive
// from the parity matrices corresponding to these expander graphs.
#[derive(Clone, Debug, Default, ExpSerde)]
pub struct OrionCode {
    pub hamming_weight: f64,

    // empirical parameters for this instance of expander code on input/codeword
    pub msg_len: usize,
    pub codeword_len: usize,

    // g0s (affecting left side alphabets of the codeword)
    // generated from the largest to the smallest
    pub g0s: Vec<OrionExpanderGraphPositioned>,

    // g1s (affecting right side alphabets of the codeword)
    // generated from the smallest to the largest
    pub g1s: Vec<OrionExpanderGraphPositioned>,
}

pub type OrionCodeword<F> = Vec<F>;

impl OrionCode {
    pub fn new(params: OrionCodeParameter, msg_len: usize, mut rng: impl rand::RngCore) -> Self {
        // NOTE: sanity check - 1 / threshold_len > hamming_weight
        // as was part of Druk-Ishai-14 distance proof by induction
        assert!(1f64 / (params.length_threshold_g0s as f64) > params.hamming_weight);

        // NOTE: sanity check for both alpha_g0 and alpha_g1
        assert!(0f64 < params.alpha_g0 && params.alpha_g0 < 1f64);
        assert!(0f64 < params.alpha_g1 && params.alpha_g1 < 1f64);

        // NOTE: the real deal of code instance generation starts here
        let mut recursive_g0_output_starts: Vec<usize> = Vec::new();

        let mut g0s: Vec<OrionExpanderGraphPositioned> = Vec::new();
        let mut g1s: Vec<OrionExpanderGraphPositioned> = Vec::new();

        let mut g0_input_starts = 0;
        let mut g0_output_starts = msg_len;

        while g0_output_starts - g0_input_starts > params.length_threshold_g0s {
            let n = g0_output_starts - g0_input_starts;
            let g0_output_len = (n as f64 * params.alpha_g0).round() as usize;
            let degree_g0 = cmp::min(params.degree_g0, g0_output_len);

            g0s.push(OrionExpanderGraphPositioned::new(
                g0_input_starts,
                g0_output_starts,
                g0_output_starts + g0_output_len - 1,
                degree_g0,
                &mut rng,
            ));

            recursive_g0_output_starts.push(g0_output_starts);

            (g0_input_starts, g0_output_starts) =
                (g0_output_starts, g0_output_starts + g0_output_len);
        }

        // After g0s are generated, we generate g1s
        let mut g1_output_starts = g0_output_starts;

        while let Some(g1_input_starts) = recursive_g0_output_starts.pop() {
            let n = g1_output_starts - g1_input_starts;
            let g1_output_len = (n as f64 * params.alpha_g1).round() as usize;
            let degree_g1 = cmp::min(params.degree_g1, g1_output_len);

            g1s.push(OrionExpanderGraphPositioned::new(
                g1_input_starts,
                g1_output_starts,
                g1_output_starts + g1_output_len - 1,
                degree_g1,
                &mut rng,
            ));

            g1_output_starts += g1_output_len;
        }

        let codeword_len = g1_output_starts;
        Self {
            hamming_weight: params.hamming_weight,
            msg_len,
            codeword_len,
            g0s,
            g1s,
        }
    }

    #[inline(always)]
    pub fn code_len(&self) -> usize {
        self.codeword_len
    }

    #[inline(always)]
    pub fn msg_len(&self) -> usize {
        self.msg_len
    }

    #[inline(always)]
    pub fn hamming_weight(&self) -> f64 {
        self.hamming_weight
    }

    #[inline(always)]
    pub fn encode<F: Field>(&self, msg: &[F]) -> OrionResult<OrionCodeword<F>> {
        let mut codeword = vec![F::ZERO; self.code_len()];
        self.encode_in_place(msg, &mut codeword)?;
        Ok(codeword)
    }

    #[inline(always)]
    pub fn encode_in_place<F: Field>(&self, msg: &[F], buffer: &mut [F]) -> OrionResult<()> {
        if msg.len() != self.msg_len() || buffer.len() != self.code_len() {
            return Err(OrionPCSError::ParameterUnmatchError);
        }

        buffer[..self.msg_len()].copy_from_slice(msg);
        let mut scratch = vec![F::ZERO; self.code_len()];

        chain!(&self.g0s, &self.g1s).try_for_each(|g| g.expander_mul(buffer, &mut scratch))
    }
}

// ===========================================================================
// `LinearCode<F>` wrapper bridging to our crate's trait.
// ===========================================================================

use crate::code::LinearCode;

/// Production-grade linear-code instantiation backed by Expander's
/// `OrionCode` with the published `ORION_CODE_PARAMETER_INSTANCE`
/// parameters (Orion paper §5: `alpha_g0 = 0.33, degree_g0 = 6,
/// alpha_g1 = 0.337, degree_g1 = 6, hamming_weight = 0.055`).
///
/// Replaces the bench-only `SpielmanCode` / `IdentityCode` stubs on the
/// production WARP path. Distance is carried by the Druk–Ishai-14
/// induction proof cited in the Orion paper.
///
/// MLE compatibility: `OrionCode::code_len()` is not generally a power
/// of two; the wrapper pads the codeword to the next power of two with
/// zeros so the multilinear-extension layer (Constructions 7.2 / 8.2)
/// can index by `log_n` bits.
#[derive(Clone, Debug)]
pub struct OrionLinearCode {
    inner: OrionCode,
    codeword_len_padded: usize,
}

impl OrionLinearCode {
    /// Build a deterministic Orion code instance for messages of length
    /// `msg_len` (must be a power of two ≥ 16 — Orion's recursive code
    /// construction needs enough room for `length_threshold_g0s = 12`
    /// to bottom out cleanly).
    pub fn new(msg_len: usize, seed: [u8; 32]) -> Self {
        use rand::SeedableRng;
        assert!(
            msg_len.is_power_of_two() && msg_len >= 16,
            "OrionLinearCode requires power-of-two msg_len ≥ 16 (got {msg_len})"
        );
        let rng = rand_chacha::ChaCha20Rng::from_seed(seed);
        let inner = OrionCode::new(ORION_CODE_PARAMETER_INSTANCE, msg_len, rng);
        let codeword_len_padded = inner.code_len().next_power_of_two();
        Self {
            inner,
            codeword_len_padded,
        }
    }

    /// Raw codeword length before MLE-padding to the next power of two.
    pub fn raw_codeword_len(&self) -> usize {
        self.inner.code_len()
    }

    /// Hamming weight (relative distance bound) for the underlying
    /// Orion code. Carried from `ORION_CODE_PARAMETER_INSTANCE`.
    pub fn hamming_weight(&self) -> f64 {
        self.inner.hamming_weight()
    }
}

impl<F: Field> LinearCode<F> for OrionLinearCode {
    fn message_len(&self) -> usize {
        self.inner.msg_len()
    }

    fn codeword_len(&self) -> usize {
        self.codeword_len_padded
    }

    fn encode(&self, message: &[F]) -> Vec<F> {
        let mut codeword = self
            .inner
            .encode(message)
            .expect("OrionCode::encode invariants violated");
        codeword.resize(self.codeword_len_padded, F::zero());
        codeword
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
    fn orion_linear_code_is_linear() {
        let code = OrionLinearCode::new(64, [0x42; 32]);
        let a: Vec<F> = (0..64).map(|i| f((i + 1) as u32)).collect();
        let b: Vec<F> = (0..64).map(|i| f((100 + i) as u32)).collect();
        let combined: Vec<F> = a.iter().zip(b.iter()).map(|(x, y)| *x + *y).collect();

        let enc_a = <OrionLinearCode as LinearCode<F>>::encode(&code, &a);
        let enc_b = <OrionLinearCode as LinearCode<F>>::encode(&code, &b);
        let enc_combined = <OrionLinearCode as LinearCode<F>>::encode(&code, &combined);

        let summed: Vec<F> = enc_a
            .iter()
            .zip(enc_b.iter())
            .map(|(x, y)| *x + *y)
            .collect();
        assert_eq!(enc_combined, summed);
    }

    #[test]
    fn orion_codeword_length_is_power_of_two() {
        for log_k in 4..=10 {
            let k = 1usize << log_k;
            let code = OrionLinearCode::new(k, [0xAB; 32]);
            assert!(<OrionLinearCode as LinearCode<F>>::codeword_len(&code).is_power_of_two());
            assert!(
                <OrionLinearCode as LinearCode<F>>::codeword_len(&code) >= code.raw_codeword_len()
            );
        }
    }

    #[test]
    fn orion_is_deterministic_per_seed() {
        let c1 = OrionLinearCode::new(64, [0xCD; 32]);
        let c2 = OrionLinearCode::new(64, [0xCD; 32]);
        let msg: Vec<F> = (0..64).map(|i| f(i as u32)).collect();
        assert_eq!(
            <OrionLinearCode as LinearCode<F>>::encode(&c1, &msg),
            <OrionLinearCode as LinearCode<F>>::encode(&c2, &msg),
        );
    }

    #[test]
    fn orion_codeword_starts_with_message() {
        // Like SpielmanCode the systematic prefix means `c[0..k] = w`.
        let code = OrionLinearCode::new(64, [0xEF; 32]);
        let msg: Vec<F> = (0..64).map(|i| f((i + 1) as u32)).collect();
        let cw = <OrionLinearCode as LinearCode<F>>::encode(&code, &msg);
        assert_eq!(&cw[..64], &msg[..]);
    }

    #[test]
    fn orion_carries_published_hamming_weight() {
        // From `ORION_CODE_PARAMETER_INSTANCE` in the Orion paper §5.
        let code = OrionLinearCode::new(64, [0x00; 32]);
        assert!((code.hamming_weight() - 0.055).abs() < 1e-9);
    }
}
