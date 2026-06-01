//! Fiat-Shamir compilation of Construction 9.4.
//!
//! Wraps the IOR-level prove/verify functions in a transcript-driven
//! flow that interleaves message absorbs with challenge squeezes
//! according to the paper's protocol order. Under the random-oracle
//! model this gives a non-interactive fold.
//!
//! The transcript-driven path is the production-relevant entry point;
//! the explicit-challenge functions in `constr_*` remain for unit-
//! testing the IOR layer.

use expander_arith::Field;
use serdes::ExpSerde;

use crate::constr_6_3::{self, evaluate_h, fold_at, SchemeParams, TwinPseudoBatchingMsg};
use crate::constr_7_2::{BatchedEvalClaims, CodewordBatchingMsg};
use crate::constr_8_2::{
    batching_weights, fix_bottom_variable, initial_eq_star, interpolate_degree_2, round_message,
    sigma_2, MultilinearBatchingMsg,
};
use crate::constr_9_4::FoldMessage;
use crate::error::{FoldingError, Result};
use crate::transcript::Transcript;
use crate::twin::{
    eq_scalar, mle_eval, BundledConstraint, TwinConstrainedInstance, TwinConstrainedWitness,
};
use crate::univariate::UnivariatePoly;

/// Sampling parameters for the FS-compiled fold. Together with
/// `SchemeParams`, these pin the transcript shape so prover and
/// verifier derive matching challenges.
#[derive(Clone, Debug)]
pub struct SamplingParams {
    /// Number of out-of-domain samples `s` for Construction 7.2.
    pub n_ood: usize,
    /// Number of in-domain shift queries `t` for Construction 7.2.
    pub n_shifts: usize,
}

const TRANSCRIPT_LABEL: &[u8] = b"willow-folding/warp/v0";

pub fn prove_with_transcript<F: Field + ExpSerde>(
    instances: &[TwinConstrainedInstance<F>; 2],
    witnesses: &[TwinConstrainedWitness<F>; 2],
    p_b: &BundledConstraint<F>,
    params: &SchemeParams,
    sampling: &SamplingParams,
) -> Result<(
    TwinConstrainedInstance<F>,
    TwinConstrainedWitness<F>,
    FoldMessage<F>,
)> {
    prove_with_transcript_rep(instances, witnesses, p_b, params, sampling, 0, &[])
}

/// Run the FS-compiled fold prover with a specific repetition index.
/// Used by `prove_with_parallel_rep` to derive independent transcripts
/// per repetition for parallel-repetition soundness amplification.
///
/// `external_binding` is absorbed into the FS transcript at the start,
/// **before** the instances. Higher layers use this to bind the fold
/// proof to authenticated per-block data (block hash, output root,
/// completeness-proof hash, etc.) — a prover that lies about any of
/// those inputs gets divergent FS challenges and the IOR rejects.
/// Pass `&[]` to keep the legacy unbound transcript.
pub fn prove_with_transcript_rep<F: Field + ExpSerde>(
    instances: &[TwinConstrainedInstance<F>; 2],
    witnesses: &[TwinConstrainedWitness<F>; 2],
    p_b: &BundledConstraint<F>,
    params: &SchemeParams,
    sampling: &SamplingParams,
    rep_index: u32,
    external_binding: &[u8],
) -> Result<(
    TwinConstrainedInstance<F>,
    TwinConstrainedWitness<F>,
    FoldMessage<F>,
)> {
    let mut t = Transcript::new(TRANSCRIPT_LABEL);
    t.absorb_bytes(b"rep");
    t.absorb_bytes(&rep_index.to_le_bytes());
    if !external_binding.is_empty() {
        t.absorb_bytes(b"ext-bind");
        t.absorb_bytes(&(external_binding.len() as u64).to_le_bytes());
        t.absorb_bytes(external_binding);
    }
    absorb_instances(&mut t, instances);

    let (pseudo_inst, pseudo_wit, msg_6_3) =
        prove_6_3_via_transcript(&mut t, instances, witnesses, p_b, params)?;

    let (claims, msg_7_2) =
        prove_7_2_via_transcript(&mut t, &pseudo_inst, &pseudo_wit, sampling, params)?;

    let (final_inst, msg_8_2) =
        prove_8_2_via_transcript(&mut t, &claims, &pseudo_wit.f, params.log_n)?;

    Ok((
        final_inst,
        pseudo_wit,
        FoldMessage {
            twin_pseudo_batching: msg_6_3,
            codeword_batching: msg_7_2,
            multilinear_batching: msg_8_2,
        },
    ))
}

pub fn verify_with_transcript<F: Field + ExpSerde>(
    instances: &[TwinConstrainedInstance<F>; 2],
    params: &SchemeParams,
    sampling: &SamplingParams,
    msg: &FoldMessage<F>,
) -> Result<TwinConstrainedInstance<F>> {
    verify_with_transcript_rep(instances, params, sampling, msg, 0, &[])
}

/// Verify a single-rep fold message against an `external_binding`. Must
/// match the `external_binding` the prover used or the FS challenges
/// diverge and the IOR rejects.
pub fn verify_with_transcript_rep<F: Field + ExpSerde>(
    instances: &[TwinConstrainedInstance<F>; 2],
    params: &SchemeParams,
    sampling: &SamplingParams,
    msg: &FoldMessage<F>,
    rep_index: u32,
    external_binding: &[u8],
) -> Result<TwinConstrainedInstance<F>> {
    let mut t = Transcript::new(TRANSCRIPT_LABEL);
    t.absorb_bytes(b"rep");
    t.absorb_bytes(&rep_index.to_le_bytes());
    if !external_binding.is_empty() {
        t.absorb_bytes(b"ext-bind");
        t.absorb_bytes(&(external_binding.len() as u64).to_le_bytes());
        t.absorb_bytes(external_binding);
    }
    absorb_instances(&mut t, instances);

    let pseudo_inst =
        verify_6_3_via_transcript(&mut t, instances, params, &msg.twin_pseudo_batching)?;

    let claims = verify_7_2_via_transcript(
        &mut t,
        &pseudo_inst,
        sampling,
        params,
        &msg.codeword_batching,
    )?;

    let final_inst =
        verify_8_2_via_transcript(&mut t, &claims, params.log_n, &msg.multilinear_batching)?;

    Ok(final_inst)
}

/// Run the prover with `r` parallel repetitions for soundness
/// amplification. Returns the rep-0 folded instance/witness (the
/// canonical accumulator the chain uses going forward) plus all `r`
/// fold messages — each rep folds at its own (τ, ω, γ, …) so the
/// folded values DIFFER across reps; the other reps are independent
/// soundness audits proved with the same instances.
///
/// Soundness amplification: if per-rep error is `ε`, the verifier
/// rejects a cheating prover with probability `≥ 1 − ε^r`. We rely on
/// the per-rep WARP soundness bound from eprint 2025/753 (see
/// Theorem 10.4 and the supporting bounds in §6.3, §7.2, §8.2). At
/// `r = 2` over M31Ext3 the squared bound clears the 128-bit target
/// for the parameter ranges this crate targets; the exact derivation
/// lives in the paper rather than being recomputed here.
///
/// Cost is `r ×` single-rep prove. Verifier work is also `r ×`.
pub fn prove_with_parallel_rep<F: Field + ExpSerde>(
    instances: &[TwinConstrainedInstance<F>; 2],
    witnesses: &[TwinConstrainedWitness<F>; 2],
    p_b: &BundledConstraint<F>,
    params: &SchemeParams,
    sampling: &SamplingParams,
    r: u32,
) -> Result<(
    TwinConstrainedInstance<F>,
    TwinConstrainedWitness<F>,
    Vec<FoldMessage<F>>,
)> {
    prove_with_parallel_rep_bound(instances, witnesses, p_b, params, sampling, r, &[])
}

/// As [`prove_with_parallel_rep`] but with an `external_binding` that
/// the FS transcript absorbs at the start of each rep. Higher layers
/// pass per-block public data (block hash, output root,
/// completeness-proof hash, etc.) so a wrong-input prover diverges.
pub fn prove_with_parallel_rep_bound<F: Field + ExpSerde + Send + Sync>(
    instances: &[TwinConstrainedInstance<F>; 2],
    witnesses: &[TwinConstrainedWitness<F>; 2],
    p_b: &BundledConstraint<F>,
    params: &SchemeParams,
    sampling: &SamplingParams,
    r: u32,
    external_binding: &[u8],
) -> Result<(
    TwinConstrainedInstance<F>,
    TwinConstrainedWitness<F>,
    Vec<FoldMessage<F>>,
)> {
    use rayon::prelude::*;
    assert!(r >= 1, "parallel rep count must be ≥ 1");

    // Reps are independent — each builds its own FS transcript seeded
    // from (external_binding, rep). Parallelize across rayon's pool.
    let results: Vec<_> = (0..r)
        .into_par_iter()
        .map(|rep| {
            prove_with_transcript_rep(
                instances,
                witnesses,
                p_b,
                params,
                sampling,
                rep,
                external_binding,
            )
        })
        .collect::<Result<Vec<_>>>()?;

    let mut messages = Vec::with_capacity(r as usize);
    let mut canonical_inst = None;
    let mut canonical_wit = None;
    for (rep, (inst, wit, msg)) in results.into_iter().enumerate() {
        if rep == 0 {
            canonical_inst = Some(inst);
            canonical_wit = Some(wit);
        }
        messages.push(msg);
    }
    Ok((canonical_inst.unwrap(), canonical_wit.unwrap(), messages))
}

/// Verify all `r` parallel-rep fold messages. Each rep produces an
/// independent folded instance (different γ per rep); we return rep
/// 0's folded instance as the canonical chain output.
pub fn verify_with_parallel_rep<F: Field + ExpSerde>(
    instances: &[TwinConstrainedInstance<F>; 2],
    params: &SchemeParams,
    sampling: &SamplingParams,
    messages: &[FoldMessage<F>],
) -> Result<TwinConstrainedInstance<F>> {
    verify_with_parallel_rep_bound(instances, params, sampling, messages, &[])
}

/// As [`verify_with_parallel_rep`] but with an `external_binding` the
/// verifier absorbs at the start of each rep's transcript. Must match
/// what the prover used.
pub fn verify_with_parallel_rep_bound<F: Field + ExpSerde>(
    instances: &[TwinConstrainedInstance<F>; 2],
    params: &SchemeParams,
    sampling: &SamplingParams,
    messages: &[FoldMessage<F>],
    external_binding: &[u8],
) -> Result<TwinConstrainedInstance<F>> {
    if messages.is_empty() {
        return Err(FoldingError::ShapeMismatch(
            "parallel-rep verify requires at least one message".into(),
        ));
    }
    let mut canonical = None;
    for (rep, msg) in messages.iter().enumerate() {
        let inst = verify_with_transcript_rep(
            instances,
            params,
            sampling,
            msg,
            rep as u32,
            external_binding,
        )?;
        if rep == 0 {
            canonical = Some(inst);
        }
    }
    Ok(canonical.unwrap())
}

fn absorb_instances<F: Field + ExpSerde>(
    t: &mut Transcript,
    instances: &[TwinConstrainedInstance<F>; 2],
) {
    for inst in instances {
        t.absorb_field_vec(&inst.alpha);
        t.absorb_field(&inst.mu);
        t.absorb_field_vec(&inst.beta);
        t.absorb_field(&inst.eta);
        // Bind the input-codeword Merkle commit. The decider catches
        // forgery terminally, but the IOR's soundness analysis assumes
        // a BCS-style compilation where every public commitment is
        // absorbed before the first challenge is squeezed.
        t.absorb_bytes(&inst.merkle_root);
    }
}

// -------------------------------------------------------------
// Construction 6.3 — twin pseudo-batching, FS-driven (ℓ = 2).
// -------------------------------------------------------------

fn prove_6_3_via_transcript<F: Field + ExpSerde>(
    t: &mut Transcript,
    instances: &[TwinConstrainedInstance<F>; 2],
    witnesses: &[TwinConstrainedWitness<F>; 2],
    p_b: &BundledConstraint<F>,
    params: &SchemeParams,
) -> Result<(
    TwinConstrainedInstance<F>,
    TwinConstrainedWitness<F>,
    TwinPseudoBatchingMsg<F>,
)> {
    let tau: F = t.squeeze_field();
    let omega: F = t.squeeze_field();

    let degree = params.h_degree();
    // Parallel over the degree+1 evaluation points — each is an
    // independent O(n) MLE eval over the linearly-interpolated codeword.
    // Worth parallelizing only when the inner work is non-trivial; at
    // small log_n the overhead dominates.
    const PAR_LOG_N_THRESHOLD: usize = 8;
    let h_evals: Vec<F> = if params.log_n >= PAR_LOG_N_THRESHOLD {
        use rayon::prelude::*;
        (0..=degree)
            .into_par_iter()
            .map(|i| {
                let x = F::from(i as u32);
                evaluate_h(instances, witnesses, p_b, params, tau, omega, x)
            })
            .collect()
    } else {
        (0..=degree)
            .map(|i| {
                let x = F::from(i as u32);
                evaluate_h(instances, witnesses, p_b, params, tau, omega, x)
            })
            .collect()
    };
    let h = UnivariatePoly { evals: h_evals };
    t.absorb_field_vec(&h.evals);

    let gamma: F = t.squeeze_field();
    let (folded_inst, folded_wit) = fold_at(instances, witnesses, p_b, gamma);

    // Bind the prover's claimed (mu_new, eta_new) into the transcript
    // so subsequent IOR challenges depend on them.
    t.absorb_field(&folded_inst.mu);
    t.absorb_field(&folded_inst.eta);

    Ok((
        folded_inst.clone(),
        folded_wit,
        TwinPseudoBatchingMsg {
            h,
            mu_new: folded_inst.mu,
            eta_new: folded_inst.eta,
        },
    ))
}

fn verify_6_3_via_transcript<F: Field + ExpSerde>(
    t: &mut Transcript,
    instances: &[TwinConstrainedInstance<F>; 2],
    params: &SchemeParams,
    msg: &TwinPseudoBatchingMsg<F>,
) -> Result<TwinConstrainedInstance<F>> {
    let tau: F = t.squeeze_field();
    let omega: F = t.squeeze_field();

    if msg.h.degree() != params.h_degree() {
        return Err(FoldingError::DegreeExceeded {
            expected: params.h_degree(),
            actual: msg.h.degree(),
        });
    }
    t.absorb_field_vec(&msg.h.evals);

    let gamma: F = t.squeeze_field();

    let inst = constr_6_3::verify_ell_2(instances, params, tau, omega, gamma, msg)?;
    t.absorb_field(&inst.mu);
    t.absorb_field(&inst.eta);
    Ok(inst)
}

// -------------------------------------------------------------
// Construction 7.2 — codeword batching, FS-driven.
// -------------------------------------------------------------

fn prove_7_2_via_transcript<F: Field + ExpSerde>(
    t: &mut Transcript,
    instance: &TwinConstrainedInstance<F>,
    witness: &TwinConstrainedWitness<F>,
    sampling: &SamplingParams,
    params: &SchemeParams,
) -> Result<(BatchedEvalClaims<F>, CodewordBatchingMsg<F>)> {
    let log_n = params.log_n;
    let n = 1usize << log_n;

    // Build Merkle tree over folded codeword and absorb the root
    // BEFORE squeezing OOD/shift challenges so the prover is bound
    // to the codeword before seeing the verifier's queries.
    let tree = crate::merkle::MerkleTree::build(&witness.f);
    let merkle_root = tree.root();
    t.absorb_bytes(&merkle_root);

    // Squeeze OOD points, compute and absorb their evaluations.
    let mut ood_points = Vec::with_capacity(sampling.n_ood);
    for _ in 0..sampling.n_ood {
        ood_points.push(t.squeeze_field_vec::<F>(log_n));
    }
    let ood_evals: Vec<F> = ood_points.iter().map(|z| mle_eval(&witness.f, z)).collect();
    t.absorb_field_vec(&ood_evals);

    // Squeeze shift queries, expose the leaf values + Merkle paths.
    let mut shift_queries = Vec::with_capacity(sampling.n_shifts);
    for _ in 0..sampling.n_shifts {
        shift_queries.push(t.squeeze_index(n));
    }
    let shift_values: Vec<F> = shift_queries.iter().map(|&i| witness.f[i]).collect();
    let shift_paths: Vec<crate::merkle::MerklePath> =
        shift_queries.iter().map(|&i| tree.open(i)).collect();
    t.absorb_field_vec(&shift_values);

    // Squeeze the batching point ξ (length log r where r = 1 + s + t).
    let r = 1 + sampling.n_ood + sampling.n_shifts;
    if !r.is_power_of_two() {
        return Err(FoldingError::ShapeMismatch(format!(
            "r = 1 + n_ood + n_shifts = {r} must be a power of two"
        )));
    }
    let log_r = r.trailing_zeros() as usize;
    let xi = t.squeeze_field_vec::<F>(log_r);

    let claims = assemble_claims_7_2(
        instance,
        &ood_points,
        &shift_queries,
        &xi,
        &ood_evals,
        &shift_values,
        log_n,
        merkle_root,
    );
    Ok((
        claims,
        CodewordBatchingMsg {
            merkle_root,
            ood_evals,
            shift_values,
            shift_paths,
        },
    ))
}

fn verify_7_2_via_transcript<F: Field + ExpSerde>(
    t: &mut Transcript,
    instance: &TwinConstrainedInstance<F>,
    sampling: &SamplingParams,
    params: &SchemeParams,
    msg: &CodewordBatchingMsg<F>,
) -> Result<BatchedEvalClaims<F>> {
    let log_n = params.log_n;
    let n = 1usize << log_n;

    if msg.ood_evals.len() != sampling.n_ood
        || msg.shift_values.len() != sampling.n_shifts
        || msg.shift_paths.len() != sampling.n_shifts
    {
        return Err(FoldingError::ShapeMismatch(
            "7.2 message length mismatch with sampling params".into(),
        ));
    }

    // Absorb the prover's Merkle root commitment before deriving any
    // OOD or shift-query challenges.
    t.absorb_bytes(&msg.merkle_root);

    let mut ood_points = Vec::with_capacity(sampling.n_ood);
    for _ in 0..sampling.n_ood {
        ood_points.push(t.squeeze_field_vec::<F>(log_n));
    }
    t.absorb_field_vec(&msg.ood_evals);

    let mut shift_queries = Vec::with_capacity(sampling.n_shifts);
    for _ in 0..sampling.n_shifts {
        shift_queries.push(t.squeeze_index(n));
    }
    // Authenticate every shift-query value against the committed root.
    for ((leaf, path), &idx) in msg
        .shift_values
        .iter()
        .zip(msg.shift_paths.iter())
        .zip(shift_queries.iter())
    {
        if !crate::merkle::verify_path(&msg.merkle_root, leaf, idx, n, path) {
            return Err(FoldingError::ShapeMismatch(format!(
                "FS Merkle path verification failed at shift index {idx}"
            )));
        }
    }
    t.absorb_field_vec(&msg.shift_values);

    let r = 1 + sampling.n_ood + sampling.n_shifts;
    if !r.is_power_of_two() {
        return Err(FoldingError::ShapeMismatch(format!(
            "r = 1 + n_ood + n_shifts = {r} must be a power of two"
        )));
    }
    let xi = t.squeeze_field_vec::<F>(r.trailing_zeros() as usize);

    Ok(assemble_claims_7_2(
        instance,
        &ood_points,
        &shift_queries,
        &xi,
        &msg.ood_evals,
        &msg.shift_values,
        log_n,
        msg.merkle_root,
    ))
}

#[allow(clippy::too_many_arguments)]
fn assemble_claims_7_2<F: Field>(
    instance: &TwinConstrainedInstance<F>,
    ood_points: &[Vec<F>],
    shift_queries: &[usize],
    xi: &[F],
    ood_evals: &[F],
    shift_values: &[F],
    log_n: usize,
    merkle_root: crate::merkle::Digest32,
) -> BatchedEvalClaims<F> {
    let mut zetas = Vec::with_capacity(1 + ood_points.len() + shift_queries.len());
    zetas.push(instance.alpha.clone());
    for z in ood_points {
        zetas.push(z.clone());
    }
    for &i in shift_queries {
        zetas.push(index_to_boolean::<F>(i, log_n));
    }

    let mut nus = Vec::with_capacity(zetas.len());
    nus.push(instance.mu);
    nus.extend_from_slice(ood_evals);
    nus.extend_from_slice(shift_values);

    BatchedEvalClaims {
        zetas,
        nus,
        xi: xi.to_vec(),
        beta: instance.beta.clone(),
        eta: instance.eta,
        merkle_root,
    }
}

fn index_to_boolean<F: Field>(mut idx: usize, nbits: usize) -> Vec<F> {
    let mut out = Vec::with_capacity(nbits);
    for _ in 0..nbits {
        out.push(if idx & 1 == 1 { F::one() } else { F::zero() });
        idx >>= 1;
    }
    out
}

// -------------------------------------------------------------
// Construction 8.2 — multilinear-constraint batching, FS-driven.
// One sumcheck round per α coordinate; each round absorbs the
// round polynomial before squeezing the next challenge.
// -------------------------------------------------------------

fn prove_8_2_via_transcript<F: Field + ExpSerde>(
    t: &mut Transcript,
    claims: &BatchedEvalClaims<F>,
    codeword: &[F],
    log_n: usize,
) -> Result<(TwinConstrainedInstance<F>, MultilinearBatchingMsg<F>)> {
    if codeword.len() != 1 << log_n {
        return Err(FoldingError::CodewordLengthMismatch {
            n: 1 << log_n,
            got: codeword.len(),
        });
    }

    let weights = batching_weights(claims);
    let mut eq_star = initial_eq_star(&claims.zetas, &weights, log_n);
    let mut f_current = codeword.to_vec();
    let mut alpha = Vec::with_capacity(log_n);
    let mut round_polys = Vec::with_capacity(log_n);

    for _ in 0..log_n {
        let msg = round_message(&eq_star, &f_current);
        t.absorb_field_vec(&msg.evals);
        round_polys.push(msg);

        let alpha_r: F = t.squeeze_field();
        alpha.push(alpha_r);
        fix_bottom_variable(&mut eq_star, alpha_r);
        fix_bottom_variable(&mut f_current, alpha_r);
    }
    debug_assert_eq!(eq_star.len(), 1);
    debug_assert_eq!(f_current.len(), 1);
    let mu_new = f_current[0];
    t.absorb_field(&mu_new);

    Ok((
        TwinConstrainedInstance {
            alpha,
            mu: mu_new,
            beta: claims.beta.clone(),
            eta: claims.eta,
            merkle_root: claims.merkle_root,
        },
        MultilinearBatchingMsg {
            round_polys,
            mu_new,
        },
    ))
}

fn verify_8_2_via_transcript<F: Field + ExpSerde>(
    t: &mut Transcript,
    claims: &BatchedEvalClaims<F>,
    log_n: usize,
    msg: &MultilinearBatchingMsg<F>,
) -> Result<TwinConstrainedInstance<F>> {
    if msg.round_polys.len() != log_n {
        return Err(FoldingError::ShapeMismatch(format!(
            "msg.round_polys.len() = {}, expected log_n = {log_n}",
            msg.round_polys.len()
        )));
    }

    let weights = batching_weights(claims);
    let mut current_claim = sigma_2(&weights, &claims.nus);
    let mut alpha = Vec::with_capacity(log_n);

    for (round_idx, round_msg) in msg.round_polys.iter().enumerate() {
        let sum = round_msg.evals[0] + round_msg.evals[1];
        if sum != current_claim {
            return Err(FoldingError::ShapeMismatch(format!(
                "round {round_idx}: ĥ(0) + ĥ(1) ≠ current claim"
            )));
        }
        t.absorb_field_vec(&round_msg.evals);
        let alpha_r: F = t.squeeze_field();
        current_claim = interpolate_degree_2(&round_msg.evals, alpha_r);
        alpha.push(alpha_r);
    }

    let eq_star_at_alpha = eval_eq_star(&claims.zetas, &weights, &alpha);
    if eq_star_at_alpha * msg.mu_new != current_claim {
        return Err(FoldingError::ShapeMismatch(
            "final 8.2 claim fails eq*(α) · μ_new = last-round-poly(α_{log n})".into(),
        ));
    }
    t.absorb_field(&msg.mu_new);

    Ok(TwinConstrainedInstance {
        alpha,
        mu: msg.mu_new,
        beta: claims.beta.clone(),
        eta: claims.eta,
        merkle_root: claims.merkle_root,
    })
}

fn eval_eq_star<F: Field>(zetas: &[Vec<F>], weights: &[F], alpha: &[F]) -> F {
    let mut acc = F::zero();
    for (z, w) in zetas.iter().zip(weights.iter()) {
        acc += *w * eq_scalar(z, alpha);
    }
    acc
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::code::IdentityCode;
    use crate::constr_5_10;
    use crate::decider;
    use crate::pesat::{Constraint, PesatIndex, PesatInstance, Term};
    use expander_mersenne31::M31Ext6;

    type F = M31Ext6;
    fn f(n: u32) -> F {
        F::from(n)
    }

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

    fn setup() -> (
        [TwinConstrainedInstance<F>; 2],
        [TwinConstrainedWitness<F>; 2],
        BundledConstraint<F>,
        SchemeParams,
        SamplingParams,
        IdentityCode,
    ) {
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
        // r = 1 + 1 + 2 = 4 → log r = 2 ✓ power of two
        let sampling = SamplingParams {
            n_ood: 1,
            n_shifts: 2,
        };
        (
            [twin_0, twin_1],
            [wit_0, wit_1],
            p_b,
            params,
            sampling,
            code,
        )
    }

    #[test]
    fn fs_round_trip() {
        let (instances, witnesses, p_b, params, sampling, code) = setup();
        let (folded_inst, folded_wit, msg) =
            prove_with_transcript(&instances, &witnesses, &p_b, &params, &sampling).unwrap();
        let verified = verify_with_transcript(&instances, &params, &sampling, &msg).unwrap();
        assert_eq!(folded_inst, verified);
        decider::decide(&folded_inst, &folded_wit, &code, &p_b).unwrap();
    }

    #[test]
    fn fs_tampered_h_rejected() {
        let (instances, witnesses, p_b, params, sampling, _) = setup();
        let (_, _, mut msg) =
            prove_with_transcript(&instances, &witnesses, &p_b, &params, &sampling).unwrap();
        msg.twin_pseudo_batching.h.evals[0] += f(1);
        assert!(verify_with_transcript(&instances, &params, &sampling, &msg).is_err());
    }

    #[test]
    fn fs_tampered_ood_eval_rejected() {
        let (instances, witnesses, p_b, params, sampling, _) = setup();
        let (_, _, mut msg) =
            prove_with_transcript(&instances, &witnesses, &p_b, &params, &sampling).unwrap();
        msg.codeword_batching.ood_evals[0] += f(1);
        // Tampering ood_evals shifts the squeezed shift-query indices in
        // the verifier's transcript replay, breaking the σ⁽²⁾ check or
        // the final eq* product.
        assert!(verify_with_transcript(&instances, &params, &sampling, &msg).is_err());
    }

    #[test]
    fn fs_tampered_merkle_root_rejected() {
        let (instances, witnesses, p_b, params, sampling, _) = setup();
        let (_, _, mut msg) =
            prove_with_transcript(&instances, &witnesses, &p_b, &params, &sampling).unwrap();
        msg.codeword_batching.merkle_root[0] ^= 1;
        // Path verification fails because the root is now wrong.
        assert!(verify_with_transcript(&instances, &params, &sampling, &msg).is_err());
    }

    #[test]
    fn fs_tampered_shift_path_rejected() {
        let (instances, witnesses, p_b, params, sampling, _) = setup();
        let (_, _, mut msg) =
            prove_with_transcript(&instances, &witnesses, &p_b, &params, &sampling).unwrap();
        msg.codeword_batching.shift_paths[0].siblings[0][0] ^= 1;
        assert!(verify_with_transcript(&instances, &params, &sampling, &msg).is_err());
    }

    #[test]
    fn fs_tampered_round_poly_rejected() {
        let (instances, witnesses, p_b, params, sampling, _) = setup();
        let (_, _, mut msg) =
            prove_with_transcript(&instances, &witnesses, &p_b, &params, &sampling).unwrap();
        msg.multilinear_batching.round_polys[0].evals[0] += f(1);
        assert!(verify_with_transcript(&instances, &params, &sampling, &msg).is_err());
    }

    #[test]
    fn fs_changing_input_changes_challenges() {
        // Same protocol, different instance → different transcript →
        // different folded result.
        let (instances_a, witnesses_a, p_b, params, sampling, _) = setup();
        let mut instances_b = instances_a.clone();
        instances_b[0].mu += f(1);
        // Note: swapping mu without correspondingly fixing the witness
        // will fail soundness, so we don't expect verify to accept; we
        // only verify the prover produces a *different* folded instance.
        let mut witnesses_b = witnesses_a.clone();
        witnesses_b[0].f[0] += f(1); // make it self-consistent so prover succeeds
        let (folded_a, _, _) =
            prove_with_transcript(&instances_a, &witnesses_a, &p_b, &params, &sampling).unwrap();
        let (folded_b, _, _) =
            prove_with_transcript(&instances_b, &witnesses_b, &p_b, &params, &sampling).unwrap();
        assert_ne!(folded_a.alpha, folded_b.alpha);
    }
}
