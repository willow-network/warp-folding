//! WARP Construction 8.2 — Multilinear-constraint batching IOR.
//!
//! Collapses the `r = 1 + s + t` multilinear-evaluation claims from
//! Construction 7.2 into a single `f̂(α_new) = μ_new` claim via a
//! log-n-round sumcheck on the virtual polynomial
//!
//!   P(a) = eq*(a) · f̂(a),  where
//!   eq*(a) = Σ_{i=0..r-1} eq(bin(i), ξ) · eq(ζ_i, a)
//!
//! The prover's sumcheck claim is
//!   σ⁽²⁾ = Σ_{a ∈ {0,1}^{log n}} eq*(a) · f̂(a)
//!        = Σ_i eq(bin(i), ξ) · ν_i
//! which the verifier can compute from `(ξ, ν)` directly.
//!
//! Each round polynomial has degree 2 (product of two multilinears
//! linear in the current variable), sent as evaluations at X=0,1,2.
//! After log n rounds, the prover commits to α_new and opens
//! μ_new = f̂(α_new); the verifier checks that the sumcheck's final
//! claim factors as `eq*(α_new) · μ_new`.

use expander_arith::Field;

use crate::constr_7_2::BatchedEvalClaims;
use crate::error::{FoldingError, Result};
use crate::twin::{eq_scalar, TwinConstrainedInstance};

/// One round's sumcheck message: evaluations of the round polynomial
/// at X = 0, 1, 2. (Degree-2 polynomial ⇒ 3 evaluations uniquely
/// determine it.)
#[derive(Clone, Debug, PartialEq, Eq, serdes::ExpSerde)]
pub struct SumcheckRoundMsg<F: Field + serdes::ExpSerde> {
    pub evals: [F; 3],
}

/// Prover's Construction 8.2 message.
#[derive(Clone, Debug, PartialEq, Eq, serdes::ExpSerde)]
pub struct MultilinearBatchingMsg<F: Field + serdes::ExpSerde> {
    /// One per sumcheck round; len = log n.
    pub round_polys: Vec<SumcheckRoundMsg<F>>,
    /// Claimed f̂(α_new) after the sumcheck completes.
    pub mu_new: F,
}

#[cfg(all(test, feature = "cuda"))]
mod cuda_correctness_tests {
    use super::*;
    use crate::constr_7_2::BatchedEvalClaims;
    use crate::merkle::Digest32;
    use crate::twin::mle_eval;
    use expander_arith::Field;
    use expander_mersenne31::M31Ext3;
    use rand::rngs::StdRng;
    use rand::SeedableRng;

    fn make_inputs(
        batch: usize,
        log_n: usize,
        seed: u64,
    ) -> Vec<(BatchedEvalClaims<M31Ext3>, Vec<M31Ext3>, Vec<M31Ext3>)> {
        let n = 1 << log_n;
        let mut rng = StdRng::seed_from_u64(seed);
        (0..batch)
            .map(|_| {
                let codeword: Vec<M31Ext3> =
                    (0..n).map(|_| M31Ext3::random_unsafe(&mut rng)).collect();
                let z0: Vec<M31Ext3> = (0..log_n)
                    .map(|_| M31Ext3::random_unsafe(&mut rng))
                    .collect();
                let z1: Vec<M31Ext3> = (0..log_n)
                    .map(|_| M31Ext3::random_unsafe(&mut rng))
                    .collect();
                let zetas = vec![z0.clone(), z1.clone()];
                let nus = vec![mle_eval(&codeword, &z0), mle_eval(&codeword, &z1)];
                let xi = vec![M31Ext3::random_unsafe(&mut rng)];
                let claims = BatchedEvalClaims {
                    zetas,
                    nus,
                    xi,
                    beta: vec![],
                    eta: M31Ext3::default(),
                    merkle_root: Digest32::default(),
                };
                let alpha_new: Vec<M31Ext3> = (0..log_n)
                    .map(|_| M31Ext3::random_unsafe(&mut rng))
                    .collect();
                (claims, codeword, alpha_new)
            })
            .collect()
    }

    #[test]
    fn single_cuda_matches_cpu() {
        let inputs = make_inputs(1, 6, 0xc0deu64);
        let (claims, codeword, alpha_new) = &inputs[0];
        let (cpu_inst, cpu_msg) = prove(claims, codeword, alpha_new).unwrap();
        let (gpu_inst, gpu_msg) = prove_cuda(claims, codeword, alpha_new).unwrap();
        assert_eq!(cpu_inst.mu, gpu_inst.mu);
        assert_eq!(cpu_msg.mu_new, gpu_msg.mu_new);
        assert_eq!(cpu_msg.round_polys.len(), gpu_msg.round_polys.len());
        for (r, (cpu_r, gpu_r)) in cpu_msg
            .round_polys
            .iter()
            .zip(gpu_msg.round_polys.iter())
            .enumerate()
        {
            assert_eq!(cpu_r.evals, gpu_r.evals, "round {r} evals mismatch");
        }
    }

    #[test]
    fn batched_matches_cpu() {
        for &batch in &[1usize, 4, 16] {
            let inputs = make_inputs(batch, 6, 0xfeedu64 + batch as u64);
            let cpu_out: Vec<_> = inputs
                .iter()
                .map(|(c, f, a)| prove(c, f, a).unwrap())
                .collect();
            let gpu_out = prove_cuda_batched(&inputs).unwrap();
            assert_eq!(cpu_out.len(), gpu_out.len());
            for (i, ((cpu_inst, cpu_msg), (gpu_inst, gpu_msg))) in
                cpu_out.iter().zip(gpu_out.iter()).enumerate()
            {
                assert_eq!(cpu_inst.mu, gpu_inst.mu, "fold {i} mu mismatch");
                assert_eq!(cpu_msg.mu_new, gpu_msg.mu_new, "fold {i} mu_new mismatch");
                assert_eq!(
                    cpu_msg.round_polys.len(),
                    gpu_msg.round_polys.len(),
                    "fold {i} round count mismatch"
                );
                for (r, (cpu_r, gpu_r)) in cpu_msg
                    .round_polys
                    .iter()
                    .zip(gpu_msg.round_polys.iter())
                    .enumerate()
                {
                    assert_eq!(
                        cpu_r.evals, gpu_r.evals,
                        "fold {i} round {r} evals mismatch"
                    );
                }
            }
        }
    }
}

/// CUDA-backed prover for Construction 8.2's log-n sumcheck. Mirrors
/// `prove` but offloads `round_message` and `fix_bottom_variable` to
/// the M31Ext3 kernels under `cuda_kernels`. Only buildable when the
/// `cuda` feature is active *and* `nvcc` was found at build time.
#[cfg(feature = "cuda")]
pub fn prove_cuda(
    claims: &BatchedEvalClaims<expander_mersenne31::M31Ext3>,
    codeword: &[expander_mersenne31::M31Ext3],
    alpha_new: &[expander_mersenne31::M31Ext3],
) -> Result<(
    TwinConstrainedInstance<expander_mersenne31::M31Ext3>,
    MultilinearBatchingMsg<expander_mersenne31::M31Ext3>,
)> {
    use crate::cuda_kernels::{
        cudaFree, cudaMalloc, cudaMemcpy, cuda_m31ext3_poly_eval, cuda_m31ext3_receive_challenge,
        CUDA_MEMCPY_DEVICE_TO_HOST, CUDA_MEMCPY_HOST_TO_DEVICE,
    };
    use expander_arith::{ExtensionField, Field};
    use expander_mersenne31::{M31Ext3, M31};

    let log_n = claims.zetas[0].len();
    if alpha_new.len() != log_n {
        return Err(FoldingError::ShapeMismatch(format!(
            "alpha_new.len() = {}, expected log_n = {log_n}",
            alpha_new.len(),
        )));
    }
    let n = 1usize << log_n;
    if codeword.len() != n {
        return Err(FoldingError::CodewordLengthMismatch {
            n,
            got: codeword.len(),
        });
    }

    let weights = batching_weights(claims);
    let eq_star_host = initial_eq_star(&claims.zetas, &weights, log_n);

    // Pack to u32 limbs for the CUDA kernels (each Ext3 = 3 u32).
    let codeword_words: Vec<u32> = codeword
        .iter()
        .flat_map(|x| x.v.iter().map(|m| m.v))
        .collect();
    let eq_star_words: Vec<u32> = eq_star_host
        .iter()
        .flat_map(|x| x.v.iter().map(|m| m.v))
        .collect();

    let bytes = codeword_words.len() * 4;
    let mut round_polys = Vec::with_capacity(log_n);
    let mut alpha_observed: Vec<M31Ext3> = Vec::with_capacity(log_n);

    unsafe {
        let mut d_f: *mut std::ffi::c_void = std::ptr::null_mut();
        let mut d_hg: *mut std::ffi::c_void = std::ptr::null_mut();
        let mut d_result: *mut std::ffi::c_void = std::ptr::null_mut();
        let mut d_challenge: *mut std::ffi::c_void = std::ptr::null_mut();
        if cudaMalloc(&mut d_f, bytes) != 0
            || cudaMalloc(&mut d_hg, bytes) != 0
            || cudaMalloc(&mut d_result, 9 * 4) != 0
            || cudaMalloc(&mut d_challenge, 12) != 0
        {
            return Err(FoldingError::ShapeMismatch("CUDA allocation failed".into()));
        }
        cudaMemcpy(
            d_f,
            codeword_words.as_ptr() as *const _,
            bytes,
            CUDA_MEMCPY_HOST_TO_DEVICE,
        );
        cudaMemcpy(
            d_hg,
            eq_star_words.as_ptr() as *const _,
            bytes,
            CUDA_MEMCPY_HOST_TO_DEVICE,
        );

        let mut current_size = (n as u32) / 2;
        for &alpha_r in alpha_new {
            // Round-message kernel.
            let rc = cuda_m31ext3_poly_eval(
                d_f as *const u32,
                d_hg as *const u32,
                d_result as *mut u32,
                current_size,
            );
            if rc != 0 {
                cudaFree(d_f);
                cudaFree(d_hg);
                cudaFree(d_result);
                cudaFree(d_challenge);
                return Err(FoldingError::ShapeMismatch(format!(
                    "poly_eval kernel failed (rc={rc})"
                )));
            }

            // Pull back the 3 evaluation values to host. `cuda_m31ext3_poly_eval`
            // returns evals at X=0,1 directly in p0,p1 and a derived
            // p2 = (a0+a1)·(b0+b1) which equals our `f₂·eq*₂` form
            // (since f(2)=2f(1)−f(0) and similarly for eq*).
            let mut result_words = [0u32; 9];
            cudaMemcpy(
                result_words.as_mut_ptr() as *mut _,
                d_result as *const _,
                9 * 4,
                CUDA_MEMCPY_DEVICE_TO_HOST,
            );
            let unpack = |off: usize| -> M31Ext3 {
                M31Ext3::from_limbs(&[
                    M31 {
                        v: result_words[off],
                    },
                    M31 {
                        v: result_words[off + 1],
                    },
                    M31 {
                        v: result_words[off + 2],
                    },
                ])
            };
            let p0 = unpack(0);
            let p1 = unpack(3);
            let p_paired = unpack(6); // (f0+f1)·(eq0+eq1)
                                      // Convert paired form into our X=2 form. With pairs
                                      //   f₂ = 2·f1 − f0,  eq*₂ = 2·eq1 − eq0
                                      // the product f₂·eq*₂ = 4·f1·eq1 − 2·(f0·eq1 + f1·eq0) + f0·eq0.
                                      // The kernel's p_paired = (f0+f1)(eq0+eq1) = p0 + p1 + (f0·eq1 + f1·eq0),
                                      // so (f0·eq1 + f1·eq0) = p_paired − p0 − p1, giving
                                      //   f₂·eq*₂ = 4·p1 − 2·(p_paired − p0 − p1) + p0
                                      //           = 6·p1 + 3·p0 − 2·p_paired.
            let p2 = p1.double().double() + p1.double() + p0 + p0 + p0 - p_paired.double();
            round_polys.push(SumcheckRoundMsg {
                evals: [p0, p1, p2],
            });

            // Challenge update kernel: bk_f[i] = bk_f[2i] + (bk_f[2i+1]−bk_f[2i])·r
            let challenge_words: [u32; 3] = [alpha_r.v[0].v, alpha_r.v[1].v, alpha_r.v[2].v];
            cudaMemcpy(
                d_challenge,
                challenge_words.as_ptr() as *const _,
                12,
                CUDA_MEMCPY_HOST_TO_DEVICE,
            );
            let rc = cuda_m31ext3_receive_challenge(
                d_f as *mut u32,
                d_hg as *mut u32,
                d_challenge as *const u32,
                current_size,
                0,
                std::ptr::null(),
            );
            if rc != 0 {
                cudaFree(d_f);
                cudaFree(d_hg);
                cudaFree(d_result);
                cudaFree(d_challenge);
                return Err(FoldingError::ShapeMismatch(format!(
                    "receive_challenge kernel failed (rc={rc})"
                )));
            }
            alpha_observed.push(alpha_r);
            current_size /= 2;
        }

        // After log_n rounds the codeword is reduced to a single scalar.
        let mut final_words = [0u32; 3];
        cudaMemcpy(
            final_words.as_mut_ptr() as *mut _,
            d_f as *const _,
            12,
            CUDA_MEMCPY_DEVICE_TO_HOST,
        );
        cudaFree(d_f);
        cudaFree(d_hg);
        cudaFree(d_result);
        cudaFree(d_challenge);

        let mu_new = M31Ext3::from_limbs(&[
            M31 { v: final_words[0] },
            M31 { v: final_words[1] },
            M31 { v: final_words[2] },
        ]);

        let new_instance = TwinConstrainedInstance {
            alpha: alpha_observed,
            mu: mu_new,
            beta: claims.beta.clone(),
            eta: claims.eta,
            merkle_root: claims.merkle_root,
        };
        Ok((
            new_instance,
            MultilinearBatchingMsg {
                round_polys,
                mu_new,
            },
        ))
    }
}

/// Batched GPU prover: runs `batch_size = inputs.len()` independent
/// Construction 8.2 sumchecks in a single kernel dispatch sequence.
/// All folds use the SAME `eval_size`/`log_n` (must match) but
/// independent codewords, eq*, alpha_new sequences. Amortizes PCIe
/// transfer + kernel launch overhead across the batch.
#[cfg(feature = "cuda")]
pub fn prove_cuda_batched(
    inputs: &[(
        BatchedEvalClaims<expander_mersenne31::M31Ext3>,
        Vec<expander_mersenne31::M31Ext3>,
        Vec<expander_mersenne31::M31Ext3>,
    )],
) -> Result<
    Vec<(
        TwinConstrainedInstance<expander_mersenne31::M31Ext3>,
        MultilinearBatchingMsg<expander_mersenne31::M31Ext3>,
    )>,
> {
    use crate::cuda_kernels::{
        cudaFree, cudaMalloc, cudaMemcpy, cuda_m31ext3_poly_eval_batched,
        cuda_m31ext3_receive_challenge_batched, CUDA_MEMCPY_DEVICE_TO_HOST,
        CUDA_MEMCPY_HOST_TO_DEVICE,
    };
    use expander_arith::{ExtensionField, Field};
    use expander_mersenne31::{M31Ext3, M31};

    if inputs.is_empty() {
        return Ok(Vec::new());
    }
    let batch_size = inputs.len();
    let log_n = inputs[0].0.zetas[0].len();
    let n = 1usize << log_n;
    for (claims, codeword, alpha_new) in inputs {
        if claims.zetas[0].len() != log_n || alpha_new.len() != log_n || codeword.len() != n {
            return Err(FoldingError::ShapeMismatch(
                "all batched folds must share the same log_n / n".into(),
            ));
        }
    }

    // Pack codewords + initial eq* across the batch.
    let mut packed_f: Vec<u32> = Vec::with_capacity(batch_size * n * 3);
    let mut packed_hg: Vec<u32> = Vec::with_capacity(batch_size * n * 3);
    for (claims, codeword, _) in inputs {
        let weights = batching_weights(claims);
        let eq_star = initial_eq_star(&claims.zetas, &weights, log_n);
        for x in codeword {
            packed_f.extend(x.v.iter().map(|m| m.v));
        }
        for x in &eq_star {
            packed_hg.extend(x.v.iter().map(|m| m.v));
        }
    }

    let bytes = packed_f.len() * 4;
    let result_bytes = batch_size * 9 * 4;
    let challenge_bytes = batch_size * 3 * 4;

    unsafe {
        let mut d_f: *mut std::ffi::c_void = std::ptr::null_mut();
        let mut d_hg: *mut std::ffi::c_void = std::ptr::null_mut();
        let mut d_result: *mut std::ffi::c_void = std::ptr::null_mut();
        let mut d_challenge: *mut std::ffi::c_void = std::ptr::null_mut();
        if cudaMalloc(&mut d_f, bytes) != 0
            || cudaMalloc(&mut d_hg, bytes) != 0
            || cudaMalloc(&mut d_result, result_bytes) != 0
            || cudaMalloc(&mut d_challenge, challenge_bytes) != 0
        {
            return Err(FoldingError::ShapeMismatch(
                "CUDA allocation failed (batched)".into(),
            ));
        }
        cudaMemcpy(
            d_f,
            packed_f.as_ptr() as *const _,
            bytes,
            CUDA_MEMCPY_HOST_TO_DEVICE,
        );
        cudaMemcpy(
            d_hg,
            packed_hg.as_ptr() as *const _,
            bytes,
            CUDA_MEMCPY_HOST_TO_DEVICE,
        );

        let mut all_round_polys: Vec<Vec<SumcheckRoundMsg<M31Ext3>>> =
            (0..batch_size).map(|_| Vec::with_capacity(log_n)).collect();
        let mut current_size = (n as u32) / 2;
        let fold_stride_u32 = (n * 3) as u32;

        for round_idx in 0..log_n {
            // Run batched poly_eval.
            let rc = cuda_m31ext3_poly_eval_batched(
                d_f as *const u32,
                d_hg as *const u32,
                d_result as *mut u32,
                current_size,
                batch_size as u32,
                fold_stride_u32,
            );
            if rc != 0 {
                cudaFree(d_f);
                cudaFree(d_hg);
                cudaFree(d_result);
                cudaFree(d_challenge);
                return Err(FoldingError::ShapeMismatch(format!(
                    "batched poly_eval failed (rc={rc})"
                )));
            }

            // Pull per-fold p0/p1/p2 results back to host and convert
            // the (p0, p1, paired) triple into our (p0, p1, p2) form
            // — same conversion as the single-fold path.
            let mut all_results = vec![0u32; batch_size * 9];
            cudaMemcpy(
                all_results.as_mut_ptr() as *mut _,
                d_result as *const _,
                result_bytes,
                CUDA_MEMCPY_DEVICE_TO_HOST,
            );

            // Pack per-fold challenges for the next receive_challenge.
            let mut challenges_packed: Vec<u32> = Vec::with_capacity(batch_size * 3);
            for (b, (_, _, alpha_new)) in inputs.iter().enumerate() {
                let off = b * 9;
                let unpack = |idx: usize| -> M31Ext3 {
                    M31Ext3::from_limbs(&[
                        M31 {
                            v: all_results[off + idx],
                        },
                        M31 {
                            v: all_results[off + idx + 1],
                        },
                        M31 {
                            v: all_results[off + idx + 2],
                        },
                    ])
                };
                let p0 = unpack(0);
                let p1 = unpack(3);
                let p_paired = unpack(6);
                // Same conversion as single-fold: p2 = 6·p1 + 3·p0 − 2·p_paired.
                let p2 = p1.double().double() + p1.double() + p0 + p0 + p0 - p_paired.double();
                all_round_polys[b].push(SumcheckRoundMsg {
                    evals: [p0, p1, p2],
                });

                let r = alpha_new[round_idx];
                challenges_packed.push(r.v[0].v);
                challenges_packed.push(r.v[1].v);
                challenges_packed.push(r.v[2].v);
            }

            // Run batched receive_challenge.
            cudaMemcpy(
                d_challenge,
                challenges_packed.as_ptr() as *const _,
                challenge_bytes,
                CUDA_MEMCPY_HOST_TO_DEVICE,
            );
            let rc = cuda_m31ext3_receive_challenge_batched(
                d_f as *mut u32,
                d_hg as *mut u32,
                d_challenge as *const u32,
                current_size,
                batch_size as u32,
                fold_stride_u32,
            );
            if rc != 0 {
                cudaFree(d_f);
                cudaFree(d_hg);
                cudaFree(d_result);
                cudaFree(d_challenge);
                return Err(FoldingError::ShapeMismatch(format!(
                    "batched receive_challenge failed (rc={rc})"
                )));
            }
            current_size /= 2;
        }

        // Read final scalars (one per fold). Per-fold byte offset is
        // `fold_stride_u32 * 4` = `3 * n * 4` bytes; the final 3-u32
        // scalar sits at the start of each fold's slot.
        let stride_bytes = (fold_stride_u32 as usize) * 4;
        let mut all_finals = vec![0u32; batch_size * 3];
        for b in 0..batch_size {
            let mut three = [0u32; 3];
            cudaMemcpy(
                three.as_mut_ptr() as *mut _,
                ((d_f as *const u8).add(b * stride_bytes)) as *const _,
                12,
                CUDA_MEMCPY_DEVICE_TO_HOST,
            );
            all_finals[b * 3] = three[0];
            all_finals[b * 3 + 1] = three[1];
            all_finals[b * 3 + 2] = three[2];
        }

        cudaFree(d_f);
        cudaFree(d_hg);
        cudaFree(d_result);
        cudaFree(d_challenge);

        let mut out = Vec::with_capacity(batch_size);
        for (b, ((claims, _, alpha_new), round_polys)) in
            inputs.iter().zip(all_round_polys.into_iter()).enumerate()
        {
            let mu_new = M31Ext3::from_limbs(&[
                M31 {
                    v: all_finals[b * 3],
                },
                M31 {
                    v: all_finals[b * 3 + 1],
                },
                M31 {
                    v: all_finals[b * 3 + 2],
                },
            ]);
            let new_instance = TwinConstrainedInstance {
                alpha: alpha_new.clone(),
                mu: mu_new,
                beta: claims.beta.clone(),
                eta: claims.eta,
                merkle_root: claims.merkle_root,
            };
            out.push((
                new_instance,
                MultilinearBatchingMsg {
                    round_polys,
                    mu_new,
                },
            ));
        }
        Ok(out)
    }
}

/// Run Construction 8.2 as prover. Takes the claims package from
/// Construction 7.2 plus the full codeword `f` (held prover-side)
/// and the verifier's per-round challenges.
pub fn prove<F: Field>(
    claims: &BatchedEvalClaims<F>,
    codeword: &[F],
    alpha_new: &[F],
) -> Result<(TwinConstrainedInstance<F>, MultilinearBatchingMsg<F>)> {
    let log_n = claims.zetas[0].len();
    if alpha_new.len() != log_n {
        return Err(FoldingError::ShapeMismatch(format!(
            "alpha_new.len() = {}, expected log_n = {log_n}",
            alpha_new.len(),
        )));
    }
    let n = 1usize << log_n;
    if codeword.len() != n {
        return Err(FoldingError::CodewordLengthMismatch {
            n,
            got: codeword.len(),
        });
    }

    let weights = batching_weights(claims);
    let mut eq_star = initial_eq_star(&claims.zetas, &weights, log_n);
    let mut f_current = codeword.to_vec();

    let mut round_polys = Vec::with_capacity(log_n);
    for alpha_r in alpha_new {
        let msg = round_message(&eq_star, &f_current);
        round_polys.push(msg);
        fix_bottom_variable(&mut eq_star, *alpha_r);
        fix_bottom_variable(&mut f_current, *alpha_r);
    }
    // After log_n rounds both polynomials are a single scalar.
    assert_eq!(eq_star.len(), 1);
    assert_eq!(f_current.len(), 1);
    let mu_new = f_current[0];

    let new_instance = TwinConstrainedInstance {
        alpha: alpha_new.to_vec(),
        mu: mu_new,
        beta: claims.beta.clone(),
        eta: claims.eta,
        merkle_root: claims.merkle_root,
    };
    Ok((
        new_instance,
        MultilinearBatchingMsg {
            round_polys,
            mu_new,
        },
    ))
}

/// Run Construction 8.2 as verifier.
pub fn verify<F: Field>(
    claims: &BatchedEvalClaims<F>,
    alpha_new: &[F],
    msg: &MultilinearBatchingMsg<F>,
) -> Result<TwinConstrainedInstance<F>> {
    let log_n = claims.zetas[0].len();
    if alpha_new.len() != log_n {
        return Err(FoldingError::ShapeMismatch(format!(
            "alpha_new.len() = {}, expected log_n = {log_n}",
            alpha_new.len()
        )));
    }
    if msg.round_polys.len() != log_n {
        return Err(FoldingError::ShapeMismatch(format!(
            "round_polys.len() = {}, expected log_n = {log_n}",
            msg.round_polys.len()
        )));
    }

    let weights = batching_weights(claims);
    let mut current_claim = sigma_2(&weights, &claims.nus);

    for (round_idx, (round_msg, alpha_r)) in
        msg.round_polys.iter().zip(alpha_new.iter()).enumerate()
    {
        let sum_0_1 = round_msg.evals[0] + round_msg.evals[1];
        if sum_0_1 != current_claim {
            return Err(FoldingError::ShapeMismatch(format!(
                "round {round_idx}: round poly(0) + round poly(1) \
                 ≠ current claim"
            )));
        }
        current_claim = interpolate_degree_2(&round_msg.evals, *alpha_r);
    }

    let eq_star_at_alpha = eval_eq_star(&claims.zetas, &weights, alpha_new);
    let expected = eq_star_at_alpha * msg.mu_new;
    if expected != current_claim {
        return Err(FoldingError::ShapeMismatch(
            "final sumcheck claim fails eq*(α_new) · μ_new = last round poly(α_{log n})".into(),
        ));
    }

    Ok(TwinConstrainedInstance {
        alpha: alpha_new.to_vec(),
        mu: msg.mu_new,
        beta: claims.beta.clone(),
        eta: claims.eta,
        merkle_root: claims.merkle_root,
    })
}

/// Compute `w_i = eq(bin(i), ξ)` for `i = 0..r-1` where r = zetas.len().
pub(crate) fn batching_weights<F: Field>(claims: &BatchedEvalClaims<F>) -> Vec<F> {
    let r = claims.zetas.len();
    let log_r = r.trailing_zeros() as usize;
    let mut weights = Vec::with_capacity(r);
    for i in 0..r {
        let i_bits: Vec<F> = (0..log_r)
            .map(|j| {
                if (i >> j) & 1 == 1 {
                    F::one()
                } else {
                    F::zero()
                }
            })
            .collect();
        weights.push(eq_scalar(&i_bits, &claims.xi));
    }
    weights
}

pub(crate) fn sigma_2<F: Field>(weights: &[F], nus: &[F]) -> F {
    weights
        .iter()
        .zip(nus.iter())
        .fold(F::zero(), |acc, (w, n)| acc + *w * *n)
}

/// Build the initial `eq*` polynomial over the hypercube:
/// `eq*_vec[a] = Σ_i w_i · eq(ζ_i, a)`.
pub(crate) fn initial_eq_star<F: Field>(zetas: &[Vec<F>], weights: &[F], log_n: usize) -> Vec<F> {
    let n = 1usize << log_n;
    let mut out = vec![F::zero(); n];
    for (zeta, w) in zetas.iter().zip(weights.iter()) {
        let per_zeta = build_eq_evals(zeta);
        for (slot, v) in out.iter_mut().zip(per_zeta.iter()) {
            *slot += *w * *v;
        }
    }
    out
}

/// Hypercube evaluations of eq(r, ·), indexed little-endian in r.
fn build_eq_evals<F: Field>(r: &[F]) -> Vec<F> {
    let mut evals = vec![F::zero(); 1 << r.len()];
    evals[0] = F::one();
    let mut cur_len = 1;
    for ri in r {
        for j in 0..cur_len {
            let product = evals[j] * *ri;
            evals[j + cur_len] = product;
            evals[j] -= product;
        }
        cur_len <<= 1;
    }
    evals
}

/// Evaluate `eq*` at an arbitrary point α ∈ F^{log n} directly:
/// `eq*(α) = Σ_i w_i · eq(ζ_i, α)`.
fn eval_eq_star<F: Field>(zetas: &[Vec<F>], weights: &[F], alpha: &[F]) -> F {
    let mut acc = F::zero();
    for (zeta, w) in zetas.iter().zip(weights.iter()) {
        acc += *w * eq_scalar(zeta, alpha);
    }
    acc
}

/// Compute one round's sumcheck message for the product polynomial
/// `eq* · f`, each stored as hypercube evaluations indexed little-
/// endian. Round polynomial has degree 2 ⇒ 3 evaluations determine it.
///
/// The round binds the CURRENT bottom variable (index bit 0), so the
/// i-th challenge corresponds to the i-th coordinate of α (matching
/// `mle_eval(f, α)` semantics).
/// Below this pair count, sequential is faster than rayon's
/// thread-pool overhead. Tuned empirically against the bench suite.
const PAR_PAIR_THRESHOLD: usize = 1024;

pub(crate) fn round_message<F: Field>(eq_star: &[F], f: &[F]) -> SumcheckRoundMsg<F> {
    assert_eq!(eq_star.len(), f.len());
    assert!(eq_star.len() >= 2 && eq_star.len().is_power_of_two());
    let pairs = eq_star.len() / 2;

    let pair_op = |i: usize| {
        let e0 = eq_star[2 * i];
        let e1 = eq_star[2 * i + 1];
        let f0 = f[2 * i];
        let f1 = f[2 * i + 1];
        let e2 = e1.double() - e0;
        let f2 = f1.double() - f0;
        (e0 * f0, e1 * f1, e2 * f2)
    };
    let combine = |a: (F, F, F), b: (F, F, F)| (a.0 + b.0, a.1 + b.1, a.2 + b.2);

    let (eval_0, eval_1, eval_2) = if pairs >= PAR_PAIR_THRESHOLD {
        use rayon::prelude::*;
        (0..pairs)
            .into_par_iter()
            .map(pair_op)
            .reduce(|| (F::zero(), F::zero(), F::zero()), combine)
    } else {
        let mut acc = (F::zero(), F::zero(), F::zero());
        for i in 0..pairs {
            acc = combine(acc, pair_op(i));
        }
        acc
    };

    SumcheckRoundMsg {
        evals: [eval_0, eval_1, eval_2],
    }
}

/// Fix the bottom (bit-0) variable of a multilinear stored as
/// hypercube evaluations in little-endian order to value `r`.
/// After the fix, `out[i] = (1 − r) · v[2i] + r · v[2i+1]`, so the
/// next round's bottom bit is what used to be bit 1.
pub(crate) fn fix_bottom_variable<F: Field>(v: &mut Vec<F>, r: F) {
    let pairs = v.len() / 2;
    if pairs >= PAR_PAIR_THRESHOLD {
        use rayon::prelude::*;
        let folded: Vec<F> = (0..pairs)
            .into_par_iter()
            .map(|i| {
                let v0 = v[2 * i];
                let v1 = v[2 * i + 1];
                v0 + r * (v1 - v0)
            })
            .collect();
        v.clear();
        v.extend_from_slice(&folded);
    } else {
        for i in 0..pairs {
            let v0 = v[2 * i];
            let v1 = v[2 * i + 1];
            v[i] = v0 + r * (v1 - v0);
        }
        v.truncate(pairs);
    }
}

/// Lagrange-interpolate a degree-2 polynomial given evaluations at
/// X = 0, 1, 2 and evaluate at an arbitrary point.
/// p(x) = p(0)·(x−1)(x−2)/2 − p(1)·x(x−2) + p(2)·x(x−1)/2.
pub(crate) fn interpolate_degree_2<F: Field>(evals: &[F; 3], x: F) -> F {
    let two_inv = F::from(2u32).inv().unwrap();
    let xm1 = x - F::one();
    let xm2 = x - F::from(2u32);
    evals[0] * xm1 * xm2 * two_inv - evals[1] * x * xm2 + evals[2] * x * xm1 * two_inv
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::constr_7_2::{prove as prove_7_2, CodewordBatchingChallenges};
    use crate::{BundledConstraint, Term, TwinConstrainedInstance, TwinConstrainedWitness};
    use expander_mersenne31::M31Ext6;
    use rand::SeedableRng;
    use rand_chacha::ChaCha20Rng;

    type F = M31Ext6;
    fn f(n: u32) -> F {
        F::from(n)
    }

    fn setup() -> (
        TwinConstrainedInstance<F>,
        TwinConstrainedWitness<F>,
        BundledConstraint<F>,
    ) {
        let p_b = BundledConstraint {
            terms: vec![Term {
                coeff: f(1),
                vars: vec![0, 1],
            }],
        };
        let wit = TwinConstrainedWitness {
            f: vec![f(2), f(4), f(6), f(8)],
            w: vec![f(5)],
        };
        let inst = TwinConstrainedInstance::from_honest(vec![f(0), f(1)], vec![f(3)], &p_b, &wit);
        (inst, wit, p_b)
    }

    #[test]
    fn round_trip_accepts() {
        let (inst, wit, _) = setup();
        let ch_7_2 = CodewordBatchingChallenges {
            ood_points: vec![vec![f(13), f(17)]],
            shift_queries: vec![0, 2],
            xi: vec![f(19), f(23)],
        };
        let (claims, _) = prove_7_2(&inst, &wit, &ch_7_2).unwrap();

        let alpha_new = vec![f(29), f(31)];
        let (folded_inst, msg) = prove(&claims, &wit.f, &alpha_new).unwrap();
        let verified_inst = verify(&claims, &alpha_new, &msg).unwrap();
        assert_eq!(folded_inst, verified_inst);
    }

    #[test]
    fn mu_new_equals_mle_at_alpha_new() {
        let (inst, wit, _) = setup();
        let ch_7_2 = CodewordBatchingChallenges {
            ood_points: vec![vec![f(13), f(17)]],
            shift_queries: vec![0, 2],
            xi: vec![f(19), f(23)],
        };
        let (claims, _) = prove_7_2(&inst, &wit, &ch_7_2).unwrap();
        let alpha_new = vec![f(29), f(31)];
        let (folded_inst, msg) = prove(&claims, &wit.f, &alpha_new).unwrap();

        let expected_mu = crate::mle_eval(&wit.f, &alpha_new);
        assert_eq!(msg.mu_new, expected_mu);
        assert_eq!(folded_inst.mu, expected_mu);
    }

    #[test]
    fn beta_and_eta_preserved() {
        let (inst, wit, _) = setup();
        let ch_7_2 = CodewordBatchingChallenges {
            ood_points: vec![vec![f(13), f(17)]],
            shift_queries: vec![0, 2],
            xi: vec![f(19), f(23)],
        };
        let (claims, _) = prove_7_2(&inst, &wit, &ch_7_2).unwrap();
        let alpha_new = vec![f(29), f(31)];
        let (folded_inst, _) = prove(&claims, &wit.f, &alpha_new).unwrap();

        assert_eq!(folded_inst.beta, inst.beta);
        assert_eq!(folded_inst.eta, inst.eta);
    }

    #[test]
    fn tampered_mu_rejected() {
        let (inst, wit, _) = setup();
        let ch_7_2 = CodewordBatchingChallenges {
            ood_points: vec![vec![f(13), f(17)]],
            shift_queries: vec![0, 2],
            xi: vec![f(19), f(23)],
        };
        let (claims, _) = prove_7_2(&inst, &wit, &ch_7_2).unwrap();
        let alpha_new = vec![f(29), f(31)];
        let (_, mut msg) = prove(&claims, &wit.f, &alpha_new).unwrap();
        msg.mu_new += f(1);
        assert!(verify(&claims, &alpha_new, &msg).is_err());
    }

    #[test]
    fn tampered_round_message_rejected() {
        let (inst, wit, _) = setup();
        let ch_7_2 = CodewordBatchingChallenges {
            ood_points: vec![vec![f(13), f(17)]],
            shift_queries: vec![0, 2],
            xi: vec![f(19), f(23)],
        };
        let (claims, _) = prove_7_2(&inst, &wit, &ch_7_2).unwrap();
        let alpha_new = vec![f(29), f(31)];
        let (_, mut msg) = prove(&claims, &wit.f, &alpha_new).unwrap();
        msg.round_polys[0].evals[0] += f(1);
        assert!(verify(&claims, &alpha_new, &msg).is_err());
    }

    #[test]
    fn round_trip_random_points() {
        let mut rng = ChaCha20Rng::seed_from_u64(0xbeef);
        let (inst, wit, _) = setup();
        for _ in 0..10 {
            let z1: Vec<F> = (0..2).map(|_| F::random_unsafe(&mut rng)).collect();
            let z2: Vec<F> = (0..2).map(|_| F::random_unsafe(&mut rng)).collect();
            let ch_7_2 = CodewordBatchingChallenges {
                ood_points: vec![z1, z2],
                shift_queries: vec![0],
                xi: vec![F::random_unsafe(&mut rng), F::random_unsafe(&mut rng)],
            };
            let (claims, _) = prove_7_2(&inst, &wit, &ch_7_2).unwrap();
            let alpha_new: Vec<F> = (0..2).map(|_| F::random_unsafe(&mut rng)).collect();
            let (folded_inst, msg) = prove(&claims, &wit.f, &alpha_new).unwrap();
            let verified_inst = verify(&claims, &alpha_new, &msg).unwrap();
            assert_eq!(folded_inst, verified_inst);
        }
    }

    #[test]
    fn interpolate_degree_2_sanity() {
        // p(x) = 3 + 2x + x². p(0)=3, p(1)=6, p(2)=11.
        let evals = [f(3), f(6), f(11)];
        assert_eq!(interpolate_degree_2(&evals, f(0)), f(3));
        assert_eq!(interpolate_degree_2(&evals, f(1)), f(6));
        assert_eq!(interpolate_degree_2(&evals, f(2)), f(11));
        // p(3) = 3 + 6 + 9 = 18
        assert_eq!(interpolate_degree_2(&evals, f(3)), f(18));
    }
}
