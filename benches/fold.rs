//! Phase 3 component-cost benchmarks.
//!
//! Measures the three cost dominators predicted by
//! `docs/research/warp-over-m31.md §5.2`:
//!
//! 1. Spielman code encoding (`enc(w) → C(w)`).
//! 2. Keccak-256 binary Merkle tree build over the codeword.
//! 3. End-to-end fold (Construction 9.4 prove + verify) at varying
//!    witness sizes. Phase 3 uses `IdentityCode` for the in-band
//!    fold; Phase 4 will rewire this once Merkle paths land in 7.2.
//!
//! A composite "predicted per-fold" cost is computed by summing
//! Spielman + Merkle + IdentityCode-based fold and printed to stderr
//! for the bench reader.

use criterion::{criterion_group, criterion_main, BenchmarkId, Criterion, Throughput};
use expander_arith::Field;
use expander_mersenne31::M31Ext3;
use rand::{rngs::StdRng, SeedableRng};

use expander_mersenne31::{M31Ext6, M31};
use willow_folding::{
    code::{IdentityCode, LinearCode, SpielmanCode},
    constr_5_10,
    fs::SamplingParams,
    merkle::MerkleTree,
    pesat::{Constraint, PesatIndex, PesatInstance, Term},
    prove_with_parallel_rep, prove_with_parallel_rep_bound, prove_with_transcript,
    twin::mle_eval,
    verify_with_parallel_rep, verify_with_parallel_rep_bound, verify_with_transcript, SchemeParams,
};

type F = M31Ext3;

fn random_witness(k: usize, seed: u64) -> Vec<F> {
    let mut rng = StdRng::seed_from_u64(seed);
    (0..k).map(|_| F::random_unsafe(&mut rng)).collect()
}

fn bench_spielman_encode(c: &mut Criterion) {
    let mut group = c.benchmark_group("spielman_encode");
    for &log_k in &[10usize, 14, 18] {
        let k = 1usize << log_k;
        let code: SpielmanCode<F> = SpielmanCode::new(k, 0xc0de);
        let msg = random_witness(k, 0xbeef);
        group.throughput(Throughput::Elements(k as u64));
        group.bench_with_input(BenchmarkId::from_parameter(k), &k, |b, _| {
            b.iter(|| {
                let _ = code.encode(&msg);
            });
        });
    }
    group.finish();
}

fn bench_merkle_build(c: &mut Criterion) {
    let mut group = c.benchmark_group("merkle_build");
    for &log_n in &[10usize, 14, 18] {
        let n = 1usize << log_n;
        let leaves: Vec<F> = (0..n)
            .map(|i| F::from(((i as u32).wrapping_mul(0x9E37_79B1)) | 1))
            .collect();
        group.throughput(Throughput::Elements(n as u64));
        group.bench_with_input(BenchmarkId::from_parameter(n), &n, |b, _| {
            b.iter(|| {
                let _ = MerkleTree::build(&leaves);
            });
        });
    }
    group.finish();
}

/// Build a satisfying PESAT instance with the given witness length.
/// Constraints: `w[0] + w[1] - x[0] = 0` and `w[2]·w[3] - x[1] = 0`,
/// witness padded with zeros to length `k`.
fn satisfying_pesat(k: usize) -> (PesatIndex<F>, PesatInstance<F>) {
    assert!(k >= 4 && k.is_power_of_two());
    let c1 = Constraint {
        terms: vec![
            Term {
                coeff: F::one(),
                vars: vec![2],
            },
            Term {
                coeff: F::one(),
                vars: vec![3],
            },
            Term {
                coeff: -F::one(),
                vars: vec![0],
            },
        ],
    };
    let c2 = Constraint {
        terms: vec![
            Term {
                coeff: F::one(),
                vars: vec![4, 5],
            },
            Term {
                coeff: -F::one(),
                vars: vec![1],
            },
        ],
    };
    let idx = PesatIndex {
        constraints: vec![c1, c2],
        n_pub: 2,
        k,
        d: 2,
    };
    // Minimum-effort witness: w = (1, 2, 3, 5, 0, 0, …); x = (3, 15).
    let mut w = vec![F::zero(); k];
    w[0] = F::from(1u32);
    w[1] = F::from(2u32);
    w[2] = F::from(3u32);
    w[3] = F::from(5u32);
    let inst = PesatInstance {
        x: vec![F::from(3u32), F::from(15u32)],
        w,
    };
    (idx, inst)
}

fn bench_fold_prove_verify(c: &mut Criterion) {
    let mut group = c.benchmark_group("fold_prove_verify_identity_code");
    // r = 1 + n_ood + n_shifts must be a power of two.
    let sampling = SamplingParams {
        n_ood: 1,
        n_shifts: 2,
    };
    for &log_k in &[2usize, 6, 10, 14] {
        let k = 1usize << log_k;
        let code = IdentityCode::new(k);
        let (idx, inst_a) = satisfying_pesat(k);
        let (_, inst_b) = satisfying_pesat(k);
        let tau_a = vec![F::from(7u32); idx.m().trailing_zeros() as usize];
        let tau_b = vec![F::from(11u32); idx.m().trailing_zeros() as usize];
        let (twin_a, wit_a, p_b) = constr_5_10::reduce(&idx, &inst_a, &code, &tau_a).unwrap();
        let (twin_b, wit_b, _) = constr_5_10::reduce(&idx, &inst_b, &code, &tau_b).unwrap();
        let params = SchemeParams {
            log_n: <IdentityCode as LinearCode<F>>::log_codeword_len(&code),
            k,
            m: idx.n_pub + tau_a.len(),
            d: p_b.degree(),
        };
        let instances = [twin_a, twin_b];
        let witnesses = [wit_a, wit_b];

        group.throughput(Throughput::Elements(k as u64));
        group.bench_with_input(BenchmarkId::new("prove", k), &k, |b, _| {
            b.iter(|| {
                let _ = prove_with_transcript(&instances, &witnesses, &p_b, &params, &sampling)
                    .unwrap();
            });
        });
        let (_, _, msg) =
            prove_with_transcript(&instances, &witnesses, &p_b, &params, &sampling).unwrap();
        group.bench_with_input(BenchmarkId::new("verify", k), &k, |b, _| {
            b.iter(|| {
                let _ = verify_with_transcript(&instances, &params, &sampling, &msg).unwrap();
            });
        });
    }
    group.finish();
}

/// 128-bit secure parallel-rep bench: r=2 reps over M31Ext3 give
/// `(D*/|F|)^2 ≈ 2^-176` soundness. The same fold sweep as
/// `bench_fold_prove_verify`, but every prove and verify call runs
/// the whole protocol twice with independent transcripts.
fn bench_fold_prove_verify_parallel_rep_2(c: &mut Criterion) {
    let mut group = c.benchmark_group("fold_pr2_identity_code");
    let sampling = SamplingParams {
        n_ood: 1,
        n_shifts: 2,
    };
    for &log_k in &[2usize, 6, 10, 14] {
        let k = 1usize << log_k;
        let code = IdentityCode::new(k);
        let (idx, inst_a) = satisfying_pesat(k);
        let (_, inst_b) = satisfying_pesat(k);
        let tau_a = vec![F::from(7u32); idx.m().trailing_zeros() as usize];
        let tau_b = vec![F::from(11u32); idx.m().trailing_zeros() as usize];
        let (twin_a, wit_a, p_b) = constr_5_10::reduce(&idx, &inst_a, &code, &tau_a).unwrap();
        let (twin_b, wit_b, _) = constr_5_10::reduce(&idx, &inst_b, &code, &tau_b).unwrap();
        let params = SchemeParams {
            log_n: <IdentityCode as LinearCode<F>>::log_codeword_len(&code),
            k,
            m: idx.n_pub + tau_a.len(),
            d: p_b.degree(),
        };
        let instances = [twin_a, twin_b];
        let witnesses = [wit_a, wit_b];

        group.throughput(Throughput::Elements(k as u64));
        group.bench_with_input(BenchmarkId::new("prove", k), &k, |b, _| {
            b.iter(|| {
                let _ =
                    prove_with_parallel_rep(&instances, &witnesses, &p_b, &params, &sampling, 2)
                        .unwrap();
            });
        });
        let (_, _, msgs) =
            prove_with_parallel_rep(&instances, &witnesses, &p_b, &params, &sampling, 2).unwrap();
        group.bench_with_input(BenchmarkId::new("verify", k), &k, |b, _| {
            b.iter(|| {
                let _ = verify_with_parallel_rep(&instances, &params, &sampling, &msgs).unwrap();
            });
        });
    }
    group.finish();
}

/// Same shape as `bench_fold_prove_verify_parallel_rep_2` but uses the
/// `_bound` variants that absorb a 32-byte `external_binding` (typically
/// the WARP per-block seed bound to block hash + completeness-proof
/// hash) into the FS transcript before squeezing any challenges. The
/// delta vs the unbound bench measures the cost of the new
/// anti-censorship binding layer.
fn bench_fold_prove_verify_pr2_bound(c: &mut Criterion) {
    let mut group = c.benchmark_group("fold_pr2_bound_identity_code");
    let sampling = SamplingParams {
        n_ood: 1,
        n_shifts: 2,
    };
    // 32-byte binding mirrors what consensus computes from
    // (block_hash || output_root || config_hash || completeness_hash || block_number).
    let external_binding = [0xA5u8; 32];
    for &log_k in &[2usize, 6, 10, 14] {
        let k = 1usize << log_k;
        let code = IdentityCode::new(k);
        let (idx, inst_a) = satisfying_pesat(k);
        let (_, inst_b) = satisfying_pesat(k);
        let tau_a = vec![F::from(7u32); idx.m().trailing_zeros() as usize];
        let tau_b = vec![F::from(11u32); idx.m().trailing_zeros() as usize];
        let (twin_a, wit_a, p_b) = constr_5_10::reduce(&idx, &inst_a, &code, &tau_a).unwrap();
        let (twin_b, wit_b, _) = constr_5_10::reduce(&idx, &inst_b, &code, &tau_b).unwrap();
        let params = SchemeParams {
            log_n: <IdentityCode as LinearCode<F>>::log_codeword_len(&code),
            k,
            m: idx.n_pub + tau_a.len(),
            d: p_b.degree(),
        };
        let instances = [twin_a, twin_b];
        let witnesses = [wit_a, wit_b];

        group.throughput(Throughput::Elements(k as u64));
        group.bench_with_input(BenchmarkId::new("prove", k), &k, |b, _| {
            b.iter(|| {
                let _ = prove_with_parallel_rep_bound(
                    &instances,
                    &witnesses,
                    &p_b,
                    &params,
                    &sampling,
                    2,
                    &external_binding,
                )
                .unwrap();
            });
        });
        let (_, _, msgs) = prove_with_parallel_rep_bound(
            &instances,
            &witnesses,
            &p_b,
            &params,
            &sampling,
            2,
            &external_binding,
        )
        .unwrap();
        group.bench_with_input(BenchmarkId::new("verify", k), &k, |b, _| {
            b.iter(|| {
                let _ = verify_with_parallel_rep_bound(
                    &instances,
                    &params,
                    &sampling,
                    &msgs,
                    &external_binding,
                )
                .unwrap();
            });
        });
    }
    group.finish();
}

/// Micro-bench: `mle_eval(f, r)` cost across (W, C) field
/// combinations. The evaluate_h hot loop boils down to this exact
/// kernel; per-fold cost ratio ≈ ratio of these per-element times.
///
/// Combinations:
/// - `<F, F>` for `F ∈ {M31, M31Ext3, M31Ext6}` — current same-field
///   paths.
/// - `<W, C>` cross-field with `W` a base field of `C` — demonstrates
///   the dual-field architecture's per-op savings.
fn bench_mle_eval_field_sensitivity(c: &mut Criterion) {
    use rand::rngs::StdRng;
    use rand::SeedableRng;
    let mut group = c.benchmark_group("mle_eval_field_sensitivity");
    let log_n = 18;
    let n = 1usize << log_n;

    let mut rng = StdRng::seed_from_u64(0xfeed);
    let f_m31: Vec<M31> = (0..n).map(|_| M31::random_unsafe(&mut rng)).collect();
    let f_ext3: Vec<M31Ext3> = (0..n).map(|_| M31Ext3::random_unsafe(&mut rng)).collect();
    let f_ext6: Vec<M31Ext6> = (0..n).map(|_| M31Ext6::random_unsafe(&mut rng)).collect();
    let r_ext3: Vec<M31Ext3> = (0..log_n)
        .map(|_| M31Ext3::random_unsafe(&mut rng))
        .collect();
    let r_ext6: Vec<M31Ext6> = (0..log_n)
        .map(|_| M31Ext6::random_unsafe(&mut rng))
        .collect();

    group.throughput(Throughput::Elements(n as u64));

    group.bench_function("M31xM31Ext3 (dual-field, ideal)", |b| {
        b.iter(|| mle_eval::<M31, M31Ext3>(&f_m31, &r_ext3))
    });
    group.bench_function("M31Ext3xM31Ext6 (dual-field, larger C)", |b| {
        b.iter(|| mle_eval::<M31Ext3, M31Ext6>(&f_ext3, &r_ext6))
    });
    group.bench_function("M31Ext3xM31Ext3 (same-field, small)", |b| {
        b.iter(|| mle_eval::<M31Ext3, M31Ext3>(&f_ext3, &r_ext3))
    });
    group.bench_function("M31Ext6xM31Ext6 (same-field, current)", |b| {
        b.iter(|| mle_eval::<M31Ext6, M31Ext6>(&f_ext6, &r_ext6))
    });

    group.finish();
}

/// CUDA-backed sumcheck for Construction 8.2. Compares the GPU
/// prove_cuda path against the rayon CPU path on the SAME workload
/// to bound the per-fold GPU speedup empirically. Available only
/// when the `cuda` feature is enabled at build time.
#[cfg(feature = "cuda")]
fn bench_fold_8_2_sumcheck_cuda(c: &mut Criterion) {
    use expander_mersenne31::M31Ext3;
    use rand::rngs::StdRng;
    use rand::SeedableRng;
    use willow_folding::{
        constr_7_2::BatchedEvalClaims,
        constr_8_2::{prove as prove_cpu, prove_cuda},
        merkle::Digest32,
    };

    // First, smoke-test the kernels on a small input to catch obvious
    // wiring errors before timing.
    if let Err(e) = willow_folding::cuda_kernels::smoke_test() {
        panic!("CUDA smoke test failed: {e}");
    }

    let mut group = c.benchmark_group("fold_8_2_sumcheck_cuda_vs_cpu");
    for &log_n in &[10usize, 14, 18] {
        let n = 1usize << log_n;
        let mut rng = StdRng::seed_from_u64(0xc0ffee);

        // Synthetic claims package. We bypass Construction 7.2 and
        // directly construct the BatchedEvalClaims needed by 8.2.
        // r = 2 → log r = 1, single ζ entry.
        let alpha: Vec<M31Ext3> = (0..log_n)
            .map(|_| M31Ext3::random_unsafe(&mut rng))
            .collect();
        let codeword: Vec<M31Ext3> = (0..n).map(|_| M31Ext3::random_unsafe(&mut rng)).collect();
        // Place a single ζ (r=2 means 1 zeta + 1 nu, log r = 0). Use
        // 2 to keep the batching meaningful; needs xi.len() = log r.
        let zetas = vec![alpha.clone(), {
            (0..log_n)
                .map(|_| M31Ext3::random_unsafe(&mut rng))
                .collect()
        }];
        let nus = vec![
            willow_folding::twin::mle_eval(&codeword, &zetas[0]),
            willow_folding::twin::mle_eval(&codeword, &zetas[1]),
        ];
        let xi = vec![M31Ext3::random_unsafe(&mut rng)];
        let claims: BatchedEvalClaims<M31Ext3> = BatchedEvalClaims {
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

        group.throughput(Throughput::Elements(n as u64));
        group.bench_with_input(BenchmarkId::new("cpu", n), &n, |b, _| {
            b.iter(|| {
                let _ = prove_cpu(&claims, &codeword, &alpha_new).unwrap();
            });
        });
        group.bench_with_input(BenchmarkId::new("cuda", n), &n, |b, _| {
            b.iter(|| {
                let _ = prove_cuda(&claims, &codeword, &alpha_new).unwrap();
            });
        });
    }
    group.finish();
}

/// Phase 7 batched GPU bench. Compares:
/// - sequential CPU (B folds × prove_cpu)
/// - sequential GPU (B folds × prove_cuda — Phase 6 single-dispatch)
/// - batched GPU (single prove_cuda_batched on all B folds)
/// at fixed `n = 2^14` for various batch sizes.
#[cfg(feature = "cuda")]
fn bench_fold_8_2_batched_cuda(c: &mut Criterion) {
    use expander_arith::Field;
    use expander_mersenne31::M31Ext3;
    use rand::rngs::StdRng;
    use rand::SeedableRng;
    use willow_folding::{
        constr_7_2::BatchedEvalClaims,
        constr_8_2::{prove as prove_cpu, prove_cuda, prove_cuda_batched},
        merkle::Digest32,
    };

    let mut group = c.benchmark_group("fold_8_2_batched_cuda");
    let log_n = 14;
    let n = 1usize << log_n;

    for &batch_size in &[1usize, 8, 32, 128] {
        let mut rng = StdRng::seed_from_u64(0xba7c4 + batch_size as u64);
        let mut inputs: Vec<(BatchedEvalClaims<M31Ext3>, Vec<M31Ext3>, Vec<M31Ext3>)> =
            Vec::with_capacity(batch_size);
        for _ in 0..batch_size {
            let alpha: Vec<M31Ext3> = (0..log_n)
                .map(|_| M31Ext3::random_unsafe(&mut rng))
                .collect();
            let codeword: Vec<M31Ext3> = (0..n).map(|_| M31Ext3::random_unsafe(&mut rng)).collect();
            let zetas = vec![
                alpha.clone(),
                (0..log_n)
                    .map(|_| M31Ext3::random_unsafe(&mut rng))
                    .collect(),
            ];
            let nus = vec![
                willow_folding::twin::mle_eval(&codeword, &zetas[0]),
                willow_folding::twin::mle_eval(&codeword, &zetas[1]),
            ];
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
            inputs.push((claims, codeword, alpha_new));
        }

        // Per-fold throughput so the y-axis is comparable across batch sizes.
        group.throughput(Throughput::Elements((batch_size * n) as u64));

        group.bench_with_input(
            BenchmarkId::new("cpu_seq", batch_size),
            &batch_size,
            |b, _| {
                b.iter(|| {
                    for (claims, codeword, alpha_new) in &inputs {
                        let _ = prove_cpu(claims, codeword, alpha_new).unwrap();
                    }
                });
            },
        );
        group.bench_with_input(
            BenchmarkId::new("cuda_seq", batch_size),
            &batch_size,
            |b, _| {
                b.iter(|| {
                    for (claims, codeword, alpha_new) in &inputs {
                        let _ = prove_cuda(claims, codeword, alpha_new).unwrap();
                    }
                });
            },
        );
        group.bench_with_input(
            BenchmarkId::new("cuda_batched", batch_size),
            &batch_size,
            |b, _| {
                b.iter(|| {
                    let _ = prove_cuda_batched(&inputs).unwrap();
                });
            },
        );
    }
    group.finish();
}

/// Raw batched poly_eval throughput vs batch size, at representative
/// completeness-layer eval_size values. The diagnostic question:
/// does the speedup curve scale linearly with batch size up to N≥256
/// (suggesting cross-instance batching unlocks the ~5–10× GPU win
/// over CPU we'd want for production), or does it plateau early
/// (suggesting H2D bandwidth or kernel launch granularity is the
/// next-level bottleneck and a different attack is needed)?
///
/// Sweeps batch ∈ {16, 64, 256, 1024, 4096} × eval_size ∈ {64, 1024, 16384}.
/// Reports the per-kernel-call wall-clock for each (batch, eval_size) cell.
/// Compare per-fold cost between adjacent batch values: ideal scaling is
/// per-fold cost CONSTANT as batch grows; a linear rise vs batch means
/// the batched kernel is no faster per-fold than serial.
#[cfg(feature = "cuda")]
fn bench_batched_dispatch_scaling(c: &mut Criterion) {
    use expander_arith::Field;
    use expander_mersenne31::M31Ext3;
    use rand::rngs::StdRng;
    use rand::SeedableRng;
    use willow_folding::cuda_kernels::{
        cudaFree, cudaMalloc, cudaMemcpy, cuda_m31ext3_poly_eval_batched,
        CUDA_MEMCPY_HOST_TO_DEVICE,
    };

    let mut group = c.benchmark_group("batched_dispatch_scaling");
    group.sample_size(10);

    for &eval_size in &[64usize, 1024, 16384] {
        for &batch in &[16usize, 64, 256] {
            let n = eval_size;
            // The kernel reads paired elements at index 2i / 2i+1, so it
            // needs `2 * eval_size` M31Ext3 per fold = 6 * eval_size u32.
            // Both `bk_f` and `bk_hg` get this layout. fold_stride_u32 must
            // match: `6 * eval_size`.
            let per_fold_ext3 = 2 * n;
            let per_fold_u32 = per_fold_ext3 * 3; // 6n
            let total_u32 = batch * per_fold_u32;
            let total_bytes = total_u32 * 4;

            // Build host data deterministically.
            let mut rng = StdRng::seed_from_u64(0xc0de + (batch as u64) + (eval_size as u64));
            let mut bk_f_words: Vec<u32> = Vec::with_capacity(total_u32);
            let mut bk_hg_words: Vec<u32> = Vec::with_capacity(total_u32);
            for _ in 0..batch {
                for _ in 0..per_fold_ext3 {
                    let f = M31Ext3::random_unsafe(&mut rng);
                    let h = M31Ext3::random_unsafe(&mut rng);
                    bk_f_words.extend(f.v.iter().map(|m| m.v));
                    bk_hg_words.extend(h.v.iter().map(|m| m.v));
                }
            }

            unsafe {
                let mut d_f: *mut std::ffi::c_void = std::ptr::null_mut();
                let mut d_hg: *mut std::ffi::c_void = std::ptr::null_mut();
                let mut d_result: *mut std::ffi::c_void = std::ptr::null_mut();
                if cudaMalloc(&mut d_f, total_bytes) != 0
                    || cudaMalloc(&mut d_hg, total_bytes) != 0
                    || cudaMalloc(&mut d_result, batch * 9 * 4) != 0
                {
                    eprintln!("cudaMalloc failed at batch={batch} eval_size={eval_size}; skipping");
                    continue;
                }

                cudaMemcpy(
                    d_f,
                    bk_f_words.as_ptr() as *const _,
                    total_bytes,
                    CUDA_MEMCPY_HOST_TO_DEVICE,
                );
                cudaMemcpy(
                    d_hg,
                    bk_hg_words.as_ptr() as *const _,
                    total_bytes,
                    CUDA_MEMCPY_HOST_TO_DEVICE,
                );

                // Per-fold elements as throughput.
                group.throughput(Throughput::Elements(batch as u64));
                let label = format!("eval_size={eval_size}/batch={batch}");
                group.bench_function(label, |b| {
                    b.iter(|| {
                        let rc = cuda_m31ext3_poly_eval_batched(
                            d_f as *const u32,
                            d_hg as *const u32,
                            d_result as *mut u32,
                            n as u32,
                            batch as u32,
                            (n * 3) as u32,
                        );
                        assert_eq!(rc, 0);
                    });
                });

                cudaFree(d_f);
                cudaFree(d_hg);
                cudaFree(d_result);
            }
        }
    }
    group.finish();
}

#[cfg(feature = "cuda")]
criterion_group!(
    benches,
    bench_spielman_encode,
    bench_merkle_build,
    bench_fold_prove_verify,
    bench_fold_prove_verify_parallel_rep_2,
    bench_fold_prove_verify_pr2_bound,
    bench_mle_eval_field_sensitivity,
    bench_fold_8_2_sumcheck_cuda,
    bench_fold_8_2_batched_cuda,
    bench_batched_dispatch_scaling,
);
#[cfg(not(feature = "cuda"))]
criterion_group!(
    benches,
    bench_spielman_encode,
    bench_merkle_build,
    bench_fold_prove_verify,
    bench_fold_prove_verify_parallel_rep_2,
    bench_fold_prove_verify_pr2_bound,
    bench_mle_eval_field_sensitivity,
);
criterion_main!(benches);
