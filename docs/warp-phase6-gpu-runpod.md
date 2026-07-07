# WARP Phase 6 — GPU Spike Setup (RunPod)

**Status**: Phase 6 instructions for empirical GPU validation.
**Code state**: ready to build on a CUDA machine. Build verified
locally (no-CUDA path) — 81 tests + strict clippy clean.

## What this measures

The fold prover's hottest loop is `Construction 8.2`'s sumcheck:
- `round_message` — degree-2 round polynomial reduction over n
  pairs of (eq*, f) products.
- `fix_bottom_variable` — half-the-array linear interpolation
  given the round's challenge.

Both kernels exist in Expander's `sumcheck/cuda_m31/` and are
M31Ext3-aware. Phase 6 vendors them into `cuda/`,
exposes a `prove_cuda` function in `constr_8_2.rs`, and benches
CPU vs CUDA on the same synthetic claims package across n = 2^10,
2^14, 2^18.

This is a *single-fold* benchmark — not yet batched across many
folds. The point is to bound the kernel-level speedup. If
`prove_cuda` already beats `prove_cpu` at single-fold sizes, batch
folding will only widen the gap (transfer cost amortized across
batch).

## RunPod request

**Instance type**: anything with an NVIDIA GPU. Recommended:
- RTX 4090 / RTX 5090 (consumer, ~$0.50/hr)
- L40S / A100 / H100 (data center, ~$1–4/hr)

Either is fine. Bigger memory is irrelevant for this single-fold
spike; we top out at ~50 MB of GPU buffers per run.

**Image**: any Ubuntu 22.04 base with CUDA 12.x. RunPod's
"PyTorch 2.x" templates work — they ship `nvcc` and `cudart`.

**Disk**: 30+ GB. Expander's transitive deps (halo2curves,
tokenizers, ark-std) compile to a lot of artifacts.

**Approximate cost**: 10–20 minutes of GPU time for build + bench.
~$0.15–0.50 total.

## One-time setup on the instance

```bash
# Install Rust (RunPod Pytorch images don't ship it).
curl --proto '=https' --tlsv1.2 -sSf https://sh.rustup.rs | sh -s -- -y
source $HOME/.cargo/env

# Confirm nvcc + cuda runtime present.
nvcc --version
ls /usr/local/cuda/lib64/libcudart.so

# Clone the repo.
git clone https://github.com/willow-network/warp-folding.git
cd warp-folding
```

## Run the benches

```bash
# Sanity: build with the CUDA feature on. This compiles
# cuda/m31_sumcheck.cu via nvcc. Should produce a libwarp_cuda_m31.a
# in target/debug/build/warp-folding-*/out/.
cargo build --release --features cuda

# Run the unit + integration tests with CUDA on (the kernels are
# only exercised in the bench, but this confirms the build links).
cargo test --release --features cuda

# Run the CUDA-vs-CPU bench. The smoke_test runs FIRST inside the
# bench — if there's a wiring error, you'll see a panic with a
# specific kernel return code.
cargo bench --features cuda \
  -- fold_8_2_sumcheck_cuda_vs_cpu

# (Optional) For a quick comparison on the existing M31Ext3 + r=2
# parallel-rep path without CUDA, run:
cargo bench --release fold_pr2_identity_code
```

## What to paste back

The Criterion output for `fold_8_2_sumcheck_cuda_vs_cpu`. Specifically
the `time:` lines for each `cpu/N` and `cuda/N` benchmark across
`N ∈ {1024, 16384, 262144}`.

Roughly the format:

```
fold_8_2_sumcheck_cuda_vs_cpu/cpu/1024
                        time:   [???.?? µs ???.?? µs ???.?? µs]
fold_8_2_sumcheck_cuda_vs_cpu/cuda/1024
                        time:   [???.?? µs ???.?? µs ???.?? µs]
fold_8_2_sumcheck_cuda_vs_cpu/cpu/16384
                        time:   [???.?? ms ???.?? ms ???.?? ms]
fold_8_2_sumcheck_cuda_vs_cpu/cuda/16384
                        time:   [???.?? ms ???.?? ms ???.?? ms]
fold_8_2_sumcheck_cuda_vs_cpu/cpu/262144
                        time:   [???.?? ms ???.?? ms ???.?? ms]
fold_8_2_sumcheck_cuda_vs_cpu/cuda/262144
                        time:   [???.?? ms ???.?? ms ???.?? ms]
```

## What I'll do with the numbers

Three possible outcomes:

1. **GPU faster than CPU at all n**: validate the architectural
   claim. Plan Phase 7 = batched GPU prover (process 100 folds per
   kernel dispatch). Estimated additional 10–30× over single-fold
   CUDA.

2. **GPU faster only at large n (e.g., n=2^18)**: confirms the
   memory-bandwidth thesis. Worth pursuing for production scale
   (k=2^22, n=2^23). Phase 7 still goes ahead.

3. **GPU not faster at any n**: matches your previous experience
   with hand-built circuits. Stop. Document the negative result;
   the dual-field + SIMD path on CPU is the way forward.

## Common build issues

- `nvcc not found`: install via `apt install nvidia-cuda-toolkit`
  (or use a different RunPod image). Re-run cargo build.
- `cannot find -lcudart`: set `LIBRARY_PATH` to include
  `/usr/local/cuda/lib64`. RunPod templates usually have this in
  `LD_LIBRARY_PATH` already.
- `error: linking with cc failed: undefined reference to cudaMalloc`:
  cargo isn't picking up the `rustc-link-lib=cudart` directive.
  Try `cargo clean && cargo build --features cuda`.
- Kernel returns nonzero rc: the smoke_test will catch this with a
  specific error message. Likely indicates a CUDA context issue
  (no GPU visible, e.g., from inside a container without `--gpus all`).

## What's hard-coded vs configurable

- Field type: M31Ext3 (matches Phase 4-B's bench config).
- Bench sizes: `log_n ∈ {10, 14, 18}` in the criterion group. To
  test other sizes, edit `bench_fold_8_2_sumcheck_cuda_vs_cpu` in
  `benches/fold.rs`.
- Architecture targets: `sm_70` (Volta) and `sm_80` (Ampere). RTX
  40/50 series fall back to `sm_80`. If your GPU is older than
  Volta, edit `build.rs`.
