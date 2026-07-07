# warp-folding

[![CI](https://github.com/willow-network/warp-folding/actions/workflows/ci.yml/badge.svg)](https://github.com/willow-network/warp-folding/actions/workflows/ci.yml)
[![License: Apache 2.0](https://img.shields.io/badge/License-Apache%202.0-blue.svg)](LICENSE-APACHE)
[![License: MIT](https://img.shields.io/badge/License-MIT-yellow.svg)](LICENSE-MIT)

A public implementation of **WARP** (Linear-Time Accumulation Schemes,
Bünz/Chiesa/Fenzi/Wang, [eprint 2025/753](https://eprint.iacr.org/2025/753),
TCC 2025) instantiated over the Polyhedra Expander M31 stack.

> **Pre-release research code.** The implementation is complete and tested,
> but the soundness *story* is not yet settled — in particular the headline
> 128-bit claim depends on a parallel-repetition argument that is **not yet
> proven** for this setting. Read [Security status](#security-status) before
> relying on it or quoting its security level. We're publishing it because the
> gap it fills — folding for the small-field fast-proving stack — is one a lot
> of people are going to hit, and there hasn't been a public answer.
>
> **Maintenance status: retired research.** Willow's production stack does not
> use WARP, and this repository is not actively developed. It is published as a
> faithful reference implementation; issues and PRs are welcome but responses
> may be slow.

## Status

The core code path is complete: IOR + Fiat-Shamir compilation + parallel-rep
amplification + vendored Polyhedra Orion linear code (`OrionLinearCode`, with
the published `ORION_CODE_PARAMETER_INSTANCE` from §5 of the Orion paper) +
BLAKE3 Merkle commitments + optional GPU batched-dispatch sumcheck. **101 tests
run in CI (95 unit + 6 end-to-end); 107 total** including the optional
`gf2_compile_check`. CI is green on linux and macos.

The IOR-level proofs and the parallel-rep composition argument have **not** been
independently reviewed by a cryptographer outside the implementation loop, and
the parallel-rep-under-Fiat-Shamir composition is not analyzed in the original
paper. See [Security status](#security-status).

## Concrete instantiation

- **Field:** `M31Ext3` (Mersenne-31 cubic extension, `|F| ≈ 2^93`), with
  parallel-repetition `r = 2`. **The security this delivers is the open
  question, not a settled number** — see [Security status](#security-status).
  This crate's own design note (`docs/warp-over-m31.md §4`) concludes that a
  *provable* single-repetition 128-bit bound needs `M31Ext5` (`|F| ≈ 2^155`);
  production landed on `M31Ext3 + r=2` because Expander ships neither
  `M31Ext4` nor `M31Ext5` and a direct degree-5 extension stalled on
  irreducible-polynomial selection. The `r = 2` amplification is a **heuristic
  stand-in** for that larger field, not an equivalent.
- **Commitment:** Orion (Xie–Zhang–Song 2022), **BLAKE3**-Merkle over the
  vendored `OrionCode` from Polyhedra Expander with the published
  `ORION_CODE_PARAMETER_INSTANCE` (Orion paper §5: `alpha_g0 = 0.33`,
  `degree_g0 = 6`, `alpha_g1 = 0.337`, `degree_g1 = 6`, relative distance
  `δ(C) = 0.055`). Distance carries the Druk–Ishai-14 induction proof.
  `IdentityCode` and `SpielmanCode` are **test/benchmark stubs only**
  (`#[cfg(test)]` and benchmark stand-in); the production fold path uses
  `OrionLinearCode` via [`default_orion_code`].
- **Sampling profile:** the shipped default is `n_ood = 1, n_shifts = 2`
  (`WarpProverState::genesis`). **This is a development/benchmark profile, not a
  high-soundness one** — the codeword-proximity bound the scheme relies on
  needs far more queries (the design note targets `s ≈ 16` OOD samples and
  `t` in the thousands). Raising these is a configuration change (`with_sampling`)
  with a corresponding prover-time cost; the defaults are not the 128-bit
  profile.
- **Fiat-Shamir:** Keccak-256 transcript; parallel-rep uses independent
  per-rep transcripts (the rep index is absorbed before any challenge is
  squeezed). External-binding (block hash, output root, config hash,
  completeness-proof hash, block number) is absorbed before any challenge to
  bind the fold to per-block authenticated public data.
- **GPU:** optional `cuda` feature compiles M31Ext3 sumcheck kernels via
  `nvcc`. Batched-dispatch sumcheck — fold instances as the batch dimension —
  bypasses Expander's per-lane sequential dispatch. Timed at ~1 ms/fold at
  batch=32, log_n=14 on an RTX 5090 (RunPod). CPU↔GPU **bit-exactness is
  unit-tested at log_n=6, batch ≤ 16** (the `cuda`-gated `single_cuda_matches_cpu`
  / `batched_matches_cpu` tests); the headline batch=32/log_n=14 config is timed
  but not yet covered by an equality test, and CI does not build the CUDA
  feature (no `nvcc` on runners). Build is a no-op if `nvcc` is not in `PATH`.

## Benchmarks

**Caveat: the only benchmarks currently wired measure the `IdentityCode` path —
a no-op encoder (`encode(w) = w`, no error-correcting code, no Merkle
authentication).** They are an IOR-level *lower bound* on the prover, **not** the
production Orion+Merkle path. The production path is not yet covered by a wired
end-to-end benchmark; the Phase 5 write-up estimates Orion+Merkle adds ~24% over
these numbers.

Per-fold prove time, `IdentityCode`, `M31Ext3 + r=2`, `k = 2^14`, Apple M2
(re-measured 2026-06-16, Criterion, 40 samples, default `opt-level=3`):

| Path | Time |
|---|---|
| single-thread (`RAYON_NUM_THREADS=1`) | ~27.7 ms |
| rayon (all cores) | ~7.2 ms |

> Earlier revisions of this table quoted 9.1 ms / 3.83 ms for this path; those
> figures did not reproduce on the same M2 and have been replaced with the
> re-measured values. Component benchmarks (Spielman encode, Merkle build) and
> the historical-sync *extrapolations* live in
> [`docs/warp-phase3-bench.md`](./docs/warp-phase3-bench.md) — note those
> wall-clock figures (hours/days for 10M-block sync) are explicitly linear
> extrapolations, not measurements.

## Build

```sh
cargo check                # base build, no GPU
cargo test                 # full test suite
cargo test --release       # benchmarks-mode test pass
cargo bench --bench fold   # per-fold prove + verify benchmarks
cargo check --features cuda  # GPU sumcheck kernels (requires nvcc)
```

Tests pass without a CUDA toolchain; only the optional `cuda` feature needs
`nvcc` (and `--features cuda` requires `nvcc` at link time — there is no silent
no-op fallback once the feature is enabled).

## Layout

| Path | Role |
|---|---|
| `src/lib.rs` | Public re-exports |
| `src/fs.rs` | Fiat-Shamir compilation + parallel-rep prover/verifier |
| `src/prover.rs` | `WarpProverState`, per-block fold |
| `src/decider.rs` | `D_ACC` algebraic checks (indexer-side self-check) |
| `src/constr_5_10.rs` | PESAT → Twin reduction |
| `src/constr_6_3.rs` | Twin pseudo-batching |
| `src/constr_7_2.rs` | Codeword batching with OOD + shift queries |
| `src/constr_8_2.rs` | Multilinear-constraint batching sumcheck |
| `src/constr_9_4.rs` | Composition |
| `src/twin.rs` | `TwinConstrainedInstance` / `TwinConstrainedWitness` |
| `src/orion_code.rs` | `OrionLinearCode` (production code) + `default_orion_code` |
| `src/code.rs` | `IdentityCode` + `SpielmanCode` (IOR-level test/bench stubs) |
| `src/merkle.rs` | BLAKE3 Merkle tree |
| `src/wire.rs` | `FoldStepWire` — on-chain serialization |
| `src/cuda_kernels.rs` | Optional GPU sumcheck bindings |
| `cuda/` | M31Ext3 sumcheck CUDA kernels |
| `tests/end_to_end.rs` | Round-trip + negative tests + chain-completeness |
| `docs/` | Design rationale and benchmark write-ups |

## Design rationale

Two long-form research write-ups walk through the scheme selection and
adaptation:

- [`docs/interstellar-over-m31.md`](./docs/interstellar-over-m31.md) —
  Phase 1: why Interstellar / NeutronNova / Nova / Mova / ProtoGalaxy / Lova /
  Neo were each rejected for an M31 stack.
- [`docs/warp-over-m31.md`](./docs/warp-over-m31.md) — Phase 1.5: WARP adapted
  for M31, soundness lemma-by-lemma transfer, concrete field-size derivation
  (the §4 derivation targeting M31Ext5; see [Security status](#security-status)
  for why production shipped M31Ext3 + r=2 instead, and what that costs).

## Security status

This is the load-bearing section; please read it before quoting a security level.

1. **The 128-bit / `ε² ≈ 2⁻¹⁷⁶` figure is not established.** It comes from
   squaring a per-repetition soundness error under `r = 2` parallel repetition.
   `ε^r` amplification is the soundness bound for `r` *independent interactive*
   executions. Under Fiat-Shamir the two reps here share the same statement,
   witness, codeword commitment, and external binding (only the transcript salt
   differs), so the per-rep failure events are **correlated**, and the product
   bound is **not justified** by any theorem we can cite. This is the open
   question, not a detail.

2. **The per-rep error itself is optimistic.** The `D*/|F| ≈ 2⁻⁸⁸` figure used
   elsewhere is the sumcheck/degree term; this crate's own `docs/warp-over-m31.md §4`
   identifies the **OOD-sampling term** as the binding one and concludes a
   provable 128-bit single-rep bound needs `|F|` well above the `M31Ext3 ≈ 2^93`
   shipped here (it calls even `M31Ext4 ≈ 2^124` "unusable at the 128-bit
   target").

3. **The default sampling profile (`n_ood=1, n_shifts=2`) does not deliver the
   advertised codeword-proximity binding.** With `δ = 0.055`, two shift queries
   miss a far-from-codeword witness with probability `≈ 0.945² ≈ 0.89`. A
   high-soundness profile needs many more queries (and is slower).

4. **What *is* solid:** the implementation faithfully realizes what it claims to
   do — transcript ordering, independent per-rep salting, verifying *all* reps,
   Merkle gating of shift values, and the decider checks are all correctly
   implemented (no transcript or control-flow soundness bug was found in an
   internal multi-agent audit). The gap is in the *claimed security level*, not
   in the code's fidelity to the protocol.

5. **Scope.** WARP here provides **accumulation only** — it chains and proves
   per-fold computations. Per-block *correctness* (that an indexer's output
   really came from the block) is enforced by a separate completeness + GKR
   layer that **lives outside this crate** (see `src/prover.rs`). This crate's
   guarantees are conditional on that external component.

If you need a number to rely on today, treat the provable guarantee as the
**single-repetition** bound for the configured field/sampling profile, and
treat `r = 2` as a heuristic hedge pending either (a) a real
parallel-rep-under-FS composition theorem for WARP, or (b) migration to a larger
field per `§4`.

## Citation

If you use this in academic work, please cite both the original WARP paper and
this implementation:

```bibtex
@misc{warp2025,
  author = {B\"unz, Benedikt and Chiesa, Alessandro and Fenzi, Giacomo and Wang, William},
  title  = {Linear-Time Accumulation Schemes},
  howpublished = {Cryptology ePrint Archive, Paper 2025/753},
  year   = {2025},
  url    = {https://eprint.iacr.org/2025/753}
}

@misc{warp-folding,
  author = {DeLucia, Paul},
  title  = {warp-folding: a WARP implementation over M31Ext3 + Orion},
  year   = {2026},
  url    = {https://github.com/willow-network/warp-folding}
}
```

## License

Dual-licensed under [Apache-2.0](./LICENSE-APACHE) or [MIT](./LICENSE-MIT) at
your option.
