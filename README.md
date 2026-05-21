# warp-folding

First public production implementation of **WARP** (Linear-Time Accumulation
Schemes, Bünz/Chiesa/Fenzi/Wang, [eprint 2025/753](https://eprint.iacr.org/2025/753),
TCC 2025) instantiated over the Polyhedra Expander M31 stack.

## Status

Pre-release. The IOR + Fiat-Shamir compilation + parallel-rep amplification
are complete and tested; full Spielman-code wiring is staged in source
(`SpielmanCode`, `#[doc(hidden)]`) but not yet on the production code path —
see [Roadmap](#roadmap) below.

## Concrete instantiation

- **Field:** `M31Ext3` (Mersenne-31 cubic extension, `|F| ≈ 2^93`)
  with parallel-repetition `r = 2` for `ε² ≈ 2⁻¹⁷⁶` soundness (128-bit
  target). The natural choice from WARP's Theorem 10.3 would be
  `M31Ext5` (`|F| ≈ 2^155`, provable single-rep), but Expander doesn't
  ship `M31Ext4`/`M31Ext5` and a direct degree-5 extension stalled on
  irreducible-polynomial selection. Benchmarks below justify Ext3+r=2
  over Ext6 single-rep at the same security level.
- **Commitment:** Orion (Xie–Zhang–Song 2022), Keccak-Merkle over the
  vendored `OrionCode` from Polyhedra Expander with the published
  `ORION_CODE_PARAMETER_INSTANCE` (Orion paper §5: `alpha_g0 = 0.33`,
  `degree_g0 = 6`, `alpha_g1 = 0.337`, `degree_g1 = 6`, relative distance
  `δ(C) = 0.055`). Distance carries the Druk–Ishai-14 induction proof.
  `IdentityCode` and `SpielmanCode` remain in the crate as IOR-level
  unit-test stubs and benchmark stand-in respectively; production fold
  path uses `OrionLinearCode` via [`default_orion_code`].
- **Fiat-Shamir:** Keccak-256 transcript, parallel-rep with
  independent per-rep transcripts; external-binding absorbed before
  any challenge to bind the fold to per-block authenticated public
  data (block hash, output root, config hash, completeness-proof
  hash, block number).
- **GPU:** optional `cuda` feature compiles M31Ext3 sumcheck kernels
  via `nvcc`. Batched-dispatch sumcheck — fold instances as the batch
  dimension — bypasses Expander's per-lane sequential dispatch.
  Measured ~1 ms/fold at batch=32, log_n=14 on RTX 5090. Bit-for-bit
  validated against the CPU prover. Build is a no-op if `nvcc` is
  not in `PATH`.

## Benchmarks

Per-fold prove time at `k = 2^14` (Apple M2, single-thread, M31Ext3):

| Variant | Time | Soundness |
|---|---|---|
| M31Ext6 single-rep | 17.2 ms | ε ≈ 2⁻¹⁸¹ |
| **M31Ext3 + r=2** (production) | **9.1 ms** | ε² ≈ 2⁻¹⁷⁶ |
| M31Ext3 + r=2 + rayon | 3.83 ms | ε² ≈ 2⁻¹⁷⁶ |

Per-fold GPU prove time at `log_n = 14, batch = 32`:

| Variant | Time |
|---|---|
| RTX 5090 (batched-dispatch sumcheck) | 1.0 ms |

Full benchmark methodology and Phase 3/6 measurement runs are in
[`docs/warp-phase3-bench.md`](./docs/warp-phase3-bench.md) and
[`docs/warp-phase6-gpu-runpod.md`](./docs/warp-phase6-gpu-runpod.md).

## Build

```sh
cargo check                # base build, no GPU
cargo test                 # full test suite (~80 unit + 6 e2e)
cargo test --release       # benchmarks-mode test pass
cargo bench --bench fold   # per-fold prove + verify benchmarks
cargo check --features cuda  # GPU sumcheck kernels (requires nvcc)
```

Tests pass without a CUDA toolchain; only the optional `cuda` feature
needs `nvcc`.

## Layout

| Path | Role |
|---|---|
| `src/lib.rs` | Public re-exports |
| `src/fs.rs` | Fiat-Shamir compilation + parallel-rep prover/verifier |
| `src/prover.rs` | `WarpProverState`, per-block fold |
| `src/decider.rs` | `D_ACC` algebraic checks |
| `src/constr_5_10.rs` | PESAT → Twin reduction |
| `src/constr_6_3.rs` | Twin pseudo-batching |
| `src/constr_7_2.rs` | Codeword batching with OOD + shift queries |
| `src/constr_8_2.rs` | Multilinear-constraint batching sumcheck |
| `src/constr_9_4.rs` | Composition |
| `src/twin.rs` | `TwinConstrainedInstance` / `TwinConstrainedWitness` |
| `src/code.rs` | `IdentityCode` (production) and `SpielmanCode` (staged) |
| `src/merkle.rs` | Keccak-Merkle tree |
| `src/wire.rs` | `FoldStepWire` — on-chain serialization |
| `src/cuda_kernels.rs` | Optional GPU sumcheck bindings |
| `cuda/` | M31Ext3 sumcheck CUDA kernels |
| `tests/end_to_end.rs` | Round-trip + 4 negative tests + chain-completeness |
| `docs/` | Design rationale and benchmark write-ups |

## Design rationale

Two long-form research write-ups walk through the scheme selection and
adaptation:

- [`docs/interstellar-over-m31.md`](./docs/interstellar-over-m31.md) —
  Phase 1: why Interstellar / NeutronNova / Nova / Mova / ProtoGalaxy
  / Lova / Neo were each rejected for an M31 stack.
- [`docs/warp-over-m31.md`](./docs/warp-over-m31.md) — Phase 1.5:
  WARP adapted for M31, soundness lemma-by-lemma transfer, concrete
  field-size derivation (originally targeting M31Ext5; see code for
  why production landed on M31Ext3 + parallel-rep r=2 instead).

## Roadmap

- [x] Phase 1: scheme selection (Interstellar rejected, WARP selected).
- [x] Phase 2: IOR + Fiat-Shamir + parallel-rep prover/verifier over
      M31Ext3.
- [x] Phase 3: CPU benchmarks across field choices.
- [x] Phase 4: parallel-rep r=2 locked, M31Ext3 production path.
- [x] Phase 5/7: production code path wired to vendored Polyhedra Orion
      (`OrionLinearCode` + `default_orion_code`). `IdentityCode` /
      `SpielmanCode` retained as unit-test stubs only.
- [x] Phase 6: GPU batched-dispatch sumcheck (RTX 5090 validated).
- [ ] On-chain decider settlement transaction (currently the decider
      runs as an indexer-side self-check; see `src/prover.rs` and
      `src/decider.rs`).
- [ ] Soundness sanity-check / collaboration with the WARP authors on
      the parallel-rep composition argument.

## Security caveats

Pre-release. The IOR-level proofs and FS compilation have not yet
been independently reviewed. The parallel-rep `r = 2` soundness
argument is `ε² ≈ 2⁻¹⁷⁶`, which clears 128-bit by ~48 bits, but
the composition of parallel-rep amplification on top of WARP's
FS-compiled IOR is not directly analyzed in the original paper —
this is the load-bearing open question for the production deployment
and the one we'd most like external review on.

## Citation

If you use this in academic work, please cite both the original WARP
paper and this implementation:

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
  title  = {warp-folding: production implementation of WARP over M31Ext3 + Orion},
  year   = {2026},
  url    = {https://github.com/willow-network/warp-folding}
}
```

## License

Dual-licensed under [Apache-2.0](./LICENSE-APACHE) or
[MIT](./LICENSE-MIT) at your option.
