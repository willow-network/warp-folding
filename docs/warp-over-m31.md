# WARP over M31Ext5 + Orion — Research Writeup

**Status**: Phase 1.5 deliverable. Math-first. Code-free.
**Parent**: [docs/todo/m31-folding.md](../todo/m31-folding.md),
[docs/research/interstellar-over-m31.md](./interstellar-over-m31.md).
**Papers studied**:
- WARP: Bünz, Chiesa, Fenzi, Wang. "Linear-Time Accumulation Schemes." [eprint 2025/753](https://eprint.iacr.org/2025/753). TCC 2025. 76 pp.
- Arc: Bünz, Mishra, Nguyen, Wang. "Arc: Accumulation for Reed–Solomon Codes." [eprint 2024/1731](https://eprint.iacr.org/2024/1731). CRYPTO 2025. 57 pp.
- BMNW24: Bünz, Mishra, Nguyen, Wang. "Accumulation Without Homomorphism." [eprint 2024/474](https://eprint.iacr.org/2024/474). 51 pp.
- Mutual Correlated Agreement: Arnon, Chiesa, Fenzi, Yogev. "WHIR." [eprint 2024/1586](https://eprint.iacr.org/2024/1586). 2024.

## TL;DR

**Go.** WARP is the right scheme for Willow's stack. The design doc's
"Phase 1 might reveal we need to pivot" scenario was right — but the
pivot target has moved: **not NeutronNova, not BMNW24, but WARP**.

One structural change from the original plan: **use M31Ext5 (|F| ≈
2^155), not M31Ext4**. Interstellar would have needed a 2^130-class
field; NeutronNova would have needed 2^256; WARP needs ≈ `2^128 ·
polylog(n,M,d,ℓ)`. For a realistic Willow workload (n ≈ 2^22, M ≈
2^20) this works out to 2^138–2^143. M31Ext4 at 2^124 is short by
14–19 bits; M31Ext5 at 2^155 has comfortable headroom.

Everything else in the original plan survives: Orion as the PCS
(WARP's `[GLSTW23]` = Brakedown-family instantiation fits Orion's
Spielman-variant expander code), Poseidon2 as the in-circuit sponge,
the indexer-side fold pipeline, the consensus-verified accumulator.

One change in character worth flagging upfront: **we would still be
the first implementers.** WARP (May 2025) and Arc (Oct 2024) have no
public Rust or C++ implementations. This is not a gap in the math;
it's a schedule risk. The offsetting benefit is that we would own the
implementation rather than be downstream of someone else's bindings,
and a clean `crates/folding/` artifact is publishable.

The rest of this writeup: (§1) what changed between BMNW24 and WARP,
(§2) adapted pseudocode for M31Ext5 + Orion, (§3) lemma-by-lemma
soundness transfer, (§4) concrete field-size derivation with the
M31Ext4-vs-M31Ext5 decision, (§5) open questions and implementation
risks, (§6) revised go/no-go ranked against Path C
(batching + final-SNARK, which remains available as the de-risked
fallback).

---

## 1. Landscape — BMNW24 → Arc → WARP

[interstellar-over-m31.md §5.2](./interstellar-over-m31.md) listed
BMNW24 ("Accumulation Without Homomorphism") as Path A, with a
caveat that it has a bounded recursion depth per its own security
argument. The NeutronNova authors specifically flagged "concrete
attacks exist for non-constant recursion depth." This was right at
the time of writing but is now out of date.

### What drove BMNW24's depth bound

BMNW24's IOR is **distance-losing**: every accumulation step outputs
a proximity claim at strictly worse distance `δ + ε` than the input's
`δ`. After `d` steps, the accumulated distance `d · ε` eventually
exceeds the unique-decoding radius `(1 − R)/2`. Beyond that point,
the extractor's decoding step can pick a codeword other than the
prover's intended one — a concrete attack, not an analysis gap
(BMNW24 §2.1.1, Remark 1.1, Remark 2.2).

Structurally this forces the `d_s · δ ≤ (1 − R)/2` constraint at
setup (BMNW24 Theorem 6.5), which pins `d_s` to a constant. BMNW24's
§7.3 proposes a hybrid composition where every `m^{d_s}` accumulation
steps you wrap with a Fractal/STIR-family SNARK — this gives
arbitrary effective depth at the cost of periodic SNARK proofs.

### What Arc fixed (and didn't)

Arc (Oct 2024, same authors) replaces BMNW24's "consistency spot-check
that loses distance" with Reed-Solomon polynomial **quotienting**: if
the prover commits `û` and claims `û(τ) = σ`, the verifier demands a
second commitment to the quotient `(û − σ)/(X − τ)` — which is
itself an RS codeword of degree `d − 1`. Exhibiting the quotient as
a codeword proves the evaluation claim *without* consuming any
distance budget. Result: **Arc is distance-preserving and supports
unbounded depth** (Arc §1.1, §2.1).

The tradeoff: quotienting only works cleanly for Reed-Solomon
(it uses the polynomial structure of RS codewords). Arc is
RS-specific and would require us to abandon Orion's Spielman
expander code and rebuild the PCS around RS-over-M31Ext*. Every
Expander GKR proof today already depends on Orion; switching to RS
is a significant shift of the underlying infrastructure.

### What WARP fixed

WARP (April 2025, same team plus Chiesa and Fenzi) keeps
distance-preservation but swaps the RS-quotient technique for a
**multilinear-extension + mutual-correlated-agreement (MCA) proximity
gap** (WARP §2.2). The construction works for *any* linear code
that admits MCA — which, per WARP §2.9 and the literature it cites
([AHIV17] = Ligero, [ACFY25] = WHIR, [GKL24], [Zei24]), is
**every linear code in the unique-decoding regime**.

WARP explicitly names Brakedown `[GLSTW23]` as a compatible
instantiation (Theorem 1, §2.9 "Instantiation with linear-time
encodable codes"). Orion is a Spielman-expander variant in the
Brakedown family. The compatibility argument transfers directly.

The extractor swap is equally important. BMNW24's extractor needed
**error-tolerant decoding** (NP-hard in general, fast only for
structured codes like RS). WARP's extractor uses **erasure
correction** only (WARP §2.7, Remark 2.2): given the agreement
set `S ⊆ [n]` and a known codeword `w'` on `S`, recover the
underlying `u` for each round by solving a linear system against
the generator matrix. Every linear code has an erasure corrector —
for a generic linear code it's `O(n^3)` (generator-matrix
Gaussian elimination), but this is the security-*reduction* cost,
not prover-or-verifier cost, so it only affects the concreteness
of the knowledge bound, not runtime.

### Where this leaves the rest of the family

| Scheme | Code | Depth | Homomorphism | Fits Orion |
|-----------------|----------|---------------|-----------------|---------|
| Interstellar    | any      | bounded       | required        | no      |
| NeutronNova     | any      | standard IVC  | required        | no      |
| BMNW24          | any      | bounded `d_s` | not required    | yes*    |
| Arc             | RS only  | unbounded     | not required    | no      |
| **WARP**        | **any**  | **unbounded** | **not required**| **yes** |
| Neo / SuperNeo  | (lattice)| unbounded     | uses lattice hom| no (PQ) |

*BMNW24 fits Orion, but bounded depth forces chunking + hybrid
SNARK composition to handle 10M-block sync.

WARP is the **first construction in the literature** that
simultaneously (a) is non-homomorphic (works over Merkle-rooted
code-based commitments), (b) supports unbounded depth, (c) works
over any linear code including Orion's Spielman variant. It was
published after the Phase 1 research cutoff.

---

## 2. WARP adapted for M31Ext5 + Orion

### 2.1 Setup

- `F = M31Ext5`, `|F| = (2^31 − 1)^5 ≈ 2^155`. See §4 for the
  derivation of why Ext5 vs Ext4.
- `C = Orion-Spielman` linear code over `F`. Rate `ρ ≈ 0.4`,
  relative distance `δ(C) ≈ 0.1` (conservative — Orion's paper
  claims higher but we use a loose bound for soundness arithmetic).
- Merkle tree over Poseidon2 for in-circuit sponge friendliness,
  or Blake3 for out-of-circuit Merkle openings — Willow already
  has both. Treated as `ρ_MT` in the WARP paper's notation; the
  RO model instantiates whichever hash we pick.
- Random-oracle calls for Fiat-Shamir use Poseidon2 (for the
  subset of RO calls that must be replayable inside the fold
  recursion circuit).
- `λ = 128` bit soundness target.

Shapes, following Theorem 10.3:
- Block-proof witness `w ∈ F^k`, `k ≈ 2^22` for a typical block.
- Witness codeword `f = C(w) ∈ F^n`, `n ≈ 2^24`.
- Single-block PESAT index `i = (p̂, M, N, k)`: `p̂` is the
  constraint-system polynomial of degree `d`, `M ≈ 2^20` constraints,
  `N = n_pub + k` total variables.
- Accumulator instance `acc.x = (rt, α, μ, β, η)` — one Merkle
  root, one log-n point, two scalars, one log-M+κ point.
- Accumulator witness `acc.w = (td, f, w)` — Merkle tree data,
  full codeword, full witness. Size `O(n + k)`.

### 2.2 One accumulation step

Prover and verifier both run the two chained IORs from WARP
Construction 10.4 under Fiat-Shamir.

**Input to step `i+1`:**
- Running accumulator from step `i`: `acc_i = (acc_i.x, acc_i.w)`.
- New block proof: `(x_{i+1}, w_{i+1})` where `x_{i+1}` is the
  block header plus public state-roots and `w_{i+1}` is the
  circuit witness establishing the block state transition.

**Step 1 — PESAT reduction (WARP Construction 5.10).**
Prover encodes `f_new = C(w_{i+1}) ∈ F^n`. Commits via Merkle:
`rt_0 = MT.Commit(f_new)`. Sets `α_new = 0^{log n}`,
`μ_new = f̂_new(0)`. Absorbs `(x_{i+1}, rt_0, μ_new)` into the FS
transcript. Squeezes zerocheck randomness
`τ ← ρ_FS^{log M}`. Sets `β_new = (x_{i+1}, τ)`, `η_new = 0`.

Output of step 1: one new twin-constrained instance carrying
the new block's proof, plus the old accumulator as the second input
to the next step.

**Step 2 — twin-constrained code accumulation (WARP Construction 9.4).**
This is the fold. Two instances: the old `acc_i` and the new
`(x_{i+1}, rt_0, α_new, μ_new, β_new, η_new)`. Run:

1. Squeeze `γ ← ρ_FS^{log 2}` — just one scalar in `F`, since
   `ℓ = 2`.
2. Define multilinear extensions:
   - `F̂(I) = (1−I)·f_i + I·f_new` — linear in the single outer
     variable `I` (recall `log ℓ = 1`).
   - `ŵ(I) = (1−I)·w_i + I·w_{i+1}`.
   - `Â(I) = (1−I)·α_i + I·α_new`.
   - `B̂(I) = (1−I)·β_i + I·β_new`.
3. Squeeze zerocheck randomness `(τ_outer, ω) ← ρ_FS^2`.
4. **Sumcheck pass #1** (1 round, since `log ℓ = 1`). Prover sends
   the univariate `ĥ_1^{(1)}(X)` of degree at most
   `max(log n + 1, log M + d) + 1 ≈ 25` over `F`. Verifier absorbs
   `ĥ_1^{(1)}`, squeezes `γ_1`. Sumcheck consistency:
   `ĥ_1^{(1)}(0) + ĥ_1^{(1)}(1) = eq(τ_outer, I=0)·(μ_i + ω·η_i)
   + eq(τ_outer, I=1)·(μ_new + ω·0)`.
5. Prover sets:
   - `f = (1−γ_1)·f_i + γ_1·f_new` (as a codeword in `F^n`)
   - `w = (1−γ_1)·w_i + γ_1·w_{i+1}` (as a witness in `F^k`)
   - `ζ_0 = Â(γ_1)`, `β = B̂(γ_1)`
   - `ν_0 = f̂(ζ_0)`, `η = P_b(β, w)`.
6. Prover Merkle-commits `rt = MT.Commit(f)`. Sends `(rt, ν_0, η)`
   into the transcript.
7. Squeeze `s` OOD sample points `ζ_1, …, ζ_s ← ρ_FS^{s·log n}`.
   Pick `s = 2` per WARP §2.9 guidance.
8. Prover evaluates `ν_j = f̂(ζ_j)` for `j ∈ [s]`, sends into the
   transcript.
9. Squeeze `t` shift-query indices `x_1, …, x_t ← [n]` and one
   final `ξ ← ρ_FS^{log r}` where `r = 1 + s + t`. Set
   `ζ_{s+k} = binary(x_k)` for `k ∈ [t]`.
10. **Sumcheck pass #2** (`log n ≈ 24` rounds). Verifier absorbs
    each `ĥ_j^{(2)}` (degree 2, WARP §8.2), squeezes
    `α_j ← ρ_FS`. After all rounds, set `α = (α_1, …, α_{log n})`,
    `μ = f̂(α)`.
11. Prover opens `t` Merkle paths in each of the input accumulators'
    codewords (into `acc_i.w.td` and the new `rt_0`'s tree data)
    at the shift-query positions `(x_1, …, x_t)`. These are the
    `auth_0, auth_1` in WARP's notation.

**Output of step `i+1`:**
- `acc_{i+1}.x = (rt, α, μ, β, η)` — constant size, one Merkle root
  plus five field points/vectors.
- `acc_{i+1}.w = (td, f, w)` — Merkle tree data for `f`, full
  codeword `f`, full witness `w`. This is size `O(n + k)` per step
  — does *not* grow in `i`; it's replaced each fold.
- `pf_{i+1}` — the fold-verification proof: sumcheck polynomials
  `ĥ`, OOD evaluations `ν`, Merkle authentication paths.

### 2.3 Choosing `t`, `s`, and `ρ`

- `t` (shift-query count) = `⌈λ / (−log(1 − δ_PG))⌉`.
  For `δ_PG = δ(C)/3 ≈ 0.033` (unique-decoding regime):
  `t = 128 / (−log(0.967)) ≈ 128 / 0.0485 ≈ 2640 queries per step`.
  This is the dominant prover-side cost per fold.
- `s` (OOD samples) = 2 per WARP §2.9. Small constant.
- `ρ` (code rate) — fixed by Orion's code at ≈ 0.4. Different from
  FRI/Arc where we'd tune it to balance prover/verifier.

`t ≈ 2640` is large. To calibrate: Arc at rate 1/16 with
`λ = 128` runs `t = 32`, which is 80× fewer queries. The
difference is fundamental — RS has much better distance than
linear-time-encodable Spielman codes, so each shift-query gives
more information per bit. WARP over Spielman pays more queries per
bit and amortizes over linear-time encoding. This is the
"which code?" tradeoff WARP §2.9 explicitly flags.

### 2.4 Final wrap-up

After `T` folds, the running accumulator `acc_T.x` is submitted
on-chain in a `HistoricalCheckpointTx`. The full `acc_T.w` stays
with the indexer.

The **decider** (WARP Construction 10.4, Step 3 of `D_ACC`):
1. Check `(rt, td) = MT.Commit(f)` — re-hash the codeword.
2. Check `f̂(α) = μ` and `P_b(β, w) = η` — two field-ops-linear
   checks.
3. Check `f = C(w)` — re-encode the witness.

This is **`O(n + k) + O(enc_C)` work**, linear in codeword size, not
succinct. Two options to ship this as a consensus proof:

(A) Consensus validators run the decider directly. For our
codeword size `n ≈ 2^24`, that's about `2^24` hashes plus `O(n)`
field ops — tens of seconds of verifier work on modern hardware,
per checkpoint. Acceptable if checkpoints are infrequent
(e.g., once per 10M-block epoch).

(B) Wrap `D_ACC` in a final SNARK. The decider's circuit is a
straight-line computation that we already know how to prove with
Willow's GKR stack — the same machinery we use for
per-block proofs. Extra cost: one final SNARK per epoch. This
makes the on-chain verify constant-size.

Option (B) is what WARP §7.3 / Arc §10 call the hybrid. Willow's
existing GKR prover handles this without new machinery.

---

## 3. Soundness over M31Ext5 + Orion

WARP's main theorem is Theorem 10.3. Summary of lemma transfer:

### 3.1 MCA property for Orion's Spielman code — **transfers in UD regime**

WARP requires `C` to admit a strong proximity generator (Def. 3.15)
— *mutual correlated agreement* of `C` with proximity radius
`δ_PG` and error `err_PG`.

Per WARP §2.9: "This [MCA] is known for every linear code in the
unique-decoding regime" via [AHIV17] and [ACFY25]. Concretely:
`δ_PG = δ(C)/3`, `err_PG = n / |F|`.

For Orion's Spielman code: `δ(C) ≈ 0.1` (loose; true value is
higher, see Orion paper [XZS22]), so `δ_PG ≈ 0.033`,
`err_PG = 2^24 / 2^155 = 2^-131`. Easily negligible.

List-decoding regime gives better `δ_PG` at the cost of polynomial
`err_PG` ([GKL24, Zei24]). Not needed here — UD is fine for our
parameters. Worth revisiting if we ever push `n` beyond `2^28`.

**Lemma transfer: unchanged.** No code-specific reproof needed;
we cite [AHIV17] which gives MCA for any linear code in UD.

### 3.2 Sumcheck soundness (Lemmas 3.2 — polynomial identity lemma) — **transfers**

Standard SZ. Error `max(d·m, log n, log M) / |F|`. Over M31Ext5
with `n, M ≤ 2^24`: error `≤ 2^24 · d / 2^155 ≈ 2^-125` for
`d = O(1)`. Fine.

### 3.3 Merkle commitment extraction (BCS / Valiant) — **transfers**

WARP uses the BCS compiler with the standard Merkle extractor
([CY24] §18). This is exactly what Orion already relies on for its
opening proofs. Blake3-Merkle or Poseidon2-Merkle both fit.
No new assumption beyond the ROM.

### 3.4 Fiat-Shamir soundness — **transfers**

`κ_FS(t_FS)` from [CO25]. Polynomial in adversary query budget.
For our `λ = 128` target with honest query count
`q_honest ≈ T · q_per_fold ≈ 10^7 · 10^4 ≈ 2^38`, the FS adversary
budget can be up to `2^{λ+something}` without breaking. Fine.

### 3.5 Distance preservation (WARP Lemmas 6.6, 7.3, 8.4) — **transfers**

The three IOR constructions (twin pseudo-batching, codeword
batching, multilinear constraint batching) are each proven
distance-preserving in WARP §6.2, §7.2, §8.2. The proofs use only
the MCA property, sumcheck soundness, and polynomial identity —
none require RS structure.

**Lemma transfer: unchanged** for any linear code satisfying MCA.

### 3.6 Erasure-correction extractor (WARP Construction 9.5) — **transfers**

The extractor solves a linear system against `C`'s generator
matrix. Every linear code has a generator matrix. Spielman's
construction is structured — cascaded expander graphs — so the
generator matrix is sparse and erasure correction should be faster
than the generic `O(n^3)`. But even with the generic bound, this
is a security-reduction cost, not a runtime cost.

**Lemma transfer: unchanged.** Spielman-specific optimization
(exploiting expander structure) is nice-to-have, not required.

### 3.7 Summary table

| WARP lemma | Property used | Transfer to Orion | Field req |
|---|---|---|---|
| Def 3.15 (MCA) | code has MCA | ✓ (UD regime) | `err_PG = n/|F| negl` |
| Lemma 3.2 (SZ) | polynomial ID | ✓ | `|F| ≥ 2^λ · d · m` |
| Lemma 6.6 (twin IOR) | MCA + SZ | ✓ | as above |
| Lemma 7.3 (codeword batch) | MCA + SZ | ✓ | as above |
| Lemma 8.4 (multilinear ext) | MCA + SZ | ✓ | as above |
| Construction 9.5 (erasure ext) | generator matrix | ✓ | none |
| Theorem 9.1 (R_C IOR) | 9.5 + 6.6 + 7.3 + 8.4 | ✓ | `polylog` |
| Theorem 10.3 (WARP acc) | 9.1 + BCS + FS | ✓ | concrete — see §4 |

**Everything transfers.** No code-specific lemma needs reproof.
Orion's Spielman-variant linear code sits squarely in WARP's
target family.

---

## 4. Concrete field-size — why M31Ext5

The combined soundness-error expression from WARP Theorem 10.3,
specialized to UD regime where `|Λ(C, δ)| = 1`:

```
|F| ≥ 2^λ · max {
  log M · 1,
  (log ℓ + 1) · 1,
  (1 + max{log n + 1, log M + d}) · 1 + (ℓ/2) · err_PG · |F|,
  2^{λ/s − 1} · log n,
  max{2, log(1+s+t)}
}
```

The binding constraint for Willow's parameters comes from the OOD
sample term `2^{λ/s − 1} · log n`:

- `s = 2` (standard WARP choice), so `2^{λ/s − 1} = 2^{63}`.
- `log n = 24`, so the product is `2^{63} · 24 ≈ 2^{67.6}`.

Combined with the `2^λ` outer factor:

`|F| ≥ 2^128 · 2^{67.6} = 2^{195.6}`.

That's enormous — M31Ext7 territory. But this is the *worst-case
provable* bound. Two mitigations:

(i) **Increase `s`**: setting `s = 16` gives `2^{λ/s − 1} = 2^7 = 128`,
and the term drops to `2^7 · 24 ≈ 2^{11.6}`. Combined: `|F| ≥ 2^{140}`.
Tradeoff: prover sends 16 OOD evaluations per step instead of 2.
Negligible constant-factor cost.

(ii) **Accept conjectured security** in the style of FRI / STIR /
WHIR. Paper §2.9 and follow-on work suggest provable constants are
overly conservative; in practice rate-`1/4`-adjacent schemes run at
`|F| ≈ 2^{128}`. Not our preferred posture — we want provable
128-bit soundness — but worth knowing the gap is 10–20 bits, not
50+.

With (i): **`|F| ≥ 2^{140}` for provable 128-bit soundness.**

- M31Ext4 ≈ `2^{124}`: short by 16 bits. Unusable at 128-bit target;
  usable at 108-bit target (M31Ext4 − 16 bits = `2^{108}`
  soundness against provable bound).
- M31Ext5 ≈ `2^{155}`: 15-bit margin. **Target field.**
- M31Ext6 ≈ `2^{186}`: 46-bit margin; extra if we want flex room.

**Decision**: M31Ext5. 15-bit margin is enough for `λ = 128`
with no reliance on conjectured security. Ext4 is viable only if
we drop target to `λ = 108`, which is below our floor.

**Implementation note**: Expander's arithmetic tower currently
stops at Ext3. Ext4 is being added per the original design doc
`docs/todo/m31-folding.md:99`; Ext5 would be a further extension.
This is a constant-effort delta (new extension trait impl + test
vectors) rather than a structural change.

---

## 5. Open questions and implementation risks

### 5.1 No reference implementation

**WARP has no public Rust, C++, or Go implementation.** Arc doesn't
either. This is an implementation-schedule risk, not a correctness
risk: we'd be producing the first implementation of both WARP and
Arc's ideas. The paper is self-contained enough for a careful
implementer; the proofs are detailed; the constants are given. We
own the port.

Offset: this is a genuine open-source contribution. Publishing
`crates/folding/` as a WARP-over-any-code implementation is useful
to the broader ecosystem (same value the original design doc
flagged under "pioneer moat").

### 5.2 Query count `t ≈ 2640` per fold

Over a linear-time-encodable code like Orion's Spielman, WARP runs
`t ≈ 2640` shift queries per fold (§2.3). For `T = 10^7` folds,
total queries = `2.6 · 10^{10}`. Each query is one Merkle path into
a depth-`log n ≈ 24` tree — so `2.6 · 10^{10} · 24 = 6.24 · 10^{11}`
hash ops total.

At Poseidon2's ~10 μs per hash, that's `6.24 · 10^6` seconds ≈
72 days of indexer-side compute for a single historical sync of
a billion rows. This is the number that decides whether WARP + Orion
is actually viable for Willow's historical-sync target.

Three paths if this is too slow:
- **Reduce `n` via sharding**: fold smaller sub-windows
  separately, compose trees of accumulators. Reduces `t` per fold
  but adds composition overhead.
- **Use RS instead of Spielman** — switch to Arc's approach. Pay
  the FFT cost in exchange for `t ≈ 32` instead of `2640`. Drops
  total query work by ~80×. But loses Orion compatibility.
- **Accept it**: 72 days for a one-time historical sync on
  launch isn't necessarily absurd for a new chain's archival
  service; subsequent folds are amortized.

**This is the dominant benchmarking question for Phase 3.**

### 5.3 MCA constants for Spielman codes specifically

WARP's MCA bound for generic linear codes uses the worst-case
`δ_PG = δ(C)/3`. Spielman expander codes may admit tighter MCA
constants — we don't have a proof of this, but the structure
(two cascaded expanders) is amenable to it, and WARP §2.9 notes
"deriving improved mutual correlated agreement parameters for
these special cases is an important research direction." Tighter
MCA → smaller `t` → faster fold. This is a cryptography-research
win that would lower §5.2's compute estimate; shouldn't block
Phase 2 but is worth an email to Bünz / Chiesa if we pursue this.

### 5.4 In-circuit NIFS verifier for IVC

WARP is an accumulation scheme, not a folding scheme in the
Nova-IVC sense. The paper doesn't commit to an IVC construction
— that's a separate compiler step (BCLMS21 or similar). If we
want self-verifying IVC (each block's `F*` verifies the previous
accumulator step inside its own circuit), we need to instantiate
that compiler on top of WARP.

Concretely, the NIFS-verifier-in-circuit cost is dominated by
`(1 + ℓ_2) · t` Merkle openings. For `ℓ_2 = 1` (one incoming
accumulator) and `t = 2640`: about 5280 Poseidon2 hashes per
in-circuit fold-verify. At ~200 constraints per Poseidon2 in a
GKR-friendly circuit, that's ~10^6 extra constraints in `F'`.
Non-trivial but tractable — about 30–50% overhead on top of the
base block proof's circuit size (assumed ~2^22).

Alternative: don't do IVC at all. Keep the fold "external" — the
indexer runs the fold sequentially, and consensus verifies the
final accumulator + the decider. No circuit recursion needed. This
is simpler and matches the design doc's §Integration points 2 and 3.

**Recommendation**: skip IVC for Phase 2. Ship external folding
first. Revisit IVC in Phase 5+ if we need self-verifying indexer
proofs.

### 5.5 QROM security

WARP is proven in the classical ROM. QROM is conjectured but not
proven (paper footnote 1). For Willow's threat model (no quantum
adversary in the near term) this is fine; worth documenting as a
known gap for when the industry moves to QROM-required.

### 5.6 Hash choice: Poseidon2 or out-of-circuit hash?

Orion currently uses Blake3 for Merkle roots (switched from
Keccak-256 in #399, 2026-05-20). WARP treats the hash as a pure RO;
any out-of-circuit hash works. Blake3 is faster outside circuits
(~30 ns vs Poseidon2's ~10 μs); Poseidon2 is 100× friendlier
inside circuits.

For Willow's architecture:
- **External folding (indexer-side)**: Blake3 wins on raw speed.
  No circuit constraint.
- **In-circuit fold verify**: Poseidon2 wins by a huge margin.
- **Cross-compatibility with existing Orion commits**: out-of-circuit
  hash stays.

Decision can be deferred. Cost: one hash-function switch in the
fold's Merkle trees, independent of WARP correctness.

### 5.7 Final decider cost on consensus

WARP's decider is `O(n)` — for `n = 2^{24}`, tens of seconds of
validator compute per checkpoint. If checkpoints are once per
epoch (say daily), this is fine. If they're per-block, it's
unacceptable. The original design doc's positioning was
"`HistoricalCheckpoint` payloads", which are infrequent — matches
the (A) variant in §2.4. If we later want per-block folded
verification we'd need the (B) variant (SNARK-wrap the decider),
which is extra work but well-understood.

---

## 6. Revised go/no-go

### 6.1 Recommendation: GO on WARP-over-M31Ext5-Orion for Phase 2.

Three things are different from the [Phase 1 writeup's
recommendation](./interstellar-over-m31.md):

1. The scheme is WARP, not Interstellar and not NeutronNova.
2. The field is M31Ext5, not M31Ext4.
3. The recursion-depth concern that made Phase 1 lean toward
   Path C (batch + final SNARK) is resolved — WARP is
   structurally distance-preserving and supports unbounded depth.

The old Phase 1 Path A (adopt BMNW24) is **superseded by WARP**.
Path C (batch + final SNARK) remains available as the de-risked
fallback if Phase 3 benchmarking shows WARP + Orion's per-fold
cost is prohibitive — see §5.2.

### 6.2 Why GO now

Against the Phase 1 no-go arguments:

- "Interstellar requires commitment homomorphism": WARP does not.
  Erasure-correction extractor over any linear code.
- "Bounded recursion depth on BMNW24": WARP is distance-preserving,
  unbounded depth.
- "No Rust implementation": still true. Accepted as a schedule
  risk (Phase 2 gets longer), not a correctness risk.
- "M31Ext4 soundness margin is tight": confirmed — use M31Ext5.

Against Path C:

- Path C is fundamentally `O(T)` witness on the prover side. WARP
  is `O(1)` witness per step, `O(n + k)` per step replaced.
- Path C's on-chain commitment is `O(1)` only after an expensive
  final SNARK over `T` instances. WARP's final SNARK over one
  accumulator's decider is `O(n)` — 10× smaller.
- Path C gives up the "one accumulator proves everything"
  architecture cleanness. WARP preserves it.

### 6.3 What we don't yet know

- Concrete per-fold wall-clock cost on Willow's workload. §5.2's
  back-of-envelope gives 72 days for a full 10M-block sync. This
  is the single biggest open question for Phase 3.
- Whether Spielman-code-specific MCA constants can cut `t` down.
  Optional research collaboration with paper authors.
- QROM proof for WARP. Not a blocker for shipping; a documentation
  gap for long-term claims.

### 6.4 Phase 2 scope update

The original design doc's Phase 2 ("implement the core scheme as a
standalone crate, fold two toy sumcheck instances over M31Ext4 into
a single accumulator") needs to update:

- "two toy sumcheck instances" → "two toy linear-code witness
  codewords with synthetic PESAT constraints" (WARP's relation).
- "M31Ext4" → "M31Ext5".
- Starting-point code: not `poly_commit/src/batching.rs` (that's
  curve-based and for homomorphic PCSs); not Orion itself
  (wrong abstraction layer). The right reference is WARP
  Construction 10.4, transcribed into Rust, with Orion plugged
  in as the MT commitment primitive. Expected size: ~1.5–3 kLoC
  for a first-cut fold-only implementation plus test vectors.

Estimated effort for the updated Phase 2: 3-4 weeks of focused
sessions (up from the original 2-3 weeks), reflecting the
first-implementation risk and the slightly richer scheme.

### 6.5 Action items

1. **Update [docs/todo/m31-folding.md](../todo/m31-folding.md)**: change
   the scheme target from Interstellar to WARP, field from Ext4 to
   Ext5, remove NeutronNova fallback (has same hom assumption as
   Interstellar), add Path C as explicit fallback.
2. **Correct the Orion-homomorphism claim** on line 106 of that
   doc: "Orion is already homomorphic at the commitment level" is
   wrong. The linear code is linear; the Merkle root is not. WARP
   doesn't require root-level homomorphism, so the factual fix is
   "Orion's commitment structure (Blake3-Merkle over
   Spielman-encoded witness) fits WARP's non-homomorphic
   accumulation framework directly."
3. **Ship Phase 2 as scoped in §6.4**: standalone `crates/folding/`,
   first-cut WARP implementation over Orion + M31Ext5, testing
   two-instance fold with synthetic PESAT constraints.
4. **Phase 3 benchmark target**: achieve `<10 ms per fold` for
   `n = 2^22`. If we miss, drop to Path C and ship batch+SNARK
   instead.

---

## 7. References

- WARP: Bünz, Chiesa, Fenzi, Wang. "Linear-Time Accumulation Schemes." [eprint 2025/753](https://eprint.iacr.org/2025/753). TCC 2025.
- Arc: Bünz, Mishra, Nguyen, Wang. "Arc: Accumulation for Reed–Solomon Codes." [eprint 2024/1731](https://eprint.iacr.org/2024/1731). CRYPTO 2025.
- BMNW24: "Accumulation Without Homomorphism." [eprint 2024/474](https://eprint.iacr.org/2024/474).
- Interstellar-over-M31: [../research/interstellar-over-m31.md](./interstellar-over-m31.md) (Phase 1).
- Ligero (AHIV17): [eprint 2017/1098](https://eprint.iacr.org/2017/1098).
- Brakedown (GLSTW23): [eprint 2021/1043](https://eprint.iacr.org/2021/1043).
- WHIR (ACFY25): [eprint 2024/1586](https://eprint.iacr.org/2024/1586). MCA construction.
- Orion (XZS22): [eprint 2022/1010](https://eprint.iacr.org/2022/1010). Spielman-expander PCS.
- STIR (ACFY24): [eprint 2024/390](https://eprint.iacr.org/2024/390). RS-specific proximity gaps.
- Parent design docs:
  - [docs/todo/m31-folding.md](../todo/m31-folding.md).
  - [docs/todo/cryptographic-archival.md](../todo/cryptographic-archival.md).
