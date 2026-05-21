# Interstellar over M31Ext4 + Orion — Research Writeup

**Status**: Phase 1 deliverable. Math-first. Code-free.
**Parent**: [docs/todo/m31-folding.md](../todo/m31-folding.md)
**Papers studied**:
- Interstellar. Jieyi Long. [eprint 2025/1294](https://eprint.iacr.org/2025/1294) (v2, July 2025). 71 pp.
- NeutronNova. Kothapalli & Setty. [eprint 2024/1606](https://eprint.iacr.org/2024/1606) (Oct 2024). 58 pp.
- Accumulation without homomorphism. Bünz, Mishra, Nguyen, Wang. [eprint 2024/474](https://eprint.iacr.org/2024/474) (referenced, not the primary object of study).
- Expander: `poly_commit/src/orion/` (Orion impl), `poly_commit/src/batching.rs` (existing merge-points primitive).

## TL;DR

**Interstellar as written does not transfer to Willow's M31Ext4 + Orion
stack.** The paper requires an *additively homomorphic* multilinear
polynomial commitment (Def. of `PolyCom` in §5.1, and verifier step
`com_{w_γ} ← (1−γ)·com_{w_0} + γ·com_{w_1}` in Construction 12).
Orion's commitment is the Blake3 Merkle root of an encoded
codeword — linearity at the codeword layer, but the Merkle root
destroys additive homomorphism and cannot be reconstructed from the
component roots without access to the original messages.

The paper's two named instantiations — Pedersen+Bulletproofs and Dory
— are both elliptic-curve-group commitments and would push us back
into the non-native-EC-over-M31 regime (the ~1000× pain that motivated
rejecting Nova in the first place).

**NeutronNova does not escape this.** Its Def. 16 states the
additive-homomorphism assumption verbatim as a hard requirement, and
the authors themselves (§1.2, lines 421–427) flag Merkle-rooted
accumulation as a separate research line (Bünz et al. 2024/474)
outside their scope.

The "fallback" named in the design doc therefore has the same blocker
as the primary scheme. This is not a parameter-tuning problem; it is
a structural mismatch between the commitment-additivity requirement of
the Nova-family folding literature and the hash-based commitment layer
Willow uses everywhere else.

**Recommendation**: no-go on Phase 2 as currently scoped. Pivot
options are detailed in §5, ranked:

1. **Re-scope to non-homomorphic accumulation** (BMNW24 / hash-based
   accumulation schemes). Known costs: extra Merkle openings per
   fold; bounded recursion depth per BMNW24's own security argument.
2. **Wait ~6 months on Neo / SuperNeo** (eprint 2025/294, 2026/242).
   These explicitly target small prime fields and avoid the
   homomorphism dependency, but have no Rust implementation and the
   lattice tradeoff was not-preferred in the design doc.
3. **Abandon folding; do final-SNARK-compression over a running
   batch**. Not a fold in the IVC sense; the witness still grows with
   T, but the on-chain accumulator stays constant once compressed.
   Already close to what `poly_commit/src/batching.rs` can do.

The cost of learning this now vs. after Phase 2 implementation is
roughly the budget difference the design doc itself flagged as the
purpose of Phase 1.

---

## 0. Setup

Throughout:

- `F = M31Ext4`, where `M31 = Z/(2^31 − 1)`. `|F| ≈ 2^124`. `λ` denotes
  the soundness-security parameter (target 128 bits; 100 bits is the
  minimum we'd accept).
- All multilinear polynomials are in `F[X_1,…,X_ν]` with evaluation
  domain `{0,1}^ν`, matching Expander's existing `MultiLinearPoly`
  convention.
- `Orion(pk, f)` denotes the Orion commit function, returning
  `Node = [u8;32]` (a Keccak-256 digest). See
  `poly_commit/src/orion/utils.rs:193` for the alias,
  `:210–247` for `commit_encoded`.
- `Orion.open(pk, f, r, sp)` returns an `OrionProof`
  (`utils.rs:201–207`) — an `eval_row`, a set of `proximity_rows`,
  Merkle `query_openings`, and a `merkle_cap`.
- `enc : F^M → F^N` is the Spielman-expander linear code
  (`poly_commit/src/orion/linear_code.rs:274–290`). Linear by
  construction (proved in `linear_code_tests.rs:26–74`):
  `enc(α·a + β·b) = α·enc(a) + β·enc(b)`.
- `MerkleRoot(·)` is the Blake3 binary Merkle tree over the
  transposed packed codeword (`utils.rs:241–244`).

The Interstellar paper's notation conflict to flag upfront: they use
`F` both for the field and for the circuit. I'll write `F*` for the
normalised circuit (paper's convention preserved) and `F` for the
field, with no ambiguity.

---

## 1. Interstellar adapted for M31Ext4 + Orion — the intended scheme

This section writes out what a faithful port would look like. §2
then analyses where it breaks.

### 1.1 Circuit normalisation (paper §4.1, transferred unchanged)

Given the circuit a Willow block-proof step computes,
`C : F^n_pub × F^n_wit → F^n_out`, the prover normalises it into a
shallow, single-output circuit

```
F*(β, x, w) : F^{log n_out} × F^n_pub × F^n_wit  →  F
```

via three steps (paper Lemmas 5–8):

1. **Augmentation** `C → C'`: append the NIFS verifier circuit plus
   two sponge hashes (over Poseidon2 — Willow's existing
   hash-in-circuit choice) so each step proves not just its own
   transition but also that the last fold was valid.
2. **Flattening** `C' → C̄`: split depth-`d̄` circuit into `k` parallel
   blocks of depth `⌈d̄/k⌉`. Intermediate block outputs become extra
   witness entries `h_{k−1},…,h_1`. Extra gates enforce the output
   vector is zero-when-satisfied. `k` is a free design parameter.
3. **Single-output reduction** `C̄ → F*`: collapse the
   length-`n_out` output vector to a single `F`-scalar via
   `y = s · y⃗`, where `s = s(β) ∈ F^{n_out}` is the MLE-of-`eq`
   expansion
   `s_i = ∏_{j=0}^{log n_out − 1}
          [i_j·β_j + (1−i_j)·(1−β_j)]`.
   The verifier samples `β ∈ F^{log n_out}` uniformly.

Output: `F*` with inputs `(β, x, w)` and a single `F`-scalar output.
Degree `D* = d̄ + log n_out`. Depth `d* = min(d̄, log n_out) + 2`. All
arithmetic in `F = M31Ext4`.

**Nothing in this step is field- or commitment-specific.** It
transfers to M31Ext4 unchanged, and a Willow GKR prover can evaluate
`F*` with no new machinery beyond a Poseidon2-sponge gadget, which we
already have (see recent `feat(gkr): hand-built Poseidon2 sponge`
commit on master).

### 1.2 The interactive folding scheme (paper Construction 12) — as
written

State going into one fold step:

```
Acc (running):  U = (β_U, x_U, com_{w_U}, y_U)
                W = w_U                (prover-only)
New instance:   u = (β=⊥, x, com_w, y=0)
                w = w                  (prover-only)
```

where `com_{w_U}, com_w` are multilinear commitments to the
*normalised witnesses*
`ŵ_U, ŵ : F^{log|w|} → F` (MLE of the witness vectors).

One round of the fold (interactive):

1. V → P: `β_u ← F^{log n_out}` uniform.
2. P → V: `{y(2), y(3), …, y(D*)}`, where
   `y(t) = F*(β(t), x(t), w(t))`
   with `β(t) = (1−t)β_U + t·β_u`, `x(t)` similarly, `w(t)` similarly.
   Points `t=0,1` are known: `y(0)=y_U, y(1)=0`. Only `D*−1` new
   evaluations on the wire.
3. V → P: `γ ← F` uniform.
4. P and V each compute:
   - `β_γ ← (1−γ)·β_U + γ·β_u`   (in `F^{log n_out}`)
   - `x_γ ← (1−γ)·x_U + γ·x`      (in `F^{n_pub}`)
   - `y_γ ← y(γ)`, interpolated from `{(0,y_U),(1,0),(2,y(2)),…,(D*,y(D*))}`  (in `F`)
   - `com_γ ← (1−γ)·com_{w_U} + γ·com_w`    **(★ the load-bearing step)**
5. P additionally computes:
   - `w_γ ← (1−γ)·w_U + γ·w` (in `F^{|w|}`)

Output: `U' = (β_γ, x_γ, com_γ, y_γ)`, `W' = w_γ`.

Fiat-Shamir (Construction 15): replace V's `β_u` and `γ` samples with
`ρ(vk, U, u, …)` where `ρ` is a domain-separated random oracle (we'd
use Poseidon2, as we do for GKR already).

Size of `U` stays constant per fold. Size of `W` stays constant per
fold (equals `|w|`; does not grow in the number of folds). This is
the "folding" property.

### 1.3 Where it breaks — step 4's `com_γ`

If `Orion(·)` is the commitment primitive and `(+,·)` act on its
output type `Node = [u8;32]`, then step 4's final line reads:

```
com_γ ← (1−γ) * Node_U + γ * Node_u              ??
         ──────────────   ───────────
         "scalar-mul of   "scalar-mul of
         a Keccak digest"  a Keccak digest"
```

This is nonsense. `Node` is not an `F`-vector space element. There is
no well-defined `+` or `F`-scalar-mul on Keccak digests.

Looking deeper: what the verifier *wants* `com_γ` to be is a valid
commitment to `w_γ = (1−γ)w_U + γ·w`. The codeword layer cooperates
— `enc` is linear, so
`enc(w_γ) = (1−γ)·enc(w_U) + γ·enc(w)`. But the commitment layer
bolts a Merkle tree on top of the codeword. Merkle trees are not
linear:
```
MerkleRoot(enc(w_γ)) ≠ (1−γ)·MerkleRoot(enc(w_U)) + γ·MerkleRoot(enc(w)),
```
and in fact the RHS is not well-typed (scalar-mul of hash outputs).

There are three candidate workarounds, each with its own cost:

**(W1) Store the full codeword, not its root, in the accumulator.**
Then accumulator-linearity holds:
`cw_γ = (1−γ)·cw_U + γ·cw_u`. But the accumulator is now size `O(n)`
rather than `O(1)` — a *batched commitment*, not a folding
accumulator. Expander's `prover_merge_points` already does this
shape (`poly_commit/src/batching.rs:22`); it's the starting
template the design doc flagged, but it is explicitly not a fold
(witness grows linearly in the number of instances). Moving from
Merkle-root to codeword storage is a strict regression on
succinctness.

**(W2) Prover commits `w_γ` fresh each step; provides an opening
proof that `w_γ = (1−γ)w_U + γ·w`.** This preserves constant
accumulator size at the commitment layer, but each fold now
requires:
  - 1 fresh Orion commit to `w_γ`, size `O(n_wit)`.
  - 2 Orion openings (`w_U(r), w(r)` at a verifier-chosen point
    `r`) plus 1 opening of `w_γ(r)`.
  - A field-level consistency check: `w_γ(r) =?= (1−γ)w_U(r) + γ·w(r)`.

  Per-fold cost dominated by the fresh commit, which is `Θ(n_wit)`
  field ops plus Θ(n_wit) hashes. For a typical
  Willow block proof (`n_wit ≈ 2^22`), this is in the same ballpark
  as *re-running the block prover*, erasing the folding advantage
  entirely. Additionally, each such "fresh-commit-plus-opening" must
  enter the augmented circuit `F*` of the *next* step (the IVC-style
  self-verification loop). An Orion-verifier-in-circuit is a
  substantial gadget — Orion opening verification runs an
  encoding check plus `q ≈ 80` Merkle-path verifications per
  proximity query. This is the "non-native EC in a circuit" problem
  restated in the language of hash trees: it doesn't help.

  BMNW24 (Bünz et al. 2024/474, "Accumulation without homomorphism")
  is the research line that formalises (W2) rigorously, with
  worst-case recursion-depth bounds. Their own security statement
  (quoted via NeutronNova §1.2, lines 424–427) warns: "concrete
  attacks exist for non-constant recursion depth". Willow's
  historical-sync use-case is definitionally non-constant recursion
  depth (10M+ blocks at Ethereum scale), so we cannot ignore this
  warning.

**(W3) Use a natively-homomorphic commitment.**
Pedersen/Bulletproofs (the paper's `PolyCom_BP` instantiation) or
Dory (`PolyCom_Dory`) both provide the `com_γ` operation for free
— but both require an EC of cryptographic size (256-bit-class
scalar field). Such groups don't exist over M31-compatible primes.
Emulating them inside the `F*` circuit is the Nova-anti-pattern the
design doc already rejected at ~1000× overhead. The SIS-based
Ajtai commitment is another homomorphic option; this is what
LatticeFold / Neo / SuperNeo use, but the design doc explicitly
parks the lattice direction.

### 1.4 Per-step cost, if (★) worked

Recorded for completeness. Assume (W3) or equivalent worked. Per
Interstellar Theorem 14 and Table 1, per fold:

- 1 MSM of size `|w|` over `F` (the `com_γ` combination).
- `D* − 1 ≈ O(d̄ + log n_out) ≈ O(30)` field multiplications on the
  prover side for computing `{y(t)}_{t=2..D*}` evaluations.
- 1 scalar-field `F` uniform sample + 1 vector `F^{log n_out}`
  uniform sample by the verifier (or RO calls under Fiat-Shamir).
- 0 sumcheck rounds per fold (GKR is deferred to final wrap-up).

Verifier online work: `O(D*)` field ops + 1 group-scalar-mul +
1 group-add for `com_γ`.

Final wrap-up (Construction 41): a single GKR-based SNARK on the
accumulated `F*` instance, with commitment `com_{w_U}`. Over Willow's
existing GKR machinery this is already a known quantity — same prover
pipeline as today's per-block proof, just over the flattened
normalised circuit.

Wall-clock: the paper provides no measurements. All speedups are
asymptotic. Their reported 1.59×–6.74× advantage over Nova /
HyperNova / Mova / Protostar is analytical, using `C = 100` as the
MSM-per-field-op cost ratio. This matters — if Phase 2 were to
proceed, the first benchmark would also be the first empirical data
point for the scheme, not a reproduction.

---

## 2. Soundness analysis over M31Ext4 + Orion

Per-lemma, what transfers unchanged, what needs reproving, what
breaks.

### 2.1 Lemma 5 (flattening completeness) — **transfers unchanged**

Pure combinatorial arithmetic identity. No field-size or commitment
dependency. Transfer is trivial.

### 2.2 Lemma 6 (single-output reduction soundness) — **transfers with a soundness-margin caveat**

The lemma: if `β ← F^{log n_out}` uniform and `F*(β, x, w) = 0`,
then `C'(x', w') = y'` with probability `≥ 1 − log n_out / |F|`.

Proof technique: Schwartz–Zippel applied to the multilinear
polynomial `eq(·, β)` paired with the difference of two witness
hypotheses. No 2-adicity, no pairing, no characteristic dependency.
Only `|F|` size.

Concrete soundness over M31Ext4:
- `log n_out ≤ 30` for realistic block proofs (`n_out ≤ 2^30`).
- `|M31Ext4| ≈ 2^124`.
- Per-fold error `≤ 2^30 / 2^124 = 2^-94`.

94 bits is below the 128-bit target but above the 100-bit floor. This
is tight enough to matter. Two mitigation paths:

- **Parallel repetition** (Fiat-Shamir safe): run `r` independent
  β-samples and check all give `y=0`. Error reduces to `(log n_out
  / |F|)^r`; `r=2` gives `≤ 2^-188`, comfortable. Cost: `r × D*`
  extra `y(t)` evaluations per fold, a constant-factor prover cost.
- **Upgrade to M31Ext5** (`|F| ≈ 2^155`). Per-fold error `2^-125`.
  Cost: Expander's current M31 extension tower stops at Ext3;
  Ext4 is being added per the design doc; Ext5 would be a new
  extension definition, non-trivial arithmetic gadget work.

Recommendation in the no-go-overturned case: parallel repetition on
M31Ext4. Cheaper to code than Ext5, and the margin is comfortable.

### 2.3 Lemma 7 (s-vector computation) — **transfers unchanged**

`O(n_out)` computation of `s` via doubling-tree. Field-agnostic.
Transfers.

### 2.4 Lemma 8 (degree bounds) — **transfers unchanged**

Pure combinatorics. Transfers.

### 2.5 Lemma 20 (lookup argument soundness) — **transfers with a characteristic caveat**

The lemma requires `char(F) > max(l, P)` where `l` is lookup-gate
count and `P` is table size. `char(M31Ext4) = char(M31) = 2^31 − 1 ≈
2.15 × 10^9`.

This is fine for `P, l ≤ 2^30`. For larger lookup tables we'd hit the
characteristic wall. Willow's current GKR lookups stay well within
`2^24` entries, so this is not a near-term blocker, but it does bound
what the folded scheme could support long-term. Worth flagging as an
open question for any architecture that wants to fold lookup-heavy
circuits at billion-row scales.

### 2.6 Theorem 14 (fold completeness + knowledge soundness) — **completeness transfers; knowledge soundness has the structural break**

Completeness (prover produces a valid `U'` given valid `U, u`) is a
direct arithmetic identity — it transfers.

**Knowledge soundness is where the wheels come off.** The extractor
in the paper's proof (pp. 61–63) works by:

1. Rewinding two transcripts with the same `β_u` but different `γ_0,
   γ_1 ∈ F`.
2. Solving a 2×2 linear system in `(w_U, w)` over `F`:
   ```
   w_γ_0 = (1−γ_0)·w_U + γ_0·w
   w_γ_1 = (1−γ_1)·w_U + γ_1·w
   ```
   to extract `(w_U, w)`.
3. Verifying extraction consistency at the commitment layer: for
   each extracted pair, check `com_{w_U}`/`com_w` are the actual
   commitments to the extracted witnesses.

Step 3 uses the binding and extractability properties of `PolyCom`
at the commitment layer — i.e., given the extracted `w_U` and the
recorded `com_{w_U}`, the extractor must verify the commitment
equation holds. With Pedersen this is trivial: `com_{w_U} =
Pedersen(ŵ_U, r)` for some randomness `r` the extractor also
recovers.

With Orion, the commitment equation is
`com_{w_U} = MerkleRoot(enc(ŵ_U))`. Orion's binding comes from
Merkle (a random-oracle binding), not a ring/group binding. The
extractor argument as written in the paper assumes an
*algebraically* extractable commitment. Orion is only *RO*
extractable, and only at the positions *queried* in the opening
proof — not at all positions in `w_U`.

This is not a small gap. The forking-lemma extractor needs to
recover *the entire witness* `w_U`, but Orion's opening only
commits to `q`-many alphabet positions out of `N`. To recover the
full witness the extractor must either:
- Run many openings at different points, each forking independently,
  giving a probabilistic reconstruction via the distance argument
  from the Ligero/Brakedown family — this is workable but has not
  been done for folding; it's genuinely new analysis.
- Assume full-codeword access inside the extractor — but then the
  succinctness argument collapses (see W1 above).

**This is the core soundness break.** It is not a missing
calculation — the paper's extractor construction *does not work* for
non-algebraically-homomorphic commitments. Repairing it requires a
distance-based extraction argument that is neither proved in
Interstellar nor in the Orion papers.

For comparison, the BMNW24 paper (Bünz et al. 2024/474) is
specifically the construction that *does* prove a
non-homomorphic-commitment extractor, by leaning on a soundness-test
RLC over proximity tests. It pays for this with
- bounded recursion depth (the paper states concrete attacks exist
  beyond that bound, not merely lack-of-proof),
- substantially higher per-fold hash work.

Interstellar's extractor argument cannot be dropped onto Orion
without importing BMNW24-style machinery, and doing so changes both
the per-fold cost profile and the asymptotic depth-soundness claim.

### 2.7 Theorem 17 (IVC knowledge soundness) — **inherits the Theorem 14 break**

Standard downward induction over step index. If Theorem 14's
extractor fails, so does Theorem 17's. No independent break — this
is just the same failure propagating.

### 2.8 Theorem 22 (lookup-fold soundness) — **transfers contingent on Theorem 14 being repaired**

Independent of the commitment question; uses the pigeonhole argument
on log-derivative polynomials. If a non-homomorphic-commitment
replacement for Theorem 14 is found, Theorem 22 does not impose
additional field requirements.

### 2.9 Theorem 44 (multi-instance / k > 2 fold) — **inherits the Theorem 14 break, with a tighter field-size bound**

Multi-instance fold's soundness error is `k·D*/|F| + k·log|F*|/|F|`.
For `k=8`, `D*=32`, `|F*| ≈ 2^{40}` (log-circuit-size):
error `≈ 8·32/2^124 + 8·40/2^124 ≤ 2^-115`. Still comfortable on
M31Ext4. But again — inherits the Theorem 14 extractor break.

### 2.10 Theorem 25 (collaborative fold) — **inherits the Theorem 14 break plus new extractability requirement**

Collaborative/MPC variant. Explicitly requires `PolyCom` be
*extractable* (Def 16 in paper). Orion's RO-only extractability is
the wrong flavor of extractability for this theorem's MPC simulator
argument.

### 2.11 Summary table

| Lemma/Thm            | Transfers? | Field requirement over M31Ext4                | Commitment requirement | Blocker? |
|----------------------|:----------:|----------------------------------------------|------------------------|:--------:|
| Lemma 5 (flatten)    | ✓          | none                                         | none                   | no       |
| Lemma 6 (single-out) | ✓ (margin) | `log n_out / \|F\| = 2^-94`; use parallel-rep | none                   | no       |
| Lemma 7 (s comp)     | ✓          | none                                         | none                   | no       |
| Lemma 8 (degrees)    | ✓          | none                                         | none                   | no       |
| Lemma 20 (lookups)   | ✓ (bound) | `char(F) > l, P`; OK for `≤ 2^30`            | none                   | no       |
| **Thm 14 (fold KS)** | ✗          | `D*/\|F\|` fine                               | **needs algebraic ext** | **YES** |
| Thm 17 (IVC KS)      | ✗ (inh.)   | —                                            | inherits               | yes      |
| Thm 22 (lookup-fold) | ✓*         | none extra                                   | inherits               | blocked  |
| Thm 44 (k>2 fold)    | ✗ (inh.)   | `k·D*/\|F\|` fine                             | inherits               | yes      |
| Thm 25 (collab.)     | ✗ (inh.)   | —                                            | inherits + MPC ext     | yes      |

(✓\* = would transfer if 14 were repaired.)

**The field side is comfortable on M31Ext4 with parallel repetition
for the SZ terms and attention to lookup-table size. The
commitment side is not: Theorem 14's extractor is the single failure
point, and it cascades through every subsequent result.**

---

## 3. Open questions beyond the three in the design doc

The design doc ([docs/todo/m31-folding.md](../todo/m31-folding.md))
lists five open items; the first three are commitment-interaction
(Orion homomorphism, accumulator-constant-size, M31Ext4 soundness
margin). The remaining two (no public impl; no M31 benchmarks) are
about empirical validation, not research.

Beyond those, this research surfaced:

### 3.1 Augmented-circuit `F'` cost with Orion-opening gadgets

Interstellar's IVC Construction 16 requires `F'` to include the
NIFS verifier for the *previous* fold step. If (W2) is the chosen
workaround, that NIFS verifier contains an Orion-opening-verify
gadget per fold. Estimated circuit size:

- Proximity test: one RLC of proximity rows (linear combination of
  `q ≈ 80` codeword columns, `n` elements each).
- Encoding check: one linear-code encoding of the RLC'd eval_row.
  Spielman code over two expander-graph multiplications at ~2.5×
  message length — `O(n)` gates, but with a non-uniform expander
  structure that's hostile to GKR's uniform-circuit assumption.
- Merkle-path verify: `q · log_2(N)` Keccak/Poseidon2 hashes.
  For `N = 2^22`, `q = 80`: `80 × 22 = 1760` hashes per opening,
  per fold.

Total: on the order of `10^4`–`10^5` gates added to `F'` per fold,
on top of the base circuit. For a base circuit of `~2^20` gates,
that's a 1–10% overhead per step — tolerable, but the proximity
test's non-uniform expander structure may require a dedicated
circuit-interpolation gadget that doesn't exist in our codebase.

### 3.2 Forking-lemma extraction over Orion's proximity test

If we pursue (W2) / BMNW24-style, the extractor uses an RLC over
proximity rows rather than the paper's `(γ_0, γ_1)` rewinding. The
probabilistic-recovery argument requires: number of independent
fork branches × probability-of-consistency-per-branch over the
codeword distance. This calculation has not been done for the
M31-specific Spielman code Orion uses. The paper's analysis
assumes Reed-Solomon codes; Orion's Spielman instantiation has a
different distance-parameter profile (see
`poly_commit/src/orion/linear_code.rs:168–189`). This is net-new
soundness analysis — probably tractable, but not a "read the paper"
exercise.

### 3.3 IVC base case `com_0`

Construction 16 initialises `(U_0, W_0) = ((β=0, x=0, com_0, y=0), w_0 = 0)`.
`com_0` must be `Orion(0, r_0)` for some randomness. Under a
Merkle-rooted commitment, deterministic `r_0 = 0` gives a fixed
starting root (trivially computable). Under homomorphism-enforcing
variants, `r_0` matters. Flag for implementation; not a research
issue.

### 3.4 Parallel-repetition interaction with Fiat-Shamir

If we take the parallel-repetition fix for the Lemma 6 soundness
margin (§2.2), each repetition samples an independent `β`. Under
Fiat-Shamir, these samples come from RO calls over a common
transcript. The usual concern is whether parallel repetitions remain
sound under Fiat-Shamir when the underlying protocol is only
*computationally* sound; for Interstellar's zero-check-to-sumcheck
structure, this is standard (RO binds each sample independently) and
the r-fold repetition gives error `ε^r` cleanly. Not a blocker,
worth confirming in the writeup any cryptographer reviews.

### 3.5 Degree of `F*` under Willow's indexing-circuit workload

`D* = d̄ + log n_out`. For our blockchain-indexing workload,
`d̄ ≈ 14` (GKR layers in `completeness-prover`) and
`log n_out ≈ 22` (`2^22` output rows per block). So `D* ≈ 36`. This
is at the high end of the paper's measured range (`D* ∈ [14, 38]`,
page 18, remark 10). Per-fold soundness `D*/|F| ≈ 2^-118`, fine on
M31Ext4. Per-fold prover cost `O(D* · |F*|)` field ops scales
linearly with `D*`. Worth modeling before any implementation.

### 3.6 Random-oracle domain separation for fold-in-circuit

Under Fiat-Shamir (Construction 15), the NIFS verifier inside `F*`
must reproduce the RO calls for `(β_u, γ)`. This means Poseidon2
sponge calls inside `F*`. Willow already has this
(`feat(gkr): hand-built Poseidon2 sponge primitive`, commit
`9b6cb74c`), so no new gadget. But domain separation — each fold
step's RO input must bind its step index and the accumulator state —
needs explicit protocol-level care. Not a research issue, but a spec
item that will bite in implementation if not written down.

### 3.7 Interaction with Willow's existing `gkr-verify-pure` crate

The design doc wants the folded checkpoint to be verified
cryptographically on consensus. That means the
`WrapupProof` verify function must run inside
`crates/gkr-verify-pure` (portable Rust, no SIMD, deterministic
bincode decoding). Orion verify is already there. But the fold-layer
verify would need to run the NIFS-verify computation plus the final
SNARK-verify. This is not listed as a new crate in the design doc's
§Integration section — should be added before Phase 5.

---

## 4. NeutronNova comparison

NeutronNova (Kothapalli & Setty, October 2024) is the design doc's
named fallback. It is strictly older than Interstellar and does not
resolve the Orion-compatibility issue. Summary of the comparison
(full extraction elsewhere on request):

- **Running instance**: a triple `(NSC, NSCPC, ZCPC)` — one
  nested-sumcheck instance, one "power-check"-shaped variant, one
  deferred power-check over the fresh `e` vector. Constant-shape
  across folds.
- **Fold step**: apply `Π_ZCR` (zero-check→nested-sumcheck
  reduction) then `Π_FNSC` (fold NSC via `SumFold`). One sum-check
  round per fold, degree `d+2`.
- **Commitment requirement**: literal quote from Def. 16: "Let
  `(Gen, Commit)` denote an additively homomorphic commitment
  scheme for vectors over finite field F." Every construction in
  the paper starts with this clause. NeutronNova cannot instantiate
  over Orion without the same workaround Interstellar needs.
- **Field**: no 2-adicity or pairing requirement. The paper
  footnote 4 writes `|F| ≈ 2^256` in the concrete instantiation,
  and the Clover-variant zero-check reduction has error `2^ℓ/|F|`.
  On M31Ext4 at circuit size `ℓ = 30`, Clover's error is
  `2^-94` — same parallel-repetition mitigation as Interstellar,
  or switch to Spartan's `ℓ/|F|` variant (error `2^-119`) at the
  cost of `log ℓ` extra verifier-circuit hashes. Soundness
  arithmetic is not a blocker on M31Ext4, but the margin is
  similar.
- **Recursion wrap-up**: standard NIFS-to-IVC compiler from
  HyperNova [KS24, Lemma 4]. The verifier circuit does group
  scalar multiplications (quote from §1.2: "k + 1 group scalar
  multiplications"). On pure M31 there is no cryptographic-size
  elliptic-curve group, so the recursion circuit either jumps to
  a curve (cycle-of-curves) or suffers the same Nova-anti-pattern
  overhead.
- **Benchmarks**: none. The paper is purely asymptotic. grep for
  "ms", "table", "benchmark", "implementation" returns no concrete
  numbers.

**Net**: NeutronNova ≈ group-based Interstellar minus 8 months of
polish. For Willow's Merkle-commitment constraint, it has the same
blocker; for the small-field-commitment speed advantage that motivated
the design, it loses. As a fallback to Interstellar under the
*current* architecture constraints, it buys nothing.

---

## 5. Go/no-go recommendation

### 5.1 Recommendation: NO-GO on Interstellar-over-M31Ext4-Orion as specified.

The blocking argument is the one in §2.6: the paper's knowledge-
soundness extractor (Theorem 14) requires an algebraically
extractable additively-homomorphic commitment, and Orion's
Merkle-rooted construction is neither. The blocker propagates to
every subsequent theorem in the paper.

This is not a tuning issue, a parameter choice, or an arithmetic
margin. It is a structural mismatch between the Nova-family fold
verifier's `com_γ ← (1−γ)com_0 + γ·com_1` step and any hash-based
commitment. Interstellar, NeutronNova, HyperNova, Protostar,
ProtoGalaxy, Mova all make the same assumption. The papers that
explicitly address non-homomorphic commitments are:

- **BMNW24**: Bünz, Mishra, Nguyen, Wang, "Accumulation without
  Homomorphism", [eprint 2024/474](https://eprint.iacr.org/2024/474).
  The only paper in the fold/accumulation literature that builds a
  formal extractor over a Merkle-rooted PCS. Bounded recursion depth
  per its own security proof.
- **Neo / SuperNeo**: [eprint 2025/294](https://eprint.iacr.org/2025/294),
  [eprint 2026/242](https://eprint.iacr.org/2026/242). Target small
  prime fields explicitly, including M31. Lattice-based PCS (Ajtai
  SIS) provides homomorphism natively. Post-quantum trade-off the
  design doc parked for later consideration.

### 5.2 Pivot options, ranked

**Path A — Adopt BMNW24 as the folding-layer reference. (Preferred if we proceed.)**

- Known-working extractor for Merkle-rooted PCS.
- Integrates directly with existing Orion infrastructure.
- Per-fold cost: base fold + proximity-test RLC + `q ≈ 80` extra
  Merkle paths per step.
- Bounded recursion depth — this is a real constraint for
  10M-block historical sync. Resolution options:
  (i) Split historical sync into chunks of bounded length each
     with its own accumulator; compress the chunk-accumulators at
     consensus.
  (ii) Periodically "refresh" the accumulator by re-running a
       non-folded wrap-up SNARK on a chunk and starting a new fold
       from its output.
- Estimated research effort: another ~1 week to write out the
  BMNW24-over-Orion-for-M31Ext4 writeup, then Phase 2 can proceed.

**Path B — Wait for Neo / SuperNeo maturation, ~6–12 months.**

- Published Feb 2026 (Neo) and very recently (SuperNeo). No
  reference implementation. Authors actively iterating.
- Lattice tradeoff: Ajtai commitments are natively homomorphic over
  small-characteristic lattices. Fits M31 directly — this is
  SuperNeo's whole pitch.
- Post-quantum benefit is a plus, not a blocker.
- Risk: 6–12 months of watching the paper vs shipping now.

**Path C — Abandon folding; ship final-SNARK-compression over batching.**

- Expander's `prover_merge_points` is already the batching primitive
  (multi-point → single-point sumcheck reduction). `HistoricalCheckpoint`
  carries a batch of `T` instances + one
  compression SNARK over them.
- Not a fold: witness-side storage is `O(T)` for the prover.
- But on-chain and in-consensus-verify, it's `O(1)` — the same
  external property the folding scheme was trying to achieve.
- Cost: prover holds a large intermediate state during the
  historical-sync. For a 10M-block sync at `~2^22` bytes per block
  state, that's ~40 TB in the worst case. Impractical unless we
  chunk.
- With chunking: recovers bounded recursion depth at the cost of
  chunk-boundary overhead. Similar profile to Path A but without
  the BMNW24 correctness dependency.

**Path D — Non-native EC PCS (Nova anti-pattern). (Not recommended.)**

Included for completeness. Embed Pedersen or Dory over a
`~256`-bit prime-order group inside an M31 GKR circuit. Prior
art says ~1000× overhead per gate. Design doc already rejected
this. No reason to revisit.

**Path E — Commit to the codeword directly, not its root.**

Accumulator is `O(n)` per fold. The accumulator sits on the prover
and only the final compressed proof goes on-chain. Could work if
the on-chain size is what matters and the prover-side RAM is OK.
For Willow's per-block workload (`n = |F*| ≈ 2^40` gate count,
`n_wit ≈ 2^22` witness length), per-fold accumulator size is
`~2^22 · 16B = 64 MB`. Across `10^7` folds, that's `~640 TB` of
accumulator state, which is impractical to hold in memory or
stream. This path essentially just restates the batching primitive
with a different name. Reject.

### 5.3 Concrete next step

If the recommendation is accepted:

1. **Move the design doc from "Interstellar is the target scheme" to
   "Interstellar's architectural shape + BMNW24's extractor + Orion
   as the commitment"**. Framing the scheme as a custom hybrid
   rather than an off-the-shelf paper implementation.
2. **Write a Phase 1.5 companion writeup** that does for BMNW24
   what this document does for Interstellar: pseudocode adapted,
   soundness transferred, open questions listed. Estimated ~1 week.
3. **Then decide Phase 2 go/no-go**. If BMNW24-over-Orion reads
   clean, proceed. If it surfaces its own blocker, Path C is the
   fallback.

If the recommendation is rejected and the team wants to press on
with Interstellar as-is, the mandatory prerequisite is
**(W3) — introduce a homomorphic PCS for the folding layer only**,
accepting the 1000× non-native EC emulation cost inside `F*`. This
is the scenario the design doc explicitly rejected when eliminating
Nova. I'd need a new motivation for why it's acceptable now that
wasn't acceptable there.

### 5.4 What this Phase 1 bought us

The design doc's own framing (line 240 of
`docs/todo/m31-folding.md`): "Key milestone: Phase 1 ships in ~1
week. If the research writeup surfaces a fundamental soundness
problem for M31Ext4, we learn early and pivot to NeutronNova (or
reassess entirely) before burning implementation time."

The writeup surfaced one — not over M31Ext4 (the field is fine) but
over Orion (the commitment layer isn't). NeutronNova has the same
blocker. The pivot is "reassess entirely," to one of Paths A–C.

Phase 1's purpose has been served. The cost of finding this out now
vs. in the middle of Phase 2 (~2-3 weeks of implementation work,
per the design doc) is the saved budget Phase 1 was designed to
save.

---

## 6. References (full list, de-duplicated from design doc)

- Interstellar: Long. [eprint 2025/1294](https://eprint.iacr.org/2025/1294) (v2, July 2025).
- NeutronNova: Kothapalli, Setty. [eprint 2024/1606](https://eprint.iacr.org/2024/1606) (Oct 2024).
- Accumulation without Homomorphism: Bünz, Mishra, Nguyen, Wang. [eprint 2024/474](https://eprint.iacr.org/2024/474).
- Nova (rejected, context): Kothapalli, Setty, Tzialla. [eprint 2021/370](https://eprint.iacr.org/2021/370).
- Packed sumcheck over small fields: [eprint 2025/719](https://eprint.iacr.org/2025/719).
- Neo / SuperNeo (future PQ direction): [eprint 2025/294](https://eprint.iacr.org/2025/294), [eprint 2026/242](https://eprint.iacr.org/2026/242).
- Orion (the PCS): Xie, Zhang, Song. [eprint 2022/1010](https://eprint.iacr.org/2022/1010).
- Expander local code:
  - `poly_commit/src/orion/utils.rs:193` (commitment type),
    `:210–247` (commit_encoded).
  - `poly_commit/src/orion/linear_code.rs:168–290` (Spielman encoder).
  - `poly_commit/src/orion/linear_code_tests.rs:26–74` (proof of
    encoder linearity).
  - `poly_commit/src/orion/verify.rs:52–131` (proximity test).
  - `poly_commit/src/orion/expander_api.rs:39` (`BatchOpening = ()`
    — Orion exposes no batch-opening API).
  - `poly_commit/src/batching.rs:22` (`prover_merge_points`, the
    curve-based multi-point→single-point primitive the design doc
    pointed at as the template).
- Awesome-folding index: [lurk-lab/awesome-folding](https://github.com/lurk-lab/awesome-folding).
- Parent design docs:
  - [docs/todo/m31-folding.md](../todo/m31-folding.md).
  - [docs/todo/cryptographic-archival.md](../todo/cryptographic-archival.md).
