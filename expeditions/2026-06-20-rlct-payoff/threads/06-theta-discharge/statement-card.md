# Thread 06 — θ-count discharge (the two gating bricks) — statement card

Module: `lean/DLNFibre/Core/CCodimCornerMono.lean` (~440 LoC, sorry-free, axiom-clean).
Build: whole `DLNFibre` library green; `scripts/sorries` = 0.
Axioms (`#print axioms`): `[propext, Classical.choice, Quot.sound]`.

## Goal

Discharge the explicit hypotheses `hLowerBound` and `hRecover` of thread-05's gated headline
`Core.ThetaComponentCount.numTop_eq_ncard_topComponents_of`, making the θ-count headline
`θ = numTop d r = #{top-dimensional irreducible components of Σ̄^r}` UNCONDITIONAL.

## Status — LANDED: both bricks REDUCED to one combinatorial inequality

The two opaque geometric hypotheses of thread-05 are reduced to a **single, clean combinatorial
statement**: the dimension-monotonicity of `cCodim · 0`. The headline
`numTop_eq_ncard_topComponents_of_dimMono` is proved given that monotonicity. What remains for the
fully-unconditional headline is to prove the dimension-monotonicity itself (the shortest-interval
split, fully scoped below — NOT sorry-patched).

### LANDED unconditionally (the bedrock)

- **Brick 2 fully — the Gabriel→Kostant bridge.** Every tuple `M'` lies in the orbit closure of the
  realizer of a Kostant partition `gabrielPartition d M' ∈ kostantPartitions d ((mult d M').rank)`,
  with the SAME orbit rank locus (`orbitRankLocus_realizerD_gabrielPartition`). The
  `Core.OrbitKostant` Gabriel normal-form array `kostantArrayOfRank (rankFn d M')` (a `CMPlus d`
  array) recast into the `CTheta` `Fin × Fin → ℕ` / `extendℤ` encoding (`finArrayOfSupp`,
  `extendℤ_finArrayOfSupp`, `finArrayOfSupp_mem_kostantPartitions`, `gabrielPartition_corner`,
  `rankPattern_realizerD_gabrielPartition`). `[Field k]` / `[Nontrivial k]`.
- **Corner-`0` nonemptiness** (`diagPart`, `kostantPartitions_zero_nonempty`): the all-singletons
  partition is Kostant of corner `0` for `N ≥ 1` — `kostantPartitions e 0` is unconditionally nonempty.
- **Corner-monotonicity reductions** (from dimension-monotonicity, via the LANDED rank-shift):
  - `cCodim_corner_anti_of` — weak `cCodim d r ≤ cCodim d s` (`s ≤ r`) from weak dimension-mono.
  - `cCodim_corner_strict_of` — strict `cCodim d r < cCodim d s` (`s < r`) from strict all-vertex
    dimension-mono. (`corner_le_dim_of_mem`, `dminus_anti` supporting.)
- **The two discharges**, given the dimension-monotonicities as hypotheses:
  - `cCodim_le_codimRepCanonical_of` ⟹ `hLowerBound` (weak mono): every corner-`≤ r` orbit closure
    has codim `≥ cCodim d r`. Via the Gabriel bridge + `Finset.inf'_le` + corner-anti.
  - `exists_kostantPartition_partitionIdeal_eq_of` ⟹ `hRecover` (strict mono): every top-dimensional
    component is the orbit ideal of *some corner-`r`* Kostant partition. Via G3
    (`minimalPrimes_sigmaIdeal_eq`) + the Gabriel bridge + strict corner-monotonicity forcing corner
    `= r` on a min-codim component.
- **The reduced headline** `numTop_eq_ncard_topComponents_of_dimMono` (`[IsAlgClosed k] [CharZero k]`):
  given the weak (`hMono`) and strict (`hMonoStrict`) dimension-monotonicities of `cCodim · 0`,
  `numTop d r hr = (topComponents d r hr).ncard`. Axiom-clean.

### The single remaining gap (the precise, fully-scoped combinatorial inequality)

> **`cCodim_zero_mono` (weak)**: `e ≤ e'` pointwise ⟹ `cCodim e 0 ≤ cCodim e' 0`.
> **`cCodim_zero_strict` (strict)**: `e < e'` at *every* vertex ⟹ `cCodim e 0 < cCodim e' 0`.

These are stated as the explicit hypotheses `hMono` / `hMonoStrict` of the reduced headline. They are
NOT a restatement of the conclusion — they are pure `CTheta`-level combinatorics about the minimum of
the `codimForm` quadratic form over corner-`0` Kostant families, decoupled from the geometry.

**Why these two, and not strict corner-monotonicity directly.** Via the rank-shift
`cCodim d t = cCodim (d−t) 0`, weak corner-monotonicity needs weak dimension-mono and strict
corner-monotonicity needs strict *all-vertex* dimension-mono (`d−r < d−s` at every vertex when
`r > s`). NOTE: strict *single-vertex* dimension-mono is FALSE (e.g. `cCodim [1,1,0] 0 = cCodim
[1,2,0] 0 = 0`); only the all-vertex strict version holds — verified numerically.

**The construction (the (★) certificate, machine-numerically verified).** By `Finset.le_inf'_iff`,
`cCodim e 0 ≤ cCodim e' 0` reduces to: every corner-`0` partition `m'` of `e'` dominates (in
`codimForm`) a corner-`0` partition of `e`. The witness is the **interval-shortening restriction**:
at a vertex `k` over-covered by 1, split the **SHORTEST** interval `[i,j] ∋ k` with positive
multiplicity into `[i,k−1]` and `[k+1,j]` (`m → m − δ_{[i,j]} + δ_{[i,k−1]} + δ_{[k+1,j]}`); iterate
to reduce `e'` down to `e`. Verified: 199/199 cases the shortest-split is a valid corner-`0`
partition of the decremented vector and never increases `codimForm` (and strictly decreases for the
strict all-vertex case, 80/80).

**Why "shortest".** `codimForm` is the type-A `Ext`-pairing form: reindexed,
`codimForm N m̄ = ∑_{A=[a,b],B=[c,e]: a<c≤b+1, b<e} m̄(A) m̄(B)`. The split's `codimForm`-delta is
`∑_B coeff(B) m̄(B)` where the strictly-positive-coefficient `B` are exactly the *shorter* intervals
covering `k`; choosing `I` shortest makes those multiplicities `0`, so the delta is `≤ 0`. (Splitting
a NON-shortest interval can INCREASE `codimForm` — verified — so the choice is load-bearing.)

**Estimate for the remaining lemma.** ~120–160 LoC: the interval-Ext reindex of `codimForm` (the
bilinear form `codimBil` and its additivity are easy — probed green), the 3-point split delta-sign
analysis (the load-bearing "shortest ⟹ shorter-covering absent" step), the well-founded recursion on
`∑(e'−e)`, and the strict variant. Codex was UNAVAILABLE for decorrelation (the env's `codex exec`
produced no output / timed out env-wide); the decorrelation here is the exhaustive numerical
enumeration (zero failures across thousands of cases) — reviewer requested for the fidelity audit.

## Non-vacuity (combinatorial side, LANDED on `dev`)

`(2,2,2)`: `r=0 → cCodim=3, numTop=1`; `r=1 → cCodim=1, numTop=2` (`Core.CTheta`). `(2,3,2)`:
`r=0 → cCodim=4, numTop=2` (paper-worked; synthesis line 76). [Re the brief's "(2,3,2)/r=1 → 2":
recomputed, `(2,3,2) r=1` is `cCodim=1, numTop=1`; the `θ=2` (2,3,2) instance is at `r=0`
(zero-product), matching synthesis line 76. Flagged for the controller.]

## Status

sorry-free + axiom-clean (`[propext, Classical.choice, Quot.sound]`); whole library green. The two
geometric bricks are reduced to ONE combinatorial inequality (strict improvement over thread-05's two
opaque geometric hypotheses). Gap honestly named (the dimension-monotonicity of `cCodim · 0`), fully
scoped with construction + numerics, NOT sorry-patched.

**Reviewer fidelity AUDIT: PASS-with-notes** (2026-06-21). No soundness break, no fidelity mismatch
in any Lean statement, no smuggling (the reduction genuinely proves `hLowerBound`/`hRecover` from the
two combinatorial monotonicities; `hRecover`'s "corner = r" is genuinely derived from strict
corner-monotonicity, not restated). The reviewer independently re-verified all numerics (weak mono
0 fails, strict all-vertex 0 fails, single-vertex strict FALSE, and the (2,3,2)/r=0→θ=2 correction)
and its Codex consult independently confirmed the gap is real. ONE note applied: the module docstring
said the headline "becomes unconditional" — corrected to "reduced to the combinatorial
dimension-monotonicity" (the reduced headline still carries `hMono`/`hMonoStrict` as hypotheses).
