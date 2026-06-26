# G3 (general-M) scoping memo — what generalizing the (2,2,2) RLCT cover requires

Seat: `fm-2` (formalisation), task #106. **SCOPING analysis, not building** — input for the operator's
G3 scope-decision at the active-scope milestone. Written having just built the (2,2,2) ≥-cover
(`rlctAtOn_myF222_eq : rlctAtOn myF222 0 = 3/2`, @`703db62`), so this maps what the *specific* build
taught us about the *general* obstruction.

## The target

The general-M headline already has its skeleton statement:

```text
resolution_charts (M : Fin (L + 1) → ℕ) :
  ∃ (ι : Type) (_ : Fintype ι) (d : ι → ℕ) (k h : (i:ι) → Fin (d i) → ℕ),
    rlctAtOn (fun A : Params M => dlnLoss M 0 A) (fun _ => 0) = ⨅ i, monomialThreshold (d i)(k i)(h i)
  := sorry        -- Skeleton.lean:1000
```

`aoyagi_learning_coefficient` (the project headline) reduces to this via `deepest_point_reduction`
(D1) + `product_reduction` (L2/S1). My `resolution_charts_case222` IS this theorem instantiated at
`M = ![2,2,2]` (depth `L+1 = 3`, all widths `2`, rank `r = 1`, deepest point `B = 0`). G3 = proving
`resolution_charts` for **general `M`** — arbitrary depth `L+1` and widths `M i`, and general rank
`r` (the deepest rank-`r` stratum, not just `r = 1`).

The geometric content is the cover (≥) + the leaf-threshold values; the analytic `≤`-bound is the
cited `monomial_rlct` (Aoyagi/Watanabe) and is already general (it is stated for arbitrary `(d,k,h)`).
So **G3 is a ≥-cover-generalization problem**, the same shape as the (2,2,2) ≥-mountain I just built.

---

## 1. WHAT GENERALIZES CLEANLY (already general, or general-by-construction)

These are network-free / `N`-generic and need no new (2,2,2)-specific work:

- **The recStep / g5_pivotNode cover engine.** `recStep {N} (active) (p) (hp) (L) (hL) (h)` and
  `univ_ae_cover {N} (active) (p) (hp)` are stated for **arbitrary `N` and arbitrary nonempty
  `active : Finset (Fin N)`**. The whole per-node geometry substrate — `pivotBlowupOn`,
  `pivotBlowupOnDeriv_det = (x p)^{|active|−1}`, `pivotBlowupOn_hasFDerivWithinAt`,
  `pivotBlowupOn_injOn`, `argmaxCellOn_cover`, `argmaxCellOn_aedisjoint`, `coordZero_null`,
  `chartDomOn_diff_measurableSet` (all in `S1G5Charts`) — is `{N}`-generic. A general-M cover is more
  recStep levels with larger `active` sets; the engine carries it unchanged. **Reusable as-is.**
- **The S1 transport substrate.** `rlctAtOn_ge_of_integral_lt`, `cover_integral_lt_top_iff`,
  `rlctAtOn_le_of_box_diverges`, the Params↔flat seam pattern (`paramsEquivFlat` / `measurePreserving`
  via `piCurry` + `arrowCongr'`), and the `Fin n → ℝ` host-space choice (the instance-wall lesson:
  build on `Fin N → ℝ`, transport to `Params M` at the gated seam) — all general. The (2,2,2) `e222`
  seam is the `M = ![2,2,2]` instance of the general `paramsEquivFlat`.
- **The box / Tonelli / monomial toolkit.** `cube8_tonelli_peel`, `boxT_coord_rpow_lt_top`,
  `boxT_peel_spectator`, `boxT_pivot_peel`, `abs_rpow_lintegral_Icc_lt_top`,
  `monomialIntegrand_integrable_of_lt`, `integrableOn_monomial_mul_unit_iff` — these are stated for
  general `Fin n`/`d`/`(k,h)`; the (2,2,2) build just instantiates them. `sumSq4_box_lt_top` is
  `n = 4`-specific in its statement but its method (`PiLp.volume_preserving_toLp` +
  `radial_ball_iff` + spectator-peel) generalizes to any `Σ^m` smooth block trivially (radial_ball_iff
  is general-`m`).
- **The δ-branch smooth-block route (the METHOD).** "A vanishing residual that is a smooth sum of
  squares after a det-`1` shear has RLCT `= (#squares)/2`, finite below it via the EuclideanSpace
  radial bound" — the method is dimension-generic. (Whether the *general* δ-residuals ARE smooth
  blocks is a §3 unknown.)
- **A1 (the arithmetic core) is ALREADY general-M.** `lambdaCore`, `cleanCore`, `printedCore`,
  `balancedSplit`, the BG/forwardMax achiever (`lambdaCore_eq_clean`, #84/#92/#101/#102) are stated
  for general `M : Fin (L+1) → ℕ`. The `⨅ monomialThreshold = lambdaCore M` value-match is A1's job and
  is being closed generally. **So the VALUE side of G3 is already general; G3 is purely the COVER
  (geometry) side.**
- **D1 / L2 / S1 (the reductions around the cover) are stated general-M** (`deepest_point_reduction`,
  `product_reduction` over `Fin (L+1)`). They consume `resolution_charts` as a black box.

**Net:** the *engine, substrate, toolkit, arithmetic, and reductions* are general. G3's new work is
concentrated in producing the general-M **cover instance** that feeds `resolution_charts`.

---

## 2. WHAT IS (2,2,2)-SPECIFIC AND NEEDS NEW WORK

These are the pieces I hand-built for `M = ![2,2,2]`, `r = 1`; each needs a general-M analogue:

- **The resolution tree (the chart sequence).** (2,2,2) used a *specific* 3-deep tree: step-1 A-block
  blow-up (`pivotBlowupOn {0,1,2,3} 0`, |det|=x0³) → **Lemma-2** det-`±1` splice (the regular change
  resolving the residual `Q = ‖Â·B‖²` to the normal form `resolvedForm`) → step-2 (`{1,2,3}`,
  |det|=z1²) → step-3 (block blow-up, |det|=u³). For general `M` the tree depth, the blow-up active
  sets, and — critically — **the Lemma-2 analogue** (the regular change of variables resolving the
  multi-layer residual to a normal form) all change. **The Lemma-2 generalization is the hardest
  single unknown** (see §3): for (2,2,2) it was one explicit det-`±1` polynomial map I cross-validated
  slot-for-slot; for general `M` it is the iterated-L1 / regular-sequence resolution of `‖A_L ⋯ A_1‖²`,
  which the paper handles via the L1-elimination tower but which has no closed `lemma2Fwd`-style
  one-shot form yet.
- **The leaf enumeration.** (2,2,2) had exactly 24 leaves (8 unit `d=2 (1,1)(3,2)` + 16 block
  `d=3 (1,1,1)(3,2,3)`), all `monomialThreshold = 3/2`. General-M leaf count is a function of the tree
  (the product of the per-node `|active|` over the recursion paths) and is NOT a fixed number; the
  per-leaf `(d,k,h)` exponents vary with the layer widths. The enumeration is implicit in the recStep
  recursion (not a flat `Fin 24`), which is good — but proving "every leaf threshold `≥ lambdaCore M`"
  generally (vs the (2,2,2) "all `= 3/2`") needs the general per-leaf `(d,k,h)` and a general
  `monomialThreshold_ge` argument (the spectator/binding-axis split generalizes; the *values* don't
  collapse to a single `3/2`).
- **The conjugation symmetries σ1/σ2/σ3.** (2,2,2) closed the 3 non-pivot A-block summands by
  coordinate-conjugation to the proven pivot-0 summand, using the genuine Frobenius symmetries of
  `‖A·B‖²` (A-row swap, A-col+B-row swap, composite). For general `M` the per-layer block is `M i × M
  i'` matrices, and the relevant symmetry group is the *product of row/column permutations across all
  layers* fixing `‖A_L ⋯ A_1‖²` — much larger than `S₂`-style swaps. The conjugation *method*
  (reduce non-pivot summands to the pivot one via measure-preserving coordinate perms) generalizes IF
  the symmetry group acts transitively on the pivot choices per layer; whether it does for general
  widths is a §3 unknown. **Alternatively** the 4-cheap-rings route (re-derive each pivot summand)
  generalizes but scales with the per-node `|active|` (= the layer width², a lot for wide layers).
- **The per-node "unit vs block" classification + the step-3 block resolution.** (2,2,2): E/F0 pivots
  → unit leaves (residual `≥ 1`), δ pivot → block (needs the further smooth-4D treatment). For general
  `M` the classification of which pivot cells are units vs need deeper resolution, and the deeper
  resolution itself, depend on the residual structure at each layer.

---

## 3. RISKS / UNKNOWNS — where the (2,2,2) tricks might break

Ranked by how load-bearing + how uncertain:

1. **(HIGHEST) The Lemma-2 / regular-change generalization.** (2,2,2)'s `lemma2Fwd` was a single
   explicit det-`±1` map resolving `‖Â·B‖²` to `resolvedForm`. The general multi-layer residual
   `‖A_L ⋯ A_1‖²` has no known one-shot regular change; the paper resolves it via the **iterated
   L1-elimination tower** (peel one layer at a time, each an L1 block-elimination). Formalizing that
   tower as a measure-preserving / det-controlled chart sequence — and proving the residual at each
   level is a smooth block (so the δ-branch method applies) — is the **core G3 risk**. If the iterated
   tower doesn't yield clean det-controlled charts at general width, the whole recStep-cover approach
   may need re-architecting. **This is the make-or-break unknown; scope a pen-and-paper adjudication of
   the general regular-change BEFORE committing G3.**
2. **(HIGH) Do the per-leaf thresholds stay computable / `≥ lambdaCore M`?** (2,2,2) had the luxury
   of all-leaves-`= 3/2`. General-M leaves have varying `(d,k,h)`; proving `⨅ = lambdaCore M` requires
   each leaf's `monomialThreshold` to be computable AND the `⨅` to match A1's `lambdaCore`. A1 gives
   the *value*; the cover must produce leaves whose `⨅` hits it. A mismatch (a leaf below `lambdaCore`)
   would be a soundness break OR signal the tree is wrong. The codim-ordering argument (deeper strata
   have strictly larger ratios) generalizes in principle but needs the general regular-sequence
   structure to confirm.
3. **(MEDIUM) Conjugation-symmetry transitivity.** If the per-layer symmetry group does NOT act
   transitively on pivot choices, the conjugation shortcut fails and every pivot summand needs its own
   chain (4-cheap-rings), scaling as Σ(layer widths²). For wide layers this is a large but mechanical
   LoC cost, not a soundness risk — degrades effort, not correctness.
4. **(MEDIUM) General rank `r > 1`.** (2,2,2) was `r = 1` (deepest stratum `B = 0`). General `r`
   changes the deepest point and the residual's vanishing structure (the regular part shifts by
   `[−r²+r(H¹+Hᴸ⁺¹)]/2` per the Skeleton). D1 handles the regular-part shift; the cover's singular core
   at general `r` is a §1-engine application but the residual geometry differs.
5. **(LOW) Combinatorial blow-up of the leaf count.** General-M trees have exponentially many leaves
   in depth × width. recStep handles this structurally (leaves implicit, no `Fin (huge)` enumeration),
   so it's a non-issue for the proof *structure*; it only matters if any step needs a per-leaf
   case-split (the spectator/binding `monomialThreshold_ge` is uniform, so it shouldn't).

---

## 4. ROUGH EFFORT (line-counts / sub-tasks, no wall-clock)

Conditional on risk #1 resolving favorably (the iterated regular-change yields det-controlled charts):

- **Pen-and-paper pre-work (gating, do FIRST):** adjudicate the general regular-change / iterated-L1
  tower as a measure-preserving chart sequence + confirm general residuals are smooth blocks. This is
  a `pen-and-paper` (scout) certificate, ~the depth of the (2,2,2) Lemma-2 cross-validation but for
  general width — **the gate**; if it walls, G3 is a re-architecture, not an extension.
- **The general cover (the recStep instantiation):** the engine is reusable, so this is "instantiate
  recStep at general active-sets + the general regular-change splice + general per-leaf threshold."
  Comparable in shape to my (2,2,2) `Case222CoverGETail` (~1000 LoC) but with the tree parametrized
  over `M` — likely **larger** (the per-layer splice + the general unit/block classification), call it
  a multiple of the (2,2,2) cover, dominated by the regular-change tower.
- **The conjugation/symmetry layer:** if transitive, ~the (2,2,2) conjugation block (σ + `aPivotSummand_conj`,
  ~150 LoC) generalized to the layer symmetry group; if not, the 4-cheap-rings scaling (Σ widths²).
- **A1 value-match wiring:** A1 is already general (#84/#92), so this is the `⨅ = lambdaCore` connector
  — small, IF the leaves' thresholds compute to `lambdaCore`.

**Signal for the operator:** G3 is NOT a mechanical scale-up of (2,2,2). The engine/substrate/arithmetic
are general (genuine down-payment value already banked), but the **regular-change generalization (risk
#1)** is a real research question, not a formalization grind. Recommend: **if G3 is greenlit, gate it on
a pen-and-paper adjudication of the general iterated-regular-change FIRST** (the same discipline that
de-risked the (2,2,2) Lemma-2 + the conjugation). If that adjudication says "iterated-L1 yields clean
det-controlled charts + smooth-block residuals," G3 is a large-but-tractable extension; if it walls,
G3 needs a different resolution architecture (and the (2,2,2) result stands alone as the validated
instance). The weighted-product-split (flagged earlier) is the right reusable down-payment IF the
operator scopes general-M — it's the general-width analogue of the Tonelli pivot-peel.

## 5. The clean down-payment already banked

Independent of the G3 decision, the (2,2,2) build banked reusable general-M infrastructure: the
recStep/g5_pivotNode cover engine, the box/Tonelli/monomial toolkit, the EuclideanSpace smooth-block
method, the conjugation-symmetry *technique*, and the host-space/seam pattern. None of these is
(2,2,2)-specific; all are network-free `{N}`-generic. So even a "G3 deferred" decision leaves the
engine in place for whenever the boundary is scoped.
