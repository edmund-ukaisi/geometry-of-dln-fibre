# Route M (monomial) `resolution_charts` — gap-analysis: BANKED vs NEEDED (crux2, 2026-06-22, #137)

Route-before-lines for the general per-node mechanism, after the squeeze lane was confirmed off-path
(g134: `dlnLoss M 0 ∘ pivotBlowupOn = x_p²·Q`, the monomial route carries the `x_p²` exceptional weight
the squeeze drops). The LIVE per-node mechanism is the MONOMIAL route. This maps what is already banked
against what the general `resolution_charts` needs — to inform pp2's #26 design and de-risk the #27
(fm3 + crux2) formalisation.

## The target (g133 `IsResolutionAtlas` obligation)

`resolution_charts` (`Skeleton.lean:1017`, currently `sorry`) concludes
`rlctAtOn (dlnLoss M 0) (deepest) = ⨅ᵢ monomialThreshold (d i)(k i)(h i)`, and the value
`⨅ = ofReal (lambdaCore M)` follows from an `IsResolutionAtlas` witness. The atlas (g133 card) is the
chart-tree data `(ι : paths, d : ι→ℕ, k h : (i)→Fin(d i)→ℕ, stratum : ι→(Fin L→ℕ))` with 4 conjuncts:
- **(A) `stratum_admissible`** — every path's binding center ∈ `Adm M`. Structural.
- **(S) `stratum_surjective`** — every admissible stratum reached by a path. THE residual real work
  (the pivot branches enumerate the admissible rank cone; proof carrier `Core.RankPattern`/Gabriel).
- **(K) `mult_one`** — `k_E = 1` on every exceptional divisor (multilinearity, #132).
- **(C) `threshold_eq`** — path `monomialThreshold = ½·Mval(stratum)` (#131 Schur codim + `axisRatio_regularSeq`).
⟹ `resolution_value_of_atlas`: `⨅ monomialThreshold = ofReal (lambdaCore M)`. **SURJECTION not bijection**
(paths ↠ Adm M; (2,2,2) had 24 leaves for 3 strata — only S matters for the `⨅`).

## BANKED (reusable, green)

| Asset | Where | What it gives the general route |
|---|---|---|
| `(2,2,2)` monomial tree | `Case222Resolution.lean` | The CONCRETE template: `step1A`/`step2E`/`step2D`/`step3`, each `F = pivot²·(unit ≥ 1)` → a monomial leaf. The shape to generalize. |
| `step1A_eq_pivotBlowupOn` | `Case222Resolution:169` | The step chart IS `pivotBlowupOn` — the recursion uses the banked atlas chart. |
| `monomialThreshold` / `monomialOrder` / `axisRatio` | `Skeleton:88–101` | The per-leaf threshold `⨅_j axisRatio(h_j)(k_j)`; the value each path contributes. |
| `monomialThreshold_le_regularSeq`, `_le_axis`, `_ge_of_mult` | `Skeleton:134–149` | The `≤`/`≥` bounds on a leaf threshold (feed (C) `threshold_eq` + the cover `≤`/`≥`). |
| `axisRatio_regularSeq` (`(c−1,1) ↦ c/2`) | `Lambda` | The regular-sequence ratio = `½·codim` — the heart of (C). |
| `pivotBlowupOn` / `…Deriv` / `…_hasFDerivWithinAt` / `…_injOn` / `argmaxCellOn` / `argmaxCellOn_cover` / `_aedisjoint` | `S1G5Charts.lean` (`fm/r1-cover`) | The blow-up chart + its Jacobian (`pivotBlowupOnDeriv`) + the a.e. cover of `{∃ active ≠ 0}` by argmax cells. The COVER-GLUE atom. |
| `g5_pivotNode` | `S1G5Charts:614` | The single packaged measure c-o-v step: `∫⁻_U g = Σ_p ∫⁻ |det φ_p'|·(g∘φ_p)` over the next blow-up's active cells. The RECURSION DRIVER. |
| `Adm M`, `Mval M T`, `lambdaCore M`, `Adm_nonempty`, `Mval_nonneg` | `Lambda.lean` | The VALUE side: admissible strata, codim, `lambdaCore = ½(Adm M).inf' Mval`. A1's green output — the RHS of `resolution_value_of_atlas`. |
| `cover_integral_lt_top_iff` | (cover) | All-leaves-finite-below-`⨅` ⟺ `U`-integral finite (the `≤` direction packaging). |

## NEEDED (the general construction — unbuilt)

1. **The general blow-up TREE** (the recursion generalizing step1A→step2→step3 to arbitrary `M`/depth).
   At a node, `F = ‖∏C‖²` over `{∏C=0}`; blow up the active rank-stratum center via `pivotBlowupOn`,
   factor `F = x_p^{2}·(residual)` (the homogeneity factorisation, the `myF222_step1A` analogue), recurse
   on the residual. Terminates at unit leaves (`F = monomial·(unit ≥ 1)`). **fm3's geometry** (the producer).
   — Open: the recursion's well-founded measure (ΣM drop, banked as `ChainDimSplit`/`measure_drops`
     pattern), the per-node center choice, the `Fin`-indexing of the growing coordinate tree.
2. **The chart family `(ι, d, k, h)`** read off the tree: `ι` = root-to-leaf paths, `d i` = leaf chart
   dim, `k i`/`h i` = the leaf's monomial exponents (`k` from F-vanishing = 1 by (K); `h` from the
   accumulated Jacobian `∏ x_p^{...}` per `pivotBlowupOnDeriv_det`). **fm3** (read from its construction).
3. **The cover-glue**: assemble the per-node `g5_pivotNode` steps into the whole-tree
   `∫⁻_U F^{−c'} = Σ_paths ∫⁻_leaf`, the `≤`/`≥` both ways (`rlctAtOn` = the leaf `⨅`). Generalizes
   `Case222Block`'s route-R recursion (`univ_ae_cover` + `recStep`). **Shared / fm3-leaning** (it's cover infra).
4. **C1–C4 node handling** (pp3 g136 taxonomy): the per-node-type cases the general recursion must cover
   (the node taxonomy + the (S-min) selection). **pp2/pp3 design → fm3 construction.**
5. **`resolution_value_of_atlas`** (the `⨅`-rearrangement: atlas ⟹ `⨅ = ofReal lambdaCore`). PURE VALUE
   ALGEBRA, gate-independent of the construction. = cover's task #21 (`IsResolutionAtlas` scaffold +
   this lemma). **crux2's natural half IF deconflicted with cover** — the 4-step assembly is spelled in
   g133 (`threshold_eq` → pull out ½ → image=Adm via A+S → `lambdaCore` def). Clean, ~30–50 lines.

## DIVISION — SET by controller (2026-06-22, supersedes the proposal below)

The proposal below mis-attributed crux2's half as item 5 (the value-rearrangement). CORRECTED, final:
- **fm3 = items 1, 2, 4** — the blow-up tree + the `(ι,d,k,h,stratum)` chart family + C1–C4 node
  handling; discharges (A)/(K)/(C) from the geometry.
- **crux2 = item 3** — the rlct-cover BRIDGE = `resolution_charts` proper: `rlctAtOn(core) 0 =
  ⨅ monomialThreshold` given fm3's cover + per-chart thresholds (the `Case222Cover`/`Case222CoverGE`
  generalization — the ≤/≥ leaf-integrability + the `g5_pivotNode` cover-integral assembly). Plays to the
  RLCT-measure strength; NOT item 5.
- **cover = item 5** — `resolution_value_of_atlas` (`⨅ monomialThreshold = ofReal(lambdaCore M)`); = #21.
- **(S)/(S-min)** — a formaliser per pp2's design (likely folds into fm3's tree as the achiever path).
Headline: `resolution_charts` [crux2 item 3 ∘ fm3 geometry] ▸ `resolution_value_of_atlas` [cover]
⟹ `rlctAtOn(core) = lambdaCore`. Interface pinned by pp2's #26.

## Proposed division (#27, mirrors the producer/consumer decorrelation that caught g134)

- **fm3 = blow-up-tree / GEOMETRY producer:** items 1–3 + 4's construction. Builds the recursive
  `pivotBlowupOn` tree, produces `(ι,d,k,h,stratum)`, discharges (A)/(K)/(C) from the geometry (read off
  the chart Jacobians + the Schur codim). The interface `(ι,d,k,h)` spec comes from pp2's #26 design.
- **crux2 = rlct-assembly / THRESHOLD-VALUE consumer:** item 5 (`resolution_value_of_atlas`) + the
  `lambdaCore`/`Mval`/`Adm` value-side wiring + the `monomialThreshold` leaf-value lemmas. Gate-independent
  of (S) and of fm3's geometry — consumes the atlas as a hypothesis.
- **(S) surjectivity** (item 4's hard claim) = pp2 #20 (witness) / pp3 #17 (obstruction), proof carrier
  `Core.RankPattern`. Not crux2's unless assigned.

This keeps the consumer (value algebra) decorrelated from the producer (geometry) — the same split that
caught the squeeze's symbolic-vs-coordinate confound.

## DECONFLICTION needed (flagged to controller)
`resolution_value_of_atlas` + the `IsResolutionAtlas` scaffold are task #21 (cover). Not yet on origin.
Either crux2 takes the value-consequence as its #27 half and #21 folds in, or cover keeps #21 and crux2
takes a different #27 slice. Resolve before either builds, to avoid two parallel `resolution_value_of_atlas`.

## Scope note (CLAUDE.md precision)
`resolution_charts` / the atlas is **core-only** (`rlctAtOn(dlnLoss M 0) 0`, `M` = reduced widths). The
regular `[−r²+r(H⁰+Hᴸ)]/2` shift is L2/Fubini (`product_reduction`), assembled downstream by
`deepest_point_reduction`. `IsResolutionAtlas` carries no `nReg` — purely the singular-core
`⨅ = ofReal(lambdaCore M)`. Do not fold the regular shift in here.
