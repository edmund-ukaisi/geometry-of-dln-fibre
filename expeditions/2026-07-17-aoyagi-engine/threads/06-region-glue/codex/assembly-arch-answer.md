## 1. RECOMMENDED ARCHITECTURE

Use a localized version of (a), followed by the scaling bridge. Do not route through `rlctAtOn`.

This architecture requires one strengthening currently absent from `ChartBridge`:

```lean
MeasurableSet l.srcBox ∧
∃ R > 0, l.srcBox ⊆ (paramsEquivFlat M) ⁻¹' cubeBox (flatDim M) R
```

Equivalently, require a measurable bounded refinement of each source that still covers a small target box.

Top-level chain:

```lean
routeMLayerBoxIntegral_nonpos_lt_top
    (hc : c' ≤ 0) :
    routeMLayerBoxIntegral M c' 1 < ⊤
```

```lean
terminal_ratios_of_hrat
    (hl : l ∈ leaves t) :
    (∀ k, c' < (l.divExp k : ℝ) / 2) ∧
    (0 < l.resRank → c' < (l.resRank : ℝ) / 2)
```

```lean
resolved_model_bounded_lintegral_lt_top
    (hsrc : MeasurableSet l.srcBox)
    (hbdd : ∃ R > 0, l.srcBox ⊆ flatCube M R)
    (hc : 0 < c')
    (hdiv : ∀ k, c' < (l.divExp k : ℝ) / 2)
    (hres : l.resRank = 0 ∨ c' < (l.resRank : ℝ) / 2) :
    ∫⁻ w in l.srcBox,
      ENNReal.ofReal
        ((∏ k, |u k| ^ (l.divExp k - 1)) *
          (((∏ k, (u k)^2) * residualBaseForm l w) ^ (-c'))) < ⊤
```

The source need not itself be a product. Enlarge it to the containing flat cube. A coordinate permutation separates:

```text
divisor coordinates × Morse coordinates × spectator coordinates.
```

Then Tonelli gives:

- one one-dimensional monomial integral per divisor;
- one radial integral in `resRank` variables;
- finite cube volume for spectators.

Next:

```lean
leaf_chart_image_lintegral_lt_top
    (hl : l ∈ leaves t)
    (hleaf : ... LeafPullback l ∧ LeafJacobian l ...)
    (hsrc : MeasurableSet l.srcBox)
    (hbdd : IsBounded l.srcBox)
    (hc : 0 < c')
    (hdiv ...) (hres ...) :
    ∫⁻ A in l.chartMap '' l.srcBox,
      ENNReal.ofReal ((frobSq (prod M A)) ^ (-c')) < ⊤
```

For this lemma, write `φ := ψ ∘ β`. Replace the source-null exceptional set `N` by a measurable null superset `N̄`. On `l.srcBox \ N̄`:

- `φ = l.chartMap`;
- `φ` is injective;
- the chain rule gives
  `Dφ w = Dψ (β w) ∘L Dβ w`;
- its determinant is bounded above by the stated Jacobian monomial.

Use Mathlib’s:

```lean
lintegral_image_eq_lintegral_abs_det_fderiv_mul
```

The discarded image is null by:

```lean
addHaar_image_eq_zero_of_differentiableOn_of_addHaar_eq_zero
```

Finally:

```lean
finite_chart_cover_lintegral_lt_top
    (hcover : B ⊆ ⋃ l ∈ leaves t, l.chartMap '' l.srcBox)
    (hleaf : ∀ l ∈ leaves t, ∫⁻ A in l.chartMap '' l.srcBox, g A < ⊤) :
    ∫⁻ A in B, g A < ⊤
```

This is `lintegral_mono_set`, repeated `lintegral_union_le`, and finiteness of a finite sum. Overlaps cause no problem; there is no need to choose which chart contains the origin.

For globalization:

```lean
exists_small_paramsBox_subset_open
    (hU : IsOpen U) (h0 : 0 ∈ U) :
    ∃ ε > 0, paramsBoxM M ε ⊆ U
```

and

```lean
routeMLayerBoxIntegral_lt_top_of_small_box
    (hε : 0 < ε)
    (hsmall :
      ∫⁻ A in paramsBoxM M ε,
        ENNReal.ofReal ((frobSq (prod M A)) ^ (-c')) < ⊤) :
    routeMLayerBoxIntegral M c' 1 < ⊤
```

The latter is the scaling bridge through `paramsEquivFlat`. Handle `L = 0` separately; for `L > 0`, `F 0 = 0`, hence the cover’s open `U` contains the origin.

Thus the recommendation is: finite image-cover integration near the origin, then homogeneous scaling. It avoids both the non-open chart-image problem and any compactness argument over the whole box.

## 2. THE ROLE OF EACH BANKED TOOL

- `rlctAtOn_boundedUnit_localHomeomorph`: unused, and not applicable to the current `LeafJacobian`. That lemma requires an open neighborhood, continuity, derivatives of both directions, determinant bounds for both directions, and a fixed basepoint. `LeafJacobian` supplies none of: openness of `β '' srcBox`, a derivative of `ψsymm`, or a fixed point. The area formula needs only the upper bound on `|det Dψ|`.

- Scaling bridge: the final local-to-global step. It transfers finiteness from `paramsBoxM M ε ⊆ U` to the unit box. It does not repair an uncontrolled source domain.

- Radial/monomial reads: the analytic core of `resolved_model_bounded_lintegral_lt_top`, after enlarging the bounded abstract source to a product cube.

- `rlctAtOn_ray_scaling_invariant` and `deepest_le_of_homogeneous_core`: unnecessary here. Pointwise RLCT does not follow merely because a point belongs to a chart image, since that image need not contain a neighborhood.

## 3. THE `c' ≤ 0` VS `c' > 0` SPLIT

For `c' ≤ 0`, put `q := -c' ≥ 0`. The function `F^q` is bounded on the compact parameter cube because `F` is continuous and nonnegative. The cube is measurable and has finite volume. Hence the lintegral is finite without `hbridge` or `hrat`.

For `c' > 0`, the negative-power domination uses the lower residual bound:

```text
residualCore ≥ lo · residualBaseForm,   lo > 0.
```

The terminal-exponent hypothesis supplies exactly:

```text
-1 < divExp k - 1 - 2c'
c' < resRank / 2
```

for the monomial and Morse reads.

## 4. THE BIGGEST RISK / MOST LIKELY TO WALL

The wall is `leaf_chart_image_lintegral_lt_top`. It is not derivable for an arbitrary `srcBox`.

Request either:

```lean
∀ l ∈ leaves t,
  MeasurableSet l.srcBox ∧
  ∃ R > 0, l.srcBox ⊆ flatCube M R
```

or the weaker local refinement:

```lean
∃ ε > 0, ∃ S : Leaf → Set (Params M),
  (∀ l, S l ⊆ l.srcBox ∧ MeasurableSet (S l) ∧ IsBounded (S l)) ∧
  paramsBoxM M ε ⊆ ⋃ l, l.chartMap '' S l
```

Nonempty interior is not needed. Measurability and bounded localization are.

Once supplied, the principal new analytic helper is the bounded-set resolved-model integral. The rest is area-formula and finite-cover plumbing.

## 5. IS THE STATEMENT EVEN TRUE / PROVABLE FROM THIS EXACT `ChartBridge`?

Not as an implication of the displayed `ChartBridge` data.

Boundedness is genuinely necessary, not merely a Lean convenience. A model obstruction exists for `F(y)=y₁²+y₂²`. For `a ≥ 3`, take sector charts

```text
φ₁(u,v) = (u, u^(a-1)v),
φ₂(u,v) = (u^(a-1)v, u)
```

on the unbounded sources

```text
0 < |u| < δ,   |v| ≤ |u|^(-(a-2)),
```

plus the null exceptional fibre `u=0`. Their images cover a neighborhood of the origin, and

```text
F(φᵢ(u,v)) = u² · (1 + u^(2a-4)v²),   1 ≤ residual ≤ 2,
|det Dφᵢ| = |u|^(a-1).
```

Thus the stated leaf conditions advertise `divExp = a`, allowing `c' < a/2`, while the actual radial integral diverges for `c' ≥ 1`. The missing source width contributes exactly the lost power.

This counterexample targets the generic `ChartBridge → finiteness` architecture, not necessarily the particular fully constructed `resolutionOf`, which has additional ledger constraints. The DLN conclusion may independently be true, but the current chart interface does not prove it. Strengthen the source-domain part before attempting `region_glue`.