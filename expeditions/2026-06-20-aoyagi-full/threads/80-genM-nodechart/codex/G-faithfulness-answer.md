Your finding is correct. The faithful object is the radial **arrow**, not a diagonal scaled-column Jacobian and not the Jacobian of a “radial = 1” surrogate.

1. **Do not make `Prad⁻¹ * J` the main Lean spine.** It is valid as a punctured-locus diagnostic when `u p ≠ 0`, but it introduces division, a zero case, and a left/right multiplication trap. In Mathlib, `LinearMap.toMatrix'_comp` gives
   `toMatrix' (B.comp R) = toMatrix' B * toMatrix' R`,
   so if the map-level shape is `φ = B ∘ R`, the radial matrix is the **right** factor. `det (Prad⁻¹ * J)` may still have the right determinant, but it is not necessarily the boundary matrix with the right block structure.

2. **Use map-level or CLM-level factorization instead.** The clean spine is:
   ```lean
   φ = B ∘ pivotBlowupOn active p
   Dφ u = DB (pivotBlowupOn active p u) ∘L pivotBlowupOnDeriv active p u
   ```
   then:
   ```lean
   rw [LinearMap.det_comp, pivotBlowupOnDeriv_det active p hp]
   ```
   and take absolute values. This is division-free and works at `u p = 0` automatically, including the `minAdm = 1` edge where the “both sides are zero” argument would be false.

3. **Do not define `ψ := pivotBlowupOn.symm ∘ φ` globally.** `pivotBlowupOn` is not a global equivalence; it is only injective off `{u p = 0}`, and its inverse divides by `u p`. On the punctured locus it is a useful rational check, but it is the wrong primary Lean object. Define the boundary factor directly from the chart construction, or prove the existing staircase/factor-fold conjugacy.

4. **Yes, the pivot-column entries are exactly consistent with the pinned radial model.** In [S1G5Charts.lean](/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/agent-a9bb11c22680d93d4/lean/DLNFibre/DLN/RLCT/Foundations/S1G5Charts.lean:390), `pivotBlowupOnDeriv` sends active non-pivot rows to
   ```lean
   x p • proj i + x i • proj p
   ```
   so the pivot column contains the ratio/active values `x i`. That is the arrow. The determinant theorem [pivotBlowupOnDeriv_det](/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/agent-a9bb11c22680d93d4/lean/DLNFibre/DLN/RLCT/Foundations/S1G5Charts.lean:509) proves its det is `(x p)^(active.card - 1)` despite that pivot column.

The division-free Lean target should be either:

```lean
|det (fderiv ℝ φ u)| =
  |u p| ^ (minAdm M - 1) * engineProduct u
```

from a factor-fold equality `composeFold fs = φ`, using [RouteMChartFactorFold.lean](/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/agent-a9bb11c22680d93d4/lean/DLNFibre/DLN/RLCT/Validate/RouteMChartFactorFold.lean:31), `radialFactor_abs_det`, `schurChartFactor_abs_det`, `lduChartFactor_abs_det`, etc.; or the already-shaped staircase theorem [interiorDet_phiFlatLiveR1_of_stairConj](/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/agent-a9bb11c22680d93d4/lean/DLNFibre/DLN/RLCT/Validate/RouteMInteriorDetReal.lean:35), whose layer `0` is the radial arrow and layers `s+1` are the boundary engine blocks.

So: refute the scaled-columns `G`; keep `RouteMColumnFactor` only as a lemma with its explicit hypothesis; prove the real chart’s derivative factors through `pivotBlowupOnDeriv` plus boundary blocks. The faithful spine is chain rule plus `LinearMap.det_comp`, not `det_mul_row` and not a global deblow-up inverse.