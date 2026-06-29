import DLNFibre.DLN.RLCT.Validate.RouteMChartIdxEquiv

/-!
# `RouteMGradingObstruction` — the partition mismatch blocking the single-grading block-triangular route

The decisive obstruction surfaced when commissioning the COARSE-route unconditional interior-det
headline. `Matrix.BlockTriangular` (Mathlib v4.29) consumes a SINGLE grading on rows and columns; for
the interior chart's frame Jacobian `D(T_M)` (an endomorphism of `Fin N → ℝ`) to be block-triangular
under one grading `g`, the OUTPUT-coordinate layering and the INPUT-coordinate layering must agree as
the same function `g : Fin N → ℕ`.

* The INPUT coordinates are graded by `bLayer` = the `chartIdxEquiv` boundary index: layer `s` carries
  `schurDim s + liftDim s` coordinates (the Schur `K/X/N/E` + lift `W` of boundary `s`).
* The OUTPUT coordinates are graded by the `paramsEquivFlat` / `FlatIdx` layer (the chart output is
  `paramsEquivFlat (chartParamsGen …)`, and `chartParamsGen ⟨s⟩ = Agen s` is flattened into FlatIdx
  layer `s`): layer `s` carries `M_s · M_{s+1}` coordinates.

A single grading needs a bijection `e : Fin N ≃ FlatIdx` with `FlatIdx-layer ∘ e.symm = bLayer`, which
needs the two per-boundary counts to AGREE: `schurDim s + liftDim s = M_s · M_{s+1}` for every `s`.
**They do not.** Only the TOTALS agree (`∑ = flatDim`, `chartDim_eq_flatDim`) — the lift `W_s` of boundary
`s` (size `(M_{s+1}−t_{s+1})·M_{s+2}`) is counted at INPUT-boundary `s` but its weight lands in a
DIFFERENT output layer. So no layer-aligned bijection exists, even at the coarse boundary level.

This module banks the concrete witness at `(2,2,2)`: the FlatIdx layer counts are `(4, 4)` while the
ChartIdx boundary counts are `(6, 2)` — same total `8`, different partitions. This is the hard evidence
that the single-grading `BlockTriangular` route on the REAL frame is blocked (the obstruction is
mathematical, not a Lean-cast artifact); the headline needs a rectangular/staircase factorization (the
`Agen s` output block reads input boundaries `≤ s` but the blocks are not square under one grading), not
a square `BlockTriangular` under `bLayer` or the FlatIdx layer.

Axiom-clean `[propext, Classical.choice, Quot.sound]` (ℕ arithmetic; `decide`).
-/

namespace DLNFibre.DLN.RLCT

/-- The `(2,2,2)` widths `M = (2,2,2)` and descent `t = (2,1,1)` (`t222`-shaped), as raw `ℕ` functions
for the count comparison. -/
def Mobs : Fin 3 → ℕ := ![2, 2, 2]
/-- The `(2,2,2)` descent path `t = (2,1,1)` as a raw `ℕ → ℕ`. -/
def tobs : ℕ → ℕ := fun k => [2, 1, 1].getD k 1

/-- **The FlatIdx layer-`s` count is `M_s · M_{s+1}`; the ChartIdx boundary-`s` count is
`schurDim s + liftDim s`. At `(2,2,2)` these partitions DIFFER**: FlatIdx layers `(4, 4)` vs ChartIdx
boundaries `(6, 2)`. The decisive witness that no layer-aligned bijection `Fin N ≃ FlatIdx` exists, so
the single-grading `Matrix.BlockTriangular` route on the real interior frame is blocked — the headline
needs a non-square (staircase) factorization, not a square block-triangular collapse under one grading. -/
theorem flatLayer_ne_chartBoundary_222 :
    (Mobs 0 * Mobs 1, Mobs 1 * Mobs 2) = (4, 4) ∧
    (schurDim Mobs tobs 0 + liftDim Mobs tobs 0, schurDim Mobs tobs 1 + liftDim Mobs tobs 1) = (6, 2) ∧
    (Mobs 0 * Mobs 1, Mobs 1 * Mobs 2)
      ≠ (schurDim Mobs tobs 0 + liftDim Mobs tobs 0, schurDim Mobs tobs 1 + liftDim Mobs tobs 1) := by
  refine ⟨by decide, by decide, by decide⟩

/-- **The totals DO agree** (`= flatDim = 8`): the obstruction is purely the per-boundary partition, not
the count. Confirms the mismatch is a re-grouping incompatibility (the lift `W_s` is at a different
output layer), not a dimension error. -/
theorem flatTotal_eq_chartTotal_222 :
    Mobs 0 * Mobs 1 + Mobs 1 * Mobs 2
      = schurDim Mobs tobs 0 + liftDim Mobs tobs 0 + schurDim Mobs tobs 1 + liftDim Mobs tobs 1 := by
  decide

end DLNFibre.DLN.RLCT
