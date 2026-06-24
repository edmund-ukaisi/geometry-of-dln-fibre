import DLNFibre.DLN.RLCT.Foundations.S1G5Charts

/-!
# `DLNFibre.DLN.RLCT.Validate.NodeHomogeneity` — the per-node homogeneity factorization (G2, fm3)

The Route-M per-node GEOMETRIC seed: at a blow-up node, the loss pulled back through the atlas chart
`pivotBlowupOn active p` factors as `(pivot)² · (hard-pivot residual)`, with the chart Jacobian
`(pivot)^(active.card − 1)`. The general analog of `Case222Resolution.myF222_step1A`
(`myF222(step1A y) = y0²·residual`), tied to the banked atlas (`pivotBlowupOn` /
`pivotBlowupOnDeriv_det`).

## Why this is the right altitude (team-lead-approved 2026-06-22)

The load-bearing geometric fact is HOMOGENEITY: the DLN core loss is degree-2 in each layer's matrix
block (a matrix product is multilinear; scaling one factor by `c` scales `‖∏C‖²` by `c²`). The atlas
chart `pivotBlowupOn active p` scales the whole `active` block by the pivot `x p` (off-pivot active
`x j ↦ x p · x j`, pivot `x p ↦ x p`), so the loss pulls back with an `(x p)²` exceptional factor.

This factorization is EXHAUSTIVENESS-INDEPENDENT and MECHANISM-INDEPENDENT: it holds at EVERY blow-up
node (C1 / C2 / C4 all blow up via `pivotBlowupOn`), regardless of the C1–C4 node taxonomy. It is the
R1.2 geometric seed: the `(x p)²` is the exceptional divisor whose `(k,h) = (1, card−1)` feeds
`axisRatio_regularSeq` (ratio `card/2`); the `(x p)²` is carried by the monomial/cover lane (NOT
folded into the residual — that fold telescopes to `ambient/2`, the SOUNDNESS-NOTE-false value;
`GeneralR1Recursion.lean:18`). The residual `L ∘ hardPivotAt` is the loss the recursion descends on
AFTER the Schur det-unit dimension drop (the blow-up alone does not shrink `ΣM`).

## The decomposition (the load-bearing structural identity)

`pivotBlowupOn active p x = scaleActiveBy (x p) active (hardPivotAt p x)`, where
- `scaleActiveBy c active` scales the `active` coordinates by `c` (others fixed);
- `hardPivotAt p` sets the pivot coordinate to `1`, leaves all others (the post-blow-up hard
  pivot `Â p = 1`).
So a loss homogeneous of degree 2 in the `active` block pulls back as `(x p)² · (L ∘ hardPivotAt)`.
-/

open MeasureTheory Matrix
open scoped BigOperators
namespace DLNFibre.DLN.RLCT

variable {N : ℕ}

/-- Scale the `active` coordinates by `c`, leaving the others fixed: `i ↦ (c · x i if i ∈ active; x i
else)`. The action under which the node loss is degree-2 homogeneous. -/
def scaleActiveBy (c : ℝ) (active : Finset (Fin N)) (x : Fin N → ℝ) : Fin N → ℝ :=
  fun i => if i ∈ active then c * x i else x i

/-- The hard-pivot normalization: set the pivot coordinate to `1`, leave all others. The post-blow-up
hard pivot `Â p = 1`; `L ∘ hardPivotAt` is the residual the recursion descends on. -/
def hardPivotAt (p : Fin N) (x : Fin N → ℝ) : Fin N → ℝ :=
  fun i => if i = p then 1 else x i

/-- **The chart decomposition (structural, no hypothesis).** `pivotBlowupOn active p` factors as
"scale the active block by the pivot `x p`" applied to "the hard-pivot normalization". Pure unfolding
(`p ∈ active` so the pivot row is `x p · 1 = x p`). -/
theorem pivotBlowupOn_eq_scaleActive_hardPivot (active : Finset (Fin N)) (p : Fin N) (hp : p ∈ active)
    (x : Fin N → ℝ) :
    pivotBlowupOn active p x = scaleActiveBy (x p) active (hardPivotAt p x) := by
  funext i
  simp only [pivotBlowupOn, scaleActiveBy, hardPivotAt]
  rcases eq_or_ne i p with rfl | hi
  · simp [hp]
  · by_cases ha : i ∈ active <;> simp [hi, ha]

/-- **G2 — the per-node homogeneity factorization.** If the loss `L` is degree-2 homogeneous in the
`active` block (`L (scaleActiveBy c active x) = c² · L x`), then pulling it back through the blow-up
chart factors out the pivot square: `L (pivotBlowupOn active p x) = (x p)² · L (hardPivotAt p x)`. The
general `myF222_step1A`; the `(x p)²` is the exceptional factor, `L ∘ hardPivotAt p` the residual. -/
theorem node_loss_pivot_factor (active : Finset (Fin N)) (p : Fin N) (hp : p ∈ active)
    (L : (Fin N → ℝ) → ℝ)
    (hhomog : ∀ (c : ℝ) (x : Fin N → ℝ), L (scaleActiveBy c active x) = c ^ 2 * L x)
    (x : Fin N → ℝ) :
    L (pivotBlowupOn active p x) = (x p) ^ 2 * L (hardPivotAt p x) := by
  rw [pivotBlowupOn_eq_scaleActive_hardPivot active p hp, hhomog]

/-- **The chart Jacobian (banked, re-exported for the node).** `|det D(pivotBlowupOn active p)| =
|x p|^(active.card − 1)` — the monomial Jacobian weight whose exponent `h = card − 1` pairs with the
loss exponent `k = 1` (from `node_loss_pivot_factor`'s `(x p)²`) to give the regular-sequence axis
ratio `card/2` (`axisRatio_regularSeq`). Direct from `pivotBlowupOnDeriv_det`. -/
theorem node_jacobian_det (active : Finset (Fin N)) (p : Fin N) (hp : p ∈ active) (x : Fin N → ℝ) :
    (pivotBlowupOnDeriv active p x).det = (x p) ^ (active.card - 1) :=
  pivotBlowupOnDeriv_det active p hp x

end DLNFibre.DLN.RLCT
