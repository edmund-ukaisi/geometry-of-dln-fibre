import DLNFibre.DLN.RLCT.Validate.GeneralR1Recursion

/-!
# `DLNFibre.DLN.RLCT.Validate.SchurNodeAssembly` — the Schur node-loss presentation (fm3)

The Frobenius-norm form of the hard-pivot Schur row-decomposition: `‖Â·A2‖²` written as the pivot-row
block `∑ Erow²` plus the lower (Schur) block `∑ (b·Erow + S·Γ)²`. This is the concrete-coordinate
content the per-node squeeze datum's `hnode` presentation consumes — for the post-blow-up RESIDUAL.

## Route-check outcome (fm3, 2026-06-22 — `threads/fm3-coord-bridge/route-check-finding.md`)

The per-node squeeze datum `IsSchurStraightenSqueeze` (in `GeneralR1Recursion.lean`) presents the
node core as `flatCore = (∑ⱼ w.1ⱼ²) + ‖bcol·w.1 + SΓ‖²` with `∑ⱼ w.1ⱼ²` a REGULAR smooth block
(`rlct_additive_smooth_block`, `Skeleton.lean:235`, requires the literal coordinate projections
`p.1 i`, RLCT `nReg/2`).

This presentation is FAITHFUL to the post-blow-up **residual** `‖Â·A2‖²` (hard pivot `Â[0,0]=1`), the
identity proven below. It is NOT dischargeable for the full pulled-back loss
`dlnLoss M 0 ∘ pivotBlowupOn`: by homogeneity (degree-2 in the A-block, the blow-up scales the whole
A-row by the pivot), the pulled-back loss vanishes to ORDER 4 at the deepest point — no quadratic
part — so no regular `nReg`-coordinate block `∑(coord)²` (which carries a quadratic term a
sum-of-squares cannot cancel) can present it. The exceptional monomial (`x_p²`) carries an RLCT
contribution accounted by the SEPARATE `monomialThreshold` / cover lane (the banked route giving the
`(2,2,2)` value `3/2`). Decorrelated: Codex (xhigh) + sympy.

So the identity below is the residual-side bedrock; the full per-node step composes it with the
exceptional-factor accounting from the monomial lane (architecture pending the controller's call).
-/

open MeasureTheory Matrix
open scoped ENNReal BigOperators
namespace DLNFibre.DLN.RLCT

/-! ## The Schur node-loss presentation — `Â·A2` block algebra at the hard-pivot node

`Â` carries a HARD PIVOT `Â[0,0]=1` (the post-blow-up normalization). Write `Â` in block form with
pivot block `1`, pivot row tail `a`, pivot column tail `b`, corner block `D`; `A2` with pivot row `β`,
lower rows `Γ`. The pivot row of `Â·A2` is `Erow = β + a·Γ`; the lower rows decompose (Schur) as
`b·Erow + (D − b·a)·Γ`. So `‖Â·A2‖² = ‖Erow‖² + ‖b·Erow + S·Γ‖²` (`S = D − b·a`). -/

/-- **The hard-pivot Schur node-loss presentation.** With a hard pivot (pivot block `1`), the squared
Frobenius norm of the product `Â·A2` splits as the pivot-row block `∑ⱼ Erowⱼ²` plus the lower block
`∑ᵢⱼ (bᵢ·Erowⱼ + (S·Γ)ᵢⱼ)²`, where `Erow = β + a·Γ` (pivot row product), `b` = pivot column tail,
`S = D − b·a` the Schur complement, `Γ` = lower rows of `A2`. `schur_row_decomp` lifted to the
Frobenius sum-of-squares (the lower block's argument is rewritten by the row decomposition; the
pivot-row block is unchanged). Pure matrix algebra — the residual-side content of the per-node
squeeze datum's `hnode` presentation. -/
theorem schur_node_loss_presentation {p m k n : Type*}
    [Fintype p] [Fintype m] [Fintype k] [Fintype n] [DecidableEq p]
    (a : Matrix p k ℝ) (b : Matrix m p ℝ) (D : Matrix m k ℝ)
    (β : Matrix p n ℝ) (Γ : Matrix k n ℝ) :
    (∑ i : p, ∑ j : n, (((1 : Matrix p p ℝ) * β + a * Γ) i j) ^ 2)
      + (∑ i : m, ∑ j : n, ((b * β + D * Γ) i j) ^ 2)
    = (∑ i : p, ∑ j : n, (((1 : Matrix p p ℝ) * β + a * Γ) i j) ^ 2)
      + (∑ i : m, ∑ j : n,
          ((b * ((1 : Matrix p p ℝ) * β + a * Γ) + (D - b * a) * Γ) i j) ^ 2) := by
  rw [schur_row_decomp a b D β Γ]

end DLNFibre.DLN.RLCT
