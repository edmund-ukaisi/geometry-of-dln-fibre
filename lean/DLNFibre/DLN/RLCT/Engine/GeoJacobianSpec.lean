import DLNFibre.DLN.RLCT.Engine.GeoChart

/-!
# `DLNFibre.DLN.RLCT.Engine.GeoJacobianSpec` — the fold-Jacobian SPECIFY skeleton (for t11)

The SPECIFY handoff for the fold-Jacobian builder (coverage-t08 → t11, the wall / L2-D1 class). Full
recipe: `threads/10-coverage/fold-jacobian-specify.md`. This file carries the VALIDATED statement with
its one `sorry`; t11 grinds the path-induction.

**The crux** (see the note): `|det D(composite)| = ∏_k |z_k|^{leaf.divExp k − 1}` (ledger-ACCUMULATED,
not per-single-blow-up), by path induction + chain rule (`det(fold) = det(edge β̃)·det(child)`), each
edge's `|det Dβ̃| = |z_pivot|^{d_center−1}` via q-CONJUGATION (t09's `qOfCenter_hasFDerivAt` — fderiv is
the fixed CLE, so `det(CLE.symm)·det(pivotChart×id)·det(CLE)` cancels to the `pivotChart` det) + the
source gauge `α` det-neutral (`abs_det_fderiv_elemShear`, `|det Dα|=1`). The exponent TELESCOPING onto
`divExp k` (the elder's substitution table: u-chart `|u|^m`, d_j-chart `|d_j|^m` + the inherited `M−1`
pull-through; `stepUpdate`: case11 `+= runLen·resCols`, case12 `= divExp(mergeIdx) + runLen·resCols`) is
the wall — the dependent-index reassociation idiom. `LeafJacobian c` then closes with `β := composite`,
`ψ := id` (R-b gauge in the source, `|det Dψ|=1`).
-/

namespace DLNFibre.DLN.RLCT.Engine

open DLNFibre.DLN.RLCT
open scoped BigOperators

variable {L : ℕ} {M : Fin (L + 1) → ℕ}

/-- **The fold-Jacobian det** (SPECIFY skeleton, `sorry` owned by t11): each geometric leaf composite's
Fréchet-derivative determinant is the ledger-accumulated monomial `∏_k |z_k|^{divExp k − 1}`. This is
LeafJacobian's `Dβ` clause over the geometric atlas. Recipe: `fold-jacobian-specify.md`. -/
theorem geoChart_fold_det (t : ResolutionTree M)
    (lc : LeafData M × (Params M → Params M))
    (hlc : lc ∈ geometricLeafPaths (dCenterOfNode M) (qNodeOf M) id t)
    (w : Params M) :
    |(fderiv ℝ lc.2 w).det|
      = ∏ k : Fin lc.1.numDiv, |paramsEquivFlat M w (lc.1.divCoord k)| ^ (lc.1.divExp k - 1) := by
  sorry

end DLNFibre.DLN.RLCT.Engine
