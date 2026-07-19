import DLNFibre.DLN.RLCT.Engine.GeoDiagSwap

/-!
# `DLNFibre.DLN.RLCT.Engine.GeoLeafJacobian` — the fold-Jacobian headline over the normalized atlas (t11)

The finding-2 culmination: each geometric atlas piece's chart (the root→leaf fold of the
diagonal-normalized per-edge charts `geoChartMapNorm`) has Fréchet-derivative determinant equal to the
ledger monomial `∏_k |z_{divCoord k}|^{divExp k − 1}` — the `LeafJacobian` β-det clause, over
`geoAtlas (buildTree M (conOracle M) conRoot)`.

STATEMENT-FIRST (elder/team-lead gated, `fold-jacobian-specify-addendum-t11.md`). The **Jacobian half is
banked**: the composite det is the intermediate-point per-edge product (`abs_det_fderiv_foldr_comp`), each
per-edge factor reads the DIAGONAL cell `z_{diagTargetOf}` (`geoChartMap_swap_fderiv_det`, via the
det-neutral swap `S`). The remaining crux is the **regrouping** (cert §1,
`threads/18-fold-regroup/cert-fold-regroup.md`): the intermediate-point diagonal factors telescope onto
the source-`w` ledger `∏_k |z_{divCoord k}(w)|^{divExp k − 1}` — the relative-Jacobian cocycle threading
`stepUpdate`, now on-diagonal (no off-diagonal discrepancy, kill-condition resolved by fork-15). That
induction is the one `sorry` below (LIVE-frontier, statement-locked). -/

namespace DLNFibre.DLN.RLCT.Engine

open DLNFibre.DLN.RLCT
open scoped BigOperators

variable {L : ℕ} {M : Fin (L + 1) → ℕ}

/-- **The fold-Jacobian headline** (finding-2, over the normalized built atlas): every geometric atlas
piece's chart determinant is the ledger monomial. This is `LeafJacobian`'s β-det clause (β := chartMap,
ψ := id). Proof = the banked composite-det (`abs_det_fderiv_foldr_comp`) + per-edge diagonal read
(`geoChartMap_swap_fderiv_det`) + the cert §1 regrouping cocycle (the tracked `sorry`). -/
theorem geoAtlas_fold_det (s : ConState L)
    (c : LeafData M) (hc : c ∈ geoAtlas (buildTree M (conOracle M) s)) (w : Params M) :
    |(fderiv ℝ c.chartMap w).det|
      = ∏ k : Fin c.numDiv, |paramsEquivFlat M w (c.divCoord k)| ^ (c.divExp k - 1) := by
  sorry

end DLNFibre.DLN.RLCT.Engine
