import DLNFibre.DLN.RLCT.Engine.GeoFoldRegroup

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
piece's chart determinant is the FULL-LEDGER monomial — the R7 `LeafJacobian` β-det identity conjunct
(β := chartMap, ψ := id), with the full-divisor coordinate map `fc` carried EXISTENTIALLY.

**SCOPE = `conRoot`; FORM = full ledger** (t14, team-lead ruling (A) + charge-6/R7, 2026-07-19..20). Two
statement corrections landed here, both machine-forced:
* the predecessor's locked binder `(s : ConState L)` was FALSE at generic `s` (a terminal `s` with an
  analytic divisor of exponent ≥ 2 gives a single-leaf `chartMap = id`, so `|det D id| = 1 ≠ 0 = RHS`
  at `w = 0`; `GeoLeafJacobianDisproof.geoAtlas_fold_det_generic_false`) — corrected to `conRoot`;
* the analytic RHS (`c.numDiv`/`c.divExp`) was FALSE (reachable terminals carry stranded `t̃>0` divisors
  of `divExp > 1` that the geometric fold DOES blow up; `cert-stranded-dichotomy`, witness `M=(2,3)`) —
  corrected to the FULL ledger (`c.fullNumDiv`/`c.fullDivExp`).

Proof = `geoAtlas_cocycle` (the acc + incoming-ledger-threaded cocycle over generic `s` under
`DivBirthInv`/`DivExpPos`, `GeoFoldRegroup`) instantiated at `conRoot`/`id` with the empty incoming
ledger (`ledgerMonomial_conRoot`, `|det D id| = 1`). -/
theorem geoAtlas_fold_det (h : 0 < flatDim M) (c : LeafData M)
    (hc : c ∈ geoAtlas (buildTree M (conOracle M) (conRoot : ConState L))) :
    ∃ fc : Fin c.fullNumDiv → Fin (flatDim M), ∀ w : Params M,
      |(fderiv ℝ c.chartMap w).det|
        = ∏ j : Fin c.fullNumDiv, |paramsEquivFlat M w (fc j)| ^ (c.fullDivExp j - 1) := by
  refine geoAtlas_cocycle h conRoot DivBirthInv_conRoot DivExpPos_conRoot id differentiable_id
    (fun w => ?_) c hc
  rw [ledgerMonomial_conRoot]
  change |(fderiv ℝ (id : Params M → Params M) w).det| = 1
  rw [fderiv_id, show (ContinuousLinearMap.id ℝ (Params M)).det
      = LinearMap.det (ContinuousLinearMap.id ℝ (Params M)).toLinearMap from rfl]
  simp [LinearMap.det_id]

end DLNFibre.DLN.RLCT.Engine
