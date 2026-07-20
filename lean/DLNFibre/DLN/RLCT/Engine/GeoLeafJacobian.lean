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

/-- The `conRoot` base of the cocycle: `|det D id| = 1 = ledgerMonomial conRoot`. -/
private theorem id_det_conRoot (h : 0 < flatDim M) (w : Params M) :
    |(fderiv ℝ (id : Params M → Params M) w).det| = ledgerMonomial M (conRoot : ConState L) h w := by
  rw [ledgerMonomial_conRoot, fderiv_id, show (ContinuousLinearMap.id ℝ (Params M)).det
      = LinearMap.det (ContinuousLinearMap.id ℝ (Params M)).toLinearMap from rfl]
  simp [LinearMap.det_id]

/-- `|det|` of the identity chart is `1` (the `ψ = id` gauge of the fold's `LeafJacobian`). -/
private theorem abs_det_id_one :
    |(ContinuousLinearMap.id ℝ (Params M)).det| = 1 := by
  rw [show (ContinuousLinearMap.id ℝ (Params M)).det
      = LinearMap.det (ContinuousLinearMap.id ℝ (Params M)).toLinearMap from rfl]
  simp [LinearMap.det_id]

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
`DivBirthInv`/`DivExpPos`, `GeoFoldRegroup`) instantiated at `conRoot`/`id`; the exposed terminal state
`s'` supplies `fc := birthFlatCoord M s'`. -/
theorem geoAtlas_fold_det (h : 0 < flatDim M) (c : LeafData M)
    (hc : c ∈ geoAtlas (buildTree M (conOracle M) (conRoot : ConState L))) :
    ∃ fc : Fin c.fullNumDiv → Fin (flatDim M), ∀ w : Params M,
      |(fderiv ℝ c.chartMap w).det|
        = ∏ j : Fin c.fullNumDiv, |paramsEquivFlat M w (fc j)| ^ (c.fullDivExp j - 1) := by
  obtain ⟨s', _, _, _, hshape, hident⟩ :=
    geoAtlas_cocycle h conRoot DivBirthInv_conRoot DivExpPos_conRoot id differentiable_id
      (id_det_conRoot h) c hc
  rw [hshape, leafOfState, dif_pos h]
  exact ⟨fun j => birthFlatCoord M s' j h, fun w => by rw [hident w, ledgerMonomial]⟩

/-- **The R7 `LeafJacobian` discharge over the geometric atlas** (elder charge-6 / R7). Every
`geoAtlas` piece `c` (over `conRoot`) satisfies the full-ledger `LeafJacobian`: `β := c.chartMap`,
`ψ := id` (`lo = hi = 1`, det-1), the full coordinate map `fc := birthFlatCoord M s'` and the analytic
embedding `emb := (t0Indices s').get` at the leaf's reachable terminal state `s'` (exposed by
`geoAtlas_cocycle`). The identity conjunct is the cocycle's `|det D chartMap| = ledgerMonomial s'`; the
`∀ j, 1 ≤ fullDivExp j` conjunct is `DivExpPos s'` (PROVABLE — every born divisor's exponent is `≥ 1`,
`resRows ≥ 1` at every non-rollover node; NO zero-block case-2, so the watch-item does not fire). Fills
the R7 second frontier of `chartBridgeFaithful_buildTree`. -/
theorem geoAtlas_leaf_leafJacobian (h : 0 < flatDim M) (c : LeafData M)
    (hc : c ∈ geoAtlas (buildTree M (conOracle M) (conRoot : ConState L))) :
    LeafJacobian c := by
  obtain ⟨s', hinv', hexp', hdiff, hshape, hident⟩ :=
    geoAtlas_cocycle h conRoot DivBirthInv_conRoot DivExpPos_conRoot id differentiable_id
      (id_det_conRoot h) c hc
  have hget : Function.Injective (t0Indices s').get :=
    ((List.nodup_finRange s'.numDiv).filter _).injective_get
  rw [hshape, leafOfState, dif_pos h]
  refine ⟨c.chartMap, id, id, fun w => fderiv ℝ c.chartMap w,
    fun _ => ContinuousLinearMap.id ℝ (Params M), 1, 1,
    fun j => birthFlatCoord M s' j h, fun i => (t0Indices s').get i,
    one_pos, birthFlatCoord_injective hinv', hget, fun k => rfl, fun k => rfl, fun j => hexp' j,
    ?_, fun w _ => rfl, fun w _ => ⟨(hdiff w).hasFDerivAt, by rw [hident w, ledgerMonomial]⟩,
    fun v _ => ⟨rfl, rfl, hasFDerivAt_id v, abs_det_id_one.ge, abs_det_id_one.le⟩⟩
  rw [Set.range_eq_empty (f := (Fin.elim0 : Fin 0 → Fin (flatDim M)))]
  exact disjoint_bot_right

end DLNFibre.DLN.RLCT.Engine
