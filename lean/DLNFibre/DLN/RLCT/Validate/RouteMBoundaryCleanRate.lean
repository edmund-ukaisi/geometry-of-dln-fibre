import DLNFibre.DLN.RLCT.Validate.RouteMBoundaryCleanChart
import DLNFibre.DLN.RLCT.Foundations.ParamsReshapeMP
import DLNFibre.DLN.RLCT.Validate.LossHomogeneity

/-!
# `RouteMBoundaryCleanRate` — the ∀M BOUNDARY-CLEAN rate factorization (WALL 2, rate leg)

Option-A architecture (Codex-corroborated): the clean achiever chart is the GENERIC flat→flat radial
blow-up `phi := pivotBlowupOn (deepestCoords M hL) (deepestPivot M hL)` — NO outer reshape. The det/cov
are then DIRECTLY the generic `pivotBlowupOn` lemmas (`S1G5Charts`) at `active.card = minAdm`
(`deepestCoords_card_eq_minAdm`). The only M-specific work is the RATE decode, done ONCE generically:

* `paramsEquivFlat_symm_decode` — the per-coordinate flattening decode (`= rfl`, via `flatEquivOf`),
  reading the `(s,i,j)` Params slot of `(paramsEquivFlat M).symm x` off the flat coord `flatCoordOf q`.
* `flatCoordOf_mem_deepestCoords_iff` — membership is the only coordinate fact: `flatCoordOf q ∈
  deepestCoords M hL ↔ q.1.1 = deepLayer M hL`.

Then the layer comparison: the deepest layer of `(paramsEquivFlat M).symm (phi u)` is `u_p •` its
pivot-stripped form, earlier layers are untouched. The product pulls the scalar out of the LAST factor
(`prod = u_p • (prefix · M̄)`), so `routeMCore M (phi u) = (u p)² · ‖prefix·M̄‖²` (the rate `= (u p)²·U`).
-/

open scoped BigOperators
open Matrix MeasureTheory

namespace DLNFibre.DLN.RLCT

variable {L : ℕ}

/-! ## The generic flattening decode (Option A's one unavoidable bridge) -/

/-- The flat coordinate of a `FlatIdx` entry: the `Fintype.equivFin` image (cast to `Fin
(routeMAmbient M)`). The `paramsEquivFlat.symm` decode reads coord `flatCoordOf q` into Params slot `q`. -/
noncomputable def flatCoordOf (M : Fin (L + 1) → ℕ) (q : FlatIdx M) : Fin (routeMAmbient M) :=
  Fin.cast (by rw [routeMAmbient, flatDim]) (Fintype.equivFin (FlatIdx M) q)

/-- **The per-coordinate flattening decode** (`= rfl`): the `(s,i,j) = q` Params slot of
`(paramsEquivFlat M).symm x` is the flat coordinate `x (flatCoordOf M q)`. Since `paramsEquivFlat M`
is `flatEquivOf M (Fintype.equivFin (FlatIdx M)).symm` definitionally, this is `flatEquivOf_symm_coord`
(plus the `Fin.cast` identifying `Fin (flatDim M)` with `Fin (routeMAmbient M)`). -/
theorem paramsEquivFlat_symm_decode (M : Fin (L + 1) → ℕ)
    (x : Fin (routeMAmbient M) → ℝ) (q : FlatIdx M) :
    ((paramsEquivFlat M).symm x) q.1.1 q.1.2 q.2 = x (flatCoordOf M q) := by
  rw [flatCoordOf]
  rfl

/-- **Membership is the only coordinate fact**: `flatCoordOf M q ∈ deepestCoords M hL` iff the FlatIdx
layer of `q` is the deepest layer. (The `deepestCoords` filter round-trips `Fin.cast` ∘ `equivFin.symm`
against `flatCoordOf`'s `Fin.cast` ∘ `equivFin`.) -/
theorem flatCoordOf_mem_deepestCoords_iff (M : Fin (L + 1) → ℕ) (hL : 0 < L) (q : FlatIdx M) :
    flatCoordOf M q ∈ deepestCoords M hL ↔ q.1.1 = deepLayer M hL := by
  rw [deepestCoords, Finset.mem_filter, flatCoordOf]
  -- the round-trip `(equivFin).symm (cast (cast (equivFin q)))` collapses to `q`
  simp only [Fin.cast_cast, Fin.cast_eq_self, Equiv.symm_apply_apply, Finset.mem_univ, true_and]

/-! ## The chart map and its pivot-stripped companion -/

/-- The clean achiever pivot: a chosen flat coord lying in `deepestCoords` (the deepest-layer `(0,0)`
entry). Exists because the deepest layer is nonempty for clean `M` (`minAdm ≥ 1`). -/
noncomputable def deepestPivot (M : Fin (L + 1) → ℕ) (hL : 0 < L)
    (hne : (deepestCoords M hL).Nonempty) : Fin (routeMAmbient M) :=
  hne.choose

theorem deepestPivot_mem (M : Fin (L + 1) → ℕ) (hL : 0 < L)
    (hne : (deepestCoords M hL).Nonempty) :
    deepestPivot M hL hne ∈ deepestCoords M hL :=
  hne.choose_spec

/-- The clean achiever chart `phi := pivotBlowupOn (deepestCoords M hL) (deepestPivot …)` (flat→flat). -/
noncomputable def cleanPhi (M : Fin (L + 1) → ℕ) (hL : 0 < L)
    (hne : (deepestCoords M hL).Nonempty) :
    (Fin (routeMAmbient M) → ℝ) → (Fin (routeMAmbient M) → ℝ) :=
  pivotBlowupOn (deepestCoords M hL) (deepestPivot M hL hne)

/-- The pivot-stripped flat vector: pivot ↦ 1, everything else unchanged (so the blow-up's active
coords become the pure angulars `u_c`, the deepest layer loses its `u_p` factor). -/
noncomputable def unblownFlat (M : Fin (L + 1) → ℕ) (hL : 0 < L)
    (hne : (deepestCoords M hL).Nonempty) (u : Fin (routeMAmbient M) → ℝ) :
    Fin (routeMAmbient M) → ℝ :=
  fun c => if c = deepestPivot M hL hne then 1 else u c

/-! ## The flat-coordinate comparison (membership-only) -/

/-- On the active block (deepest-layer coords), the blow-up is `u_p · unblown`. -/
theorem cleanPhi_eq_mul_on_deepestCoords (M : Fin (L + 1) → ℕ) (hL : 0 < L)
    (hne : (deepestCoords M hL).Nonempty) (u : Fin (routeMAmbient M) → ℝ)
    (c : Fin (routeMAmbient M)) (hc : c ∈ deepestCoords M hL) :
    cleanPhi M hL hne u c = u (deepestPivot M hL hne) * unblownFlat M hL hne u c := by
  rw [cleanPhi, unblownFlat, pivotBlowupOn]
  by_cases hcp : c = deepestPivot M hL hne
  · -- pivot branch: LHS = `u p`, RHS = `u p * 1 = u p`
    rw [if_pos hcp, if_pos hcp, mul_one]
  · rw [if_neg hcp, if_pos hc, if_neg hcp]

/-- Off the active block (earlier-layer coords), the blow-up is `unblown` (unchanged). -/
theorem cleanPhi_eq_unblown_off_deepestCoords (M : Fin (L + 1) → ℕ) (hL : 0 < L)
    (hne : (deepestCoords M hL).Nonempty) (u : Fin (routeMAmbient M) → ℝ)
    (c : Fin (routeMAmbient M)) (hc : c ∉ deepestCoords M hL) :
    cleanPhi M hL hne u c = unblownFlat M hL hne u c := by
  rw [cleanPhi, unblownFlat, pivotBlowupOn]
  -- `c ≠ p` (the pivot is in `deepestCoords`, `c` is not) and `c ∉ active`
  have hcp : c ≠ deepestPivot M hL hne := fun h => hc (h ▸ deepestPivot_mem M hL hne)
  rw [if_neg hcp, if_neg hc, if_neg hcp]

/-! ## The layer-level Params comparison -/

/-- The Params tuple of the chart point: `(paramsEquivFlat M).symm (cleanPhi … u)`. -/
noncomputable def cleanParams (M : Fin (L + 1) → ℕ) (hL : 0 < L)
    (hne : (deepestCoords M hL).Nonempty) (u : Fin (routeMAmbient M) → ℝ) : Params M :=
  (paramsEquivFlat M).symm (cleanPhi M hL hne u)

/-- The pivot-stripped Params tuple: `(paramsEquivFlat M).symm (unblownFlat … u)`. -/
noncomputable def unblownParams (M : Fin (L + 1) → ℕ) (hL : 0 < L)
    (hne : (deepestCoords M hL).Nonempty) (u : Fin (routeMAmbient M) → ℝ) : Params M :=
  (paramsEquivFlat M).symm (unblownFlat M hL hne u)

/-- **The deepest layer is `u_p`-scaled**: at the deepest layer `L−1`, every entry of `cleanParams`
equals `u_p` times the corresponding `unblownParams` entry. -/
theorem cleanParams_deepLayer_scaled (M : Fin (L + 1) → ℕ) (hL : 0 < L)
    (hne : (deepestCoords M hL).Nonempty) (u : Fin (routeMAmbient M) → ℝ)
    (i : Fin (M (deepLayer M hL).castSucc)) (j : Fin (M (deepLayer M hL).succ)) :
    cleanParams M hL hne u (deepLayer M hL) i j
      = u (deepestPivot M hL hne) * unblownParams M hL hne u (deepLayer M hL) i j := by
  -- package `(deepLayer, i, j)` as a `FlatIdx M`, decode both sides, apply the active-block comparison
  set q : FlatIdx M := ⟨⟨deepLayer M hL, i⟩, j⟩ with hq
  have hdec : cleanParams M hL hne u (deepLayer M hL) i j
      = cleanPhi M hL hne u (flatCoordOf M q) :=
    paramsEquivFlat_symm_decode M (cleanPhi M hL hne u) q
  have hdec0 : unblownParams M hL hne u (deepLayer M hL) i j
      = unblownFlat M hL hne u (flatCoordOf M q) :=
    paramsEquivFlat_symm_decode M (unblownFlat M hL hne u) q
  rw [hdec, hdec0]
  exact cleanPhi_eq_mul_on_deepestCoords M hL hne u (flatCoordOf M q)
    ((flatCoordOf_mem_deepestCoords_iff M hL q).2 rfl)

/-- **Earlier layers are unchanged**: at any layer `s ≠ L−1`, `cleanParams` equals `unblownParams`. -/
theorem cleanParams_nonDeepLayer_eq (M : Fin (L + 1) → ℕ) (hL : 0 < L)
    (hne : (deepestCoords M hL).Nonempty) (u : Fin (routeMAmbient M) → ℝ)
    (s : Fin L) (hs : s ≠ deepLayer M hL) :
    cleanParams M hL hne u s = unblownParams M hL hne u s := by
  funext i j
  set q : FlatIdx M := ⟨⟨s, i⟩, j⟩ with hq
  have hdec : cleanParams M hL hne u s i j = cleanPhi M hL hne u (flatCoordOf M q) :=
    paramsEquivFlat_symm_decode M (cleanPhi M hL hne u) q
  have hdec0 : unblownParams M hL hne u s i j = unblownFlat M hL hne u (flatCoordOf M q) :=
    paramsEquivFlat_symm_decode M (unblownFlat M hL hne u) q
  rw [hdec, hdec0]
  refine cleanPhi_eq_unblown_off_deepestCoords M hL hne u (flatCoordOf M q) (fun hmem => ?_)
  exact hs ((flatCoordOf_mem_deepestCoords_iff M hL q).1 hmem)

/-! ## The product scalar pull-out + the rate

The deepest layer `deepLayer M hL = ⟨L−1,_⟩` is the LAST `Fin L` layer, so `cleanParams = scaleLayer
M u_p (deepLayer) (unblownParams)` (deepest scaled by `u_p`, earlier layers unchanged); the banked
`prod_scaleLayer` / `dlnLoss_homogeneous_layer` (`LossHomogeneity`) then pull the scalar out. -/

/-- **`cleanParams = scaleLayer u_p (deepLayer) (unblownParams)`**: only the deepest layer is scaled by
the pivot, the earlier layers are unchanged. Combines `cleanParams_deepLayer_scaled` (deepest is `u_p •`)
and `cleanParams_nonDeepLayer_eq` (earlier unchanged) into the `Function.update` form. -/
theorem cleanParams_eq_scaleLayer (M : Fin (L + 1) → ℕ) (hL : 0 < L)
    (hne : (deepestCoords M hL).Nonempty) (u : Fin (routeMAmbient M) → ℝ) :
    cleanParams M hL hne u
      = scaleLayer M (u (deepestPivot M hL hne)) (deepLayer M hL) (unblownParams M hL hne u) := by
  funext s
  rw [scaleLayer]
  by_cases hs : s = deepLayer M hL
  · subst hs
    rw [Function.update_self]
    funext i j
    rw [cleanParams_deepLayer_scaled M hL hne u i j, Matrix.smul_apply, smul_eq_mul]
  · rw [Function.update_of_ne hs]
    exact cleanParams_nonDeepLayer_eq M hL hne u s hs

/-- **The product pulls the pivot out of the deepest (last) factor**: `prod M (cleanParams u) = u_p •
prod M (unblownParams u)`. -/
theorem prod_cleanParams_eq_smul (M : Fin (L + 1) → ℕ) (hL : 0 < L)
    (hne : (deepestCoords M hL).Nonempty) (u : Fin (routeMAmbient M) → ℝ) :
    prod M (cleanParams M hL hne u)
      = (u (deepestPivot M hL hne)) • prod M (unblownParams M hL hne u) := by
  rw [cleanParams_eq_scaleLayer, prod_scaleLayer]

/-- **The rate factorization** `routeMCore M (cleanPhi … u) = (u_p)² · U` with `U := dlnLoss M 0
(unblownParams u)` (the `u_p`-free unit `= ‖prefix·M̄‖²`) — the chart's `F ∘ φ = u²·U` identity. -/
theorem routeMCore_cleanPhi (M : Fin (L + 1) → ℕ) (hL : 0 < L)
    (hne : (deepestCoords M hL).Nonempty) (u : Fin (routeMAmbient M) → ℝ) :
    routeMCore M (cleanPhi M hL hne u)
      = (u (deepestPivot M hL hne)) ^ 2 * dlnLoss M 0 (unblownParams M hL hne u) := by
  rw [routeMCore, cleanPhi]
  show dlnLoss M 0 ((paramsEquivFlat M).symm (pivotBlowupOn (deepestCoords M hL)
    (deepestPivot M hL hne) u)) = _
  rw [show (paramsEquivFlat M).symm (pivotBlowupOn (deepestCoords M hL) (deepestPivot M hL hne) u)
      = cleanParams M hL hne u from rfl,
    cleanParams_eq_scaleLayer, dlnLoss_homogeneous_layer]

end DLNFibre.DLN.RLCT
