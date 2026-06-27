import DLNFibre.DLN.RLCT.Validate.RouteMBoundaryCleanMinAdm
import DLNFibre.DLN.RLCT.Validate.RouteM4422

/-!
# `RouteMBoundaryCleanChart` — the ∀M BOUNDARY-CLEAN pure-radial chart (WIP)

The ∀M clean-boundary achiever chart: a single `pivotBlowupOn` of the whole deepest factor
(layer `L−1`), generalizing the banked concrete `(4,4,2,2)` (`RouteM4422`) / `(2,2,1)` (`RouteM221`).

`phi := pivotBlowupOn (deepestCoords M) (deepestPivot M)` (flat→flat): the `(0,0)`-entry of the deepest
layer is the pivot `u_p`, the other `m1·M_L − 1` deepest entries are the radial angulars `u_p·u_i`, the
earlier layers are free. So `paramsEquivFlat.symm (phi u)` has deepest layer `= u_p · M̄` (M̄(0,0)=1),
earlier layers free, hence `prod = u_p · (prefix · M̄)` and `routeMCore (phi u) = u_p² · ‖prefix·M̄‖²`.

The Jacobian det `|u_p|^{minAdm−1}` and the cov come from the generic `pivotBlowupOn` lemmas at
`active.card = m1·M_L = minAdm` (the clean identity `minAdm_eq_deepRows_mul_last`). The cov is POLYNOMIAL
(no rational pole — unlike the SMEARED branch).

This file builds the deepest-coordinatization + the factorization core. The full `NodeAchieverChart`
assembly + `U ≢ 0` + the det/cov fields are the remaining build.
-/

namespace DLNFibre.DLN.RLCT

open scoped BigOperators
open Matrix MeasureTheory

variable {L : ℕ}

/-! ## The deepest-layer flat coordinates -/

/-- The deepest layer index `⟨L−1, _⟩ : Fin L` (layer `A^(L−1)`). -/
def deepLayer (M : Fin (L + 1) → ℕ) (hL : 0 < L) : Fin L := ⟨L - 1, by omega⟩

/-- The flat coordinates of the deepest layer `A^(L−1)`: the `Fintype.equivFin` images of the `FlatIdx`
entries whose layer is `L−1`. Its cardinality is `M_{L−1}·M_L` (`= minAdm` for clean `M`). -/
noncomputable def deepestCoords (M : Fin (L + 1) → ℕ) (hL : 0 < L) :
    Finset (Fin (routeMAmbient M)) :=
  Finset.univ.filter (fun c : Fin (routeMAmbient M) =>
    ((Fintype.equivFin (FlatIdx M)).symm
      (Fin.cast (by rw [routeMAmbient, flatDim]) c)).1.1 = deepLayer M hL)

/-- **`deepestCoords` card = the count of `FlatIdx` entries at layer `deepLayer`** — the filter over
`Fin (routeMAmbient M)` transports along the `equivFin`/`cast` bijection to the `FlatIdx` subtype count.
(The downstream `= M_{L−1}·M_L = minAdm` step is the `Fintype.card` of the fixed-layer
`Fin (M castSucc) × Fin (M succ)` — documented below.) -/
theorem deepestCoords_card_eq_subtype (M : Fin (L + 1) → ℕ) (hL : 0 < L) :
    (deepestCoords M hL).card
      = Fintype.card {idx : FlatIdx M // idx.1.1 = deepLayer M hL} := by
  classical
  rw [deepestCoords, ← Fintype.card_subtype]
  let e : Fin (routeMAmbient M) ≃ FlatIdx M :=
    (finCongr (show routeMAmbient M = Fintype.card (FlatIdx M) by
        rw [routeMAmbient, flatDim])).trans (Fintype.equivFin (FlatIdx M)).symm
  refine Fintype.card_congr (Equiv.subtypeEquiv e (fun c => ?_))
  show _ ↔ (e c).1.1 = deepLayer M hL
  simp only [e, Equiv.trans_apply, finCongr_apply]

/-- **`deepestCoords` has cardinality `M (deepLayer).castSucc · M (deepLayer).succ`** (`= M_{L−1}·M_L`).
The fixed-layer `FlatIdx` subtype `{idx // idx.1.1 = d}` is `Fin (M d.castSucc) × Fin (M d.succ)`
(free row + col at the fixed layer). For clean `M` this is `minAdm M`. -/
theorem deepestCoords_card (M : Fin (L + 1) → ℕ) (hL : 0 < L) :
    (deepestCoords M hL).card
      = M (deepLayer M hL).castSucc * M (deepLayer M hL).succ := by
  classical
  rw [deepestCoords_card_eq_subtype]
  -- the fixed-layer subtype is `Fin (M d.castSucc) × Fin (M d.succ)`
  rw [show Fintype.card {idx : FlatIdx M // idx.1.1 = deepLayer M hL}
      = Fintype.card (Fin (M (deepLayer M hL).castSucc) × Fin (M (deepLayer M hL).succ)) from ?_]
  · rw [Fintype.card_prod, Fintype.card_fin, Fintype.card_fin]
  · refine Fintype.card_congr ?_
    refine
      { toFun := fun idx => (Fin.cast (by rw [idx.2]) idx.1.1.2, Fin.cast (by rw [idx.2]) idx.1.2)
        invFun := fun p => ⟨⟨⟨deepLayer M hL, p.1⟩, p.2⟩, rfl⟩
        left_inv := ?_
        right_inv := ?_ }
    · rintro ⟨⟨⟨s, i⟩, j⟩, hs⟩
      simp only at hs
      subst hs
      simp [Fin.cast]
    · rintro ⟨i, j⟩
      simp [Fin.cast]

/-- `M (deepLayer).castSucc = deepRows M` (`= Wext (L−1) = M_{L−1}`). -/
theorem M_deepLayer_castSucc (M : Fin (L + 1) → ℕ) (hL : 0 < L) :
    M (deepLayer M hL).castSucc = deepRows M := by
  rw [deepRows, Wext_apply M (L - 1) (by omega)]
  congr 1

/-- `M (deepLayer).succ = M (Fin.last L)` (`= M_L`). -/
theorem M_deepLayer_succ (M : Fin (L + 1) → ℕ) (hL : 0 < L) :
    M (deepLayer M hL).succ = M (Fin.last L) := by
  congr 1
  apply Fin.ext
  change (L - 1) + 1 = L
  omega

/-- **`deepestCoords` card `= minAdm M` for clean `M`** (the `active.card = minAdm` fact the chart's
radial blow-up consumes; `pivotBlowupOn` det exponent `= minAdm − 1`). Combines `deepestCoords_card`
with the clean identity `minAdm_eq_deepRows_mul_last`. -/
theorem deepestCoords_card_eq_minAdm (M : Fin (L + 1) → ℕ) (hL : 0 < L)
    (hNo : NoInteriorBothDrop M) (hclean : deepRank M = deepRows M) :
    (deepestCoords M hL).card = minAdm M := by
  rw [deepestCoords_card, M_deepLayer_castSucc M hL, M_deepLayer_succ M hL,
    minAdm_eq_deepRows_mul_last M hL hNo hclean]

/-! ## Remaining build (route documented; not yet formalised here)

The full `NodeAchieverChart M` for clean-boundary `M` needs, on top of `deepestCoords`:
* `deepestCoords_card`: `(deepestCoords M hL).card = M (deepLayer).castSucc · M (deepLayer).succ
  = M_{L−1}·M_L`, via the `equivFin` bijection (count `FlatIdx` with layer `L−1`); `= minAdm M` by
  `minAdm_eq_deepRows_mul_last` (clean). [`Finset.card` through the opaque bijection.]
* the factorization `routeMCore M (pivotBlowupOn (deepestCoords M hL) (deepestPivot M hL) u)
  = (u (deepestPivot M hL))² · U`: `paramsEquivFlat.symm (blowup u)` has deepest layer `u_p · M̄`
  (`paramsEquivFlat_apply_equivFin` decode), earlier layers free, so `prod = u_p • (prefix · M̄)`
  (`prodAux_succ` + `Matrix.mul_smul`), `dlnLoss = u_p²·‖prefix·M̄‖²`.
* `U ≢ 0` a.e. (the `MvPolynomial` null-zero-set route — M̄ has a fixed `1`, witness `[I|0]·e_{00}`).
* `leafH`/`leafH_pivot` (via the clean `minAdm` identity), `Ubound`, `Umeas`, `leaf_integrand`, `cov`
  (`pivotBlowupOn`'s `det = |u_p|^{minAdm−1}` + the generic c-o-v), `image_subset`.

These reuse the banked generic `pivotBlowupOn` det/cov/injOn (`S1G5Charts`) and the `RouteM4422`
cov-assembly template; the only M-specific opaque-equiv work is `deepestCoords_card` + the decode. -/

end DLNFibre.DLN.RLCT
