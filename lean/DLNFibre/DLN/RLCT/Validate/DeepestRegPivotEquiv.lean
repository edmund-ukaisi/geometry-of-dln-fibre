import DLNFibre.DLN.RLCT.Validate.DeepestSplitReindex
import DLNFibre.DLN.RLCT.Validate.DeepestGaugeConstruction

/-!
# `DLNFibre.DLN.RLCT.Validate.DeepestRegPivotEquiv` — the explicit boundary-pivot packing (#120 / #82)

The #120 explicit-pack atoms for the #82-deriv close (deriv-fm author, controller 2026-06-23). GREEN +
sorry-free + clean axioms. The transparent `regPivotFinEquiv` + `BoundaryPivotIdx` + the boundary
routing `regBoundaryToRegGauge` (injective, `regBoundaryToRegGauge_injective`) that replace the OPAQUE
`Fintype.equivFin` packs (the triply-confirmed wall: reg-block-id is unprovable for the opaque pack).

At the #80 handoff of `DeepestGaugeConstruction.lean`: `regResidualPack := regPivotFinEquiv` and
`regGaugeIdxSplit`'s reg-half routes via `regBoundaryToRegGauge ∘ regPivotFinEquiv`, so the two cancel
and `deepestEPivot_regSlice_fderiv_id` becomes `= id` by construction (see `deriv-120-wiring-spec.md`
+ `deriv-alignment-sandwich-tactic-cert.md`). cobuild integrates; deriv-fm authored these atoms.

## The boundary correspondence (g213/#91, the collapse-math — CERTIFIED)

At `reg = 0` every framed layer is the idempotent corner `blockdiag[I_r,0]`; Leibniz with idempotent
prefix/suffix products keep `dP|_0 = (Σ_s δX_s, δY_L, δZ_1)` — (0,0)-corner sums all X, the
last Y, first Z survive. So the reg slot carries exactly the boundary generators
`(X_first, Y_last, Z_first)`, one private coord each, routed to DISTINCT `RegGaugeIdx` entries so
the `Σ_s δX_s` cannot collapse two reg coords (injective-by-construction).
-/

open Matrix
open scoped BigOperators
namespace DLNFibre.DLN.RLCT

variable {L : ℕ}

/-- **The boundary-pivot index type** — the residual blocks `(P11−I, P12, P21)` surviving the
idempotent sandwich: `(r×r) ⊕ ((r×M_L) ⊕ (M_0×r))`, the sum type `regResidualPack` targets,
of cardinality `deepestNReg H r`. -/
abbrev BoundaryPivotIdx (H : Fin (L + 1) → ℕ) (r : ℕ) : Type :=
  (Fin r × Fin r) ⊕ ((Fin r × Fin (H (Fin.last L) - r)) ⊕ (Fin (H 0 - r) × Fin r))

/-- **The card match** — `card BoundaryPivotIdx = deepestNReg` (the SAME arithmetic
`regResidualPack` proves: `r² + r(H_L−r) + (H_0−r)r = r(H_0+H_L−r)`). The explicit Fin-equiv
exists by this; the refactor swaps the opaque `Fintype.equivFin` tail for an honest enumeration. -/
theorem card_boundaryPivotIdx (H : Fin (L + 1) → ℕ) (r : ℕ)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) :
    Fintype.card (BoundaryPivotIdx H r) = deepestNReg H r := by
  simp only [BoundaryPivotIdx, Fintype.card_sum, Fintype.card_prod, Fintype.card_fin]
  obtain ⟨a', ha'⟩ := Nat.le.dest (hr 0)
  obtain ⟨b', hb'⟩ := Nat.le.dest (hr (Fin.last L))
  unfold deepestNReg
  rw [← ha', ← hb']
  simp only [Nat.add_sub_cancel_left]
  rw [show r + a' + (r + b') - r = r + (a' + b') by omega]
  ring

/-- **The explicit pivot packing** `Fin (deepestNReg H r) ≃ BoundaryPivotIdx H r` — the TRANSPARENT
enumeration replacing `regResidualPack`'s opaque `Fintype.equivFin`: `finProdFinEquiv` on each block
(`r×r`, `r×M_L`, `M_0×r`) + `finSumFinEquiv` to assemble, with the `deepestNReg = r² + (r·M_L + M_0·r)`
reassociation by `finCongr`. Computable (has `_apply` equation lemmas), so the per-coordinate value
reduces — the property `Fintype.equivFin` lacks. This is what makes the cancellation `rfl`-able. -/
noncomputable def regPivotFinEquiv (H : Fin (L + 1) → ℕ) (r : ℕ)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) :
    Fin (deepestNReg H r) ≃ BoundaryPivotIdx H r :=
  -- `Fin nReg ≃ Fin (r*r + (r*M_L + M_0*r))` then split into the three `finProdFinEquiv` blocks.
  (finCongr (show deepestNReg H r
      = r * r + (r * (H (Fin.last L) - r) + (H 0 - r) * r) by
        obtain ⟨a', ha'⟩ := Nat.le.dest (hr 0)
        obtain ⟨b', hb'⟩ := Nat.le.dest (hr (Fin.last L))
        unfold deepestNReg
        rw [← ha', ← hb']
        simp only [Nat.add_sub_cancel_left]
        rw [show r + a' + (r + b') - r = r + (a' + b') by omega]
        ring)).trans
    (finSumFinEquiv.symm.trans
      (Equiv.sumCongr finProdFinEquiv.symm
        (finSumFinEquiv.symm.trans
          (Equiv.sumCongr finProdFinEquiv.symm finProdFinEquiv.symm))))

/-- The first layer index `⟨0,_⟩ : Fin L` (`0 < L` from `1 ≤ L`). -/
def firstLayer (hL : 1 ≤ L) : Fin L := ⟨0, by omega⟩

/-- The last layer `⟨L-1,_⟩ : Fin L`; `.succ` is `Fin.last L` (width `H (Fin.last L)`). -/
def lastLayer (hL : 1 ≤ L) : Fin L := ⟨L - 1, by omega⟩

/-- `(lastLayer hL).succ` has the same `H`-width as `Fin.last L` — the Y_last column cast. -/
theorem H_lastLayer_succ (H : Fin (L + 1) → ℕ) (hL : 1 ≤ L) :
    H ((lastLayer hL).succ) = H (Fin.last L) := by
  congr 1; apply Fin.ext; simp [lastLayer, Fin.succ, Fin.last]; omega

/-- **The boundary-generator routing** `BoundaryPivotIdx → RegGaugeIdx` (the reg-half target):
`X_first` ↦ layer-0 (0,0) entry, `Y_last` ↦ last-layer (0,1) entry, `Z_first` ↦ layer-0 (1,0) entry.
INJECTIVE (distinct layer-tag × sum-arm), killing the `Σ_s δX_s` collapse. The
`H (Fin.last L) - r` vs `H ((lastLayer).succ) - r` index forced equal by `H_lastLayer_succ`. -/
def regBoundaryToRegGauge (H : Fin (L + 1) → ℕ) (r : ℕ) (hL : 1 ≤ L) :
    BoundaryPivotIdx H r → RegGaugeIdx H r
  | Sum.inl (i, j) =>
      -- X_first: first layer, outer-inl inner-inl
      ⟨firstLayer hL, Sum.inl (Sum.inl (i, j))⟩
  | Sum.inr (Sum.inl (i, j)) =>
      -- Y_last: last layer, outer-inl inner-inr; j : Fin (H (Fin.last L) - r) cast to the layer's
      -- column width `Fin (H (lastLayer).succ - r)` via `H_lastLayer_succ`.
      ⟨lastLayer hL, Sum.inl (Sum.inr (i, (finCongr (by rw [H_lastLayer_succ H hL])) j))⟩
  | Sum.inr (Sum.inr (i, j)) =>
      -- Z_first: first layer, outer-inr
      ⟨firstLayer hL, Sum.inr (i, j)⟩

/-- A LEFT INVERSE of `regBoundaryToRegGauge` (defined on ALL of `RegGaugeIdx`, inverting the routing on
the image, defaulting elsewhere). Reads the block arm: outer-`inl` inner-`inl` → X,
outer-`inl` inner-`inr` → Y (column re-cast `H s.succ - r` to `H (Fin.last L) - r`
via `firstLayer`/`lastLayer` is only an identity on the image; off-image it lands in the X arm),
outer-`inr` → Z arm. Used only for `LeftInverse`, so the off-image behaviour is irrelevant. -/
def regGaugeDecode (H : Fin (L + 1) → ℕ) (r : ℕ) (hL : 1 ≤ L) :
    RegGaugeIdx H r → BoundaryPivotIdx H r
  | ⟨_, Sum.inl (Sum.inl (i, j))⟩ => Sum.inl (i, j)                          -- X arm (both indices `Fin r`)
  | ⟨s, Sum.inl (Sum.inr (i, j))⟩ =>
      -- Y arm: re-cast the column `j : Fin (H s.succ - r)` to `Fin (H (Fin.last L) - r)`. On the image
      -- (`s = lastLayer`) this inverts the route's `finCongr`; off-image (widths differ) it is unused.
      if h : H s.succ - r = H (Fin.last L) - r then Sum.inr (Sum.inl (i, (finCongr h) j))
      else Sum.inl (i, i)  -- off-image junk (`i : Fin r`); never hit on the image
  | ⟨s, Sum.inr (i, j)⟩ =>
      -- Z arm: re-cast the row `i : Fin (H s.castSucc - r)` to `Fin (H 0 - r)`. On the image
      -- (`s = firstLayer`, `.castSucc = 0`) identity; off-image unused.
      if h : H s.castSucc - r = H 0 - r then Sum.inr (Sum.inr ((finCongr h) i, j))
      else Sum.inl (j, j)  -- off-image junk (`j : Fin r`); never hit on the image

/-- **`regBoundaryToRegGauge` is INJECTIVE** (the controller's sharpening — the load-bearing early-check).
Distinct `BoundaryPivotIdx` coords land in distinct `RegGaugeIdx` entries: X_first/Z_first share layer 0
but differ in the OUTER sum-arm (`Sum.inl` vs `Sum.inr`); Y_last has layer-tag `Fin.last Lm ≠ 0`
(needs `1 ≤ L`, so `Lm ≥ 0` and `Fin.last Lm = ⟨Lm,_⟩`; `0 = Fin.last Lm` would force `Lm = 0`, handled).
This is what makes the reg-half read INJECTIVE, so the `Σ_s δX_s` sandwich does NOT collapse two reg
coords (X_first is the only X in the reg image). -/
theorem regBoundaryToRegGauge_injective (H : Fin (L + 1) → ℕ) (r : ℕ) (hL : 1 ≤ L) :
    Function.Injective (regBoundaryToRegGauge H r hL) := by
  -- `firstLayer ≠ lastLayer` (X/Z at layer 0, Y at layer L-1 ≥ 1; equal only if L = 1 but then the
  -- X/Z-vs-Y arms still differ by the OUTER sum-arm, so no collision). The Sigma + Sum tags are
  -- distinct across arms; within an arm, the component prods inject.
  -- `firstLayer ≠ lastLayer` unless `L = 1`; and the X/Z arms differ from each other and from Y by the
  -- OUTER sum-arm. So whenever the layer-tags coincide (L = 1), the sum-tags separate the arms.
  -- Via a LEFT INVERSE `regGaugeDecode` (avoids the per-case Sigma/Sum/HEq chase): `decode` reads the
  -- `⟨layer, sum-arm⟩` of a `RegGaugeIdx` and reconstructs the `BoundaryPivotIdx` arm (the Y cast
  -- inverted by `finCongr` symm), defaulting non-boundary entries to the X arm. `decode ∘ route = id`
  -- is structural per arm (term-mode `match` equation lemmas), so `route` is injective.
  -- The two `dif` conditions hold on the image: Y at `lastLayer` (`H_lastLayer_succ`), Z at `firstLayer`
  -- (`.castSucc` of `⟨0,_⟩` is `⟨0,_⟩`, so `H .. = H 0`). Each `- r`-shifted by `congrArg (· - r)`.
  have hY : H (lastLayer hL).succ - r = H (Fin.last L) - r := by rw [H_lastLayer_succ H hL]
  have hZ : H ((firstLayer hL).castSucc) - r = H 0 - r := by
    have hc : (firstLayer hL).castSucc = (0 : Fin (L + 1)) := by
      apply Fin.ext; simp [firstLayer, Fin.castSucc, Fin.castAdd, Fin.castLE]
    rw [hc]
  -- `decode (route b) = b` holds DEFINITIONALLY per arm: X reads straight back; Y/Z fire the `dif`
  -- (`hY`/`hZ`) and the `finCongr` round-trip collapses (the inner `finCongr` of the route composes
  -- with the decode's `finCongr` to `Fin.cast rfl = id`). All three close by reduction.
  -- VIA the LEFT INVERSE `regGaugeDecode` (`decode ∘ route = id`): X reads straight back (`rfl`); Y/Z
  -- fire their `dif` (`hY`/`hZ`) and the `finCongr` round-trip collapses on the column/row index
  -- (val-preserving, `Fin.ext`).
  refine Function.LeftInverse.injective (g := regGaugeDecode H r hL) (fun b => ?_)
  rcases b with ⟨i, j⟩ | ⟨i, j⟩ | ⟨i, j⟩
  · rfl
  · rw [regBoundaryToRegGauge, regGaugeDecode, dif_pos hY]
    exact congrArg (fun x => Sum.inr (Sum.inl (i, x))) (Fin.ext (by simp [finCongr_apply]))
  · rw [regBoundaryToRegGauge, regGaugeDecode, dif_pos hZ]
    exact congrArg (fun x => Sum.inr (Sum.inr (x, j))) (Fin.ext (by simp [finCongr_apply]))

end DLNFibre.DLN.RLCT
