import DLNFibre.DLN.RLCT.Validate.RouteMSchurRectCover

/-!
# `DLNFibre.DLN.RLCT.Validate.RouteMSchurRectAngular` — the RECTANGULAR angular-ratio coordinate layer

The asymmetric (`Δ : Fin m → Fin n`) generalisation of the square angular-ratio machinery
(`RouteMSchurFiring`'s `eG` / `RmatG` / `piRatioG` / `RmatGnorm` / `slotMatG` / `cellR` / `zσG` / `zEG`),
with `Fin r × Fin r → Fin (m*n)` becoming `Fin m × Fin n → Fin (m*n)` and the carve slots
`(r−1)×(r−1) ⊕ (r−1) ⊕ (r−1)` becoming `(m−1)×(n−1) ⊕ (m−1) ⊕ (n−1)`. This is the COORDINATE substrate
that the rectangular per-chart carve stands on; NO threshold/analytic content (that is the downstream
`innerSGenCarve_rect_le` + the wrapper).

The slot-count identity: `(m−1)(n−1) + (m−1) + (n−1) = mn − 1 = N` (vs the square `(r−1)² + 2(r−1) = r²−1`).

This file establishes the angular matrix `RmatRect`, the radial ratio reshape `piRatioRect`, the
pivot-normalised `RmatRectNorm`, the slot-decode `slotMatRect`, the carve cell-map `cellR_rect`, and the
carve-slot bijection `zσRect` / reshape `zERect` with the `M22` / row-coupling / col-coupling readbacks.
-/

namespace DLNFibre.DLN.RLCT

open MeasureTheory Set
open scoped ENNReal BigOperators

/-! ## The matrix↔flat index equiv and the angular matrix -/

/-- The matrix↔flat index equiv `eRect m n : Fin m × Fin n ≃ Fin (m*n)`, matching `matToFlatRect`'s
index reindex. The asymmetric `eG`. -/
noncomputable def eRect (m n : ℕ) : Fin m × Fin n ≃ Fin (m * n) :=
  ((Equiv.sigmaEquivProd (Fin m) (Fin n)).symm).trans
    ((Equiv.sigmaEquivProd (Fin m) (Fin n)).trans finProdFinEquiv)

/-- The unflattened angular matrix on chart `p`: `RmatRect p y` is the `m×n` matrix with `R_p = 1`,
`R_k = y_k` (`k ≠ p`). The asymmetric `RmatG`. -/
noncomputable def RmatRect (m n : ℕ) (p : Fin (m * n)) (y : Fin (m * n) → ℝ) : Fin m → Fin n → ℝ :=
  (matToFlatRect m n).symm (fun i => if i = p then 1 else y i)

/-- `RmatRect m n p y i j = if eRect m n (i,j) = p then 1 else y (eRect m n (i,j))`. -/
theorem RmatRect_entry (m n : ℕ) (p : Fin (m * n)) (y : Fin (m * n) → ℝ) (i : Fin m) (j : Fin n) :
    RmatRect m n p y i j = if eRect m n (i, j) = p then 1 else y (eRect m n (i, j)) := rfl

/-- The pivot entry of `RmatRect m n p y` is `1` (at the matrix index `(eRect m n).symm p`). -/
theorem RmatRect_pivot (m n : ℕ) (p : Fin (m * n)) (y : Fin (m * n) → ℝ) :
    RmatRect m n p y ((eRect m n).symm p).1 ((eRect m n).symm p).2 = 1 := by
  rw [RmatRect_entry, if_pos]
  rw [show (((eRect m n).symm p).1, ((eRect m n).symm p).2) = (eRect m n).symm p from rfl,
    Equiv.apply_symm_apply]

/-- `|RmatRect m n p y i j| ≤ 1` on the ratio chart `|y_k| ≤ 1` (`k ≠ p`); pivot entry `= 1`. -/
theorem RmatRect_entry_le (m n : ℕ) (p : Fin (m * n)) (y : Fin (m * n) → ℝ)
    (hy : ∀ k, k ≠ p → |y k| ≤ 1) (i : Fin m) (j : Fin n) : |RmatRect m n p y i j| ≤ 1 := by
  rw [RmatRect_entry]
  by_cases h : eRect m n (i, j) = p
  · rw [if_pos h]; norm_num
  · rw [if_neg h]; exact hy _ h

/-! ## The radial ratio reshape `piRatioRect` (the `mn`-chart pivot-axis split) -/

/-- The radial ratio reshape `piRatioRect m n N : (Fin (m*n) → ℝ) ≃ᵐ ℝ × (Fin N → ℝ)` (pivot-axis ×
ratios), via `finCongr hN` + `piFinSuccAbove`. Identical body to `piRatioG` at `N+1 = m*n`. -/
noncomputable def piRatioRect (m n N : ℕ) (hN : m * n = N + 1) (p : Fin (m * n)) :
    (Fin (m * n) → ℝ) ≃ᵐ ℝ × (Fin N → ℝ) :=
  (MeasurableEquiv.arrowCongr' (finCongr hN) (MeasurableEquiv.refl ℝ)).trans
    (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (N + 1) => ℝ) (finCongr hN p))

theorem measurePreserving_piRatioRect (m n N : ℕ) (hN : m * n = N + 1) (p : Fin (m * n)) :
    MeasurePreserving (piRatioRect m n N hN p) (volume : Measure (Fin (m * n) → ℝ))
      (volume : Measure (ℝ × (Fin N → ℝ))) := by
  unfold piRatioRect
  refine MeasurePreserving.trans ?_
    (volume_preserving_piFinSuccAbove (fun _ : Fin (N + 1) => ℝ) (finCongr hN p))
  exact volume_preserving_arrowCongr' (finCongr hN) (MeasurableEquiv.refl ℝ) (MeasurePreserving.id _)

/-- `(piRatioRect …).symm (a,z) k = insertNth (finCongr hN p) (a,z) (finCongr hN k)`. -/
theorem piRatioRect_symm_apply (m n N : ℕ) (hN : m * n = N + 1) (p : Fin (m * n))
    (a : ℝ) (z : Fin N → ℝ) (k : Fin (m * n)) :
    (piRatioRect m n N hN p).symm (a, z) k
      = Fin.insertNthEquiv (fun _ : Fin (N + 1) => ℝ) (finCongr hN p) (a, z) (finCongr hN k) := by
  show (MeasurableEquiv.arrowCongr' (finCongr hN) (MeasurableEquiv.refl ℝ)).symm
      ((MeasurableEquiv.piFinSuccAbove (fun _ : Fin (N + 1) => ℝ) (finCongr hN p)).symm (a, z)) k = _
  rw [MeasurableEquiv.piFinSuccAbove_symm_apply]
  rfl

/-- The pivot value of the read-back is `a`. -/
theorem piRatioRect_symm_pivot (m n N : ℕ) (hN : m * n = N + 1) (p : Fin (m * n))
    (a : ℝ) (z : Fin N → ℝ) : (piRatioRect m n N hN p).symm (a, z) p = a := by
  rw [piRatioRect_symm_apply]
  simp [Fin.insertNthEquiv, Fin.insertNth_apply_same]

/-- Off the pivot the read-back is `a`-independent. -/
theorem piRatioRect_symm_offpivot (m n N : ℕ) (hN : m * n = N + 1) (p : Fin (m * n))
    (a a' : ℝ) (z : Fin N → ℝ) (k : Fin (m * n)) (hk : k ≠ p) :
    (piRatioRect m n N hN p).symm (a, z) k = (piRatioRect m n N hN p).symm (a', z) k := by
  rw [piRatioRect_symm_apply, piRatioRect_symm_apply]
  have hne : finCongr hN k ≠ finCongr hN p := fun h => hk ((finCongr hN).injective h)
  obtain ⟨j, hj⟩ := Fin.exists_succAbove_eq hne
  rw [← hj]
  simp [Fin.insertNthEquiv, Fin.insertNth_apply_succAbove]

end DLNFibre.DLN.RLCT
