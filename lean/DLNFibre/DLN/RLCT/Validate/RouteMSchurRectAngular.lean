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

/-- Off the pivot, the ratio read-back lands in `[−1,1]` on the ratio box. -/
theorem piRatioRect_symm_offpivot_le (m n N : ℕ) (hN : m * n = N + 1) (p : Fin (m * n))
    (z : Fin N → ℝ) (hz : z ∈ Set.univ.pi (fun _ : Fin N => Set.Icc (-1 : ℝ) 1))
    (k : Fin (m * n)) (hk : k ≠ p) :
    |((piRatioRect m n N hN p).symm (0, z)) k| ≤ 1 := by
  have hne : finCongr hN k ≠ finCongr hN p := fun h => hk ((finCongr hN).injective h)
  obtain ⟨j, hj⟩ := Fin.exists_succAbove_eq hne
  have hk_eq : k = (finCongr hN).symm ((finCongr hN p).succAbove j) := by
    rw [hj]; exact ((finCongr hN).symm_apply_apply k).symm
  have hval : ((piRatioRect m n N hN p).symm (0, z)) k = z j := by
    rw [piRatioRect_symm_apply, hk_eq]
    have : finCongr hN ((finCongr hN).symm ((finCongr hN p).succAbove j))
        = (finCongr hN p).succAbove j := (finCongr hN).apply_symm_apply _
    rw [this]
    simp [Fin.insertNthEquiv, Fin.insertNth_apply_succAbove]
  rw [hval]
  have := hz j (Set.mem_univ j); rw [Set.mem_Icc, ← abs_le] at this; exact this

/-- `(piRatioRect … y).1 = y pivot` — the forward map's pivot-axis component. -/
theorem piRatioRect_apply_fst (m n N : ℕ) (hN : m * n = N + 1) (p : Fin (m * n)) (y : Fin (m * n) → ℝ) :
    (piRatioRect m n N hN p y).1 = y p := by
  show ((MeasurableEquiv.piFinSuccAbove (fun _ : Fin (N + 1) => ℝ) (finCongr hN p))
        ((MeasurableEquiv.arrowCongr' (finCongr hN) (MeasurableEquiv.refl ℝ)) y)).1 = y p
  simp only [MeasurableEquiv.piFinSuccAbove, MeasurableEquiv.coe_mk, Fin.insertNthEquiv]
  rfl

/-- `(piRatioRect … y).2 j = y (the succAbove-decoded index)`. -/
theorem piRatioRect_apply_snd (m n N : ℕ) (hN : m * n = N + 1) (p : Fin (m * n)) (y : Fin (m * n) → ℝ)
    (j : Fin N) :
    (piRatioRect m n N hN p y).2 j = y ((finCongr hN).symm ((finCongr hN p).succAbove j)) := by
  show ((MeasurableEquiv.piFinSuccAbove (fun _ : Fin (N + 1) => ℝ) (finCongr hN p))
        ((MeasurableEquiv.arrowCongr' (finCongr hN) (MeasurableEquiv.refl ℝ)) y)).2 j = _
  simp only [MeasurableEquiv.piFinSuccAbove, MeasurableEquiv.coe_mk, Fin.insertNthEquiv]
  rfl

/-- The decoded ratio index is never the pivot. -/
theorem piRatioRect_ratioIdx_ne (m n N : ℕ) (hN : m * n = N + 1) (p : Fin (m * n)) (j : Fin N) :
    (finCongr hN).symm ((finCongr hN p).succAbove j) ≠ p := by
  intro h
  apply Fin.succAbove_ne (finCongr hN p) j
  have h' : finCongr hN ((finCongr hN).symm ((finCongr hN p).succAbove j)) = finCongr hN p := by
    rw [h]
  rwa [(finCongr hN).apply_symm_apply] at h'

/-! ## The pivot-normalised angular matrix `RmatRectNorm` -/

/-- The pivot-normalised angular matrix: `RmatRectNorm m n p z a b = RmatRect (…symm(0,z)) (σr a) (σc b)`
with `σr = swap r₀ 0` on `Fin m`, `σc = swap c₀ 0` on `Fin n`, `(r₀,c₀) = (eRect m n).symm p`. Pivot `1`
at `(0,0)`. Needs `1 ≤ m, 1 ≤ n` for the `⟨0,_⟩` indices. The asymmetric `RmatGnorm`. -/
noncomputable def RmatRectNorm (m n N : ℕ) (hN : m * n = N + 1) (hm : 1 ≤ m) (hn : 1 ≤ n)
    (p : Fin (m * n)) (z : Fin N → ℝ) : Fin m → Fin n → ℝ :=
  fun a b => RmatRect m n p ((piRatioRect m n N hN p).symm (0, z))
    ((Equiv.swap ((eRect m n).symm p).1 ⟨0, by omega⟩) a)
    ((Equiv.swap ((eRect m n).symm p).2 ⟨0, by omega⟩) b)

/-- `RmatRectNorm … z ⟨0⟩ ⟨0⟩ = 1`. -/
theorem RmatRectNorm_pivot (m n N : ℕ) (hN : m * n = N + 1) (hm : 1 ≤ m) (hn : 1 ≤ n)
    (p : Fin (m * n)) (z : Fin N → ℝ) :
    RmatRectNorm m n N hN hm hn p z ⟨0, by omega⟩ ⟨0, by omega⟩ = 1 := by
  unfold RmatRectNorm
  rw [Equiv.swap_apply_right, Equiv.swap_apply_right, RmatRect_entry, if_pos]
  rw [show (((eRect m n).symm p).1, ((eRect m n).symm p).2) = (eRect m n).symm p from rfl,
    Equiv.apply_symm_apply]

/-- The matrix index of `(σr a, σc b)` is the pivot `p` iff `(a,b) = (0,0)`; off `(0,0)` it is `≠ p`. -/
theorem RmatRectNorm_offpivot_idx (m n : ℕ) (hm : 1 ≤ m) (hn : 1 ≤ n) (p : Fin (m * n))
    (a : Fin m) (b : Fin n) (hab : ¬ (a = ⟨0, by omega⟩ ∧ b = ⟨0, by omega⟩)) :
    eRect m n ((Equiv.swap ((eRect m n).symm p).1 ⟨0, by omega⟩) a,
        (Equiv.swap ((eRect m n).symm p).2 ⟨0, by omega⟩) b) ≠ p := by
  set σr := Equiv.swap ((eRect m n).symm p).1 (⟨0, by omega⟩ : Fin m) with hσr
  set σc := Equiv.swap ((eRect m n).symm p).2 (⟨0, by omega⟩ : Fin n) with hσc
  have hσr0 : σr ⟨0, by omega⟩ = ((eRect m n).symm p).1 := by rw [hσr, Equiv.swap_apply_right]
  have hσc0 : σc ⟨0, by omega⟩ = ((eRect m n).symm p).2 := by rw [hσc, Equiv.swap_apply_right]
  have hpe : eRect m n (((eRect m n).symm p).1, ((eRect m n).symm p).2) = p := by
    rw [show (((eRect m n).symm p).1, ((eRect m n).symm p).2) = (eRect m n).symm p from rfl,
      Equiv.apply_symm_apply]
  intro heq
  rw [← hpe] at heq
  obtain ⟨hi, hj⟩ := Prod.mk.injEq .. ▸ (eRect m n).injective heq
  rw [← hσr0] at hi; rw [← hσc0] at hj
  exact hab ⟨σr.injective hi, σc.injective hj⟩

/-- Off-`(0,0)` entries of `RmatRectNorm … z` are `z`-components, hence `|·| ≤ 1` on `[−1,1]^N`. -/
theorem RmatRectNorm_offpivot_le (m n N : ℕ) (hN : m * n = N + 1) (hm : 1 ≤ m) (hn : 1 ≤ n)
    (p : Fin (m * n)) (z : Fin N → ℝ) (hz : z ∈ Set.univ.pi (fun _ : Fin N => Set.Icc (-1 : ℝ) 1))
    (a : Fin m) (b : Fin n) (hab : ¬ (a = ⟨0, by omega⟩ ∧ b = ⟨0, by omega⟩)) :
    |RmatRectNorm m n N hN hm hn p z a b| ≤ 1 := by
  unfold RmatRectNorm
  rw [RmatRect_entry, if_neg (RmatRectNorm_offpivot_idx m n hm hn p a b hab)]
  exact piRatioRect_symm_offpivot_le m n N hN p z hz _ (RmatRectNorm_offpivot_idx m n hm hn p a b hab)

/-! ## The slot decode `slotMatRect` -/

/-- The `z`-slot of a matrix cell `(a,b) ≠ (0,0)`: the `Fin N` index whose `piRatioRect`-decode is
`eRect (σr a, σc b)`. The asymmetric `slotMatG`. -/
noncomputable def slotMatRect (m n N : ℕ) (hN : m * n = N + 1) (hm : 1 ≤ m) (hn : 1 ≤ n)
    (hmn : 2 ≤ m * n) (p : Fin (m * n)) (a : Fin m) (b : Fin n) : Fin N :=
  if h : eRect m n ((Equiv.swap ((eRect m n).symm p).1 ⟨0, by omega⟩) a,
      (Equiv.swap ((eRect m n).symm p).2 ⟨0, by omega⟩) b) ≠ p then
    (Fin.exists_succAbove_eq (show
      finCongr hN (eRect m n ((Equiv.swap ((eRect m n).symm p).1 ⟨0, by omega⟩) a,
        (Equiv.swap ((eRect m n).symm p).2 ⟨0, by omega⟩) b))
      ≠ finCongr hN p from fun he => h ((finCongr hN).injective he))).choose
  else ⟨0, by omega⟩

/-- The defining spec of `slotMatRect`: `(finCongr hN p).succAbove (slotMatRect … a b)
= finCongr hN (eRect (σr a, σc b))`. -/
theorem slotMatRect_spec (m n N : ℕ) (hN : m * n = N + 1) (hm : 1 ≤ m) (hn : 1 ≤ n)
    (hmn : 2 ≤ m * n) (p : Fin (m * n)) (a : Fin m) (b : Fin n)
    (hab : ¬ (a = ⟨0, by omega⟩ ∧ b = ⟨0, by omega⟩)) :
    (finCongr hN p).succAbove (slotMatRect m n N hN hm hn hmn p a b)
      = finCongr hN (eRect m n ((Equiv.swap ((eRect m n).symm p).1 ⟨0, by omega⟩) a,
          (Equiv.swap ((eRect m n).symm p).2 ⟨0, by omega⟩) b)) := by
  have hidx : eRect m n ((Equiv.swap ((eRect m n).symm p).1 ⟨0, by omega⟩) a,
      (Equiv.swap ((eRect m n).symm p).2 ⟨0, by omega⟩) b) ≠ p :=
    RmatRectNorm_offpivot_idx m n hm hn p a b hab
  have hne : finCongr hN (eRect m n ((Equiv.swap ((eRect m n).symm p).1 ⟨0, by omega⟩) a,
      (Equiv.swap ((eRect m n).symm p).2 ⟨0, by omega⟩) b)) ≠ finCongr hN p :=
    fun he => hidx ((finCongr hN).injective he)
  rw [slotMatRect, dif_pos hidx]
  exact (Fin.exists_succAbove_eq hne).choose_spec

/-- The read-back: `RmatRectNorm … z a b = z (slotMatRect … a b)` for `(a,b) ≠ (0,0)`. -/
theorem RmatRectNorm_eq_slot (m n N : ℕ) (hN : m * n = N + 1) (hm : 1 ≤ m) (hn : 1 ≤ n)
    (hmn : 2 ≤ m * n) (p : Fin (m * n)) (z : Fin N → ℝ) (a : Fin m) (b : Fin n)
    (hab : ¬ (a = ⟨0, by omega⟩ ∧ b = ⟨0, by omega⟩)) :
    RmatRectNorm m n N hN hm hn p z a b = z (slotMatRect m n N hN hm hn hmn p a b) := by
  set σr := Equiv.swap ((eRect m n).symm p).1 (⟨0, by omega⟩ : Fin m) with hσr
  set σc := Equiv.swap ((eRect m n).symm p).2 (⟨0, by omega⟩ : Fin n) with hσc
  have hidx : eRect m n (σr a, σc b) ≠ p := RmatRectNorm_offpivot_idx m n hm hn p a b hab
  have hentry : RmatRectNorm m n N hN hm hn p z a b
      = (piRatioRect m n N hN p).symm (0, z) (eRect m n (σr a, σc b)) := by
    rw [RmatRectNorm, RmatRect_entry, if_neg hidx]
  rw [hentry]
  have hne : finCongr hN (eRect m n (σr a, σc b)) ≠ finCongr hN p :=
    fun he => hidx ((finCongr hN).injective he)
  have hslot : slotMatRect m n N hN hm hn hmn p a b = (Fin.exists_succAbove_eq hne).choose := by
    rw [slotMatRect, dif_pos hidx]
  have hspec : (finCongr hN p).succAbove (slotMatRect m n N hN hm hn hmn p a b)
      = finCongr hN (eRect m n (σr a, σc b)) := by
    rw [hslot]; exact (Fin.exists_succAbove_eq hne).choose_spec
  rw [piRatioRect_symm_apply, ← hspec]
  simp [Fin.insertNthEquiv, Fin.insertNth_apply_succAbove]

/-! ## The carve cell enumeration `cellR_rect` and the bg-shift -/

/-- The enumeration of the off-`(0,0)` cells of `Fin m × Fin n`: `inl (a,b) ↦ (a+1, b+1)` (M22),
`inr (inl a) ↦ (a+1, 0)` (row-coupling g), `inr (inr b) ↦ (0, b+1)` (col-coupling b). Needs
`1 ≤ m, 1 ≤ n`. The asymmetric `cellR`. -/
def cellR_rect (m n : ℕ) (hm : 1 ≤ m) (hn : 1 ≤ n) :
    (Fin (m - 1) × Fin (n - 1)) ⊕ (Fin (m - 1) ⊕ Fin (n - 1)) → Fin m × Fin n
  | Sum.inl (a, b) => (⟨(a : ℕ) + 1, by omega⟩, ⟨(b : ℕ) + 1, by omega⟩)
  | Sum.inr (Sum.inl a) => (⟨(a : ℕ) + 1, by omega⟩, ⟨0, by omega⟩)
  | Sum.inr (Sum.inr b) => (⟨0, by omega⟩, ⟨(b : ℕ) + 1, by omega⟩)

/-- `cellR_rect` lands on non-`(0,0)` cells. -/
theorem cellR_rect_ne_zero (m n : ℕ) (hm : 1 ≤ m) (hn : 1 ≤ n)
    (s : (Fin (m - 1) × Fin (n - 1)) ⊕ (Fin (m - 1) ⊕ Fin (n - 1))) :
    ¬ ((cellR_rect m n hm hn s).1 = ⟨0, by omega⟩ ∧ (cellR_rect m n hm hn s).2 = ⟨0, by omega⟩) := by
  rcases s with ⟨a, b⟩ | (a | b) <;> simp [cellR_rect, Fin.ext_iff]

/-- `cellR_rect` is injective. -/
theorem cellR_rect_injective (m n : ℕ) (hm : 1 ≤ m) (hn : 1 ≤ n) :
    Function.Injective (cellR_rect m n hm hn) := by
  rintro (⟨a1, b1⟩ | (a1 | b1)) (⟨a2, b2⟩ | (a2 | b2)) h <;>
    simp only [cellR_rect, Prod.mk.injEq, Fin.ext_iff] at h
  · obtain ⟨h1, h2⟩ := h
    have ea : a1 = a2 := Fin.ext (by omega)
    have eb : b1 = b2 := Fin.ext (by omega)
    subst ea; subst eb; rfl
  · omega
  · omega
  · omega
  · have ea : a1 = a2 := Fin.ext (by omega); subst ea; rfl
  · omega
  · omega
  · omega
  · have eb : b1 = b2 := Fin.ext (by omega); subst eb; rfl

/-- The bg-shift matrix `g·bᵀ` from the `(g,b)`-cube `v : Fin (m-1) ⊕ Fin (n-1) → ℝ`:
`bgShiftRect v a b = v (inl a) · v (inr b)` (the rank-1 Cramer shift at `j=1`). `Sc : (m-1)×(n-1)`. -/
noncomputable def bgShiftRect (m n : ℕ) (v : Fin (m - 1) ⊕ Fin (n - 1) → ℝ) :
    Matrix (Fin (m - 1)) (Fin (n - 1)) ℝ :=
  fun a b => v (Sum.inl a) * v (Sum.inr b)

/-- `|bgShiftRect m n v a b| ≤ 1` when `|v| ≤ 1`. -/
theorem bgShiftRect_entry_le (m n : ℕ) (v : Fin (m - 1) ⊕ Fin (n - 1) → ℝ) (hv : ∀ s, |v s| ≤ 1)
    (a : Fin (m - 1)) (b : Fin (n - 1)) : |bgShiftRect m n v a b| ≤ 1 := by
  rw [bgShiftRect, abs_mul]
  calc |v (Sum.inl a)| * |v (Sum.inr b)| ≤ 1 * 1 :=
        mul_le_mul (hv _) (hv _) (abs_nonneg _) (by norm_num)
    _ = 1 := by norm_num

/-! ## The carve-slot bijection `zσRect` / reshape `zERect` and the carve readbacks -/

/-- The slot-composition `s ↦ slotMatRect p (cellR_rect s).1 (cellR_rect s).2 : (M22 ⊕ g ⊕ b) → Fin N`
is injective: `slotMatRect_spec` decodes the slot to `finCongr hN (eRect (σr cell, σc cell))`, injective
via `eRect`/swap/`finCongr`/`succAbove` injectivity, then `cellR_rect_injective`. -/
theorem slotFunRect_injective (m n N : ℕ) (hN : m * n = N + 1) (hm : 1 ≤ m) (hn : 1 ≤ n)
    (hmn : 2 ≤ m * n) (p : Fin (m * n)) :
    Function.Injective
      (fun s : (Fin (m - 1) × Fin (n - 1)) ⊕ (Fin (m - 1) ⊕ Fin (n - 1)) =>
        slotMatRect m n N hN hm hn hmn p (cellR_rect m n hm hn s).1 (cellR_rect m n hm hn s).2) := by
  intro s1 s2 hs
  simp only [] at hs
  have e1 := slotMatRect_spec m n N hN hm hn hmn p (cellR_rect m n hm hn s1).1
    (cellR_rect m n hm hn s1).2 (cellR_rect_ne_zero m n hm hn s1)
  have e2 := slotMatRect_spec m n N hN hm hn hmn p (cellR_rect m n hm hn s2).1
    (cellR_rect m n hm hn s2).2 (cellR_rect_ne_zero m n hm hn s2)
  rw [hs, e2] at e1
  have hcell : ((Equiv.swap ((eRect m n).symm p).1 ⟨0, by omega⟩) (cellR_rect m n hm hn s2).1,
      (Equiv.swap ((eRect m n).symm p).2 ⟨0, by omega⟩) (cellR_rect m n hm hn s2).2)
      = ((Equiv.swap ((eRect m n).symm p).1 ⟨0, by omega⟩) (cellR_rect m n hm hn s1).1,
        (Equiv.swap ((eRect m n).symm p).2 ⟨0, by omega⟩) (cellR_rect m n hm hn s1).2) :=
    (eRect m n).injective ((finCongr hN).injective e1)
  rw [Prod.mk.injEq] at hcell
  obtain ⟨hi, hj⟩ := hcell
  exact (cellR_rect_injective m n hm hn
    (Prod.ext ((Equiv.swap _ _).injective hi) ((Equiv.swap _ _).injective hj))).symm

/-- The carve-slot index count `card ((M22) ⊕ (g ⊕ b)) = (m−1)(n−1) + (m−1) + (n−1) = mn − 1 = N`. -/
theorem slotFunRect_card (m n N : ℕ) (hN : m * n = N + 1) (hm : 1 ≤ m) (hn : 1 ≤ n) :
    Fintype.card ((Fin (m - 1) × Fin (n - 1)) ⊕ (Fin (m - 1) ⊕ Fin (n - 1))) = N := by
  simp only [Fintype.card_sum, Fintype.card_prod, Fintype.card_fin]
  obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
  obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
  simp only [Nat.add_sub_cancel]
  have : (m' + 1) * (n' + 1) = N + 1 := hN
  nlinarith [this]

/-- **The carve-slot bijection** `(M22 ⊕ g ⊕ b) ≃ Fin N`. -/
theorem slotFunRect_bijective (m n N : ℕ) (hN : m * n = N + 1) (hm : 1 ≤ m) (hn : 1 ≤ n)
    (hmn : 2 ≤ m * n) (p : Fin (m * n)) :
    Function.Bijective
      (fun s : (Fin (m - 1) × Fin (n - 1)) ⊕ (Fin (m - 1) ⊕ Fin (n - 1)) =>
        slotMatRect m n N hN hm hn hmn p (cellR_rect m n hm hn s).1 (cellR_rect m n hm hn s).2) := by
  rw [Fintype.bijective_iff_injective_and_card]
  refine ⟨slotFunRect_injective m n N hN hm hn hmn p, ?_⟩
  rw [Fintype.card_fin]; exact slotFunRect_card m n N hN hm hn

/-- The slot equiv `Fin N ≃ (M22 ⊕ g ⊕ b)`. -/
noncomputable def zσRect (m n N : ℕ) (hN : m * n = N + 1) (hm : 1 ≤ m) (hn : 1 ≤ n)
    (hmn : 2 ≤ m * n) (p : Fin (m * n)) :
    Fin N ≃ ((Fin (m - 1) × Fin (n - 1)) ⊕ (Fin (m - 1) ⊕ Fin (n - 1))) :=
  (Equiv.ofBijective _ (slotFunRect_bijective m n N hN hm hn hmn p)).symm

/-- The reshape `zERect` splitting the ratios `z` into the `M22`-cube and the `(g,b)`-cube. -/
noncomputable def zERect (m n N : ℕ) (hN : m * n = N + 1) (hm : 1 ≤ m) (hn : 1 ≤ n)
    (hmn : 2 ≤ m * n) (p : Fin (m * n)) :
    (Fin N → ℝ) ≃ᵐ (((Fin (m - 1) × Fin (n - 1)) → ℝ) × ((Fin (m - 1) ⊕ Fin (n - 1)) → ℝ)) :=
  (MeasurableEquiv.piCongrLeft
    (fun _ : (Fin (m - 1) × Fin (n - 1)) ⊕ (Fin (m - 1) ⊕ Fin (n - 1)) => ℝ)
    (zσRect m n N hN hm hn hmn p)).trans
    (MeasurableEquiv.sumPiEquivProdPi
      (fun _ : (Fin (m - 1) × Fin (n - 1)) ⊕ (Fin (m - 1) ⊕ Fin (n - 1)) => ℝ))

theorem measurePreserving_zERect (m n N : ℕ) (hN : m * n = N + 1) (hm : 1 ≤ m) (hn : 1 ≤ n)
    (hmn : 2 ≤ m * n) (p : Fin (m * n)) :
    MeasurePreserving (zERect m n N hN hm hn hmn p) (volume : Measure (Fin N → ℝ))
      (volume : Measure (((Fin (m - 1) × Fin (n - 1)) → ℝ) × ((Fin (m - 1) ⊕ Fin (n - 1)) → ℝ))) :=
  (volume_measurePreserving_piCongrLeft
    (fun _ : (Fin (m - 1) × Fin (n - 1)) ⊕ (Fin (m - 1) ⊕ Fin (n - 1)) => ℝ)
    (zσRect m n N hN hm hn hmn p)).trans
    (volume_measurePreserving_sumPiEquivProdPi
      (fun _ : (Fin (m - 1) × Fin (n - 1)) ⊕ (Fin (m - 1) ⊕ Fin (n - 1)) => ℝ))

/-- The `zERect.symm` read-back: `(zERect.symm (M,v)) k = Sum.elim M v (zσRect k)`. -/
theorem zERect_symm_apply (m n N : ℕ) (hN : m * n = N + 1) (hm : 1 ≤ m) (hn : 1 ≤ n)
    (hmn : 2 ≤ m * n) (p : Fin (m * n))
    (M : (Fin (m - 1) × Fin (n - 1)) → ℝ) (v : (Fin (m - 1) ⊕ Fin (n - 1)) → ℝ) (k : Fin N) :
    (zERect m n N hN hm hn hmn p).symm (M, v) k = Sum.elim M v (zσRect m n N hN hm hn hmn p k) := by
  have hdec : (zERect m n N hN hm hn hmn p).symm (M, v)
      = (MeasurableEquiv.piCongrLeft
          (fun _ : (Fin (m - 1) × Fin (n - 1)) ⊕ (Fin (m - 1) ⊕ Fin (n - 1)) => ℝ)
          (zσRect m n N hN hm hn hmn p)).symm (Sum.elim M v) := rfl
  rw [hdec]
  set e := zσRect m n N hN hm hn hmn p
  have h1 : MeasurableEquiv.piCongrLeft
      (fun _ : (Fin (m - 1) × Fin (n - 1)) ⊕ (Fin (m - 1) ⊕ Fin (n - 1)) => ℝ) e
      ((MeasurableEquiv.piCongrLeft
        (fun _ : (Fin (m - 1) × Fin (n - 1)) ⊕ (Fin (m - 1) ⊕ Fin (n - 1)) => ℝ) e).symm
        (Sum.elim M v)) (e k) = Sum.elim M v (e k) := by
    rw [MeasurableEquiv.apply_symm_apply]
  rw [MeasurableEquiv.piCongrLeft_apply_apply] at h1
  exact h1

/-- `zσRect` round-trips on the slot of a cell. -/
theorem zσRect_slot (m n N : ℕ) (hN : m * n = N + 1) (hm : 1 ≤ m) (hn : 1 ≤ n)
    (hmn : 2 ≤ m * n) (p : Fin (m * n))
    (s : (Fin (m - 1) × Fin (n - 1)) ⊕ (Fin (m - 1) ⊕ Fin (n - 1))) :
    zσRect m n N hN hm hn hmn p (slotMatRect m n N hN hm hn hmn p
      (cellR_rect m n hm hn s).1 (cellR_rect m n hm hn s).2) = s :=
  (Equiv.ofBijective _ (slotFunRect_bijective m n N hN hm hn hmn p)).symm_apply_apply s

/-- `(zERect z).1 ik = z (zσRect.symm (inl ik))` — the forward `zERect` reads the `M22`-cube slot. -/
theorem zERect_fst_apply (m n N : ℕ) (hN : m * n = N + 1) (hm : 1 ≤ m) (hn : 1 ≤ n)
    (hmn : 2 ≤ m * n) (pv : Fin (m * n)) (z : Fin N → ℝ) (ik : Fin (m - 1) × Fin (n - 1)) :
    (zERect m n N hN hm hn hmn pv z).1 ik = z ((zσRect m n N hN hm hn hmn pv).symm (Sum.inl ik)) := by
  have : (zERect m n N hN hm hn hmn pv z).1 ik
      = MeasurableEquiv.piCongrLeft
          (fun _ : (Fin (m - 1) × Fin (n - 1)) ⊕ (Fin (m - 1) ⊕ Fin (n - 1)) => ℝ)
          (zσRect m n N hN hm hn hmn pv) z (Sum.inl ik) := rfl
  rw [this, ← Equiv.apply_symm_apply (zσRect m n N hN hm hn hmn pv) (Sum.inl ik),
    MeasurableEquiv.piCongrLeft_apply_apply, Equiv.apply_symm_apply]

/-- `(zERect z).2 s = z (zσRect.symm (inr s))` — the forward `zERect` reads the `(g,b)`-cube slot. -/
theorem zERect_snd_apply (m n N : ℕ) (hN : m * n = N + 1) (hm : 1 ≤ m) (hn : 1 ≤ n)
    (hmn : 2 ≤ m * n) (pv : Fin (m * n)) (z : Fin N → ℝ) (s : Fin (m - 1) ⊕ Fin (n - 1)) :
    (zERect m n N hN hm hn hmn pv z).2 s = z ((zσRect m n N hN hm hn hmn pv).symm (Sum.inr s)) := by
  have : (zERect m n N hN hm hn hmn pv z).2 s
      = MeasurableEquiv.piCongrLeft
          (fun _ : (Fin (m - 1) × Fin (n - 1)) ⊕ (Fin (m - 1) ⊕ Fin (n - 1)) => ℝ)
          (zσRect m n N hN hm hn hmn pv) z (Sum.inr s) := rfl
  rw [this, ← Equiv.apply_symm_apply (zσRect m n N hN hm hn hmn pv) (Sum.inr s),
    MeasurableEquiv.piCongrLeft_apply_apply, Equiv.apply_symm_apply]

/-- M22-cell carve readback. -/
theorem RmatRectNorm_carve_M22 (m n N : ℕ) (hN : m * n = N + 1) (hm : 1 ≤ m) (hn : 1 ≤ n)
    (hmn : 2 ≤ m * n) (p : Fin (m * n))
    (M : (Fin (m - 1) × Fin (n - 1)) → ℝ) (v : (Fin (m - 1) ⊕ Fin (n - 1)) → ℝ)
    (a : Fin (m - 1)) (b : Fin (n - 1)) :
    RmatRectNorm m n N hN hm hn p ((zERect m n N hN hm hn hmn p).symm (M, v))
        ⟨(a : ℕ) + 1, by omega⟩ ⟨(b : ℕ) + 1, by omega⟩ = M (a, b) := by
  have hab : ¬ ((⟨(a : ℕ) + 1, by omega⟩ : Fin m) = ⟨0, by omega⟩
      ∧ (⟨(b : ℕ) + 1, by omega⟩ : Fin n) = ⟨0, by omega⟩) := by simp [Fin.ext_iff]
  rw [RmatRectNorm_eq_slot m n N hN hm hn hmn p _ _ _ hab,
    show slotMatRect m n N hN hm hn hmn p ⟨(a : ℕ) + 1, by omega⟩ ⟨(b : ℕ) + 1, by omega⟩
      = slotMatRect m n N hN hm hn hmn p (cellR_rect m n hm hn (Sum.inl (a, b))).1
          (cellR_rect m n hm hn (Sum.inl (a, b))).2 from rfl,
    zERect_symm_apply, zσRect_slot]
  rfl

/-- g-cell carve readback. -/
theorem RmatRectNorm_carve_g (m n N : ℕ) (hN : m * n = N + 1) (hm : 1 ≤ m) (hn : 1 ≤ n)
    (hmn : 2 ≤ m * n) (p : Fin (m * n))
    (M : (Fin (m - 1) × Fin (n - 1)) → ℝ) (v : (Fin (m - 1) ⊕ Fin (n - 1)) → ℝ) (a : Fin (m - 1)) :
    RmatRectNorm m n N hN hm hn p ((zERect m n N hN hm hn hmn p).symm (M, v))
        ⟨(a : ℕ) + 1, by omega⟩ ⟨0, by omega⟩ = v (Sum.inl a) := by
  have hab : ¬ ((⟨(a : ℕ) + 1, by omega⟩ : Fin m) = ⟨0, by omega⟩
      ∧ (⟨0, by omega⟩ : Fin n) = ⟨0, by omega⟩) := by simp [Fin.ext_iff]
  rw [RmatRectNorm_eq_slot m n N hN hm hn hmn p _ _ _ hab,
    show slotMatRect m n N hN hm hn hmn p ⟨(a : ℕ) + 1, by omega⟩ ⟨0, by omega⟩
      = slotMatRect m n N hN hm hn hmn p (cellR_rect m n hm hn (Sum.inr (Sum.inl a))).1
          (cellR_rect m n hm hn (Sum.inr (Sum.inl a))).2 from rfl,
    zERect_symm_apply, zσRect_slot]
  rfl

/-- b-cell carve readback. -/
theorem RmatRectNorm_carve_b (m n N : ℕ) (hN : m * n = N + 1) (hm : 1 ≤ m) (hn : 1 ≤ n)
    (hmn : 2 ≤ m * n) (p : Fin (m * n))
    (M : (Fin (m - 1) × Fin (n - 1)) → ℝ) (v : (Fin (m - 1) ⊕ Fin (n - 1)) → ℝ) (b : Fin (n - 1)) :
    RmatRectNorm m n N hN hm hn p ((zERect m n N hN hm hn hmn p).symm (M, v))
        ⟨0, by omega⟩ ⟨(b : ℕ) + 1, by omega⟩ = v (Sum.inr b) := by
  have hab : ¬ ((⟨0, by omega⟩ : Fin m) = ⟨0, by omega⟩
      ∧ (⟨(b : ℕ) + 1, by omega⟩ : Fin n) = ⟨0, by omega⟩) := by simp [Fin.ext_iff]
  rw [RmatRectNorm_eq_slot m n N hN hm hn hmn p _ _ _ hab,
    show slotMatRect m n N hN hm hn hmn p ⟨0, by omega⟩ ⟨(b : ℕ) + 1, by omega⟩
      = slotMatRect m n N hN hm hn hmn p (cellR_rect m n hm hn (Sum.inr (Sum.inr b))).1
          (cellR_rect m n hm hn (Sum.inr (Sum.inr b))).2 from rfl,
    zERect_symm_apply, zσRect_slot]
  rfl

/-- **The carve-point Schur complement readback.** At `R = RmatRectNorm (zERect.symm (M,v))` (pivot
`R ⟨0⟩ ⟨0⟩ = 1`), the N2b (`j = 1`) Schur complement
`Sc a b = R ⟨1+a⟩ ⟨1+b⟩ − R ⟨1+a⟩ ⟨0⟩ · R ⟨0⟩ ⟨1+b⟩` reads off as `M (a,b) − v(inl a)·v(inr b)`. -/
theorem ScCarve_rect_eq (m n N : ℕ) (hN : m * n = N + 1) (hm : 1 ≤ m) (hn : 1 ≤ n)
    (hmn : 2 ≤ m * n) (p : Fin (m * n))
    (M : (Fin (m - 1) × Fin (n - 1)) → ℝ) (v : (Fin (m - 1) ⊕ Fin (n - 1)) → ℝ)
    (a : Fin (m - 1)) (b : Fin (n - 1)) :
    RmatRectNorm m n N hN hm hn p ((zERect m n N hN hm hn hmn p).symm (M, v))
        ⟨1 + (a : ℕ), by omega⟩ ⟨1 + (b : ℕ), by omega⟩
      - RmatRectNorm m n N hN hm hn p ((zERect m n N hN hm hn hmn p).symm (M, v))
          ⟨1 + (a : ℕ), by omega⟩ ⟨0, by omega⟩
        * RmatRectNorm m n N hN hm hn p ((zERect m n N hN hm hn hmn p).symm (M, v))
            ⟨0, by omega⟩ ⟨1 + (b : ℕ), by omega⟩
      = M (a, b) - bgShiftRect m n v a b := by
  have hia : (⟨1 + (a : ℕ), by omega⟩ : Fin m) = ⟨(a : ℕ) + 1, by omega⟩ := Fin.ext (Nat.add_comm 1 _)
  have hib : (⟨1 + (b : ℕ), by omega⟩ : Fin n) = ⟨(b : ℕ) + 1, by omega⟩ := Fin.ext (Nat.add_comm 1 _)
  have hM22 : RmatRectNorm m n N hN hm hn p ((zERect m n N hN hm hn hmn p).symm (M, v))
      ⟨1 + (a : ℕ), by omega⟩ ⟨1 + (b : ℕ), by omega⟩ = M (a, b) := by
    rw [hia, hib]; exact RmatRectNorm_carve_M22 m n N hN hm hn hmn p M v a b
  have hg : RmatRectNorm m n N hN hm hn p ((zERect m n N hN hm hn hmn p).symm (M, v))
      ⟨1 + (a : ℕ), by omega⟩ ⟨0, by omega⟩ = v (Sum.inl a) := by
    rw [hia]; exact RmatRectNorm_carve_g m n N hN hm hn hmn p M v a
  have hbb : RmatRectNorm m n N hN hm hn p ((zERect m n N hN hm hn hmn p).symm (M, v))
      ⟨0, by omega⟩ ⟨1 + (b : ℕ), by omega⟩ = v (Sum.inr b) := by
    rw [hib]; exact RmatRectNorm_carve_b m n N hN hm hn hmn p M v b
  rw [hM22, hg, hbb, bgShiftRect]

/-! ## The inner-`S` integral interface `innerSRect` + the pivot-normalised CoV (3b-norm) -/

/-- The inner angular `S`-integral at the angular matrix `RmatRect m n pv y`:
`innerSRect m n p c' T pv y = ∫_{S∈matBox n p T} frobSq (RmatRect · S)^{−c'}` (`S` is `n × p`, the
contracted dim `n` = `Δ`'s column count). The asymmetric `innerSGen`. -/
noncomputable def innerSRect (m n p : ℕ) (c' : ℝ) (T : ℝ) (pv : Fin (m * n)) (y : Fin (m * n) → ℝ) :
    ℝ≥0∞ :=
  ∫⁻ S in matBox n p T, ENNReal.ofReal ((frobSq (rmatMul (RmatRect m n pv y) S)) ^ (-c'))

/-- `innerSRect` is `y pv`-invariant: `RmatRect m n pv y` reads `y i` only for `i ≠ pv`. -/
theorem innerSRect_offpivot (m n p : ℕ) (c' : ℝ) (T : ℝ) (pv : Fin (m * n)) (y y' : Fin (m * n) → ℝ)
    (h : ∀ i, i ≠ pv → y i = y' i) : innerSRect m n p c' T pv y = innerSRect m n p c' T pv y' := by
  have hR : RmatRect m n pv y = RmatRect m n pv y' := by
    funext i j; rw [RmatRect_entry, RmatRect_entry]
    by_cases hij : eRect m n (i, j) = pv
    · rw [if_pos hij, if_pos hij]
    · rw [if_neg hij, if_neg hij]; exact h _ hij
  rw [innerSRect, innerSRect, hR]

/-- `innerSRect m n p c' T pv` is measurable in `y`. -/
theorem measurable_innerSRect (m n p : ℕ) (c' : ℝ) (T : ℝ) (pv : Fin (m * n)) :
    Measurable (innerSRect m n p c' T pv) := by
  unfold innerSRect
  apply Measurable.lintegral_prod_right (f := fun y S =>
    ENNReal.ofReal ((frobSq (rmatMul (RmatRect m n pv y) S)) ^ (-c')))
  apply ENNReal.measurable_ofReal.comp
  apply Measurable.comp (g := fun t : ℝ => t ^ (-c')) (by fun_prop)
  unfold frobSq rmatMul
  refine Finset.measurable_sum _ (fun i _ => Finset.measurable_sum _ (fun j _ => ?_))
  refine Measurable.pow_const (Finset.measurable_sum _ (fun k _ => ?_)) 2
  refine Measurable.mul ?_ ((measurable_pi_apply j).comp ((measurable_pi_apply k).comp measurable_snd))
  have : Measurable (fun y : Fin (m * n) → ℝ => RmatRect m n pv y i k) := by
    unfold RmatRect
    show Measurable (fun y : Fin (m * n) → ℝ =>
      (matToFlatRect m n).symm (fun l => if l = pv then 1 else y l) i k)
    have hidx : ∀ y : Fin (m * n) → ℝ,
        (matToFlatRect m n).symm (fun l => if l = pv then 1 else y l) i k
          = (fun l => if l = pv then 1 else y l) (eRect m n (i, k)) := fun y => rfl
    simp only [hidx]
    by_cases hp : eRect m n (i, k) = pv
    · simp only [if_pos hp]; exact measurable_const
    · simp only [if_neg hp]; exact measurable_pi_apply _
  exact this.comp measurable_fst

/-- `frobSq (R·S)` is invariant under a row-perm `σr` of `R` (`Fin m`) + a simultaneous col-perm `σc`
of `R` (`Fin n`) = row-perm of `S`. The rectangular `frobSq_rmatMul_permG`. -/
theorem frobSq_rmatMul_permRect {m n p : ℕ} (R : Fin m → Fin n → ℝ) (S : Fin n → Fin p → ℝ)
    (σr : Fin m ≃ Fin m) (σc : Fin n ≃ Fin n) :
    frobSq (rmatMul R S)
      = frobSq (rmatMul (fun a c => R (σr a) (σc c)) (fun k j => S (σc k) j)) := by
  unfold frobSq rmatMul
  rw [← Equiv.sum_comp σr (fun a => ∑ j, (∑ k, R a k * S k j) ^ 2)]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  refine Finset.sum_congr rfl (fun j _ => ?_)
  congr 1
  rw [← Equiv.sum_comp σc (fun k => R (σr a) k * S k j)]

/-- The `S` row-permutation CoV on `matBox n p T`: permuting the `Fin n` row-index of `S` by `σc` is
measure-preserving (`piCongrLeft`) and the box is `σc`-invariant. The rectangular
`matBox_rowperm_lintegralG`. -/
theorem matBox_rowperm_lintegralRect {n p : ℕ} (T : ℝ) (σc : Fin n ≃ Fin n)
    (f : (Fin n → Fin p → ℝ) → ℝ≥0∞) :
    (∫⁻ S in matBox n p T, f S) = ∫⁻ S in matBox n p T, f (fun k j => S (σc k) j) := by
  set E := MeasurableEquiv.piCongrLeft (fun _ : Fin n => Fin p → ℝ) σc with hE
  have hmp : MeasurePreserving E.symm volume volume :=
    (volume_measurePreserving_piCongrLeft (fun _ : Fin n => Fin p → ℝ) σc).symm E
  have hpre : matBox n p T = E.symm ⁻¹' (matBox n p T) := by
    ext S
    simp only [Set.mem_preimage, matBox, Set.mem_setOf_eq]
    constructor
    · intro h i k; exact h (σc i) k
    · intro h i k
      have := h (σc.symm i) k
      rw [show E.symm S (σc.symm i) k = S i k from by
        show S (σc (σc.symm i)) k = S i k; rw [Equiv.apply_symm_apply]] at this
      exact this
  have key := hmp.setLIntegral_comp_preimage_emb E.symm.measurableEmbedding f (matBox n p T)
  have hrhs : (∫⁻ S in matBox n p T, f (fun k j => S (σc k) j))
      = ∫⁻ S in matBox n p T, f (E.symm S) := rfl
  rw [hrhs]
  rw [← hpre] at key
  exact key.symm

/-- **`innerSRect` in the pivot-normalised form.** `innerSRect m n p c' T pv (…symm(0,z)) =
∫_{S∈matBox n p T} frobSq(RmatRectNorm·S)^{−c'}`. The asymmetric `innerSGen_eq_norm`. -/
theorem innerSRect_eq_norm (m n N p : ℕ) (hN : m * n = N + 1) (hm : 1 ≤ m) (hn : 1 ≤ n)
    (c' : ℝ) (T : ℝ) (pv : Fin (m * n)) (z : Fin N → ℝ) :
    innerSRect m n p c' T pv ((piRatioRect m n N hN pv).symm (0, z))
      = ∫⁻ S in matBox n p T,
          ENNReal.ofReal ((frobSq (rmatMul (RmatRectNorm m n N hN hm hn pv z) S)) ^ (-c')) := by
  set y := (piRatioRect m n N hN pv).symm (0, z) with hy
  set σr := Equiv.swap ((eRect m n).symm pv).1 (⟨0, by omega⟩ : Fin m) with hσr
  set σc := Equiv.swap ((eRect m n).symm pv).2 (⟨0, by omega⟩ : Fin n) with hσc
  rw [innerSRect]
  rw [matBox_rowperm_lintegralRect T σc
    (fun S => ENNReal.ofReal ((frobSq (rmatMul (RmatRectNorm m n N hN hm hn pv z) S)) ^ (-c')))]
  refine lintegral_congr (fun S => ?_)
  congr 2
  exact frobSq_rmatMul_permRect (RmatRect m n pv y) S σr σc

/-- The rectangular degree-2 radial homogeneity `frobSq ((a•R)·S) = a²·frobSq (R·S)` for
`R : Fin m → Fin n` (the asymmetric `radialDelta_loss_factor`; pure `ring`). -/
theorem radialDelta_loss_factor_rect {m n p : ℕ} (a : ℝ) (R : Fin m → Fin n → ℝ)
    (S : Fin n → Fin p → ℝ) :
    frobSq (rmatMul (fun i k => a * R i k) S) = a ^ 2 * frobSq (rmatMul R S) := by
  rw [show rmatMul (fun i k => a * R i k) S = fun i j => a * rmatMul R S i j from by
    funext i j; unfold rmatMul; rw [Finset.mul_sum]; exact Finset.sum_congr rfl (fun k _ => by ring)]
  unfold frobSq
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun j _ => ?_); ring

/-- **The radial pull-out** (degree-2 homogeneity): `gFlatRect c' T (blowup) =
∫_S ((y pv)²·frobSq(RmatRect·S))^{−c'}`. Bridges the cover (item 2) to `innerSRect`. The asymmetric
`gFlatG_blowup_radial`. -/
theorem gFlatRect_blowup_radial (m n p : ℕ) (c' : ℝ) (T : ℝ) (pv : Fin (m * n))
    (y : Fin (m * n) → ℝ) :
    gFlatRect m n p c' T (pivotBlowupOn (Finset.univ : Finset (Fin (m * n))) pv y)
      = ∫⁻ S in matBox n p T,
          ENNReal.ofReal (((y pv) ^ 2 * frobSq (rmatMul (RmatRect m n pv y) S)) ^ (-c')) := by
  unfold gFlatRect RmatRect
  refine lintegral_congr (fun S => ?_)
  congr 1
  have hbl : (matToFlatRect m n).symm (pivotBlowupOn (Finset.univ : Finset (Fin (m * n))) pv y)
      = fun a b => (y pv) * ((matToFlatRect m n).symm (fun i => if i = pv then 1 else y i)) a b := by
    funext a b
    show (matToFlatRect m n).symm (pivotBlowupOn (Finset.univ : Finset (Fin (m * n))) pv y) a b = _
    rw [show pivotBlowupOn (Finset.univ : Finset (Fin (m * n))) pv y
        = (fun i => (y pv) * (if i = pv then 1 else y i)) from by
      funext i; unfold pivotBlowupOn
      by_cases hi : i = pv
      · subst hi; simp
      · simp [hi]]
    rfl
  rw [hbl, radialDelta_loss_factor_rect (y pv)
    ((matToFlatRect m n).symm (fun i => if i = pv then 1 else y i)) S]

end DLNFibre.DLN.RLCT
