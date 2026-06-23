import DLNFibre.DLN.RLCT.Validate.DeepestGaugeConstruction

/-!
# `DLNFibre.DLN.RLCT.Validate.DeepestRegSliceFderiv` — the #82 PIN1 reg-slice derivative (#156/#157)

The single analytic obligation of the deepest-gauge `_deriv`: the regular-slice
`r0 ↦ deepestEPivot (r0, 0)` has strict derivative `id` at `0`. This file supplies the value-fold
(#156, `framedProd_regSlice_fderiv`) and the assembly (#157, `deepestEPivot_regSlice_fderiv_id`),
proving the `sorry` carried in `DeepestGaugeConstruction`.

## The geometry (post #120 def-change)

`regResidualPack := regPivotFinEquiv`, and `regGaugeIdxSplit`'s reg-half routes via
`regBoundaryToRegGauge ∘ regPivotFinEquiv` (`regBoundaryEmbed`). So the two SHARE `regPivotFinEquiv`,
and the gauge-zero reg-slice cancels by `Equiv.symm_apply_apply`:

- **Alignment** (`regGaugeSlotEquiv_regSlice_boundary`): at the gauge-zero slice, the slot read of a
  routed boundary index `regBoundaryToRegGauge b` returns `r0 (regPivotFinEquiv.symm b)`.
- **Off-image vanishing** (`regGaugeSlotEquiv_regSlice_zero_of_notMem`): a non-routed index reads `0`
  (the gauge half is held at `0`). Hence `readX/readY/readZ (r0,0) s` are nonzero ONLY at the routed
  layer (X,Z at `firstLayer`; Y at `lastLayer`), so all INTERIOR layers are the constant corner.
- **Product collapse** (`framedProd_regSlice_fderiv`): the only varying factors are `C_first`/`C_last`;
  the idempotent corner sandwich keeps `(0,0)→δX`, `(0,1)→δY_last`, `(1,0)→δZ_first`, `(1,1)→0`.
-/

open Matrix
open scoped BigOperators Topology
namespace DLNFibre.DLN.RLCT

variable {L : ℕ}

/-! ## The index-level alignment cancel (the shared `regPivotFinEquiv`) -/

/-- The reg-half of `regGaugeIdxSplit` inverts the boundary routing: `regGaugeIdxSplit.symm (inl k)`
is the routed boundary index `regBoundaryToRegGauge (regPivotFinEquiv k)`. -/
theorem regGaugeIdxSplit_symm_inl (H : Fin (L + 1) → ℕ) (r : ℕ) (hr : ∀ s : Fin (L + 1), r ≤ H s)
    (hL : 1 ≤ L) (k : Fin (deepestNReg H r)) :
    (regGaugeIdxSplit H r hr hL).symm (Sum.inl k)
      = regBoundaryToRegGauge H r hL (regPivotFinEquiv H r hr k) := by
  classical
  haveI : Fintype (↥(Set.range (regBoundaryEmbed H r hL))ᶜ) := Fintype.ofFinite _
  unfold regGaugeIdxSplit
  simp only [Equiv.symm_trans_apply, Equiv.sumCongr_symm, Equiv.symm_symm, Equiv.sumCongr_apply,
    Sum.map_inl]
  rw [Equiv.Set.sumCompl_apply_inl, Equiv.ofInjective_apply]
  rfl

/-- The forward boundary cancel: `regGaugeIdxSplit (regBoundaryToRegGauge b) = inl (pivot.symm b)`. -/
theorem regGaugeIdxSplit_boundary_apply (H : Fin (L + 1) → ℕ) (r : ℕ)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L) (b : BoundaryPivotIdx H r) :
    regGaugeIdxSplit H r hr hL (regBoundaryToRegGauge H r hL b)
      = Sum.inl ((regPivotFinEquiv H r hr).symm b) := by
  rw [← Equiv.apply_symm_apply (regPivotFinEquiv H r hr) b, Equiv.symm_apply_apply,
    ← regGaugeIdxSplit_symm_inl H r hr hL ((regPivotFinEquiv H r hr).symm b), Equiv.apply_symm_apply]

/-! ## The slot read on the regular slice -/

/-- The gauge-zero slot read in terms of the index split: `regGaugeSlotEquiv (r0,0) idx` is the joined
function `(r0, 0)` evaluated at `regGaugeIdxSplit idx`. -/
theorem regGaugeSlotEquiv_regSlice_apply (H : Fin (L + 1) → ℕ) (r : ℕ)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L)
    (r0 : Fin (deepestNReg H r) → ℝ) (idx : RegGaugeIdx H r) :
    regGaugeSlotEquiv H r hr hL (r0, 0) idx
      = (Equiv.sumPiEquivProdPi (fun _ => ℝ)).symm (r0, 0) (regGaugeIdxSplit H r hr hL idx) := by
  unfold regGaugeSlotEquiv
  change (Homeomorph.piCongrLeft (Y := fun _ => ℝ) (regGaugeIdxSplit H r hr hL)).symm
      ((Homeomorph.sumPiEquivProdPi (Fin (deepestNReg H r)) (Fin (deepestNGauge H r))
        (fun _ => ℝ)).symm (r0, 0)) idx = _
  rw [Homeomorph.piCongrLeft_symm_apply]
  rfl

/-- A routed boundary index reads back the matching reg coordinate `r0 (pivot.symm b)`. -/
theorem regGaugeSlotEquiv_regSlice_boundary (H : Fin (L + 1) → ℕ) (r : ℕ)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L)
    (r0 : Fin (deepestNReg H r) → ℝ) (b : BoundaryPivotIdx H r) :
    regGaugeSlotEquiv H r hr hL (r0, 0) (regBoundaryToRegGauge H r hL b)
      = r0 ((regPivotFinEquiv H r hr).symm b) := by
  rw [regGaugeSlotEquiv_regSlice_apply, regGaugeIdxSplit_boundary_apply H r hr hL b]
  rfl

/-- A non-routed index reads `0` (the gauge half is held at `0`). -/
theorem regGaugeSlotEquiv_regSlice_zero_of_notMem (H : Fin (L + 1) → ℕ) (r : ℕ)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L)
    (r0 : Fin (deepestNReg H r) → ℝ) (idx : RegGaugeIdx H r)
    (h : idx ∉ Set.range (regBoundaryEmbed H r hL)) :
    regGaugeSlotEquiv H r hr hL (r0, 0) idx = 0 := by
  classical
  haveI : Fintype (↥(Set.range (regBoundaryEmbed H r hL))ᶜ) := Fintype.ofFinite _
  rw [regGaugeSlotEquiv_regSlice_apply]
  obtain ⟨m, hm⟩ : ∃ m, regGaugeIdxSplit H r hr hL idx = Sum.inr m := by
    unfold regGaugeIdxSplit
    rw [Equiv.trans_apply, Equiv.Set.sumCompl_symm_apply_of_notMem h]
    exact ⟨_, rfl⟩
  rw [hm]; rfl

/-- The boundary image is the range of the routing (`regBoundaryEmbed`'s function is the routing). -/
theorem range_regBoundaryEmbed_eq (H : Fin (L + 1) → ℕ) (r : ℕ) (hL : 1 ≤ L) :
    Set.range (regBoundaryEmbed H r hL) = Set.range (regBoundaryToRegGauge H r hL) := rfl

/-! ## Layer membership: X/Z hit only `firstLayer`, Y only `lastLayer` -/

/-- An X-index `⟨s, inl(inl(a,b))⟩` at `s ≠ firstLayer` is not in the boundary image. -/
theorem notMem_X_of_ne_first (H : Fin (L + 1) → ℕ) (r : ℕ) (hL : 1 ≤ L) (s : Fin L)
    (hs : s ≠ firstLayer hL) (a b : Fin r) :
    (⟨s, Sum.inl (Sum.inl (a, b))⟩ : RegGaugeIdx H r) ∉ Set.range (regBoundaryToRegGauge H r hL) := by
  rintro ⟨b', hb'⟩
  rcases b' with ⟨i, j⟩ | ⟨i, j⟩ | ⟨i, j⟩ <;>
    simp only [regBoundaryToRegGauge, Sigma.mk.injEq] at hb'
  · exact hs hb'.1.symm
  · rcases hb' with ⟨hlay, harm⟩; subst hlay; simp at harm
  · rcases hb' with ⟨hlay, harm⟩; subst hlay; simp at harm

/-- A Z-index `⟨s, inr(a,b)⟩` at `s ≠ firstLayer` is not in the boundary image. -/
theorem notMem_Z_of_ne_first (H : Fin (L + 1) → ℕ) (r : ℕ) (hL : 1 ≤ L) (s : Fin L)
    (hs : s ≠ firstLayer hL) (a : Fin (H s.castSucc - r)) (b : Fin r) :
    (⟨s, Sum.inr (a, b)⟩ : RegGaugeIdx H r) ∉ Set.range (regBoundaryToRegGauge H r hL) := by
  rintro ⟨b', hb'⟩
  rcases b' with ⟨i, j⟩ | ⟨i, j⟩ | ⟨i, j⟩ <;>
    simp only [regBoundaryToRegGauge, Sigma.mk.injEq] at hb'
  · rcases hb' with ⟨hlay, harm⟩; subst hlay; simp at harm
  · rcases hb' with ⟨hlay, harm⟩; subst hlay; simp at harm
  · exact hs hb'.1.symm

/-- A Y-index `⟨s, inl(inr(a,b))⟩` at `s ≠ lastLayer` is not in the boundary image. -/
theorem notMem_Y_of_ne_last (H : Fin (L + 1) → ℕ) (r : ℕ) (hL : 1 ≤ L) (s : Fin L)
    (hs : s ≠ lastLayer hL) (a : Fin r) (b : Fin (H s.succ - r)) :
    (⟨s, Sum.inl (Sum.inr (a, b))⟩ : RegGaugeIdx H r) ∉ Set.range (regBoundaryToRegGauge H r hL) := by
  rintro ⟨b', hb'⟩
  rcases b' with ⟨i, j⟩ | ⟨i, j⟩ | ⟨i, j⟩ <;>
    simp only [regBoundaryToRegGauge, Sigma.mk.injEq] at hb'
  · rcases hb' with ⟨hlay, harm⟩; subst hlay; simp at harm
  · exact hs hb'.1.symm
  · rcases hb' with ⟨hlay, harm⟩; subst hlay; simp at harm

/-! ## The `readX/readY/readZ` slice values -/

/-- `readX (r0,0) (firstLayer) a b` reads back `r0` at the X-pivot coordinate. -/
theorem readX_regSlice_first (H : Fin (L + 1) → ℕ) (r : ℕ) (hr : ∀ s : Fin (L + 1), r ≤ H s)
    (hL : 1 ≤ L) (r0 : Fin (deepestNReg H r) → ℝ) (a b : Fin r) :
    readX H r hr hL (r0, 0) (firstLayer hL) a b
      = r0 ((regPivotFinEquiv H r hr).symm (Sum.inl (a, b))) := by
  simp only [readX, Matrix.of_apply]
  have : (⟨firstLayer hL, Sum.inl (Sum.inl (a, b))⟩ : RegGaugeIdx H r)
      = regBoundaryToRegGauge H r hL (Sum.inl (a, b)) := rfl
  rw [this, regGaugeSlotEquiv_regSlice_boundary]

/-- `readX (r0,0) s = 0` for `s ≠ firstLayer` (the X-routing hits only `firstLayer`). -/
theorem readX_regSlice_zero_of_ne (H : Fin (L + 1) → ℕ) (r : ℕ) (hr : ∀ s : Fin (L + 1), r ≤ H s)
    (hL : 1 ≤ L) (r0 : Fin (deepestNReg H r) → ℝ) (s : Fin L) (hs : s ≠ firstLayer hL) :
    readX H r hr hL (r0, 0) s = 0 := by
  ext a b
  simp only [readX, Matrix.of_apply, Matrix.zero_apply]
  exact regGaugeSlotEquiv_regSlice_zero_of_notMem H r hr hL r0 _
    (by rw [range_regBoundaryEmbed_eq]; exact notMem_X_of_ne_first H r hL s hs a b)

/-- `readZ (r0,0) (firstLayer) a b` reads back `r0` at the Z-pivot coordinate. -/
theorem readZ_regSlice_first (H : Fin (L + 1) → ℕ) (r : ℕ) (hr : ∀ s : Fin (L + 1), r ≤ H s)
    (hL : 1 ≤ L) (r0 : Fin (deepestNReg H r) → ℝ) (a : Fin (H (firstLayer hL).castSucc - r))
    (b : Fin r) :
    readZ H r hr hL (r0, 0) (firstLayer hL) a b
      = r0 ((regPivotFinEquiv H r hr).symm (Sum.inr (Sum.inr (a, b)))) := by
  simp only [readZ, Matrix.of_apply]
  have : (⟨firstLayer hL, Sum.inr (a, b)⟩ : RegGaugeIdx H r)
      = regBoundaryToRegGauge H r hL (Sum.inr (Sum.inr (a, b))) := rfl
  rw [this, regGaugeSlotEquiv_regSlice_boundary]

/-- `readZ (r0,0) s = 0` for `s ≠ firstLayer`. -/
theorem readZ_regSlice_zero_of_ne (H : Fin (L + 1) → ℕ) (r : ℕ) (hr : ∀ s : Fin (L + 1), r ≤ H s)
    (hL : 1 ≤ L) (r0 : Fin (deepestNReg H r) → ℝ) (s : Fin L) (hs : s ≠ firstLayer hL) :
    readZ H r hr hL (r0, 0) s = 0 := by
  ext a b
  simp only [readZ, Matrix.of_apply, Matrix.zero_apply]
  exact regGaugeSlotEquiv_regSlice_zero_of_notMem H r hr hL r0 _
    (by rw [range_regBoundaryEmbed_eq]; exact notMem_Z_of_ne_first H r hL s hs a b)

/-- `readY (r0,0) s = 0` for `s ≠ lastLayer`. -/
theorem readY_regSlice_zero_of_ne (H : Fin (L + 1) → ℕ) (r : ℕ) (hr : ∀ s : Fin (L + 1), r ≤ H s)
    (hL : 1 ≤ L) (r0 : Fin (deepestNReg H r) → ℝ) (s : Fin L) (hs : s ≠ lastLayer hL) :
    readY H r hr hL (r0, 0) s = 0 := by
  ext a b
  simp only [readY, Matrix.of_apply, Matrix.zero_apply]
  exact regGaugeSlotEquiv_regSlice_zero_of_notMem H r hr hL r0 _
    (by rw [range_regBoundaryEmbed_eq]; exact notMem_Y_of_ne_last H r hL s hs a b)

/-! ## The framed-layer values on the regular slice (interiors are the constant corner) -/

/-- An INTERIOR layer (`s ≠ firstLayer`, `s ≠ lastLayer`) of the regular slice is the constant corner
`reindex (fromBlocks 1 0 0 0)` — all of `X_s, Y_s, Z_s` vanish there. -/
theorem framedParamsReg_regSlice_interior (H : Fin (L + 1) → ℕ) (r : ℕ)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L) (r0 : Fin (deepestNReg H r) → ℝ)
    (s : Fin L) (hsf : s ≠ firstLayer hL) (hsl : s ≠ lastLayer hL) :
    framedParamsReg H r hr hL (r0, 0) s
      = Matrix.reindex (rThresholdSplit r (H s.castSucc) (hr s.castSucc)).symm
          (rThresholdSplit r (H s.succ) (hr s.succ)).symm
          (Matrix.fromBlocks (1 : Matrix (Fin r) (Fin r) ℝ) 0 0 0) := by
  simp only [framedParamsReg, framedLayer, readX_regSlice_zero_of_ne H r hr hL r0 s hsf,
    readY_regSlice_zero_of_ne H r hr hL r0 s hsl, readZ_regSlice_zero_of_ne H r hr hL r0 s hsf,
    add_zero]

/-! ## The explicit Leibniz derivative of the layer-product entries (#156, the value-fold) -/

/-- The explicit recursive Leibniz derivative of the `prodAux` entry `fun y => prodAux (g y) k i j`
at `x` — the named VALUE that `hasStrictFDerivAt_prodAux_entry` only proved to EXIST. Mirrors the
fold: `D_{k+1}(i,j) = ∑ m, prodAux k i m • g'_k(m,j) + layer_k m j • D_k(i,m)`. -/
noncomputable def prodAuxEntryDeriv {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (H : Fin (L + 1) → ℕ) (g : X → Params H) (x : X)
    (g' : ∀ (s : Fin L) (i : Fin (H s.castSucc)) (j : Fin (H s.succ)), X →L[ℝ] ℝ) :
    (k : ℕ) → (hk : k < L + 1) → Fin (H 0) → Fin (H ⟨k, hk⟩) → X →L[ℝ] ℝ
  | 0, _, _, _ => 0
  | k + 1, hk, i, j => by
      have hk' : k < L + 1 := Nat.lt_of_succ_lt hk
      have hkL : k < L := Nat.lt_of_succ_lt_succ hk
      have e1 : (⟨k, hk'⟩ : Fin (L + 1)) = (⟨k, hkL⟩ : Fin L).castSucc := by
        apply Fin.ext; simp [Fin.castSucc]
      have e2 : (⟨k + 1, hk⟩ : Fin (L + 1)) = (⟨k, hkL⟩ : Fin L).succ := by
        apply Fin.ext; simp [Fin.succ]
      exact ∑ m : Fin (H ⟨k, hk'⟩),
        ((prodAux H (g x) k hk' i m) • g' ⟨k, hkL⟩ (e1 ▸ m) (e2 ▸ j)
          + ((by rw [e1, e2]; exact g x ⟨k, hkL⟩ :
              Matrix (Fin (H ⟨k, hk'⟩)) (Fin (H ⟨k + 1, hk⟩)) ℝ) m j)
            • prodAuxEntryDeriv H g x g' k hk' i m)

/-- The explicit strict derivative of the `prodAux` entries (the value version of
`hasStrictFDerivAt_prodAux_entry`). Mirrors that proof, returning the named `prodAuxEntryDeriv`. -/
theorem hasStrictFDerivAt_prodAux_entry_explicit {X : Type*} [NormedAddCommGroup X]
    [NormedSpace ℝ X] (H : Fin (L + 1) → ℕ) (g : X → Params H) (x : X)
    (g' : ∀ (s : Fin L) (i : Fin (H s.castSucc)) (j : Fin (H s.succ)), X →L[ℝ] ℝ)
    (hg : ∀ (s : Fin L) (i : Fin (H s.castSucc)) (j : Fin (H s.succ)),
      HasStrictFDerivAt (fun y => g y s i j) (g' s i j) x)
    (k : ℕ) (hk : k < L + 1) :
    ∀ (i : Fin (H 0)) (j : Fin (H ⟨k, hk⟩)),
      HasStrictFDerivAt (fun y => prodAux H (g y) k hk i j)
        (prodAuxEntryDeriv H g x g' k hk i j) x := by
  revert hk
  induction k with
  | zero =>
      intro hk i j
      have : (fun y => prodAux H (g y) 0 hk i j)
          = fun _ => (1 : Matrix (Fin (H 0)) (Fin (H 0)) ℝ) i j := rfl
      rw [this]
      simpa only [prodAuxEntryDeriv] using hasStrictFDerivAt_const _ _
  | succ k ih =>
      intro hk i j
      have hk' : k < L + 1 := Nat.lt_of_succ_lt hk
      have hkL : k < L := Nat.lt_of_succ_lt_succ hk
      have e1 : (⟨k, hk'⟩ : Fin (L + 1)) = (⟨k, hkL⟩ : Fin L).castSucc := by
        apply Fin.ext; simp [Fin.castSucc]
      have e2 : (⟨k + 1, hk⟩ : Fin (L + 1)) = (⟨k, hkL⟩ : Fin L).succ := by
        apply Fin.ext; simp [Fin.succ]
      have hentry : (fun y => prodAux H (g y) (k + 1) hk i j)
          = fun y => ∑ m, prodAux H (g y) k hk' i m
              * ((by rw [e1, e2]; exact g y ⟨k, hkL⟩ :
                  Matrix (Fin (H ⟨k, hk'⟩)) (Fin (H ⟨k + 1, hk⟩)) ℝ) m j) := by
        funext y; rfl
      rw [hentry]
      have hsummand : ∀ m : Fin (H ⟨k, hk'⟩),
          HasStrictFDerivAt (fun y => prodAux H (g y) k hk' i m
              * ((by rw [e1, e2]; exact g y ⟨k, hkL⟩ :
                  Matrix (Fin (H ⟨k, hk'⟩)) (Fin (H ⟨k + 1, hk⟩)) ℝ) m j))
            ((prodAux H (g x) k hk' i m) • g' ⟨k, hkL⟩ (e1 ▸ m) (e2 ▸ j)
              + ((by rw [e1, e2]; exact g x ⟨k, hkL⟩ :
                  Matrix (Fin (H ⟨k, hk'⟩)) (Fin (H ⟨k + 1, hk⟩)) ℝ) m j)
                • prodAuxEntryDeriv H g x g' k hk' i m) x := by
        intro m
        have hpre := ih hk' i m
        have hlayer : HasStrictFDerivAt
            (fun y => (by rw [e1, e2]; exact g y ⟨k, hkL⟩ :
                Matrix (Fin (H ⟨k, hk'⟩)) (Fin (H ⟨k + 1, hk⟩)) ℝ) m j)
            (g' ⟨k, hkL⟩ (e1 ▸ m) (e2 ▸ j)) x := by
          have := hg ⟨k, hkL⟩ (e1 ▸ m) (e2 ▸ j)
          simp only [eq_mpr_eq_cast] at this ⊢
          exact this
        exact hpre.fun_mul hlayer
      exact HasStrictFDerivAt.fun_sum (fun m (_ : m ∈ Finset.univ) => hsummand m)

/-! ## The framed-layer reg-slice values at the boundary layers -/

/-- The `firstLayer` framed layer on the reg-slice: `Y` vanishes when `L ≥ 2` (first ≠ last). -/
theorem framedParamsReg_regSlice_first (H : Fin (L + 1) → ℕ) (r : ℕ)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L) (hL2 : 2 ≤ L)
    (r0 : Fin (deepestNReg H r) → ℝ) :
    framedParamsReg H r hr hL (r0, 0) (firstLayer hL)
      = Matrix.reindex (rThresholdSplit r (H (firstLayer hL).castSucc) (hr _)).symm
          (rThresholdSplit r (H (firstLayer hL).succ) (hr _)).symm
          (Matrix.fromBlocks (1 + readX H r hr hL (r0, 0) (firstLayer hL)) 0
            (readZ H r hr hL (r0, 0) (firstLayer hL)) 0) := by
  have hfl : firstLayer hL ≠ lastLayer hL := by
    simp only [firstLayer, lastLayer, ne_eq, Fin.mk.injEq]; omega
  simp only [framedParamsReg, framedLayer, readY_regSlice_zero_of_ne H r hr hL r0 _ hfl]

/-- The `lastLayer` framed layer on the reg-slice: `X, Z` vanish when `L ≥ 2`. -/
theorem framedParamsReg_regSlice_last (H : Fin (L + 1) → ℕ) (r : ℕ)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L) (hL2 : 2 ≤ L)
    (r0 : Fin (deepestNReg H r) → ℝ) :
    framedParamsReg H r hr hL (r0, 0) (lastLayer hL)
      = Matrix.reindex (rThresholdSplit r (H (lastLayer hL).castSucc) (hr _)).symm
          (rThresholdSplit r (H (lastLayer hL).succ) (hr _)).symm
          (Matrix.fromBlocks 1 (readY H r hr hL (r0, 0) (lastLayer hL)) 0 0) := by
  have hfl : lastLayer hL ≠ firstLayer hL := by
    simp only [firstLayer, lastLayer, ne_eq, Fin.mk.injEq]; omega
  simp only [framedParamsReg, framedLayer, readX_regSlice_zero_of_ne H r hr hL r0 _ hfl,
    readZ_regSlice_zero_of_ne H r hr hL r0 _ hfl, add_zero]

/-! ## The value-level product collapse on the regular slice

`(firstLayer hL).castSucc = (0 : Fin (L+1))` is `rfl`, so `readZ … firstLayer`'s row index
`Fin (H (firstLayer).castSucc − r)` is defeq `Fin (H 0 − r)` — no cast threading needed. -/

/-- The reg-slice `firstShape`: the running-product value after the first layer
(`reindex (fromBlocks (1+Xfirst) 0 Zfirst 0)`), at width `H 0 × H ⟨k⟩`. -/
noncomputable def firstShape (H : Fin (L + 1) → ℕ) (r : ℕ) (hr : ∀ s : Fin (L + 1), r ≤ H s)
    (hL : 1 ≤ L) (r0 : Fin (deepestNReg H r) → ℝ) (k : ℕ) (hk : k < L + 1) :
    Matrix (Fin (H 0)) (Fin (H ⟨k, hk⟩)) ℝ :=
  Matrix.reindex (rThresholdSplit r (H 0) (hr 0)).symm
    (rThresholdSplit r (H ⟨k, hk⟩) (hr ⟨k, hk⟩)).symm
    (Matrix.fromBlocks (1 + readX H r hr hL (r0, 0) (firstLayer hL)) 0
      (readZ H r hr hL (r0, 0) (firstLayer hL)) 0)

/-- `firstShape · corner = firstShape` (right-multiply by the interior corner keeps the shape):
`[[1+X,0],[Z,0]]·[[1,0],[0,0]] = [[1+X,0],[Z,0]]`, the shared interface `eB` cancelling. -/
theorem firstShape_mul_corner (H : Fin (L + 1) → ℕ) (r : ℕ) (hr : ∀ s : Fin (L + 1), r ≤ H s)
    (hL : 1 ≤ L) (r0 : Fin (deepestNReg H r) → ℝ) (k : ℕ) (hk : k < L + 1) (b : ℕ) (hb : b < L + 1) :
    firstShape H r hr hL r0 k hk
        * Matrix.reindex (rThresholdSplit r (H ⟨k, hk⟩) (hr ⟨k, hk⟩)).symm
            (rThresholdSplit r (H ⟨b, hb⟩) (hr ⟨b, hb⟩)).symm
            (Matrix.fromBlocks (1 : Matrix (Fin r) (Fin r) ℝ) 0 0 0)
      = firstShape H r hr hL r0 b hb := by
  simp only [firstShape, Matrix.reindex_apply, Equiv.symm_symm]
  rw [Matrix.submatrix_mul_equiv _ _ _ (rThresholdSplit r (H ⟨k, hk⟩) (hr ⟨k, hk⟩)) _]
  congr 1
  rw [Matrix.fromBlocks_multiply]
  congr 1 <;>
    · simp only [Matrix.zero_mul, add_zero]
      first
        | exact Matrix.mul_one _
        | exact Matrix.mul_zero _

/-- Through the first layer (`1 ≤ k ≤ L-1`): the running product is `firstShape` — only the first
layer's `X`/`Z` contributions survive; later interior layers are corners that keep the shape. -/
theorem prodAux_regSlice_through_first (H : Fin (L + 1) → ℕ) (r : ℕ)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L) (hL2 : 2 ≤ L)
    (r0 : Fin (deepestNReg H r) → ℝ) (k : ℕ) (hk : k < L + 1) (hk1 : 1 ≤ k) (hkL : k + 1 ≤ L) :
    prodAux H (framedParamsReg H r hr hL (r0, 0)) k hk = firstShape H r hr hL r0 k hk := by
  induction k with
  | zero => omega
  | succ k ih =>
      have hkL1 : k < L := by omega
      have hk' : k < L + 1 := Nat.lt_of_succ_lt hk
      -- layer `k` (the one just folded in) is an INTERIOR layer (k ≠ firstLayer=0 since k≥0 needs care;
      -- and k ≠ lastLayer=L-1 since k+1 ≤ L-1 i.e. k < L-1). Split on whether k=0 (first) or k≥1.
      rcases Nat.eq_zero_or_pos k with hk0 | hkpos
      · -- k = 0: `prodAux 1 = prodAux 0 * C_first = 1 * C_first = firstShape`.
        subst hk0
        rw [prodAux_succ_layer H (framedParamsReg H r hr hL (r0, 0)) 0 hk
            (rThresholdSplit r (H ⟨0, hk'⟩) (hr _)) (rThresholdSplit r (H ⟨0 + 1, hk⟩) (hr _))
            (Matrix.fromBlocks (1 + readX H r hr hL (r0, 0) (firstLayer hL)) 0
              (readZ H r hr hL (r0, 0) (firstLayer hL)) 0) ?_]
        · refine Eq.trans ?_ (rfl : _ = firstShape H r hr hL r0 (0 + 1) hk)
          exact Matrix.one_mul _
        · show framedParamsReg H r hr hL (r0, 0) (firstLayer hL) = _
          rw [framedParamsReg_regSlice_first H r hr hL hL2 r0]
          congr 1
      · -- k ≥ 1: `prodAux (k+1) = prodAux k * C_k`, `C_k` interior corner, `firstShape · corner`.
        have hcorner : framedParamsReg H r hr hL (r0, 0) ⟨k, hkL1⟩
            = Matrix.reindex (rThresholdSplit r (H (⟨k, hkL1⟩ : Fin L).castSucc) (hr _)).symm
                (rThresholdSplit r (H (⟨k, hkL1⟩ : Fin L).succ) (hr _)).symm
                (Matrix.fromBlocks (1 : Matrix (Fin r) (Fin r) ℝ) 0 0 0) := by
          apply framedParamsReg_regSlice_interior
          · simp only [firstLayer, ne_eq, Fin.mk.injEq]; omega
          · simp only [lastLayer, ne_eq, Fin.mk.injEq]; omega
        rw [prodAux_succ_layer H (framedParamsReg H r hr hL (r0, 0)) k hk
            (rThresholdSplit r (H (⟨k, hkL1⟩ : Fin L).castSucc) (hr _))
            (rThresholdSplit r (H (⟨k, hkL1⟩ : Fin L).succ) (hr _))
            (Matrix.fromBlocks (1 : Matrix (Fin r) (Fin r) ℝ) 0 0 0) ?_]
        · rw [ih hk' (by omega) (by omega)]
          exact firstShape_mul_corner H r hr hL r0 k hk' _ hk
        · rw [hcorner]
          congr 1

/-! ## Scalar calculus helpers (cross terms vanish at the base point) -/

/-- A product of two functions each vanishing at `x` has strict derivative `0` at `x`. -/
theorem hasStrictFDerivAt_mul_zero {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f g : E → ℝ} {f' g' : E →L[ℝ] ℝ} {x : E}
    (hf : HasStrictFDerivAt f f' x) (hg : HasStrictFDerivAt g g' x)
    (hfx : f x = 0) (hgx : g x = 0) :
    HasStrictFDerivAt (fun y => f y * g y) (0 : E →L[ℝ] ℝ) x := by
  have := hf.mul hg
  simpa [hfx, hgx] using this

/-- A finite sum of pairwise products, each factor vanishing at `x`, has strict derivative `0`. -/
theorem hasStrictFDerivAt_sum_mul_zero {ι E : Type*} [Fintype ι] [NormedAddCommGroup E]
    [NormedSpace ℝ E] (f g : ι → E → ℝ) (f' g' : ι → E →L[ℝ] ℝ) {x : E}
    (hf : ∀ i, HasStrictFDerivAt (f i) (f' i) x) (hg : ∀ i, HasStrictFDerivAt (g i) (g' i) x)
    (hf0 : ∀ i, f i x = 0) (hg0 : ∀ i, g i x = 0) :
    HasStrictFDerivAt (fun y => ∑ i, f i y * g i y) (0 : E →L[ℝ] ℝ) x := by
  have := HasStrictFDerivAt.fun_sum (u := Finset.univ)
    (A := fun i y => f i y * g i y) (A' := fun _ => (0 : E →L[ℝ] ℝ))
    (fun i _ => hasStrictFDerivAt_mul_zero (hf i) (hg i) (hf0 i) (hg0 i))
  simpa using this

/-! ## Next: the full product collapse + block-entry derivatives + assembly

PAUSED (controller, 2026-06-23): the shared `framedLayer` is migrating from the ADDITIVE chart
(`reindex (fromBlocks (1+X) Y Z 0)`) to a genuinely FRAME-CONJUGATE form
(`framedParams(split w) s = P_s · (paramsSymm w)_s · Q_s`). The reg-slice fderiv target then changes
from `id` to the constant FRAME factor (the invertible shear-CLE form crux2's #150 already accepts).
The collapse value `fromBlocks (1+X) ((1+X)Y) Z (Z·Y)` and the block-entry derivatives are written
against the OLD additive shape, so they are deferred to cobuild's branch (fm2/deepest-gauge-chart-sub34,
single-sourcing `framedParams`) once the rewrite lands. The SHAPE-INDEPENDENT bedrock above (alignment
cancel, slot reads, the explicit Leibniz `prodAuxEntryDeriv`, the scalar `mul_zero` helpers) carries
over. -/

/-! ## Generalized consumer: the shear-CLE with an INVERTIBLE (frame-factor) reg-block

The frame-conjugate `framedLayer` rewrite makes `deepestEPivot`'s reg-slice fderiv reg-block a constant
INVERTIBLE frame factor `F` (not literally `id`). `regStraightenTotalCLM_equiv_of_regBlock_id` needs the
block to be `id`; this generalization needs only `F` invertible — the total `[[F, Σ],[0, I]]` is then a
genuine `≃L` (block upper-triangular, invertible diagonal). `regAbsorb`/`rlctAtOn_comp_localDiffeo`
consume invertibility, not literal `id`, so this is the interface the resumed assembly targets (within
crux2's #150 shear-CLE calibration). -/

section RegBlockIsUnit
variable {R C S : Type*}
  [NormedAddCommGroup R] [NormedSpace ℝ R]
  [NormedAddCommGroup C] [NormedSpace ℝ C]
  [NormedAddCommGroup S] [NormedSpace ℝ S]

/-- **`regStraightenTotalCLM D_E` is an invertible CLE when `D_E`'s reg-block is an invertible `≃L`**
(the frame-factor generalization of `_of_regBlock_id`). Given a `ContinuousLinearEquiv` `F : R ≃L R`
whose coercion is the reg-block `D_E.comp regInCLM`, the total `δ ↦ (D_E(δ.1,δ.2.2), δ.2.1, δ.2.2)` is
`[[F, Σ],[0, I]]`, inverted by `(r',(c',s')) ↦ (F⁻¹(r' − D_E(0,s')), (c',s'))`. -/
theorem regStraightenTotalCLM_equiv_of_regBlock_isUnit (D_E : (R × S) →L[ℝ] R)
    (F : R ≃L[ℝ] R)
    (hF : (F : R →L[ℝ] R) = D_E.comp (regInCLM : R →L[ℝ] R × S)) :
    ∃ e : (R × (C × S)) ≃L[ℝ] (R × (C × S)),
      (e : (R × (C × S)) →L[ℝ] (R × (C × S))) = regStraightenTotalCLM (C := C) D_E := by
  -- `D_E (r, s) = F r + D_E (0, s)` (linearity); reg-out of `T` is `F δ.1 + D_E (0, δ.2.2)`.
  have hFr : ∀ r : R, F r = D_E (r, (0 : S)) := by
    intro r
    have := ContinuousLinearMap.ext_iff.1 hF r
    simpa [regInCLM] using this
  have hsplit : ∀ (r : R) (s : S), D_E (r, s) = F r + D_E (0, s) := by
    intro r s
    rw [hFr r, ← map_add]
    congr 1
    ext <;> simp
  -- `T δ = (D_E (δ.1, δ.2.2), δ.2.1, δ.2.2)`.
  have hTapp : ∀ δ : R × (C × S),
      regStraightenTotalCLM (C := C) D_E δ = (D_E (δ.1, δ.2.2), δ.2.1, δ.2.2) := by
    intro δ
    simp only [regStraightenTotalCLM, ContinuousLinearMap.prod_apply,
      ContinuousLinearMap.comp_apply, ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd']
  -- The explicit inverse `(r',(c',s')) ↦ (F⁻¹(r' − D_E(0,s')), (c',s'))`, packaged as a `≃L`.
  let inv : (R × (C × S)) →L[ℝ] (R × (C × S)) :=
    ((F.symm : R →L[ℝ] R).comp ((ContinuousLinearMap.fst ℝ R (C × S)) -
        (D_E.comp ((ContinuousLinearMap.inr ℝ R S).comp
          ((ContinuousLinearMap.snd ℝ C S).comp (ContinuousLinearMap.snd ℝ R (C × S))))))).prod
      ((ContinuousLinearMap.snd ℝ R (C × S)))
  have hinvapp : ∀ δ : R × (C × S),
      inv δ = (F.symm (δ.1 - D_E (0, δ.2.2)), δ.2.1, δ.2.2) := by
    intro δ
    simp only [inv, ContinuousLinearMap.prod_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.sub_apply, ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd',
      ContinuousLinearMap.inr_apply]
    rfl
  refine ⟨{ toLinearMap := (regStraightenTotalCLM (C := C) D_E).toLinearMap
            invFun := inv
            left_inv := ?_
            right_inv := ?_
            continuous_toFun := (regStraightenTotalCLM (C := C) D_E).continuous
            continuous_invFun := inv.continuous }, rfl⟩
  · intro δ
    show inv (regStraightenTotalCLM (C := C) D_E δ) = δ
    rw [hTapp, hinvapp, hsplit δ.1 δ.2.2]
    simp only [add_sub_cancel_right, ContinuousLinearEquiv.symm_apply_apply]
  · intro δ
    show regStraightenTotalCLM (C := C) D_E (inv δ) = δ
    rw [hinvapp, hTapp, hsplit _ δ.2.2]
    simp only [ContinuousLinearEquiv.apply_symm_apply, sub_add_cancel]

end RegBlockIsUnit

end DLNFibre.DLN.RLCT
