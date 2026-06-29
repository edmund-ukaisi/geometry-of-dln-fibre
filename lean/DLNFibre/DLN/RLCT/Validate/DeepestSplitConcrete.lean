import DLNFibre.DLN.RLCT.Validate.DeepestSplitReindex
import DLNFibre.DLN.RLCT.Validate.DeepestSchurShift

/-!
# `DLNFibre.DLN.RLCT.Validate.DeepestSplitConcrete` — the CONCRETE `deepestSplit` map (PIN2 scaffold)

`deepestSplit_exists` (in `DeepestSplitReindex`) packages the gauge-slice reindex as an EXISTENTIAL
`∃ split, MeasurePreserving split ∧ split wstar = 0`. PIN2's frame-bridge cert needs the round-trip
`gaugeReadX/Y/Z (split w) = the raw deviation block of (w − wstar)`, which is provable ONLY for the CONCRETE
witness (the slot decode must definitionally invert the role-split enumeration), not a generic `split`.

This module names that concrete witness `deepestSplit` (verbatim the `deepestSplit_exists` construction,
so its measure-preserving + basepoint spec is the same proof) and records the slot projections as `rfl`
lemmas — the durable contract the round-trip is proved against. The reg/gauge/core slots are the relabel
of `w − wstar` along `deepestRoleIndexEquiv`, restricted to the corresponding `⊕`-arm.

All declarations here are sorry-free: pure defs + `rfl` projection lemmas + the slot-read round-trip
index half. The full `gaugeReadX (deepestSplit w) = raw` layer identity is the PIN2-(i) content built on top
(a separate, larger obligation — the matrix-block step joining this index round-trip to `framedLayer`).
-/

open MeasureTheory Matrix
open scoped ENNReal BigOperators Topology
namespace DLNFibre.DLN.RLCT

variable {L : ℕ}

/-- **The concrete deepest split**: translate by `−wstar`, relabel along `deepestRoleIndexEquiv`, unpack
the `⊕` into the product. Verbatim the `deepestSplit_exists` witness, so it is measure-preserving
(`deepestSplit_mp`) and sends `wstar ↦ 0` (`deepestSplit_basepoint`). The slots decode to the per-layer
gauge blocks via `regGaugeSlotEquiv` (the round-trip the PIN2 cert consumes). -/
noncomputable def deepestSplit (H : Fin (L + 1) → ℕ) (r : ℕ)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L) (wstar : Fin (flatDim H) → ℝ) :
    (Fin (flatDim H) → ℝ) ≃ₜ DeepestSplit H r (deepestNGauge H r) :=
  (Homeomorph.subRight wstar).trans
    ((Homeomorph.piCongrLeft (Y := fun _ => ℝ) (deepestRoleIndexEquiv H r hr hL)).trans
      ((Homeomorph.sumPiEquivProdPi (Fin (deepestNReg H r))
          (Fin (flatDim (deepestM H r)) ⊕ Fin (deepestNGauge H r)) (fun _ => ℝ)).trans
        (Homeomorph.prodCongr (Homeomorph.refl _)
          (Homeomorph.sumPiEquivProdPi (Fin (flatDim (deepestM H r)))
            (Fin (deepestNGauge H r)) (fun _ => ℝ)))))

/-- The reg slot of `deepestSplit w` is the `deepestRoleIndexEquiv`-relabel of `w − wstar` at `Sum.inl`. -/
theorem deepestSplit_fst_apply (H : Fin (L + 1) → ℕ) (r : ℕ)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L) (wstar w : Fin (flatDim H) → ℝ)
    (k : Fin (deepestNReg H r)) :
    (deepestSplit H r hr hL wstar w).1 k
      = (Homeomorph.piCongrLeft (Y := fun _ => ℝ) (deepestRoleIndexEquiv H r hr hL))
          (w - wstar) (Sum.inl k) := rfl

/-- The core slot of `deepestSplit w` is the relabel of `w − wstar` at `Sum.inr (Sum.inl ·)`. -/
theorem deepestSplit_core_apply (H : Fin (L + 1) → ℕ) (r : ℕ)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L) (wstar w : Fin (flatDim H) → ℝ)
    (m : Fin (flatDim (deepestM H r))) :
    (deepestSplit H r hr hL wstar w).2.1 m
      = (Homeomorph.piCongrLeft (Y := fun _ => ℝ) (deepestRoleIndexEquiv H r hr hL))
          (w - wstar) (Sum.inr (Sum.inl m)) := rfl

/-- The gauge slot of `deepestSplit w` is the relabel of `w − wstar` at `Sum.inr (Sum.inr ·)`. -/
theorem deepestSplit_gauge_apply (H : Fin (L + 1) → ℕ) (r : ℕ)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L) (wstar w : Fin (flatDim H) → ℝ)
    (g : Fin (deepestNGauge H r)) :
    (deepestSplit H r hr hL wstar w).2.2 g
      = (Homeomorph.piCongrLeft (Y := fun _ => ℝ) (deepestRoleIndexEquiv H r hr hL))
          (w - wstar) (Sum.inr (Sum.inr g)) := rfl

/-- **`deepestSplit` is the `deepestSplit_exists` witness** — measure-preserving + basepoint, same proof.
The concrete name lets the PIN2 cert state the round-trip against THIS map. -/
theorem deepestSplit_mp_basepoint (H : Fin (L + 1) → ℕ) (r : ℕ)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L) (wstar : Fin (flatDim H) → ℝ) :
    MeasurePreserving (deepestSplit H r hr hL wstar) volume volume
      ∧ deepestSplit H r hr hL wstar wstar = 0 := by
  classical
  set nReg := deepestNReg H r
  set nM := flatDim (deepestM H r)
  set nG := deepestNGauge H r
  set eIdx : Fin (flatDim H) ≃ Fin nReg ⊕ (Fin nM ⊕ Fin nG) := deepestRoleIndexEquiv H r hr hL with heIdx
  -- MP: translation ∘ relabel ∘ unpack, each MP (verbatim `deepestSplit_exists`).
  refine ⟨?_, ?_⟩
  · have hmp_t : MeasurePreserving (Homeomorph.subRight wstar) volume volume :=
      measurePreserving_sub_right volume wstar
    have hmp_relabel : MeasurePreserving
        (Homeomorph.piCongrLeft (Y := fun _ => ℝ) eIdx) volume volume :=
      volume_measurePreserving_piCongrLeft (fun _ => ℝ) eIdx
    have hmp_unpackOuter : MeasurePreserving
        (Homeomorph.sumPiEquivProdPi (Fin nReg) (Fin nM ⊕ Fin nG) (fun _ => ℝ)) volume volume :=
      volume_measurePreserving_sumPiEquivProdPi (fun _ : Fin nReg ⊕ (Fin nM ⊕ Fin nG) => ℝ)
    have hmp_unpackInner : MeasurePreserving
        (Homeomorph.sumPiEquivProdPi (Fin nM) (Fin nG) (fun _ => ℝ)) volume volume :=
      volume_measurePreserving_sumPiEquivProdPi (fun _ : Fin nM ⊕ Fin nG => ℝ)
    have hmp_prod : MeasurePreserving
        (⇑(Homeomorph.prodCongr (Homeomorph.refl (Fin nReg → ℝ))
          (Homeomorph.sumPiEquivProdPi (Fin nM) (Fin nG) (fun _ => ℝ)))) volume volume := by
      simpa [Homeomorph.prodCongr] using (MeasurePreserving.id _).prod hmp_unpackInner
    have hmp_tail : MeasurePreserving
        (⇑((Homeomorph.sumPiEquivProdPi (Fin nReg) (Fin nM ⊕ Fin nG) (fun _ => ℝ)).trans
          (Homeomorph.prodCongr (Homeomorph.refl _)
            (Homeomorph.sumPiEquivProdPi (Fin nM) (Fin nG) (fun _ => ℝ))))) volume volume := by
      rw [show (⇑((Homeomorph.sumPiEquivProdPi (Fin nReg) (Fin nM ⊕ Fin nG) (fun _ => ℝ)).trans
            (Homeomorph.prodCongr (Homeomorph.refl _)
              (Homeomorph.sumPiEquivProdPi (Fin nM) (Fin nG) (fun _ => ℝ)))))
          = (⇑(Homeomorph.prodCongr (Homeomorph.refl (Fin nReg → ℝ))
                (Homeomorph.sumPiEquivProdPi (Fin nM) (Fin nG) (fun _ => ℝ))))
            ∘ (⇑(Homeomorph.sumPiEquivProdPi (Fin nReg) (Fin nM ⊕ Fin nG) (fun _ => ℝ)))
          from rfl]
      exact hmp_prod.comp hmp_unpackOuter
    rw [show (⇑(deepestSplit H r hr hL wstar))
          = (⇑((Homeomorph.sumPiEquivProdPi (Fin nReg) (Fin nM ⊕ Fin nG) (fun _ => ℝ)).trans
              (Homeomorph.prodCongr (Homeomorph.refl _)
                (Homeomorph.sumPiEquivProdPi (Fin nM) (Fin nG) (fun _ => ℝ)))))
            ∘ (⇑(Homeomorph.piCongrLeft (Y := fun _ => ℝ) eIdx))
            ∘ (⇑(Homeomorph.subRight wstar))
          from rfl]
    exact (hmp_tail.comp hmp_relabel).comp hmp_t
  · -- basepoint: subRight wstar sends wstar ↦ 0; relabel/unpack are linear, send 0 ↦ 0.
    change (Homeomorph.prodCongr (Homeomorph.refl _)
        (Homeomorph.sumPiEquivProdPi (Fin nM) (Fin nG) (fun _ => ℝ)))
        ((Homeomorph.sumPiEquivProdPi (Fin nReg) (Fin nM ⊕ Fin nG) (fun _ => ℝ))
          ((Homeomorph.piCongrLeft (Y := fun _ => ℝ) eIdx) (Homeomorph.subRight wstar wstar))) = 0
    have ht0 : (Homeomorph.subRight wstar) wstar = (0 : Fin (flatDim H) → ℝ) := by
      simp [Homeomorph.subRight]
    rw [ht0]
    have hr0 : (Homeomorph.piCongrLeft (Y := fun _ => ℝ) eIdx) (0 : Fin (flatDim H) → ℝ) = 0 := by
      ext j
      show (Equiv.piCongrLeft (fun _ => ℝ) eIdx) (0 : Fin (flatDim H) → ℝ) j = 0
      rw [Equiv.piCongrLeft_apply_eq_cast]; simp
    rw [hr0]
    have houter0 :
        (Homeomorph.sumPiEquivProdPi (Fin nReg) (Fin nM ⊕ Fin nG) (fun _ => ℝ))
          (0 : Fin nReg ⊕ (Fin nM ⊕ Fin nG) → ℝ) = 0 := by
      apply Prod.ext <;> ext j <;> rfl
    rw [houter0]
    apply Prod.ext
    · change (Homeomorph.refl (Fin nReg → ℝ))
          (0 : (Fin nReg → ℝ) × (Fin nM ⊕ Fin nG → ℝ)).1 = 0
      rw [Prod.fst_zero]; rfl
    · change (Homeomorph.sumPiEquivProdPi (Fin nM) (Fin nG) (fun _ => ℝ))
          (0 : (Fin nReg → ℝ) × (Fin nM ⊕ Fin nG → ℝ)).2 = 0
      rw [Prod.snd_zero]
      apply Prod.ext <;> ext j <;> rfl

/-- **The reg/gauge reinsertion map** `Fin nReg ⊕ Fin nG → Fin nReg ⊕ (Fin nM ⊕ Fin nG)` — the
de-relabel target the round-trip lands on: the reg arm stays `Sum.inl`, the gauge arm goes to
`Sum.inr (Sum.inr ·)` (the gauge slot's position in `deepestRoleIndexEquiv`'s codomain, after the
`sumAssoc`/`sumComm`). `deepestRoleIndexEquiv.symm ∘ regGaugeRecombine ∘ regGaugeIdxSplit` is the flat
coordinate of a `RegGaugeIdx` entry (the `regGaugeIdxSplit`'s cancel; the round-trip's index half). -/
def regGaugeRecombine (nReg nM nG : ℕ) :
    Fin nReg ⊕ Fin nG → Fin nReg ⊕ (Fin nM ⊕ Fin nG) :=
  Sum.elim Sum.inl (fun g => Sum.inr (Sum.inr g))

/-- **The slot-read round-trip (index half).** `regGaugeSlotEquiv` of the (reg, gauge) slots of
`deepestSplit w`, evaluated at a `RegGaugeIdx idx`, recovers `(w − wstar)` at the de-relabelled flat
coordinate `deepestRoleIndexEquiv.symm (regGaugeRecombine (regGaugeIdxSplit idx))`. The two
`regGaugeIdxSplit` enumerations (one in `regGaugeSlotEquiv`, one in `deepestRoleIndexEquiv`'s reg/gauge
half) cancel through the `Sum.rec`/`piCongrLeft` recombination — the round-trip the PIN2 cert needs to
identify `gaugeReadX/Y/Z (deepestSplit w)` with the raw layer deviation. -/
theorem regGaugeSlotEquiv_deepestSplit (H : Fin (L + 1) → ℕ) (r : ℕ)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L) (wstar w : Fin (flatDim H) → ℝ)
    (idx : RegGaugeIdx H r) :
    regGaugeSlotEquiv H r hr hL ((deepestSplit H r hr hL wstar w).1,
        (deepestSplit H r hr hL wstar w).2.2) idx
      = (w - wstar) ((deepestRoleIndexEquiv H r hr hL).symm
          (regGaugeRecombine (deepestNReg H r) (flatDim (deepestM H r)) (deepestNGauge H r)
            (regGaugeIdxSplit H r hr hL idx))) := by
  -- Step 1: `regGaugeSlotEquiv (a,b) idx = (sumPiEquivProdPi.symm (a,b)) (regGaugeIdxSplit idx)`.
  have hslot : regGaugeSlotEquiv H r hr hL ((deepestSplit H r hr hL wstar w).1,
        (deepestSplit H r hr hL wstar w).2.2) idx
      = (Equiv.sumPiEquivProdPi (fun _ => ℝ)).symm
          ((deepestSplit H r hr hL wstar w).1, (deepestSplit H r hr hL wstar w).2.2)
          (regGaugeIdxSplit H r hr hL idx) := by
    unfold regGaugeSlotEquiv
    change (Homeomorph.piCongrLeft (Y := fun _ => ℝ) (regGaugeIdxSplit H r hr hL)).symm
        ((Homeomorph.sumPiEquivProdPi (Fin (deepestNReg H r)) (Fin (deepestNGauge H r))
          (fun _ => ℝ)).symm ((deepestSplit H r hr hL wstar w).1,
            (deepestSplit H r hr hL wstar w).2.2)) idx = _
    rw [Homeomorph.piCongrLeft_symm_apply]
    rfl
  rw [hslot]
  -- Step 2: case on `regGaugeIdxSplit idx`. `sumPiEquivProdPi.symm (a,b) (inl k) = a k`,
  -- `(inr g) = b g` (the `Sum.rec` invFun, by `cases`). Then `a = piCongrLeft eIdx (w−wstar)` at
  -- `Sum.inl k` (reg) resp. `Sum.inr (Sum.inr g)` (gauge), and `regGaugeRecombine` puts them back.
  rcases h : regGaugeIdxSplit H r hr hL idx with k | g
  · -- reg arm
    show (deepestSplit H r hr hL wstar w).1 k = _
    rw [deepestSplit_fst_apply]
    -- `piCongrLeft eIdx f (Sum.inl k) = f (eIdx.symm (Sum.inl k))` (constant `ℝ`, cast trivial).
    change (Equiv.piCongrLeft (fun _ => ℝ) (deepestRoleIndexEquiv H r hr hL)) (w - wstar)
        (Sum.inl k) = _
    rw [Equiv.piCongrLeft_apply_eq_cast]
    simp [regGaugeRecombine]
  · -- gauge arm
    show (deepestSplit H r hr hL wstar w).2.2 g = _
    rw [deepestSplit_gauge_apply]
    change (Equiv.piCongrLeft (fun _ => ℝ) (deepestRoleIndexEquiv H r hr hL)) (w - wstar)
        (Sum.inr (Sum.inr g)) = _
    rw [Equiv.piCongrLeft_apply_eq_cast]
    simp [regGaugeRecombine]

/-- `gaugeReadX (deepestSplit w) s` is the `(w − wstar)` flat-coordinate at the X-block role index of layer
`s` — the round-trip specialized to the `X` arm (`Sum.inl (Sum.inl (i,j))`). The matrix-block half of
the PIN2-(i) identity (the layer entry vs the raw-product entry) is built on this + `roleSplitIdx`. -/
theorem gaugeReadX_deepestSplit (H : Fin (L + 1) → ℕ) (r : ℕ)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L) (wstar w : Fin (flatDim H) → ℝ)
    (s : Fin L) (i j : Fin r) :
    gaugeReadX H r hr hL ((deepestSplit H r hr hL wstar w).1,
        (deepestSplit H r hr hL wstar w).2.2) s i j
      = (w - wstar) ((deepestRoleIndexEquiv H r hr hL).symm
          (regGaugeRecombine (deepestNReg H r) (flatDim (deepestM H r)) (deepestNGauge H r)
            (regGaugeIdxSplit H r hr hL ⟨s, Sum.inl (Sum.inl (i, j))⟩))) := by
  simp only [gaugeReadX, Matrix.of_apply]
  exact regGaugeSlotEquiv_deepestSplit H r hr hL wstar w ⟨s, Sum.inl (Sum.inl (i, j))⟩

/-- `gaugeReadY (deepestSplit w) s` at the Y-block role index `Sum.inl (Sum.inr (i,j))`. -/
theorem gaugeReadY_deepestSplit (H : Fin (L + 1) → ℕ) (r : ℕ)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L) (wstar w : Fin (flatDim H) → ℝ)
    (s : Fin L) (i : Fin r) (j : Fin (H s.succ - r)) :
    gaugeReadY H r hr hL ((deepestSplit H r hr hL wstar w).1,
        (deepestSplit H r hr hL wstar w).2.2) s i j
      = (w - wstar) ((deepestRoleIndexEquiv H r hr hL).symm
          (regGaugeRecombine (deepestNReg H r) (flatDim (deepestM H r)) (deepestNGauge H r)
            (regGaugeIdxSplit H r hr hL ⟨s, Sum.inl (Sum.inr (i, j))⟩))) := by
  simp only [gaugeReadY, Matrix.of_apply]
  exact regGaugeSlotEquiv_deepestSplit H r hr hL wstar w ⟨s, Sum.inl (Sum.inr (i, j))⟩

/-- `gaugeReadZ (deepestSplit w) s` at the Z-block role index `Sum.inr (i,j)`. -/
theorem gaugeReadZ_deepestSplit (H : Fin (L + 1) → ℕ) (r : ℕ)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L) (wstar w : Fin (flatDim H) → ℝ)
    (s : Fin L) (i : Fin (H s.castSucc - r)) (j : Fin r) :
    gaugeReadZ H r hr hL ((deepestSplit H r hr hL wstar w).1,
        (deepestSplit H r hr hL wstar w).2.2) s i j
      = (w - wstar) ((deepestRoleIndexEquiv H r hr hL).symm
          (regGaugeRecombine (deepestNReg H r) (flatDim (deepestM H r)) (deepestNGauge H r)
            (regGaugeIdxSplit H r hr hL ⟨s, Sum.inr (i, j)⟩))) := by
  simp only [gaugeReadZ, Matrix.of_apply]
  exact regGaugeSlotEquiv_deepestSplit H r hr hL wstar w ⟨s, Sum.inr (i, j)⟩

end DLNFibre.DLN.RLCT
