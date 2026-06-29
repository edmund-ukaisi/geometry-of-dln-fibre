import DLNFibre.DLN.RLCT.Validate.RouteMSmearedChartL2
import DLNFibre.DLN.RLCT.Validate.RouteMSmearedPerFamily

/-!
# `RouteMSmearedChartOpaque` — opaque-width coordinate readbacks for the L=2 smeared chart maps

The cast-isolating bricks for the opaque-width discharge of `routeMCore_box_diverges_smearedL2`'s two
per-family hypotheses (the L=2 slice of the general smeared result). Generalizes the `(2,3,1)` precedent
(`RouteM231Smeared`) to opaque widths `M : Fin 3 → ℕ`.

The dominant cast cost (per genm-smeared3's spec) is the DECODE: `(paramsEquivFlat M).symm (ψ(R u)) =
chartL2Params …`. The map `shearM` (the rational `Λ₀`-shear) is banked ONLY in its measure-preserving form
(`measurePreserving_shearM`, the `splitOfCoreSet`-conjugate skew-product). This file banks its COORDINATE
readback (Codex `decode-arch`-confirmed: route through `splitOfCoreSet_core/_spec`, NOT an explicit per-coord
`if`-form — the latter would need a bridge proof that repeats the same indexing).
-/

open MeasureTheory
open scoped ENNReal BigOperators Matrix

namespace DLNFibre.DLN.RLCT

variable {N : ℕ}

/-- **The `shearM` body** (the inline `splitOfCoreSet`-conjugate skew-product of `measurePreserving_shearM`),
named as a function so its coordinate readback is statable. Adds `shift (∅, spec)` to the `coreSet` slots,
fixing the complement. -/
noncomputable def shearMBody (coreSet : Finset (Fin N))
    (shift : (Fin 0 → ℝ) × (Fin coreSetᶜ.card → ℝ) → (Fin coreSet.card → ℝ)) :
    (Fin N → ℝ) → (Fin N → ℝ) :=
  fun u : Fin N → ℝ =>
    (splitOfCoreSet coreSet).symm
      (let q := splitOfCoreSet coreSet u; (q.1, (q.2.1 + shift (q.1, q.2.2), q.2.2)))

/-- `shearMBody` is measure-preserving (the banked `measurePreserving_shearM`). -/
theorem measurePreserving_shearMBody (coreSet : Finset (Fin N))
    (shift : (Fin 0 → ℝ) × (Fin coreSetᶜ.card → ℝ) → (Fin coreSet.card → ℝ))
    (hshift : Measurable shift) :
    MeasurePreserving (shearMBody coreSet shift) (volume : Measure (Fin N → ℝ)) volume :=
  measurePreserving_shearM coreSet shift hshift

/-- The inverse of `shearMBody` — SUBTRACT the shift from the Core block (the shift reads `(reg, spec)`,
both preserved, so this is a two-sided inverse). -/
noncomputable def shearMBodyInv (coreSet : Finset (Fin N))
    (shift : (Fin 0 → ℝ) × (Fin coreSetᶜ.card → ℝ) → (Fin coreSet.card → ℝ)) :
    (Fin N → ℝ) → (Fin N → ℝ) :=
  fun v : Fin N → ℝ =>
    (splitOfCoreSet coreSet).symm
      (let q := splitOfCoreSet coreSet v; (q.1, (q.2.1 - shift (q.1, q.2.2), q.2.2)))

/-- `shearMBody` is measurable (the split/skew/symm composition). -/
theorem measurable_shearMBody (coreSet : Finset (Fin N))
    (shift : (Fin 0 → ℝ) × (Fin coreSetᶜ.card → ℝ) → (Fin coreSet.card → ℝ))
    (hshift : Measurable shift) : Measurable (shearMBody coreSet shift) :=
  (measurePreserving_shearMBody coreSet shift hshift).measurable

/-- `shearMBodyInv` is measurable. -/
theorem measurable_shearMBodyInv (coreSet : Finset (Fin N))
    (shift : (Fin 0 → ℝ) × (Fin coreSetᶜ.card → ℝ) → (Fin coreSet.card → ℝ))
    (hshift : Measurable shift) : Measurable (shearMBodyInv coreSet shift) := by
  unfold shearMBodyInv
  have hreg : Measurable (fun v : Fin N → ℝ => (splitOfCoreSet coreSet v).1) :=
    measurable_fst.comp (splitOfCoreSet coreSet).measurable
  have hcore : Measurable (fun v : Fin N → ℝ => (splitOfCoreSet coreSet v).2.1) :=
    measurable_fst.comp (measurable_snd.comp (splitOfCoreSet coreSet).measurable)
  have hspec : Measurable (fun v : Fin N → ℝ => (splitOfCoreSet coreSet v).2.2) :=
    measurable_snd.comp (measurable_snd.comp (splitOfCoreSet coreSet).measurable)
  refine (splitOfCoreSet coreSet).symm.measurable.comp
    (hreg.prodMk ((hcore.sub (hshift.comp (hreg.prodMk hspec))).prodMk hspec))

/-- `shearMBody` as a `MeasurableEquiv` (its inverse subtracts the shift). The shift reads the preserved
`(reg, spec)` blocks, so the two are mutually inverse. -/
noncomputable def shearMBodyME (coreSet : Finset (Fin N))
    (shift : (Fin 0 → ℝ) × (Fin coreSetᶜ.card → ℝ) → (Fin coreSet.card → ℝ))
    (hshift : Measurable shift) : (Fin N → ℝ) ≃ᵐ (Fin N → ℝ) where
  toFun := shearMBody coreSet shift
  invFun := shearMBodyInv coreSet shift
  left_inv := by
    intro u
    show (splitOfCoreSet coreSet).symm
        (let q := splitOfCoreSet coreSet (shearMBody coreSet shift u);
          (q.1, (q.2.1 - shift (q.1, q.2.2), q.2.2))) = u
    rw [shearMBody, MeasurableEquiv.apply_symm_apply]
    simp only [add_sub_cancel_right, Prod.mk.eta, MeasurableEquiv.symm_apply_apply]
  right_inv := by
    intro v
    show shearMBody coreSet shift
        ((splitOfCoreSet coreSet).symm
          (let q := splitOfCoreSet coreSet v; (q.1, (q.2.1 - shift (q.1, q.2.2), q.2.2)))) = v
    rw [shearMBody, MeasurableEquiv.apply_symm_apply]
    simp only [sub_add_cancel, Prod.mk.eta, MeasurableEquiv.symm_apply_apply]
  measurable_toFun := measurable_shearMBody coreSet shift hshift
  measurable_invFun := measurable_shearMBodyInv coreSet shift hshift

/-- `shearMBody = ⇑(shearMBodyME …)` (the ME's `toFun` is `shearMBody`). -/
theorem shearMBodyME_coe (coreSet : Finset (Fin N))
    (shift : (Fin 0 → ℝ) × (Fin coreSetᶜ.card → ℝ) → (Fin coreSet.card → ℝ))
    (hshift : Measurable shift) :
    ⇑(shearMBodyME coreSet shift hshift) = shearMBody coreSet shift := rfl

/-- `shearMBody` is a measurable embedding (it is a `MeasurableEquiv`). -/
theorem measurableEmbedding_shearMBody (coreSet : Finset (Fin N))
    (shift : (Fin 0 → ℝ) × (Fin coreSetᶜ.card → ℝ) → (Fin coreSet.card → ℝ))
    (hshift : Measurable shift) : MeasurableEmbedding (shearMBody coreSet shift) := by
  rw [← shearMBodyME_coe coreSet shift hshift]
  exact (shearMBodyME coreSet shift hshift).measurableEmbedding

/-! ### The `coreSetEquiv` images (the bridge from a `Sum`-index to a `Fin N` coord) -/

/-- `coreSetEquiv coreSet (Sum.inr (Sum.inl j)) = coreSet.equivFin.symm j` (Core block image). -/
theorem coreSetEquiv_inr_inl (coreSet : Finset (Fin N)) (j : Fin coreSet.card) :
    coreSetEquiv coreSet (Sum.inr (Sum.inl j)) = coreSet.equivFin.symm j := by
  rfl

/-- `coreSetEquiv coreSet (Sum.inr (Sum.inr k)) = coreSetᶜ.equivFin.symm k` (Spec block image). -/
theorem coreSetEquiv_inr_inr (coreSet : Finset (Fin N)) (k : Fin coreSetᶜ.card) :
    coreSetEquiv coreSet (Sum.inr (Sum.inr k)) = coreSetᶜ.equivFin.symm k := by
  rfl

/-! ### The `shearMBody` coordinate readback (Codex: through `splitOfCoreSet_core/_spec`) -/

/-- **The Core-slot readback.** At a Core coord `coreSet.equivFin.symm j`, `shearMBody` adds the shift
entry `shift (split.1, split.2.2) j` to `u` there (`split := splitOfCoreSet coreSet u`). -/
theorem shearMBody_core (coreSet : Finset (Fin N))
    (shift : (Fin 0 → ℝ) × (Fin coreSetᶜ.card → ℝ) → (Fin coreSet.card → ℝ))
    (u : Fin N → ℝ) (j : Fin coreSet.card) :
    shearMBody coreSet shift u (coreSet.equivFin.symm j)
      = u (coreSet.equivFin.symm j)
        + shift ((splitOfCoreSet coreSet u).1, (splitOfCoreSet coreSet u).2.2) j := by
  rw [shearMBody]
  set split := splitOfCoreSet coreSet u with hsplit
  rw [show ((coreSet.equivFin.symm j : Fin N))
      = coreSetEquiv coreSet (Sum.inr (Sum.inl j)) from (coreSetEquiv_inr_inl coreSet j).symm]
  rw [splitOfCoreSet, splitOfPartition_symm_apply]
  simp only [Sum.elim_inr, Sum.elim_inl, Pi.add_apply]
  rw [coreSetEquiv_inr_inl coreSet j, splitOfCoreSet_core coreSet u j]

/-- **The Spec-slot readback.** At a Spec coord `coreSetᶜ.equivFin.symm k`, `shearMBody` fixes `u`. -/
theorem shearMBody_spec (coreSet : Finset (Fin N))
    (shift : (Fin 0 → ℝ) × (Fin coreSetᶜ.card → ℝ) → (Fin coreSet.card → ℝ))
    (u : Fin N → ℝ) (k : Fin coreSetᶜ.card) :
    shearMBody coreSet shift u (coreSetᶜ.equivFin.symm k) = u (coreSetᶜ.equivFin.symm k) := by
  rw [shearMBody]
  set split := splitOfCoreSet coreSet u with hsplit
  rw [show ((coreSetᶜ.equivFin.symm k : Fin N))
      = coreSetEquiv coreSet (Sum.inr (Sum.inr k)) from (coreSetEquiv_inr_inr coreSet k).symm]
  rw [splitOfCoreSet, splitOfPartition_symm_apply]
  simp only [Sum.elim_inr]
  rw [coreSetEquiv_inr_inr coreSet k, splitOfCoreSet_spec coreSet u k]

/-- **The membership-form Spec readback.** Off `coreSet`, `shearMBody` fixes any coord `m` (rewritten as
the `coreSetᶜ.equivFin` index `m` belongs to). -/
theorem shearMBody_apply_of_not_mem (coreSet : Finset (Fin N))
    (shift : (Fin 0 → ℝ) × (Fin coreSetᶜ.card → ℝ) → (Fin coreSet.card → ℝ))
    (u : Fin N → ℝ) {m : Fin N} (hm : m ∉ coreSet) :
    shearMBody coreSet shift u m = u m := by
  have hmc : m ∈ coreSetᶜ := Finset.mem_compl.mpr hm
  have hspec := shearMBody_spec coreSet shift u (coreSetᶜ.equivFin ⟨m, hmc⟩)
  rw [Equiv.symm_apply_apply] at hspec
  exact hspec

/-- **`splitOfCoreSet.symm` reconstructs the Spec block at the `coreSetᶜ` coords.** At a complement coord
`coreSetᶜ.equivFin.symm k`, the reconstruction reads the supplied spec value `spec k` (regardless of the
reg/core blocks). The bridge for the shear-shift reconstruction. -/
theorem splitOfCoreSet_symm_spec (coreSet : Finset (Fin N))
    (reg : Fin 0 → ℝ) (core : Fin coreSet.card → ℝ) (spec : Fin coreSetᶜ.card → ℝ)
    (k : Fin coreSetᶜ.card) :
    (splitOfCoreSet coreSet).symm (reg, (core, spec)) (coreSetᶜ.equivFin.symm k) = spec k := by
  rw [show ((coreSetᶜ.equivFin.symm k : Fin N))
      = coreSetEquiv coreSet (Sum.inr (Sum.inr k)) from (coreSetEquiv_inr_inr coreSet k).symm]
  rw [splitOfCoreSet, splitOfPartition_symm_apply]
  rfl

/-- **The Spec coords of the `splitOfCoreSet` reconstruction recover the original off `coreSet`.** For any
`m ∉ coreSet`, `splitOfCoreSet.symm (reg, (core, (split u).2.2)) m = u m` — the reconstruction with the
ORIGINAL spec block agrees with `u` on the complement. -/
theorem splitOfCoreSet_symm_specBlock_eq (coreSet : Finset (Fin N))
    (reg : Fin 0 → ℝ) (core : Fin coreSet.card → ℝ) (u : Fin N → ℝ)
    {m : Fin N} (hm : m ∉ coreSet) :
    (splitOfCoreSet coreSet).symm (reg, (core, (splitOfCoreSet coreSet u).2.2)) m = u m := by
  have hmc : m ∈ coreSetᶜ := Finset.mem_compl.mpr hm
  have hk : (coreSetᶜ.equivFin.symm (coreSetᶜ.equivFin ⟨m, hmc⟩) : Fin N) = m := by
    rw [Equiv.symm_apply_apply]
  rw [← hk, splitOfCoreSet_symm_spec, splitOfCoreSet_spec]

/-- **The membership-form Core readback.** On `coreSet`, `shearMBody u m = u m + (the shift entry at the
`coreSet.equivFin` index of `m`)`. -/
theorem shearMBody_apply_of_mem (coreSet : Finset (Fin N))
    (shift : (Fin 0 → ℝ) × (Fin coreSetᶜ.card → ℝ) → (Fin coreSet.card → ℝ))
    (u : Fin N → ℝ) {m : Fin N} (hm : m ∈ coreSet) :
    shearMBody coreSet shift u m
      = u m + shift ((splitOfCoreSet coreSet u).1, (splitOfCoreSet coreSet u).2.2)
          (coreSet.equivFin ⟨m, hm⟩) := by
  -- apply the equivFin-indexed core readback at `j := equivFin ⟨m, hm⟩`, where `equivFin.symm j = m`
  have hcore := shearMBody_core coreSet shift u (coreSet.equivFin ⟨m, hm⟩)
  rw [Equiv.symm_apply_apply] at hcore
  exact hcore

end DLNFibre.DLN.RLCT
