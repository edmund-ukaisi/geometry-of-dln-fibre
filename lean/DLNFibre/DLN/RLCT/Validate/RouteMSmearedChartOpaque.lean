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

end DLNFibre.DLN.RLCT
