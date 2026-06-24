import DLNFibre.DLN.RLCT.Foundations.ParamsFlat
import DLNFibre.DLN.RLCT.Foundations.ParamsFlatLinear
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

/-!
# `DLNFibre.DLN.RLCT.Foundations.ParamsReshapeMP` — the reusable reshape measure-preservation

The per-node change-of-variables for a blow-up chart `phi = paramsEquivFlat ∘ chartParams` factors the
chart as `phi = (paramsEquivFlat ∘ pack) ∘ T` where `T` is the flat structural map (blow-up ∘ shear ∘
substitution, with the genuine structural Jacobian) and `pack : (Fin N → ℝ) → Params H` is a coordinate
RESHAPE — it rearranges the `N` flat coordinates into the matrix-entry slots of `Params H`, in the chart's
semantic order. The outer factor `Q := paramsEquivFlat ∘ pack` is a coordinate permutation of the `N` flat
coordinates, so its Jacobian determinant has `|det| = 1` and contributes the trivial factor to the chart
c-o-v.

This module banks the two reusable facts every binding node's c-o-v reuses (the "bank once, share across
all `hfin` per-node charts" reshape-MP the design certificate flags as cost driver 2):

* `measurePreserving_paramsPack_of_flatIdxEquiv` — a coordinate reshape `pack : (Fin N → ℝ) → Params H`
  specified by an EXPLICIT `Fin N ≃ FlatIdx H` (`e`) and the slot equation
  `pack w q.1.1 q.1.2 q.2 = w (e.symm q)` is measure-preserving. Built from the explicit flattening
  `flatEquivOf e` (two `MeasurableEquiv.piCurry` collapses + the `arrowCongr'` reindex by `e`, mirroring
  `paramsEquivFlat` but with the COMPUTABLE `e` in place of `Fintype.equivFin` — exactly the
  `ParamsFlat222` pattern), whose `.symm` is `pack`.

* `continuousLinearMap_abs_det_eq_one_of_measurePreserving` — a continuous ℝ-linear self-map of a
  finite-dimensional space that is measure-preserving for the Haar (`volume`) measure has `|det| = 1`.
  (`map_linearMap_addHaar_eq_smul_addHaar` on the unit box: `MeasurePreserving` ⟹ the smul factor
  `ofReal|det⁻¹| = 1`; `det ≠ 0` because a zero-det map has null range, contradicting `map volume = volume`.)
-/

open MeasureTheory
namespace DLNFibre.DLN.RLCT

variable {L : ℕ}

/-- **The explicit flattening from a chosen `Fin N ≃ FlatIdx H`.** `Params H ≃ᵐ (Fin N → ℝ)`: the two
`MeasurableEquiv.piCurry` collapses of the nested `Pi` (as in `paramsEquivFlat`) then the `arrowCongr'`
reindex by `e.symm` (the COMPUTABLE `e` in place of the noncomputable `Fintype.equivFin`). The
`ParamsFlat222` pattern, parametrised by the node's slot bijection `e`. -/
noncomputable def flatEquivOf {N : ℕ} (H : Fin (L + 1) → ℕ) (e : Fin N ≃ FlatIdx H) :
    Params H ≃ᵐ (Fin N → ℝ) :=
  (MeasurableEquiv.piCurry
      (fun (s : Fin L) (_ : Fin (H s.castSucc)) => Fin (H s.succ) → ℝ)).symm.trans
    ((MeasurableEquiv.piCurry (fun (q : FlatRowIdx H) (_ : Fin (H q.1.succ)) => ℝ)).symm.trans
      (MeasurableEquiv.arrowCongr' e.symm (MeasurableEquiv.refl ℝ)))

/-- **`flatEquivOf` is measure-preserving** — reusing `measurePreserving_piCurry` (×2, `.symm`) +
`volume_preserving_arrowCongr'` (which holds for the explicit `e` exactly as for any equiv), verbatim from
`measurePreserving_e222`/`measurePreserving_paramsEquivFlat`. -/
theorem measurePreserving_flatEquivOf {N : ℕ} (H : Fin (L + 1) → ℕ) (e : Fin N ≃ FlatIdx H) :
    MeasurePreserving (flatEquivOf H e) (volume : Measure (Params H))
      (volume : Measure (Fin N → ℝ)) := by
  unfold flatEquivOf
  have h1 := measurePreserving_piCurry
    (fun (s : Fin L) (_ : Fin (H s.castSucc)) => Fin (H s.succ) → ℝ)
    (fun q _ => (volume : Measure (Fin (H q.succ) → ℝ)))
  have h2 := measurePreserving_piCurry
    (fun (q : FlatRowIdx H) (_ : Fin (H q.1.succ)) => ℝ) (fun _ _ => (volume : Measure ℝ))
  have ha := volume_preserving_arrowCongr' e.symm (MeasurableEquiv.refl ℝ)
    (MeasurePreserving.id (volume : Measure ℝ))
  exact (h1.symm _).trans ((h2.symm _).trans ha)

/-- **Coordinate extraction (`rfl`).** The `(s,i,j)` matrix entry of `(flatEquivOf H e).symm x` is the
flat coordinate `x` at the slot `e.symm ⟨⟨s,i⟩,j⟩` — definitional, since `flatEquivOf.symm` is a
`piCurry`-collapse + reindex (the extraction mirrors `e222_symm_coord`). -/
theorem flatEquivOf_symm_coord {N : ℕ} (H : Fin (L + 1) → ℕ) (e : Fin N ≃ FlatIdx H)
    (x : Fin N → ℝ) (q : FlatIdx H) :
    ((flatEquivOf H e).symm x) q.1.1 q.1.2 q.2 = x (e.symm q) := rfl

/-- **The reusable reshape measure-preservation.** A coordinate reshape `pack : (Fin N → ℝ) → Params H`
that arranges the flat coordinates into the matrix-entry slots according to an explicit slot bijection
`e : Fin N ≃ FlatIdx H` — i.e. `pack w q.1.1 q.1.2 q.2 = w (e.symm q)` — is measure-preserving. (`pack`
is `(flatEquivOf H e).symm`, whose MP is `measurePreserving_flatEquivOf`'s `.symm`.) This is the
"bank once" fact every `hfin` per-node chart's outer reshape reuses. -/
theorem measurePreserving_paramsPack_of_flatIdxEquiv {N : ℕ} (H : Fin (L + 1) → ℕ)
    (e : Fin N ≃ FlatIdx H) (pack : (Fin N → ℝ) → Params H)
    (hpack : ∀ (w : Fin N → ℝ) (q : FlatIdx H), pack w q.1.1 q.1.2 q.2 = w (e.symm q)) :
    MeasurePreserving pack (volume : Measure (Fin N → ℝ)) (volume : Measure (Params H)) := by
  have heq : pack = ⇑(flatEquivOf H e).symm := by
    funext w
    funext s i j
    exact (hpack w ⟨⟨s, i⟩, j⟩).trans (flatEquivOf_symm_coord H e w ⟨⟨s, i⟩, j⟩).symm
  rw [heq]
  exact (measurePreserving_flatEquivOf H e).symm _

/-! ## `|det| = 1` from measure-preservation (the second reusable fact)

A measure-preserving ℝ-linear self-map of a finite-dimensional space has `|det| = 1`. The unit-box
argument: `map_linearMap_addHaar_eq_smul_addHaar` gives `map f volume = ofReal|det⁻¹| • volume`; the
hypothesis `map f volume = volume` then forces `ofReal|det⁻¹| = 1` on the finite-positive unit box. The
`det ≠ 0` precondition comes from measure-preservation: a zero-det map has Haar-null range
(`addHaar_submodule` + `range_lt_top_of_det_eq_zero`), so `map f volume univ = 0 ≠ 1`. -/

/-- **A measure-preserving continuous ℝ-linear self-map has `|det| = 1`.** For
`f : (Fin N → ℝ) →L[ℝ] (Fin N → ℝ)` with `MeasurePreserving f volume volume`,
`|det (f : ... →ₗ ...)| = 1`. The reusable discharge of the outer-reshape Jacobian factor. -/
theorem continuousLinearMap_abs_det_eq_one_of_measurePreserving {N : ℕ}
    (f : (Fin N → ℝ) →L[ℝ] (Fin N → ℝ))
    (hf : MeasurePreserving (f : (Fin N → ℝ) → (Fin N → ℝ))
      (volume : Measure (Fin N → ℝ)) volume) :
    |LinearMap.det (f : (Fin N → ℝ) →ₗ[ℝ] (Fin N → ℝ))| = 1 := by
  set L : (Fin N → ℝ) →ₗ[ℝ] (Fin N → ℝ) := (f : (Fin N → ℝ) →ₗ[ℝ] (Fin N → ℝ)) with hL
  -- `det ≠ 0`: else the range is Haar-null, contradicting `map f volume = volume` on `univ`
  have hdet : LinearMap.det L ≠ 0 := by
    intro hzero
    have hRne : LinearMap.range L ≠ ⊤ := (LinearMap.range_lt_top_of_det_eq_zero hzero).ne
    have hR0 : (volume : Measure (Fin N → ℝ)) (LinearMap.range L : Set (Fin N → ℝ)) = 0 :=
      MeasureTheory.Measure.addHaar_submodule (volume : Measure (Fin N → ℝ)) _ hRne
    have hRmeas : MeasurableSet (LinearMap.range L : Set (Fin N → ℝ)) :=
      (LinearMap.range L).closed_of_finiteDimensional.measurableSet
    have hpre : (f : (Fin N → ℝ) → (Fin N → ℝ)) ⁻¹' (LinearMap.range L : Set (Fin N → ℝ))
        = Set.univ := by
      ext x; exact ⟨fun _ => trivial, fun _ => ⟨x, rfl⟩⟩
    have huniv0 : (volume : Measure (Fin N → ℝ)) Set.univ = 0 := by
      have h : (volume : Measure (Fin N → ℝ)) (LinearMap.range L : Set (Fin N → ℝ))
          = (volume : Measure (Fin N → ℝ))
            ((f : (Fin N → ℝ) → (Fin N → ℝ)) ⁻¹' (LinearMap.range L : Set (Fin N → ℝ))) := by
        rw [← hf.measure_preimage hRmeas.nullMeasurableSet]
      rw [hpre] at h
      rw [← h, hR0]
    have hle : (volume : Measure (Fin N → ℝ)) (Set.Icc (0 : Fin N → ℝ) 1)
        ≤ (volume : Measure (Fin N → ℝ)) Set.univ := measure_mono (Set.subset_univ _)
    rw [huniv0] at hle
    have hB : (volume : Measure (Fin N → ℝ)) (Set.Icc (0 : Fin N → ℝ) 1) = 1 := by
      rw [Real.volume_Icc_pi]; simp
    rw [hB] at hle
    exact absurd (le_antisymm hle (zero_le _)) one_ne_zero
  -- scaling: `map f volume = ofReal|det⁻¹| • volume`; `= volume` forces `ofReal|det⁻¹| = 1`
  have hmap := MeasureTheory.Measure.map_linearMap_addHaar_eq_smul_addHaar
    (μ := (volume : Measure (Fin N → ℝ))) (f := L) hdet
  have hsmul : ENNReal.ofReal |(LinearMap.det L)⁻¹| • (volume : Measure (Fin N → ℝ)) = volume := by
    rw [← hmap]; exact hf.map_eq
  have hc : ENNReal.ofReal |(LinearMap.det L)⁻¹| = 1 := by
    have h := congrArg (fun μ : Measure (Fin N → ℝ) => μ (Set.Icc (0 : Fin N → ℝ) 1)) hsmul
    have hB : (volume : Measure (Fin N → ℝ)) (Set.Icc (0 : Fin N → ℝ) 1) = 1 := by
      rw [Real.volume_Icc_pi]; simp
    simp only [Measure.smul_apply, smul_eq_mul, hB, mul_one] at h
    exact h
  have hreal : |(LinearMap.det L)⁻¹| = 1 := ENNReal.ofReal_eq_one.mp hc
  rwa [abs_inv, inv_eq_one] at hreal

end DLNFibre.DLN.RLCT
