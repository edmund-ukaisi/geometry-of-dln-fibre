/-
Copyright (c) 2026. Released under Apache 2.0; see LICENSE.
-/
import Mathlib.RingTheory.Ideal.Cotangent
import Mathlib.RingTheory.Ideal.CotangentBaseChange
import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
import Mathlib.RingTheory.Localization.AtPrime.Basic
import Mathlib.RingTheory.Flat.Localization
import Mathlib.RingTheory.Localization.BaseChange
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.FiniteDimensional.Basic

/-!
# `DLNFibre.Core.RingTheory.Ideal.CotangentLocalization` — localizing the cotangent space

For a commutative ring `A` and a maximal ideal `p`, the local cotangent space
`IsLocalRing.CotangentSpace (Localization.AtPrime p)` at the localization has the same dimension as
the **global** cotangent space `p.Cotangent = p ⧸ p²`.

The key is that `p.Cotangent` is already a module over the residue field `κ(p) = A ⧸ p`, hence is
its own localization at `p.primeCompl` (`cotangent_isLocalizedModule_id`): the flat base change
`Localization.AtPrime p ⊗[A] p.Cotangent` collapses back to `p.Cotangent`
(`cotangentLocalizationTensorEquiv`). Threading this through `Ideal.tensorCotangentEquiv`
(flat-localization base change of the cotangent space) and the right-unitor cleanup
`cotangentTensorRidEquiv` gives the dimension equality
`finrank_cotangentSpace_localization_eq_cotangent`, over any base ring `k` (`[CommRing k]
[Algebra k A]`; `[Field k]` is **not** needed — the maps are `k`-linear equivs, so the `finrank`s
agree for any base).

Mirrors `Mathlib.RingTheory.Ideal.Cotangent` / `Mathlib.RingTheory.Ideal.CotangentBaseChange`; the
local-vs-global comparison at a maximal ideal is absent from Mathlib v4.29.

**Dependency rule:** `Core` only — never import `DLNFibre.DLN`.
-/

open TensorProduct IsLocalRing Module

namespace Ideal

noncomputable section

variable {A : Type*} [CommRing A] (p : Ideal A) [p.IsMaximal]

attribute [local instance] Ideal.Quotient.field

/-- `p.Cotangent` is its own localization at `p.primeCompl` (it is a `κ(p)`-module). -/
theorem cotangent_isLocalizedModule_id :
    IsLocalizedModule p.primeCompl (LinearMap.id : p.Cotangent →ₗ[A] p.Cotangent) := by
  refine ⟨?_, ?_, ?_⟩
  · intro s
    refine (Module.End.isUnit_iff _).mpr ?_
    have hs : IsUnit (Ideal.Quotient.mk p (s : A)) := by
      rw [isUnit_iff_ne_zero]
      exact fun h ↦ s.2 (Ideal.Quotient.eq_zero_iff_mem.mp h)
    let u : (A ⧸ p)ˣ := hs.unit
    have hu : (u : A ⧸ p) = Ideal.Quotient.mk p (s : A) := hs.unit_spec
    have hsmul : ∀ x : p.Cotangent,
        ((algebraMap A (Module.End A p.Cotangent) (s : A)) x) = (u : A ⧸ p) • x := fun x ↦ by
      rw [Module.algebraMap_end_apply,
        ← Module.IsTorsionBySet.mk_smul (Ideal.isTorsionBySet_cotangent p) (s : A) x, hu]; rfl
    refine ⟨fun x y hxy ↦ ?_, fun y ↦ ⟨(↑u⁻¹ : A ⧸ p) • y, ?_⟩⟩
    · have h := congrArg (fun z : p.Cotangent ↦ (↑u⁻¹ : A ⧸ p) • z) hxy
      rw [hsmul, hsmul] at h; simpa [smul_smul] using h
    · rw [hsmul]; simp [smul_smul]
  · intro y; exact ⟨⟨y, 1⟩, by simp⟩
  · intro x y h; exact ⟨1, by simpa using h⟩

/-- The flat base change of `p.Cotangent` to the localization collapses back to `p.Cotangent`. -/
def cotangentLocalizationTensorEquiv :
    Localization.AtPrime p ⊗[A] p.Cotangent ≃ₗ[A] p.Cotangent := by
  haveI : p.IsPrime := inferInstance
  let g : p.Cotangent →ₗ[A] Localization.AtPrime p ⊗[A] p.Cotangent :=
    TensorProduct.mk A (Localization.AtPrime p) p.Cotangent 1
  haveI : IsLocalizedModule p.primeCompl (LinearMap.id : p.Cotangent →ₗ[A] p.Cotangent) :=
    cotangent_isLocalizedModule_id p
  haveI : IsLocalizedModule p.primeCompl g := by dsimp only [g]; infer_instance
  exact (IsLocalizedModule.linearEquiv p.primeCompl
    (LinearMap.id : p.Cotangent →ₗ[A] p.Cotangent) g).symm

/-- Collapse the `includeRight` ideal `p.map includeRight` (in `T ⊗[A] A`) to
`p.map (algebraMap A T)` (in `T = Localization.AtPrime p`) along the right unitor
`T ⊗[A] A ≃ₐ[T] T`. -/
def cotangentTensorRidEquiv :
    (p.map (Algebra.TensorProduct.includeRight.toRingHom :
      A →+* Localization.AtPrime p ⊗[A] A)).Cotangent
      ≃ₗ[Localization.AtPrime p]
    (p.map (algebraMap A (Localization.AtPrime p))).Cotangent := by
  set T := Localization.AtPrime p
  set e : T ⊗[A] A ≃ₐ[T] T := Algebra.TensorProduct.rid A T T
  have hfwd : (p.map (Algebra.TensorProduct.includeRight.toRingHom : A →+* T ⊗[A] A)) ≤
      (p.map (algebraMap A T)).comap e.toAlgHom := by
    rw [Ideal.map_le_iff_le_comap]
    intro x hx
    simp only [Ideal.mem_comap, AlgEquiv.toAlgHom_eq_coe, AlgHom.coe_coe]
    rw [show e (Algebra.TensorProduct.includeRight.toRingHom x) = algebraMap A T x from by
      simp [e, Algebra.TensorProduct.rid_tmul, Algebra.smul_def]]
    exact Ideal.mem_map_of_mem _ hx
  have hbwd : (p.map (algebraMap A T)) ≤
      (p.map (Algebra.TensorProduct.includeRight.toRingHom : A →+* T ⊗[A] A)).comap
        e.symm.toAlgHom := by
    rw [Ideal.map_le_iff_le_comap]
    intro x hx
    simp only [Ideal.mem_comap, AlgEquiv.toAlgHom_eq_coe, AlgHom.coe_coe]
    rw [show e.symm (algebraMap A T x) = Algebra.TensorProduct.includeRight.toRingHom x from by
      apply e.injective; simp [e, Algebra.TensorProduct.rid_tmul, Algebra.smul_def]]
    exact Ideal.mem_map_of_mem _ hx
  refine LinearEquiv.ofLinear
    (Ideal.mapCotangent _ _ e.toAlgHom hfwd)
    (Ideal.mapCotangent _ _ e.symm.toAlgHom hbwd) ?_ ?_
  · ext x
    obtain ⟨y, rfl⟩ := Ideal.toCotangent_surjective _ x
    simp only [LinearMap.comp_apply, Ideal.mapCotangent_toCotangent, LinearMap.id_apply]
    congr 1; ext; simp [e]
  · ext x
    obtain ⟨y, rfl⟩ := Ideal.toCotangent_surjective _ x
    simp only [LinearMap.comp_apply, Ideal.mapCotangent_toCotangent, LinearMap.id_apply]
    congr 1; ext; simp [e]

/-- **Localization of the cotangent space.** Over any base ring `k` with `[Algebra k A]`, the local
cotangent space `CotangentSpace (Localization.AtPrime p)` and the global `p.Cotangent` have the same
`k`-dimension. -/
theorem finrank_cotangentSpace_localization_eq_cotangent
    {k : Type*} [CommRing k] [Algebra k A] :
    finrank k (CotangentSpace (Localization.AtPrime p)) = finrank k (p.Cotangent) := by
  set T := Localization.AtPrime p
  let eTensor : T ⊗[A] p.Cotangent ≃ₗ[T] (p.map (algebraMap A T)).Cotangent :=
    (Ideal.tensorCotangentEquiv A T p).trans (cotangentTensorRidEquiv p)
  have hmax : p.map (algebraMap A T) = maximalIdeal T :=
    Localization.AtPrime.map_eq_maximalIdeal
  let eCot : T ⊗[A] p.Cotangent ≃ₗ[k] CotangentSpace T := (hmax ▸ eTensor).restrictScalars k
  exact (LinearEquiv.finrank_eq eCot.symm).trans
    (LinearEquiv.finrank_eq ((cotangentLocalizationTensorEquiv p).restrictScalars k))

end

end Ideal
