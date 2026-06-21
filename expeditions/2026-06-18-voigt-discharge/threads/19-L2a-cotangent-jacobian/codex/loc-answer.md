`tensorCotangentEquiv` is the right Mathlib tool here. I did not find a cleaner direct cotangent-localization finrank lemma in v4.29.

The `includeRight` mismatch is handled by the algebra equivalence

```lean
Algebra.TensorProduct.rid A (Localization.AtPrime m) (Localization.AtPrime m) :
  Localization.AtPrime m ⊗[A] A ≃ₐ[Localization.AtPrime m] Localization.AtPrime m
```

It sends `1 ⊗ₜ a` to `algebraMap A (Localization.AtPrime m) a`.

For the `k`-finrank step, do not use `Module.finrank_baseChange` directly. The clean route is to prove that the identity map on `m.Cotangent` is already a localization at `m.primeCompl`, then use `IsLocalizedModule.linearEquiv`.

The final theorem proof is:

```lean
import Mathlib.RingTheory.Flat.Localization
import Mathlib.RingTheory.Localization.BaseChange
import Mathlib.RingTheory.Ideal.CotangentBaseChange

open TensorProduct Module IsLocalRing

attribute [local instance] Ideal.Quotient.field

noncomputable section

variable {k A : Type*} [Field k] [CommRing A] [Algebra k A]
variable (m : Ideal A) [m.IsMaximal]

/- Helper 1:
   Prove `IsLocalizedModule m.primeCompl (LinearMap.id : m.Cotangent →ₗ[A] m.Cotangent)`.

   Key lemmas:
   * `Ideal.Quotient.field`
   * `isUnit_iff_ne_zero`
   * `Ideal.Quotient.eq_zero_iff_mem`
   * `Module.End.isUnit_iff`
   * `Module.algebraMap_end_apply`
   * `Module.IsTorsionBySet.mk_smul`
   * `Ideal.isTorsionBySet_cotangent`
-/
private lemma cotangent_isLocalizedModule_id :
    IsLocalizedModule m.primeCompl
      (LinearMap.id : m.Cotangent →ₗ[A] m.Cotangent) := by
  refine ⟨?_, ?_, ?_⟩
  · intro s
    refine (Module.End.isUnit_iff _).mpr ?_
    have hs : IsUnit (Ideal.Quotient.mk m (s : A)) := by
      rw [isUnit_iff_ne_zero]
      exact fun h => s.2 (Ideal.Quotient.eq_zero_iff_mem.mp h)
    let u : (A ⧸ m)ˣ := hs.unit
    have hu : (u : A ⧸ m) = Ideal.Quotient.mk m (s : A) := hs.unit_spec
    have hsmul (x : m.Cotangent) :
        ((algebraMap A (Module.End A m.Cotangent) (s : A)) x) =
          (u : A ⧸ m) • x := by
      rw [Module.algebraMap_end_apply]
      rw [← Module.IsTorsionBySet.mk_smul
        (Ideal.isTorsionBySet_cotangent m) (s : A) x]
      rw [hu]
      rfl
    constructor
    · intro x y hxy
      have h := congrArg (fun z : m.Cotangent => (↑u⁻¹ : A ⧸ m) • z) hxy
      rw [hsmul, hsmul] at h
      simpa [smul_smul] using h
    · intro y
      refine ⟨(↑u⁻¹ : A ⧸ m) • y, ?_⟩
      rw [hsmul]
      simp [smul_smul]
  · intro y
    exact ⟨⟨y, 1⟩, by simp⟩
  · intro x y h
    exact ⟨1, by simpa using h⟩

private noncomputable def cotangentLocalizationTensorEquiv :
    Localization.AtPrime m ⊗[A] m.Cotangent ≃ₗ[A] m.Cotangent := by
  haveI : m.IsPrime := inferInstance
  let g : m.Cotangent →ₗ[A] Localization.AtPrime m ⊗[A] m.Cotangent :=
    TensorProduct.mk A (Localization.AtPrime m) m.Cotangent 1
  haveI : IsLocalizedModule m.primeCompl
      (LinearMap.id : m.Cotangent →ₗ[A] m.Cotangent) :=
    cotangent_isLocalizedModule_id m
  haveI : IsLocalizedModule m.primeCompl g := by
    dsimp [g]
    infer_instance
  exact (IsLocalizedModule.linearEquiv m.primeCompl
    (LinearMap.id : m.Cotangent →ₗ[A] m.Cotangent) g).symm
```

For the `includeRight` collapse, make one helper equivalence using `Ideal.mapCotangent` forward and backward along `Algebra.TensorProduct.rid`. The key proof obligations are:

```lean
let T := Localization.AtPrime m
let e : T ⊗[A] A ≃ₐ[T] T := Algebra.TensorProduct.rid A T T

have hcomp :
    (e.toAlgHom.toRingHom.comp
      (Algebra.TensorProduct.includeRight.toRingHom : A →+* T ⊗[A] A)) =
      algebraMap A T := by
  ext a
  simp [e, Algebra.TensorProduct.rid_tmul, Algebra.smul_def]

have hcomp' :
    (e.symm.toAlgHom.toRingHom.comp (algebraMap A T)) =
      (Algebra.TensorProduct.includeRight.toRingHom : A →+* T ⊗[A] A) := by
  ext a
  simp only [RingHom.coe_comp, Function.comp_apply]
  change (algebraMap A T a) ⊗ₜ[A] (1 : A) = (1 : T) ⊗ₜ[A] a
  rw [Algebra.algebraMap_eq_smul_one, smul_tmul]
  simp
```

Then use `Ideal.map_map`, `Ideal.le_comap_of_map_le`, `Ideal.mapCotangent`, and prove the two inverse laws by `Ideal.toCotangent_surjective` and `rfl` on representatives.

With that helper named, say:

```lean
private noncomputable def cotangentTensorRidEquiv :
    (m.map (Algebra.TensorProduct.includeRight.toRingHom :
      A →+* Localization.AtPrime m ⊗[A] A)).Cotangent
      ≃ₗ[Localization.AtPrime m]
    (m.map (algebraMap A (Localization.AtPrime m))).Cotangent :=
  -- body as described above
```

The final proof is then short:

```lean
theorem finrank_cotangentSpace_localization_eq :
    finrank k (CotangentSpace (Localization.AtPrime m)) =
      finrank k (m.Cotangent) := by
  haveI : m.IsPrime := inferInstance
  let T := Localization.AtPrime m

  let eTensor : T ⊗[A] m.Cotangent ≃ₗ[T]
      (m.map (algebraMap A T)).Cotangent :=
    (Ideal.tensorCotangentEquiv A T m).trans (cotangentTensorRidEquiv m)

  have hmax : m.map (algebraMap A T) = maximalIdeal T :=
    Localization.AtPrime.map_eq_maximalIdeal

  let eCot : T ⊗[A] m.Cotangent ≃ₗ[k] CotangentSpace T :=
    (hmax ▸ eTensor).restrictScalars k

  exact (LinearEquiv.finrank_eq eCot.symm).trans
    (LinearEquiv.finrank_eq ((cotangentLocalizationTensorEquiv m).restrictScalars k))
```

The residue-field identification `κ = k` is not needed for this specific `finrank k` equality. If you later need it, the relevant verified names are:

```lean
Localization.AtPrime.equivQuotMaximalIdeal
Ideal.bijective_algebraMap_quotient_residueField
AlgEquiv.ofRingEquiv
```

Combine `A ⧸ m ≃ₐ[k] k` with `Localization.AtPrime.equivQuotMaximalIdeal m (Localization.AtPrime m)` and the quotient-to-residue equivalence from `Ideal.bijective_algebraMap_quotient_residueField`.