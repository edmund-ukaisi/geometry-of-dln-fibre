/-
Copyright (c) 2026. Released under Apache 2.0; see LICENSE.
-/
import DLNFibre.Core.RingTheory.Ideal.CotangentLocalization
import Mathlib.RingTheory.Kaehler.Basic
import Mathlib.RingTheory.Kaehler.Polynomial
import Mathlib.RingTheory.Smooth.Kaehler
import Mathlib.RingTheory.LocalRing.ResidueField.Basic
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.TensorProduct.RightExactness
import Mathlib.LinearAlgebra.TensorProduct.Tower

/-!
# `DLNFibre.Core.RingTheory.MvPolynomial.CotangentJacobian` — cotangent dim = Jacobian-kernel dim

At a `k`-rational point of an affine variety, the Zariski **cotangent** space is the cokernel of the
transpose Jacobian `Jᵀ` of any generating family, while the **tangent** space is the kernel of the
Jacobian `J`; these are two different spaces, but over a field their finite dimensions agree
(rank–nullity + `rank_transpose`). The headline records that finrank equality:
`finrank (cotangent space) = finrank (ker J)`. **No smoothness is assumed**, so this is more general
than Mathlib's smooth/square submersive Jacobian (which produces a single scalar determinant with
`#relations = #variables`).

For `R = MvPolynomial σ k` (`σ` a `Fintype`), an ideal `I` with a finite generating family
`g : ι → R` (`ι` a `Fintype` with `DecidableEq`), and a `k`-rational point `a : σ → k` of `V(I)`
(`∀ i, eval a (g i) = 0`), set `A = R ⧸ I` and let `m_A` be the maximal ideal at `a` (the kernel of
the augmentation `ε : A →ₐ[k] k` induced by `eval a`). The cotangent space is `coker Jᵀ` and the
tangent space is `ker J`; over the field `k` their finite dimensions agree. The headline
(`finrank_cotangentSpace_eq_finrank_ker_jacobian`) records that dimension equality:

  `finrank k (CotangentSpace (Localization.AtPrime m_A)) = finrank k (ker jacobian)`,

where `jacobian : (σ → k) →ₗ[k] (ι → k)` is `v ↦ fun i ↦ ∑ x, eval a (pderiv x (g i)) • v x`
(rows = generators, cols = `σ`). The residue field `κ(m_A) = k` since `a` is `k`-rational.

Route: the conormal sequence of the surjection `R ↠ A` (`kerCotangentToTensor k R A`), base-changed
to `k` over `A`, identifies `k ⊗_A Ω[A⁄k]` with the cokernel of the transpose Jacobian `Jᵀ` on
`k ⊗_R Ω[R⁄k] ≅ (σ → k)` (the `dx`-basis at `a`, via `mvPolynomialBasis`); the augmentation conormal
map `kerCotangentToTensor k A k` is bijective because `ε` splits (`a` rational, section
`algebraMap k A`), identifying `m_A.Cotangent ≅ k ⊗_A Ω[A⁄k]`; and
`Ideal.finrank_cotangentSpace_localization_eq_cotangent` (flat localization) identifies
`CotangentSpace (Localization.AtPrime m_A)` with `p.Cotangent`. The cokernel–kernel bridge
(`finrank(coker Jᵀ) = card σ − rank Jᵀ = card σ − rank J = finrank(ker J)`) closes the equality.

Mirrors `Mathlib.RingTheory.Kaehler.Polynomial` /
`Mathlib.RingTheory.Smooth.StandardSmoothCotangent`; the rectangular point-Jacobian
cotangent-dimension formula (no smoothness) is absent from Mathlib
v4.29.

**Dependency rule:** `Core` only — never import `DLNFibre.DLN`.
-/

open TensorProduct KaehlerDifferential Module IsLocalRing Matrix

namespace MvPolynomial

noncomputable section

variable {k : Type*} [Field k] {σ : Type*} [Fintype σ] [DecidableEq σ]
  {ι : Type*} [Fintype ι] [DecidableEq ι] (g : ι → MvPolynomial σ k) (a : σ → k)

/-! ### The point-Jacobian and its transpose -/

/-- The Jacobian matrix of `g` at `a`: rows = generators (indexed by `ι`), columns = `σ`;
entry `(i, x) = eval a (pderiv x (g i))`. -/
def jacobianMatrix : Matrix ι σ k :=
  fun i x ↦ MvPolynomial.eval a (MvPolynomial.pderiv x (g i))

/-- The Jacobian of `g` at `a` as a `k`-linear map `(σ → k) →ₗ[k] (ι → k)`
(multiplication by the Jacobian matrix). -/
def jacobian : (σ → k) →ₗ[k] (ι → k) := (jacobianMatrix g a).mulVecLin

/-- The transpose Jacobian: the conormal map `(ι → k) →ₗ[k] (σ → k)` sending the `i`-th basis
vector to the gradient row of `g i` at `a` (multiplication by the transposed Jacobian matrix). -/
def jacobianTranspose : (ι → k) →ₗ[k] (σ → k) := (jacobianMatrix g a)ᵀ.mulVecLin

theorem jacobian_apply (v : σ → k) (i : ι) :
    jacobian g a v i = ∑ x, (MvPolynomial.eval a (MvPolynomial.pderiv x (g i))) • v x := by
  simp [jacobian, jacobianMatrix, Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct, smul_eq_mul]

theorem jacobianTranspose_apply (c : ι → k) (x : σ) :
    jacobianTranspose g a c x = ∑ i, (MvPolynomial.eval a (MvPolynomial.pderiv x (g i))) • c i := by
  simp only [jacobianTranspose, jacobianMatrix, Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct,
    Matrix.transpose_apply, smul_eq_mul]

/-- `jacobian` and `jacobianTranspose` are matrix transposes, hence have equal rank. -/
theorem finrank_range_jacobian_eq :
    finrank k (LinearMap.range (jacobian g a)) =
      finrank k (LinearMap.range (jacobianTranspose g a)) := by
  have h1 : finrank k (LinearMap.range (jacobian g a)) = (jacobianMatrix g a).rank := rfl
  have h2 : finrank k (LinearMap.range (jacobianTranspose g a)) = (jacobianMatrix g a)ᵀ.rank := rfl
  rw [h1, h2, Matrix.rank_transpose]

/-- **Cokernel–kernel bridge.**
`finrank (ker jacobian) = finrank ((σ→k) ⧸ range jacobianTranspose)`. Both equal `card σ − rank`,
using `rank jacobian = rank jacobianTranspose`. -/
theorem finrank_ker_jacobian_eq_finrank_coker :
    finrank k (LinearMap.ker (jacobian g a)) =
      finrank k ((σ → k) ⧸ LinearMap.range (jacobianTranspose g a)) := by
  have hJ : finrank k (LinearMap.range (jacobian g a)) + finrank k (LinearMap.ker (jacobian g a))
      = Fintype.card σ := by
    rw [LinearMap.finrank_range_add_finrank_ker]; simp [Module.finrank_pi]
  have hJt : finrank k ((σ → k) ⧸ LinearMap.range (jacobianTranspose g a))
      + finrank k (LinearMap.range (jacobianTranspose g a)) = Fintype.card σ := by
    rw [Submodule.finrank_quotient_add_finrank]; simp [Module.finrank_pi]
  have hrank := finrank_range_jacobian_eq g a
  omega

/-! ### The augmentation `ε : A →ₐ[k] k` at the rational point and its maximal ideal -/

/-- `span (range g) ≤ ker (aeval a)` since each `g i` vanishes at `a`. -/
theorem span_range_le_ker_aeval (hg : ∀ i, MvPolynomial.eval a (g i) = 0) :
    Ideal.span (Set.range g) ≤ RingHom.ker (MvPolynomial.aeval (R := k) a).toRingHom := by
  rw [Ideal.span_le]
  rintro _ ⟨i, rfl⟩
  have := hg i
  simp only [SetLike.mem_coe, RingHom.mem_ker, AlgHom.toRingHom_eq_coe, RingHom.coe_coe]
  rwa [show MvPolynomial.eval a (g i) = MvPolynomial.aeval a (g i) from rfl] at this

/-- The augmentation `A = R ⧸ I →ₐ[k] k` induced by `eval a = aeval a`, for `I = span (range g)`
(the generators all vanish at `a`, so `aeval a` descends). -/
def evalAug (hg : ∀ i, MvPolynomial.eval a (g i) = 0) :
    (MvPolynomial σ k ⧸ Ideal.span (Set.range g)) →ₐ[k] k :=
  Ideal.Quotient.liftₐ _ (MvPolynomial.aeval a) fun _ hx ↦ span_range_le_ker_aeval g a hg hx

@[simp] theorem evalAug_mk (hg : ∀ i, MvPolynomial.eval a (g i) = 0) (x : MvPolynomial σ k) :
    evalAug g a hg (Ideal.Quotient.mk _ x) = MvPolynomial.aeval a x := rfl

/-- The augmentation is split by `algebraMap k _`, hence surjective. -/
theorem evalAug_surjective (hg : ∀ i, MvPolynomial.eval a (g i) = 0) :
    Function.Surjective (evalAug g a hg) :=
  fun c ↦ ⟨algebraMap k _ c, by rw [AlgHom.commutes]; simp⟩

/-- The maximal ideal `m_A = ker ε` at the rational point `a`, an ideal **of the quotient**
`A = MvPolynomial σ k ⧸ span (range g)` (not of `MvPolynomial σ k` itself). -/
def maxIdealAtSpan (hg : ∀ i, MvPolynomial.eval a (g i) = 0) :
    Ideal (MvPolynomial σ k ⧸ Ideal.span (Set.range g)) :=
  RingHom.ker (evalAug g a hg)

instance maxIdealAtSpan_isMaximal (hg : ∀ i, MvPolynomial.eval a (g i) = 0) :
    (maxIdealAtSpan g a hg).IsMaximal :=
  RingHom.ker_isMaximal_of_surjective (evalAug g a hg).toRingHom (evalAug_surjective g a hg)

instance maxIdealAtSpan_isPrime (hg : ∀ i, MvPolynomial.eval a (g i) = 0) :
    (maxIdealAtSpan g a hg).IsPrime :=
  (maxIdealAtSpan_isMaximal g a hg).isPrime

/-! ### Steps 1–2 — the global cotangent finrank is the Jacobian cokernel

For the split augmentation `ε : A →ₐ[k] k` (`A = R ⧸ span (range g)`), the conormal map
`kerCotangentToTensor k A k : m_A.Cotangent →ₗ[A] k ⊗[A] Ω[A⁄k]` is bijective (surjective since
`Ω[k⁄k] = 0`; injective since `ε` is split by the rational point —
`retractionKerCotangentToTensorEquivSection`). And `k ⊗[A] Ω[A⁄k]` is the cokernel of the transpose
Jacobian on `k ⊗_R Ω[R⁄k] ≅ (σ → k)`. The `Algebra A k` structure (from `evalAug`) and the conormal
machinery live inside the proof; the statement is a finrank equality. -/
/-- **Step 1 (the split-augmentation bijection).** For a split augmentation `ε : A →ₐ[k] k` of a
`k`-algebra `A` (`a`-rational point gives the section), the conormal map
`kerCotangentToTensor k A k : (ker ε).Cotangent →ₗ[A] k ⊗[A] Ω[A⁄k]` is bijective: surjective since
`Ω[k⁄k] = 0`; injective since `ε` splits (a retraction comes from a section of `kerSquareLift`,
`retractionKerCotangentToTensorEquivSection`). Stated for a general `k`-algebra `A` with a
surjective `ε`, with the `Algebra A k` structure carried by the instance. Local scaffolding for
`finrank_cotangent_maxIdealAtSpan_eq_coker`. -/
private theorem kerCotangentToTensor_split_bijective {A : Type*} [CommRing A] [Algebra k A]
    [Algebra A k] [IsScalarTower k A k] (hsurj : Function.Surjective (algebraMap A k)) :
    Function.Bijective (KaehlerDifferential.kerCotangentToTensor k A k) := by
  constructor
  · -- injectivity from the section/retraction
    set gₐ : k →ₐ[k] (A ⧸ (RingHom.ker (algebraMap A k) ^ 2)) :=
      (Ideal.Quotient.mkₐ k _).comp (Algebra.ofId k A) with hgₐdef
    have hgₐ : (IsScalarTower.toAlgHom k A k).kerSquareLift.comp gₐ = AlgHom.id k k := by ext x
    obtain ⟨l, hl⟩ := (retractionKerCotangentToTensorEquivSection (R := k) (P := A) (S := k)
      hsurj).symm ⟨gₐ, hgₐ⟩
    refine Function.LeftInverse.injective (g := l) (fun x ↦ ?_)
    rw [← LinearMap.comp_apply, hl, LinearMap.id_apply]
  · -- surjectivity: range = ker(mapBaseChange) = everything since Ω[k/k] = 0
    rw [← LinearMap.range_eq_top]
    have hrange := KaehlerDifferential.range_kerCotangentToTensor k A k hsurj
    haveI : Subsingleton (Ω[k⁄k]) :=
      KaehlerDifferential.subsingleton_of_surjective (R := k) (S := k) Function.surjective_id
    apply top_unique
    intro x _
    rw [hrange]
    simp only [Submodule.restrictScalars_mem, LinearMap.mem_ker]
    exact Subsingleton.elim _ _

/-- General base-changed conormal scaffold. For a surjection of `k`-algebras `R ↠ B` (in a scalar
tower with `B` and `R` algebras over `k`), `k ⊗[B] Ω[B⁄k]` is `k`-linearly equivalent to the
cokernel of the base-changed conormal inclusion: the `B`-submodule `K := ker (mapBaseChange) =
range (kerCotangentToTensor)` of `B ⊗[R] Ω[R⁄k]`, tensored by `k ⊗[B] -` and restricted to `k`.
Local scaffolding for `finrank_tensor_kaehler_eq_coker`. -/
private theorem tensorKaehler_equiv_quotient_conormal
    {R B : Type*} [CommRing R] [CommRing B] [Algebra k R] [Algebra R B] [Algebra k B]
    [IsScalarTower k R B] [Algebra B k] [IsScalarTower k B k]
    (hsurj : Function.Surjective (algebraMap R B)) :
    Nonempty (((k ⊗[B] (B ⊗[R] Ω[R⁄k])) ⧸ LinearMap.range
        ((LinearMap.lTensor k
          (LinearMap.ker (KaehlerDifferential.mapBaseChange k R B)).subtype).restrictScalars k))
      ≃ₗ[k] k ⊗[B] Ω[B⁄k]) := by
  -- `Ω[B⁄k] = (B ⊗[R] Ω[R⁄k]) ⧸ K` via `mapBaseChange`, `K = ker(mapBaseChange)`
  have hfsurj : Function.Surjective (KaehlerDifferential.mapBaseChange k R B) :=
    KaehlerDifferential.mapBaseChange_surjective k R B hsurj
  -- exactness of the inclusion `K ↪ B⊗Ω` and `mapBaseChange`
  have hExactK : Function.Exact
      (LinearMap.ker (KaehlerDifferential.mapBaseChange k R B)).subtype
      (KaehlerDifferential.mapBaseChange k R B) := (LinearMap.exact_subtype_ker_map _)
  have hExactk : Function.Exact
      ((LinearMap.lTensor k
        (LinearMap.ker (KaehlerDifferential.mapBaseChange k R B)).subtype).restrictScalars k)
      ((LinearMap.lTensor k (KaehlerDifferential.mapBaseChange k R B)).restrictScalars k) :=
    lTensor_exact (R := B) k hExactK hfsurj
  have hfksurj : Function.Surjective
      ((LinearMap.lTensor k (KaehlerDifferential.mapBaseChange k R B)).restrictScalars k) :=
    LinearMap.lTensor_surjective k hfsurj
  exact ⟨hExactk.linearEquivOfSurjective hfksurj⟩

/-- `I.Cotangent` is `R`-spanned by `toCotangent` of a family generating `I`
(`span (range s) = I`). Local scaffolding for `finrank_tensor_kaehler_eq_coker`. -/
private theorem span_cotangent_eq_top {R : Type*} [CommRing R] {ι : Type*} (s : ι → R) (I : Ideal R)
    (hI : Ideal.span (Set.range s) = I) (hmem : ∀ i, s i ∈ I) :
    Submodule.span R (Set.range (fun i ↦ I.toCotangent ⟨s i, hmem i⟩)) = ⊤ := by
  set T := Submodule.span R (Set.range (fun i ↦ I.toCotangent ⟨s i, hmem i⟩))
  rw [eq_top_iff]
  rintro x -
  obtain ⟨⟨y, hy⟩, rfl⟩ := I.toCotangent_surjective x
  rw [← hI] at hy
  have key : ∀ (h : y ∈ I), I.toCotangent ⟨y, h⟩ ∈ T := by
    refine Submodule.span_induction
      (p := fun y _ ↦ ∀ (h : y ∈ I), I.toCotangent ⟨y, h⟩ ∈ T) ?_ ?_ ?_ ?_ hy
    · rintro z ⟨i, rfl⟩ h
      rw [show I.toCotangent ⟨s i, h⟩ = I.toCotangent ⟨s i, hmem i⟩ from rfl]
      exact Submodule.subset_span ⟨i, rfl⟩
    · intro h
      rw [show I.toCotangent ⟨0, h⟩ = 0 from by rw [show (⟨0, h⟩ : I) = 0 from rfl, map_zero]]
      exact zero_mem T
    · intro p q hp hq hsp hsq h
      rw [show I.toCotangent ⟨p + q, h⟩ =
        I.toCotangent ⟨p, hI ▸ hp⟩ + I.toCotangent ⟨q, hI ▸ hq⟩ from by rw [← map_add]; rfl]
      exact add_mem (hsp (hI ▸ hp)) (hsq (hI ▸ hq))
    · intro c p hp hsp h
      rw [show I.toCotangent ⟨c • p, h⟩ = c • I.toCotangent ⟨p, hI ▸ hp⟩ from by
        rw [← map_smul]; rfl]
      exact Submodule.smul_mem _ _ (hsp (hI ▸ hp))
  exact key (hI ▸ hy)

set_option maxHeartbeats 800000 in
-- the iterated `baseChange` of the `dx`-basis + the range-transport elaboration are heavy.
/-- **Step 2.** For the augmentation algebra structure on `A = R ⧸ span (range g)`, the conormal
sequence of `R ↠ A` base-changed to `k` identifies `k ⊗[A] Ω[A⁄k]` with the cokernel of the
transpose Jacobian on `k ⊗_R Ω[R⁄k] ≅ (σ → k)`. -/
theorem finrank_tensor_kaehler_eq_coker (hg : ∀ i, MvPolynomial.eval a (g i) = 0) :
    haveI : Algebra (MvPolynomial σ k ⧸ Ideal.span (Set.range g)) k :=
      (evalAug g a hg).toRingHom.toAlgebra
    finrank k (k ⊗[MvPolynomial σ k ⧸ Ideal.span (Set.range g)]
        Ω[(MvPolynomial σ k ⧸ Ideal.span (Set.range g))⁄k]) =
      finrank k ((σ → k) ⧸ LinearMap.range (jacobianTranspose g a)) := by
  letI instA : Algebra (MvPolynomial σ k ⧸ Ideal.span (Set.range g)) k :=
    (evalAug g a hg).toRingHom.toAlgebra
  haveI htA : IsScalarTower k (MvPolynomial σ k ⧸ Ideal.span (Set.range g)) k :=
    IsScalarTower.of_algebraMap_eq fun x ↦ (AlgHom.commutes (evalAug g a hg) x).symm
  have hsurj : Function.Surjective
      (algebraMap (MvPolynomial σ k) (MvPolynomial σ k ⧸ Ideal.span (Set.range g))) :=
    Ideal.Quotient.mk_surjective
  obtain ⟨eExact⟩ := tensorKaehler_equiv_quotient_conormal (k := k)
    (R := MvPolynomial σ k) (B := MvPolynomial σ k ⧸ Ideal.span (Set.range g)) hsurj
  -- coordinate iso `k ⊗[A] (A ⊗[R] Ω[R⁄k]) ≃ₗ[k] (σ → k)`, iterated base-change of the `dx`-basis.
  -- Pin `Module A A` to `Semiring.toModule` so both `baseChange` steps use the same self-module.
  letI : Module (MvPolynomial σ k ⧸ Ideal.span (Set.range g))
      (MvPolynomial σ k ⧸ Ideal.span (Set.range g)) :=
    @Semiring.toModule _ (Ideal.Quotient.semiring (Ideal.span (Set.range g)))
  let Ψ : k ⊗[MvPolynomial σ k ⧸ Ideal.span (Set.range g)]
      ((MvPolynomial σ k ⧸ Ideal.span (Set.range g)) ⊗[MvPolynomial σ k] Ω[MvPolynomial σ k⁄k])
      ≃ₗ[k] (σ → k) :=
    (((KaehlerDifferential.mvPolynomialBasis k σ).baseChange
      (MvPolynomial σ k ⧸ Ideal.span (Set.range g))).baseChange k).equivFun
  -- action of `Ψ` on a base-changed differential: it reads off the gradient row.
  have Ψ_D : ∀ p : MvPolynomial σ k, Ψ ((1 : k) ⊗ₜ[MvPolynomial σ k ⧸ Ideal.span (Set.range g)]
      ((1 : MvPolynomial σ k ⧸ Ideal.span (Set.range g)) ⊗ₜ[MvPolynomial σ k]
        KaehlerDifferential.D k (MvPolynomial σ k) p)) =
      fun x : σ ↦ (evalAug g a hg) (algebraMap (MvPolynomial σ k)
        (MvPolynomial σ k ⧸ Ideal.span (Set.range g)) (MvPolynomial.pderiv x p)) := by
    intro p
    ext x
    simp only [Ψ, Module.Basis.equivFun_apply, Module.Basis.baseChange_repr_tmul,
      KaehlerDifferential.mvPolynomialBasis_repr_apply, smul_eq_mul, mul_one,
      RingHom.algebraMap_toAlgebra]
    rw [Algebra.smul_def, mul_one, Algebra.smul_def, mul_one, RingHom.algebraMap_toAlgebra]
    rfl
  -- range transport: the base-changed conormal range maps under `Ψ` to `range Jᵀ`.
  -- `K := ker(mapBaseChange)` is `B`-spanned by the conormal generators `1 ⊗ D(g i)`; base-changing
  -- to `k` and applying `Ψ` yields the gradient rows = `Jᵀ` columns.
  have hRange : (LinearMap.range
      ((LinearMap.lTensor k (LinearMap.ker (KaehlerDifferential.mapBaseChange k (MvPolynomial σ k)
        (MvPolynomial σ k ⧸ Ideal.span (Set.range g)))).subtype).restrictScalars k)).map
        Ψ.toLinearMap = LinearMap.range (jacobianTranspose g a) := by
    set K := LinearMap.ker (KaehlerDifferential.mapBaseChange k (MvPolynomial σ k)
      (MvPolynomial σ k ⧸ Ideal.span (Set.range g))) with hKdef
    set sgen : ι → ((MvPolynomial σ k ⧸ Ideal.span (Set.range g)) ⊗[MvPolynomial σ k]
        Ω[MvPolynomial σ k⁄k]) :=
      fun i ↦ (1 : MvPolynomial σ k ⧸ Ideal.span (Set.range g)) ⊗ₜ[MvPolynomial σ k]
        KaehlerDifferential.D k (MvPolynomial σ k) (g i) with hsgen
    set tgen : ι → (k ⊗[MvPolynomial σ k ⧸ Ideal.span (Set.range g)]
        ((MvPolynomial σ k ⧸ Ideal.span (Set.range g)) ⊗[MvPolynomial σ k]
          Ω[MvPolynomial σ k⁄k])) :=
      fun i ↦ (1 : k) ⊗ₜ[MvPolynomial σ k ⧸ Ideal.span (Set.range g)] sgen i with htgen
    -- `ker(R → B) = span (range g)`
    have hIker : RingHom.ker (algebraMap (MvPolynomial σ k)
        (MvPolynomial σ k ⧸ Ideal.span (Set.range g))) = Ideal.span (Set.range g) :=
      Ideal.mk_ker
    have hgi_mem : ∀ i : ι, g i ∈ RingHom.ker (algebraMap (MvPolynomial σ k)
        (MvPolynomial σ k ⧸ Ideal.span (Set.range g))) := fun i ↦ by
      rw [hIker]; exact Ideal.subset_span ⟨i, rfl⟩
    -- the conormal generators span `K` over `R`, hence over `B`
    have hconormalSpan : LinearMap.range (KaehlerDifferential.kerCotangentToTensor k
        (MvPolynomial σ k) (MvPolynomial σ k ⧸ Ideal.span (Set.range g))) =
        Submodule.span (MvPolynomial σ k) (Set.range sgen) := by
      rw [LinearMap.range_eq_map,
        ← span_cotangent_eq_top g _ hIker.symm hgi_mem, Submodule.map_span, ← Set.range_comp]
      rfl
    have hK_R : K.restrictScalars (MvPolynomial σ k) =
        Submodule.span (MvPolynomial σ k) (Set.range sgen) :=
      (KaehlerDifferential.range_kerCotangentToTensor k _ _ hsurj).symm.trans hconormalSpan
    have hKspanB : K = Submodule.span (MvPolynomial σ k ⧸ Ideal.span (Set.range g))
        (Set.range sgen) := by
      apply Submodule.restrictScalars_injective (MvPolynomial σ k)
        (MvPolynomial σ k ⧸ Ideal.span (Set.range g))
      rw [hK_R, Submodule.restrictScalars_span _ _ hsurj]
    -- LHS range = `K.baseChange k` = `span k (range tgen)`
    have hLeftRange : LinearMap.range ((LinearMap.lTensor k K.subtype).restrictScalars k)
        = Submodule.span k (Set.range tgen) := by
      change K.baseChange k = _
      rw [hKspanB, Submodule.baseChange_span, ← Set.range_comp]
      rfl
    -- RHS range = `span k (range Jᵀ-columns)`
    have hRhsSpan : LinearMap.range (jacobianTranspose g a) =
        Submodule.span k (Set.range fun i : ι ↦ jacobianTranspose g a (Pi.single i 1)) := by
      have hdom : Submodule.span k (Set.range fun i : ι ↦ (Pi.single i (1 : k) : ι → k)) = ⊤ := by
        rw [← (Pi.basisFun k ι).span_eq]; congr 1
        ext v; simp [Pi.basisFun_apply, eq_comm]
      rw [← Submodule.map_top (jacobianTranspose g a), ← hdom, Submodule.map_span, ← Set.range_comp]
      rfl
    -- `Ψ` sends generator `tgen i` to the `i`-th gradient row `Jᵀ(eᵢ)`
    have hPsi_i : ∀ i : ι, Ψ.toLinearMap (tgen i) = jacobianTranspose g a (Pi.single i 1) := by
      intro i
      change Ψ (tgen i) = _
      rw [htgen, hsgen, Ψ_D (g i)]
      ext x
      rw [jacobianTranspose_apply]
      simp only [evalAug_mk, Ideal.Quotient.algebraMap_eq, Pi.single_apply, smul_eq_mul]
      rw [Finset.sum_eq_single i (fun b _ hb ↦ by simp [hb]) (by simp)]
      simp [MvPolynomial.aeval_def, MvPolynomial.eval₂_id]
    rw [hLeftRange, Submodule.map_span, hRhsSpan, ← Set.range_comp]
    congr 1
    exact congrArg Set.range (funext fun i ↦ hPsi_i i)
  have eQuot := Submodule.Quotient.equiv _
    (LinearMap.range (jacobianTranspose g a)) Ψ hRange
  exact (eExact.symm.trans eQuot).finrank_eq

theorem finrank_cotangent_maxIdealAtSpan_eq_coker (hg : ∀ i, MvPolynomial.eval a (g i) = 0) :
    finrank k ((maxIdealAtSpan g a hg).Cotangent) =
      finrank k ((σ → k) ⧸ LinearMap.range (jacobianTranspose g a)) := by
  set A := MvPolynomial σ k ⧸ Ideal.span (Set.range g) with hA
  letI : Algebra A k := (evalAug g a hg).toRingHom.toAlgebra
  haveI : IsScalarTower k A k := IsScalarTower.of_algebraMap_eq fun x ↦ by
    rw [RingHom.algebraMap_toAlgebra]; exact (AlgHom.commutes (evalAug g a hg) x).symm
  have hsurj_alg : Function.Surjective (algebraMap A k) := evalAug_surjective g a hg
  -- `m_A = ker (algebraMap A k)`
  have hmA : maxIdealAtSpan g a hg = RingHom.ker (algebraMap A k) := rfl
  -- Step 1: the conormal map is a `k`-linear equiv, so the finranks agree.
  rw [hmA, ← finrank_tensor_kaehler_eq_coker g a hg]
  exact (LinearEquiv.ofBijective
    ((KaehlerDifferential.kerCotangentToTensor k A k).restrictScalars k)
    (kerCotangentToTensor_split_bijective hsurj_alg)).finrank_eq

/-! ### Step 3 — the localization identification -/

/-- `m_A.Cotangent` (over `A`), base-changed to `k`, is the global cotangent space; its `k`-finrank
equals that of `CotangentSpace (Localization.AtPrime m_A)` via
`Ideal.finrank_cotangentSpace_localization_eq_cotangent` (flat localization). -/
theorem finrank_cotangentSpace_localization_eq (hg : ∀ i, MvPolynomial.eval a (g i) = 0) :
    finrank k (CotangentSpace (Localization.AtPrime (maxIdealAtSpan g a hg))) =
      finrank k ((maxIdealAtSpan g a hg).Cotangent) :=
  Ideal.finrank_cotangentSpace_localization_eq_cotangent (k := k) (maxIdealAtSpan g a hg)

/-! ### Headline -/

/-- **Cotangent dimension = Jacobian-kernel dimension.** The local cotangent space at the
`k`-rational point `a` of `V(I)` (`I = span (range g)`) has `k`-dimension equal to that of the
kernel of the Jacobian of the generators. (The cotangent space itself is `coker Jᵀ` and the tangent
space is `ker J`; these are distinct spaces whose finite dimensions agree over the field `k`.)
**No smoothness is assumed.** -/
theorem finrank_cotangentSpace_eq_finrank_ker_jacobian
    (hg : ∀ i, MvPolynomial.eval a (g i) = 0) :
    finrank k (CotangentSpace (Localization.AtPrime (maxIdealAtSpan g a hg))) =
      finrank k (LinearMap.ker (jacobian g a)) := by
  rw [finrank_cotangentSpace_localization_eq g a hg,
    finrank_cotangent_maxIdealAtSpan_eq_coker g a hg,
    finrank_ker_jacobian_eq_finrank_coker g a]

end

end MvPolynomial
