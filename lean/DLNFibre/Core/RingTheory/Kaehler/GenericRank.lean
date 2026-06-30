import Mathlib.RingTheory.Kaehler.Basic
import Mathlib.RingTheory.Kaehler.JacobiZariski
import Mathlib.RingTheory.Kaehler.Polynomial
import Mathlib.RingTheory.Etale.Kaehler
import Mathlib.RingTheory.Smooth.Field
import Mathlib.FieldTheory.Perfect
import Mathlib.RingTheory.AlgebraicIndependent.TranscendenceBasis
import Mathlib.RingTheory.AlgebraicIndependent.Adjoin
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.RingTheory.Localization.Module
import Mathlib.RingTheory.EssentialFiniteness
import Mathlib.RingTheory.Flat.Basic
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.Finsupp.LinearCombination

/-!
# `DLNFibre.Core.RingTheory.Kaehler.GenericRank` — generic differential rank + char-0 criterion

The field-theoretic core of route-c. For a `k`-domain `B` and a finite family `f : ι → B`, the
**generic differential rank** of `f` is the `K`-rank (`K = FractionRing B`) of the span of the
Kähler differentials `{D_k(f_i)}` in `Ω[K⁄k]`. The differential-independence criterion (char 0):

> every finite algebraically-independent family in `FractionRing B` has `FractionRing B`-linearly
> independent Kähler differentials.

The mechanism (Codex-vetted, decorrelated): a maximal algebraically-independent subfamily of `f` of
size `r = trdeg` has `K`-linearly-independent differentials in `Ω[K⁄k]`, because over a char-0
(hence perfect) base every field extension is **formally smooth**, so the Jacobi–Zariski
base-change map `K ⊗_E Ω[E⁄k] → Ω[K⁄k]` (`E = k(subfamily)`) is **injective** — and it carries the
`K`-basis
`{1 ⊗ D_E g_a}` of the purely-transcendental `Ω[E⁄k]` to `{D_K g_a}`. `CharZero` enters ONLY through
the perfect-field / formal-smoothness step.

The injectivity helper rests on `Algebra.H1Cotangent.exact_δ_mapBaseChange` + the `FormallySmooth`
instance `Subsingleton (H1Cotangent E K)`; the perfect-field formal smoothness is
`Algebra.FormallySmooth.of_perfectField` (needs `[EssFiniteType E K]`).

The `trdeg ≤ generic differential rank` wrapper that consumes this criterion lives in
`DLNFibre.Core.Dimension.Trdeg`.

**Dependency rule:** `Core` only — never import `DLNFibre.DLN`.
-/

namespace DLNFibre.Core

open Algebra KaehlerDifferential

universe u

/-! ## The generic differential rank -/

/-- The **generic differential rank** of a finite family `f : ι → B` in a `k`-domain `B`: the
`FractionRing B`-dimension of the span of the Kähler differentials `{D_k(f_i)}` in
`Ω[FractionRing B⁄k]`. This is the route-c "generic Jacobian rank", phrased Mathlib-natively as a
differential span. -/
noncomputable def genericDifferentialRank (k B : Type*) {ι : Type*} [Field k] [CommRing B]
    [IsDomain B] [Algebra k B] [Fintype ι] (f : ι → B) : ℕ :=
  Module.finrank (FractionRing B)
    (Submodule.span (FractionRing B)
      (Set.range fun i : ι ↦
        KaehlerDifferential.D k (FractionRing B) (algebraMap B (FractionRing B) (f i))))

/-! ## The Jacobi–Zariski base-change injectivity for a formally smooth top extension -/

/-- **Base-change injectivity from formal smoothness.** For a tower `k → E → K` with `K` formally
smooth over `E`, the Jacobi–Zariski map `mapBaseChange k E K : K ⊗_E Ω[E⁄k] → Ω[K⁄k]` is injective:
its kernel is the image of `δ : H1Cotangent E K → K ⊗ Ω[E⁄k]` (`exact_δ_mapBaseChange`), and formal
smoothness makes `H1Cotangent E K` a subsingleton, so that image is `0`. -/
theorem mapBaseChange_injective_of_formallySmooth (k E K : Type*) [Field k] [Field E] [Field K]
    [Algebra k E] [Algebra E K] [Algebra k K] [IsScalarTower k E K]
    [Algebra.FormallySmooth E K] :
    Function.Injective (KaehlerDifferential.mapBaseChange k E K) := by
  rw [injective_iff_map_eq_zero]
  intro x hx
  obtain ⟨y, rfl⟩ := (Algebra.H1Cotangent.exact_δ_mapBaseChange k E K x).mp hx
  rw [Subsingleton.elim y 0, map_zero]

/-! ## The char-0 differential-independence criterion (the scoped core) -/

/-- **The differential-independence criterion** (the char-0 core of A4.2), as a `Prop` on `(k, B)`:
every finite algebraically-independent family `x : Fin n → FractionRing B` over `k` has
`FractionRing B`-linearly-independent Kähler differentials `{D_k(x_i)}` in `Ω[FractionRing B⁄k]`.
PROVED in char 0 by `diffIndepCriterion_proof` (given `[EssFiniteType k (FractionRing B)]`). The
named `Prop` is kept as the clean interface the trdeg wrapper consumes. -/
def DiffIndepCriterion (k B : Type u) [Field k] [CommRing B] [IsDomain B] [Algebra k B] : Prop :=
  ∀ (n : ℕ) (x : Fin n → FractionRing B), AlgebraicIndependent k x →
    LinearIndependent (FractionRing B)
      (fun i ↦ KaehlerDifferential.D k (FractionRing B) (x i))

/-! ## Proof of the criterion in characteristic 0 -/

/-- **Base case (purely transcendental).** In `FractionRing (MvPolynomial (Fin n) k)`, the
differentials `{D_k(algebraMap (X i))}` are linearly independent: `Ω[FractionRing P⁄k]` is the
localization of the free `Ω[P⁄k]` (`KaehlerDifferential.isLocalizedModule_map`), so the
`mvPolynomialBasis` localizes to a linearly independent family
(`LinearIndependent.of_isLocalizedModule`), and `KaehlerDifferential.map_D` identifies its entries
with `D(algebraMap (X i))`. Char-free. -/
theorem linearIndependent_D_X_fractionRing (k : Type u) [Field k] (n : ℕ) :
    LinearIndependent (FractionRing (MvPolynomial (Fin n) k))
      (fun i : Fin n ↦ KaehlerDifferential.D k (FractionRing (MvPolynomial (Fin n) k))
        (algebraMap (MvPolynomial (Fin n) k) (FractionRing (MvPolynomial (Fin n) k))
          (MvPolynomial.X i))) := by
  set P := MvPolynomial (Fin n) k with hP
  set Pf := FractionRing P with hPf
  haveI : IsLocalizedModule (nonZeroDivisors P) (KaehlerDifferential.map k k P Pf) :=
    KaehlerDifferential.isLocalizedModule_map (R := k) (S := P) (T := Pf) (nonZeroDivisors P)
  have hb : LinearIndependent P (KaehlerDifferential.mvPolynomialBasis k (Fin n)) :=
    (KaehlerDifferential.mvPolynomialBasis k (Fin n)).linearIndependent
  have hli := hb.of_isLocalizedModule Pf (nonZeroDivisors P) (KaehlerDifferential.map k k P Pf)
  have heq : (KaehlerDifferential.map k k P Pf) ∘ (KaehlerDifferential.mvPolynomialBasis k (Fin n))
      = fun i ↦ KaehlerDifferential.D k Pf (algebraMap P Pf (MvPolynomial.X i)) := by
    funext i
    rw [Function.comp_apply, KaehlerDifferential.mvPolynomialBasis_apply, KaehlerDifferential.map_D]
  rwa [heq] at hli

/-- **The differential-independence criterion holds in characteristic 0** (given
`[EssFiniteType k (FractionRing B)]`). For an algebraically-independent
`x : Fin n → FractionRing B`, let `Pf = FractionRing (MvPolynomial (Fin n) k)` embed in
`K = FractionRing B` via the lift `j` of the injective `aeval x` (`IsFractionRing.liftAlgHom`). Then
`K` is formally smooth over the char-0 perfect field `Pf`
(`FormallySmooth.of_perfectField`, `EssFiniteType Pf K` by `of_comp`), so
`mapBaseChange k Pf K` is injective (`mapBaseChange_injective_of_formallySmooth`). It carries
`{1 ⊗ D_Pf(X_i)}` — `K`-independent by flat base change
(`Module.Flat.linearIndependent_one_tmul`) of the base case — to `{D_K(x_i)}`
(`mapBaseChange_tmul` + `map_D` + `lift_algebraMap`). `[CharZero k]` enters only at the
`PerfectField`/formal-smoothness step. -/
theorem diffIndepCriterion_proof (k B : Type u) [Field k] [CharZero k] [CommRing B] [IsDomain B]
    [Algebra k B] [Algebra.EssFiniteType k (FractionRing B)] :
    DiffIndepCriterion k B := by
  intro n x hx
  set P := MvPolynomial (Fin n) k with hP
  set Pf := FractionRing P with hPf
  have hxinj : Function.Injective (MvPolynomial.aeval x : P →ₐ[k] FractionRing B) :=
    algebraicIndependent_iff_injective_aeval.1 hx
  let j : Pf →ₐ[k] FractionRing B :=
    IsFractionRing.liftAlgHom (g := (MvPolynomial.aeval x : P →ₐ[k] FractionRing B)) hxinj
  letI : Algebra Pf (FractionRing B) := j.toRingHom.toAlgebra
  haveI : IsScalarTower k Pf (FractionRing B) :=
    IsScalarTower.of_algebraMap_eq fun r ↦ (j.commutes r).symm
  haveI : PerfectField Pf := PerfectField.ofCharZero
  haveI : Algebra.EssFiniteType Pf (FractionRing B) := Algebra.EssFiniteType.of_comp k Pf _
  haveI : Algebra.FormallySmooth Pf (FractionRing B) := Algebra.FormallySmooth.of_perfectField
  have hmbc : Function.Injective (KaehlerDifferential.mapBaseChange k Pf (FractionRing B)) :=
    mapBaseChange_injective_of_formallySmooth k Pf (FractionRing B)
  have hbase := linearIndependent_D_X_fractionRing k n
  have hflat : LinearIndependent (FractionRing B)
      ((1 : FractionRing B) ⊗ₜ[Pf] (fun i : Fin n ↦
        KaehlerDifferential.D k Pf (algebraMap P Pf (MvPolynomial.X i))) ·) :=
    Module.Flat.linearIndependent_one_tmul hbase
  have himg : ∀ i : Fin n, KaehlerDifferential.mapBaseChange k Pf (FractionRing B)
      ((1 : FractionRing B) ⊗ₜ[Pf]
        KaehlerDifferential.D k Pf (algebraMap P Pf (MvPolynomial.X i)))
      = KaehlerDifferential.D k (FractionRing B) (x i) := by
    intro i
    rw [KaehlerDifferential.mapBaseChange_tmul, one_smul, KaehlerDifferential.map_D]
    congr 1
    show (algebraMap Pf (FractionRing B)) (algebraMap P Pf (MvPolynomial.X i)) = x i
    rw [show (algebraMap Pf (FractionRing B)) = j.toRingHom from rfl]
    show j (algebraMap P Pf (MvPolynomial.X i)) = x i
    rw [IsFractionRing.liftAlgHom_apply, IsFractionRing.lift_algebraMap]
    simp [MvPolynomial.aeval_X]
  have hker : LinearMap.ker (KaehlerDifferential.mapBaseChange k Pf (FractionRing B)) = ⊥ :=
    LinearMap.ker_eq_bot.mpr hmbc
  have hmap := hflat.map' (KaehlerDifferential.mapBaseChange k Pf (FractionRing B)) hker
  have heq2 : (KaehlerDifferential.mapBaseChange k Pf (FractionRing B)) ∘
      ((1 : FractionRing B) ⊗ₜ[Pf] (fun i : Fin n ↦
        KaehlerDifferential.D k Pf (algebraMap P Pf (MvPolynomial.X i))) ·)
      = fun i ↦ KaehlerDifferential.D k (FractionRing B) (x i) := by
    funext i; exact himg i
  rwa [heq2] at hmap

end DLNFibre.Core
