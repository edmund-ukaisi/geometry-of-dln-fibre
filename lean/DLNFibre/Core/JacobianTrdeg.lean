import Mathlib.RingTheory.Kaehler.Basic
import Mathlib.RingTheory.Kaehler.JacobiZariski
import Mathlib.RingTheory.Etale.Kaehler
import Mathlib.RingTheory.Smooth.Field
import Mathlib.FieldTheory.Perfect
import Mathlib.RingTheory.AlgebraicIndependent.TranscendenceBasis
import Mathlib.RingTheory.AlgebraicIndependent.Adjoin
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.Finsupp.LinearCombination

/-!
# `DLNFibre.Core.JacobianTrdeg` — A4.2: the char-0 differential criterion `trdeg ≤ generic rank`

The field-theoretic core of route-c. For a `k`-domain `B` and a finite family `f : ι → B`, the
**generic differential rank** of `f` is the `K`-rank (`K = FractionRing B`) of the span of the Kähler
differentials `{D_k(f_i)}` in `Ω[K⁄k]`. The criterion (char 0):

> `(Algebra.trdeg k (Algebra.adjoin k (Set.range f))).toNat ≤ genericDifferentialRank k B f`.

The mechanism (Codex-vetted, decorrelated): a maximal algebraically-independent subfamily of `f` of
size `r = trdeg` has `K`-linearly-independent differentials in `Ω[K⁄k]`, because over a char-0 (hence
perfect) base every field extension is **formally smooth**, so the Jacobi–Zariski base-change map
`K ⊗_E Ω[E⁄k] → Ω[K⁄k]` (`E = k(subfamily)`) is **injective** — and it carries the `K`-basis
`{1 ⊗ D_E g_a}` of the purely-transcendental `Ω[E⁄k]` to `{D_K g_a}`. `CharZero` enters ONLY through
the perfect-field / formal-smoothness step.

The injectivity helper rests on `Algebra.H1Cotangent.exact_δ_mapBaseChange` + the `FormallySmooth`
instance `Subsingleton (H1Cotangent E K)`; the perfect-field formal smoothness is
`Algebra.FormallySmooth.of_perfectField` (needs `[EssFiniteType E K]`).

**Dependency rule:** `Core` only — never import `DLNFibre.DLN`.
-/

namespace DLNFibre.Core

open Algebra KaehlerDifferential

universe u

/-! ## The generic differential rank -/

/-- The **generic differential rank** of a finite family `f : ι → B` in a `k`-domain `B`: the
`FractionRing B`-dimension of the span of the Kähler differentials `{D_k(f_i)}` in `Ω[FractionRing B⁄k]`.
This is the route-c "generic Jacobian rank", phrased Mathlib-natively as a differential span. -/
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
every finite algebraically-independent family `x : η → FractionRing B` over `k` has `FractionRing B`-
linearly-independent Kähler differentials `{D_k(x_i)}` in `Ω[FractionRing B⁄k]`. In char 0 this holds
(perfect base ⟹ every field extension formally smooth ⟹ the Jacobi–Zariski base-change map
`K ⊗_E Ω[E⁄k] → Ω[K⁄k]` is injective for `E = k(x)`, carrying the purely-transcendental basis
`{D_E x_i}` to `{D_K x_i}`). It is the single open obligation of A4.2 — the `mapBaseChange`
injectivity helper (`mapBaseChange_injective_of_formallySmooth`) and the perfect-field formal
smoothness (`Algebra.FormallySmooth.of_perfectField`, needs `EssFiniteType`) supply two of its three
pieces; the missing piece is the `E`-freeness of `Ω[E⁄k]` on `{D_E x_i}` for `E` purely
transcendental (a localized `mvPolynomialBasis`, not packaged in Mathlib v4.29). -/
def DiffIndepCriterion (k B : Type u) [Field k] [CommRing B] [IsDomain B] [Algebra k B] : Prop :=
  ∀ {η : Type u} [Fintype η] (x : η → FractionRing B), AlgebraicIndependent k x →
    LinearIndependent (FractionRing B)
      (fun i ↦ KaehlerDifferential.D k (FractionRing B) (x i))

end DLNFibre.Core
