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
  ∀ (n : ℕ) (x : Fin n → FractionRing B), AlgebraicIndependent k x →
    LinearIndependent (FractionRing B)
      (fun i ↦ KaehlerDifferential.D k (FractionRing B) (x i))

/-! ## The trdeg wrapper: criterion ⟹ `trdeg ≤ genericDifferentialRank` -/

/-- **Differentials of a generated subalgebra lie in the span of the generators' differentials.**
For `x ∈ Algebra.adjoin k (Set.range g)` in a field `K`, `D_k(x)` is a `K`-combination of
`{D_k(g_i)}`: the set `{y | D y ∈ span}` is a `k`-subalgebra (`D` kills `k` by `map_algebraMap`,
the Leibniz rule keeps products inside, additivity keeps sums) containing every `g_i`, so it
contains the whole adjoin. -/
theorem D_adjoin_mem_span (k K : Type u) {ι : Type*} [Field k] [Field K] [Algebra k K]
    [Fintype ι] (g : ι → K) {x : K} (hx : x ∈ Algebra.adjoin k (Set.range g)) :
    KaehlerDifferential.D k K x ∈
      Submodule.span K (Set.range fun i ↦ KaehlerDifferential.D k K (g i)) := by
  set W := Submodule.span K (Set.range fun i ↦ KaehlerDifferential.D k K (g i)) with hW
  let S : Subalgebra k K :=
    { carrier := {y | KaehlerDifferential.D k K y ∈ W}
      mul_mem' := fun ha hb ↦ by
        simp only [Set.mem_setOf_eq, Derivation.leibniz] at ha hb ⊢
        exact W.add_mem (W.smul_mem _ hb) (W.smul_mem _ ha)
      add_mem' := fun ha hb ↦ by
        simp only [Set.mem_setOf_eq, map_add] at ha hb ⊢; exact W.add_mem ha hb
      algebraMap_mem' := fun r ↦ by
        simp only [Set.mem_setOf_eq, Derivation.map_algebraMap]; exact W.zero_mem }
  have hsub : Algebra.adjoin k (Set.range g) ≤ S := by
    rw [Algebra.adjoin_le_iff]; rintro _ ⟨i, rfl⟩
    exact Submodule.subset_span (Set.mem_range_self i)
  exact hsub hx

/-- **A4.2 trdeg wrapper (criterion-conditional).** Given the char-0 differential criterion
`DiffIndepCriterion k B`, the transcendence degree of `Algebra.adjoin k (Set.range f)` is at most the
generic differential rank of `f`:

> `(Algebra.trdeg k (Algebra.adjoin k (Set.range f))).toNat ≤ genericDifferentialRank k B f`.

A transcendence basis `s` of `adjoin k (range g)` (`g = algebraMap B (FractionRing B) ∘ f`) is finite
(f.g. domain ⟹ `trdeg < ℵ₀`) and algebraically independent in `K = FractionRing B`; the criterion makes
`{D_k(s_a)}` `K`-linearly independent, and each lies in the span (`D_adjoin_mem_span`), so
`#s = trdeg ≤ finrank(span) = genericDifferentialRank`. The trdeg over `B` matches the trdeg over `K`
(`AlgEquiv.trdeg_eq` through the injective `B ↪ FractionRing B`). This is the routine reduction; all
the char-0 content is the single hypothesis `DiffIndepCriterion`. -/
theorem trdeg_adjoin_le_genericDifferentialRank (k B : Type u) {ι : Type*} [Field k] [CommRing B]
    [IsDomain B] [Algebra k B] [Fintype ι] (f : ι → B) (hcrit : DiffIndepCriterion k B) :
    (Algebra.trdeg k (Algebra.adjoin k (Set.range f))).toNat ≤ genericDifferentialRank k B f := by
  classical
  set K := FractionRing B with hK
  set g : ι → K := fun i ↦ algebraMap B K (f i) with hg
  have hinj : Function.Injective (algebraMap B K) := IsFractionRing.injective B K
  let ψ : B →ₐ[k] K := IsScalarTower.toAlgHom k B K
  have hψinj : Function.Injective ψ := hinj
  have htreq : Algebra.trdeg k (Algebra.adjoin k (Set.range f))
      = Algebra.trdeg k (Algebra.adjoin k (Set.range g)) := by
    have himg : Algebra.adjoin k (Set.range g) = (Algebra.adjoin k (Set.range f)).map ψ := by
      rw [show (Set.range g) = ψ '' (Set.range f) by rw [← Set.range_comp]; rfl,
        Algebra.adjoin_image]
    rw [himg, AlgEquiv.trdeg_eq (Subalgebra.equivMapOfInjective _ ψ hψinj)]
  rw [htreq]
  set Ag := Algebra.adjoin k (Set.range g) with hAg
  set W := Submodule.span K (Set.range fun i ↦ KaehlerDifferential.D k K (g i)) with hW
  obtain ⟨s, hs⟩ := exists_isTranscendenceBasis k Ag
  set xK : s → K := fun a ↦ (Ag.val (a : Ag)) with hxK
  have halg : AlgebraicIndependent k xK := hs.1.map' (f := Ag.val) Subtype.val_injective
  haveI : Algebra.FiniteType k Ag := by
    rw [hAg]; exact Algebra.FiniteType.adjoin_of_finite (Set.finite_range g)
  have hcard : Cardinal.mk s = Algebra.trdeg k Ag := hs.cardinalMk_eq_trdeg
  have hlt : Algebra.trdeg k Ag < Cardinal.aleph0 := trdeg_lt_aleph0 (R := k) (S := Ag)
  have hsfin : s.Finite := by
    rw [Set.finite_coe_iff.symm, ← Cardinal.lt_aleph0_iff_finite, hcard]; exact hlt
  haveI : Fintype s := hsfin.fintype
  -- reindex `↥s ≃ Fin (card s)` to apply the `Fin`-indexed criterion, then transfer back
  let e : Fin (Fintype.card s) ≃ ↥s := (Fintype.equivFin s).symm
  have halgF : AlgebraicIndependent k (xK ∘ e) := halg.comp e e.injective
  have hliF : LinearIndependent K (fun i ↦ KaehlerDifferential.D k K ((xK ∘ e) i)) :=
    hcrit (Fintype.card s) (xK ∘ e) halgF
  have hli : LinearIndependent K (fun a ↦ KaehlerDifferential.D k K (xK a)) := by
    have h := hliF.comp e.symm e.symm.injective
    have heq : ((fun i ↦ KaehlerDifferential.D k K ((xK ∘ e) i)) ∘ e.symm)
        = fun a ↦ KaehlerDifferential.D k K (xK a) := by
      funext a; simp only [Function.comp_apply, Equiv.apply_symm_apply]
    rwa [heq] at h
  have hmem : ∀ a : s, KaehlerDifferential.D k K (xK a) ∈ W := fun a ↦
    D_adjoin_mem_span k K g (x := xK a) (a : Ag).2
  haveI : Module.Finite K W := Module.Finite.span_of_finite K (Set.finite_range _)
  have hliW : LinearIndependent K (fun a : s ↦ (⟨KaehlerDifferential.D k K (xK a), hmem a⟩ : W)) :=
    hli.of_comp W.subtype
  have hcardle : Fintype.card s ≤ Module.finrank K W := hliW.fintype_card_le_finrank
  have htn : (Algebra.trdeg k Ag).toNat = Fintype.card s := by
    rw [← hcard, Cardinal.mk_toNat_eq_card]
  rw [htn]
  exact hcardle

end DLNFibre.Core
