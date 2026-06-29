import DLNFibre.Core.RingTheory.Kaehler.GenericRank
import Mathlib.RingTheory.AlgebraicIndependent.TranscendenceBasis
import Mathlib.RingTheory.AlgebraicIndependent.Adjoin
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.LinearAlgebra.Dimension.Finrank

/-!
# `DLNFibre.Core.Dimension.Trdeg` — the `trdeg ≤ generic differential rank` bridge

The transcendence-degree wrapper over the char-0 differential-independence criterion
(`DiffIndepCriterion`, in `Core.RingTheory.Kaehler.GenericRank`): for a `k`-domain `B` and a finite
family `f : ι → B`,

> `(Algebra.trdeg k (Algebra.adjoin k (Set.range f))).toNat ≤ genericDifferentialRank k B f`,

conditional on `DiffIndepCriterion k B` (which holds in char 0 by `diffIndepCriterion_proof`). The
characteristic enters ONLY through that criterion hypothesis; the reduction here is char-free.

**Dependency rule:** `Core` only — never import `DLNFibre.DLN`.
-/

namespace DLNFibre.Core

open Algebra KaehlerDifferential

universe u

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
`DiffIndepCriterion k B`, the transcendence degree of `Algebra.adjoin k (Set.range f)` is at most
the generic differential rank of `f`:

> `(Algebra.trdeg k (Algebra.adjoin k (Set.range f))).toNat ≤ genericDifferentialRank k B f`.

A transcendence basis `s` of `adjoin k (range g)` (`g = algebraMap B (FractionRing B) ∘ f`) is
finite (f.g. domain ⟹ `trdeg < ℵ₀`) and algebraically independent in `K = FractionRing B`; the
criterion makes `{D_k(s_a)}` `K`-linearly independent, and each lies in the span
(`D_adjoin_mem_span`), so `#s = trdeg ≤ finrank(span) = genericDifferentialRank`. The trdeg over `B`
matches the trdeg over `K` (`AlgEquiv.trdeg_eq` through the injective `B ↪ FractionRing B`). This is
the routine reduction; all
the char-0 content is the single hypothesis `DiffIndepCriterion` (which holds in char 0 by
`diffIndepCriterion_proof`). -/
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
