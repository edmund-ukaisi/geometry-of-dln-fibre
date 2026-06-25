/-
Copyright (c) 2026. Released under Apache 2.0; see LICENSE.
-/
import Mathlib.RingTheory.Localization.Free
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.RingTheory.Spectrum.Prime.FreeLocus
import Mathlib.Algebra.Module.FinitePresentation

/-!
# Generic freeness for a finite module over a domain (Grothendieck's lemma, module case)

For an integral domain `R` and a finitely *presented* `R`-module `M`, there is a nonzero `r ∈ R`
such that the localization `M[1/r]` is **free** over `R[1/r]` (hence flat; equivalently the free
locus of `M` contains the dense basic open `D(r)`). When `R` is Noetherian, "finitely presented"
weakens to "finitely generated". This is the network-free engine input the non-circular
fibre-codimension route consumes: generic flatness of the chart map on a dense open of the base, fed
to the going-down/relative-dimension machinery.

Mathlib v4.29 carries the *substrate* —
`Module.FinitePresentation.exists_free_localizedModule_powers` (free on a localization at a
submonoid descends to free after inverting a single element) and the `Module.freeLocus`
development — but not generic freeness itself. We obtain it by applying the descent lemma at the
fraction field: over the field `FractionRing R` every module is free, so the localization of `M` at
the nonzero divisors is automatically free, and the descent hands back a single nonzero
`r ∈ nonZeroDivisors R`.

**Scope.** This is the *finite-module* case of generic freeness. The full Grothendieck statement
for a finitely-generated `R`-*algebra* `B` (relative dimension possibly positive, e.g. `B = R[X]`)
is a strictly stronger theorem (EGA IV 6.9.1, by Noether normalization on top of dévissage) and is
**not** covered here; a consumer whose `B` is only finite-type-as-algebra over the base needs that
extension. When the chart ring is module-finite over the base, this module case suffices directly.

## Main results
- `Module.FinitePresentation.exists_free_localizedModule_of_isDomain` — primitive core (free form,
  `[FinitePresentation]`).
- `Module.exists_free_localizedModule_of_isDomain` — Noetherian + finite corollary (free form).
- `Module.exists_flat_localizedModule_of_isDomain` — flat form (the interface for going-down).
- `Module.exists_basicOpen_subset_freeLocus_of_isDomain` — `freeLocus` density form.
-/

open scoped nonZeroDivisors
open PrimeSpectrum

namespace Module

section FinitePresentation

variable {R : Type*} [CommRing R] [IsDomain R]
variable (M : Type*) [AddCommGroup M] [Module R M] [Module.FinitePresentation R M]

/-- **Generic freeness** (Grothendieck, module case), primitive form. Over an integral domain `R`, a
finitely *presented* module `M` becomes free after inverting a single nonzero element `r`: `M[1/r]`
is free over `R[1/r]`.

Proof: localize at the nonzero divisors. The result `LocalizedModule (nonZeroDivisors R) M` is a
module over the field `FractionRing R`, hence free; `exists_free_localizedModule_powers` descends
that freeness to `Localization (.powers r)` for some `r` in the nonzero divisors, which is nonzero
in a domain. -/
theorem FinitePresentation.exists_free_localizedModule_of_isDomain :
    ∃ r : R, r ≠ 0 ∧
      Module.Free (Localization (.powers r)) (LocalizedModule (.powers r) M) := by
  obtain ⟨r, hr, hfree, _⟩ :=
    Module.FinitePresentation.exists_free_localizedModule_powers
      (S := nonZeroDivisors R) (R := R) (M := M)
      (f := LocalizedModule.mkLinearMap (nonZeroDivisors R) M)
      (Rₛ := FractionRing R)
      (M' := LocalizedModule (nonZeroDivisors R) M)
  exact ⟨r, nonZeroDivisors.ne_zero hr, hfree⟩

end FinitePresentation

section NoetherianFinite

variable {R : Type*} [CommRing R] [IsNoetherianRing R] [IsDomain R]
variable (M : Type*) [AddCommGroup M] [Module R M] [Module.Finite R M]

/-- **Generic freeness** (Grothendieck, module case). Over a Noetherian integral domain `R`, a
finitely *generated* module `M` becomes free after inverting a single nonzero element `r`. Over a
Noetherian ring, `Module.Finite` gives `Module.FinitePresentation`. -/
theorem exists_free_localizedModule_of_isDomain :
    ∃ r : R, r ≠ 0 ∧
      Module.Free (Localization (.powers r)) (LocalizedModule (.powers r) M) := by
  have : Module.FinitePresentation R M := Module.finitePresentation_of_finite R M
  exact Module.FinitePresentation.exists_free_localizedModule_of_isDomain M

/-- **Generic flatness** (flat form of generic freeness): over a Noetherian integral domain, a
finitely generated module is flat after inverting a single nonzero element. This is the interface
the relative fibre-dimension rung consumes (flat ⟹ going-down on the dense open `r ≠ 0`). -/
theorem exists_flat_localizedModule_of_isDomain :
    ∃ r : R, r ≠ 0 ∧
      Module.Flat (Localization (.powers r)) (LocalizedModule (.powers r) M) := by
  obtain ⟨r, hr, hfree⟩ := exists_free_localizedModule_of_isDomain (R := R) M
  have : Module.Free (Localization (.powers r)) (LocalizedModule (.powers r) M) := hfree
  exact ⟨r, hr, inferInstance⟩

/-- **Density of the free locus** (`freeLocus` form). Over a Noetherian integral domain, the free
locus of a finitely generated module contains a nonempty basic open `D(r)` with `r ≠ 0` — hence it
is a *dense* open of the irreducible `PrimeSpectrum R`. (Openness alone is `isOpen_freeLocus`;
density is the new genericity content.) -/
theorem exists_basicOpen_subset_freeLocus_of_isDomain :
    ∃ r : R, r ≠ 0 ∧ (basicOpen r : Set (PrimeSpectrum R)) ⊆ Module.freeLocus R M := by
  have : Module.FinitePresentation R M := Module.finitePresentation_of_finite R M
  obtain ⟨r, hr, hfree⟩ := exists_free_localizedModule_of_isDomain (R := R) M
  refine ⟨r, hr, ?_⟩
  rw [Module.basicOpen_subset_freeLocus_iff]
  have : Module.Free (Localization (.powers r)) (LocalizedModule (.powers r) M) := hfree
  infer_instance

end NoetherianFinite

end Module

/-- Non-vacuity witness: the headline applies to `M = R = ℚ[X]` (a Noetherian domain, `M` free of
rank 1), so the existential is inhabited. -/
example : ∃ r : Polynomial ℚ, r ≠ 0 ∧
    Module.Free (Localization (.powers r)) (LocalizedModule (.powers r) (Polynomial ℚ)) :=
  Module.exists_free_localizedModule_of_isDomain (Polynomial ℚ)
