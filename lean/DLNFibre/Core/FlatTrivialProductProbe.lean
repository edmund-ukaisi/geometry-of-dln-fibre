import Mathlib.RingTheory.Flat.Basic
import Mathlib.RingTheory.Flat.Stability
import Mathlib.RingTheory.Flat.Localization
import Mathlib.RingTheory.RingHom.Flat
import Mathlib.RingTheory.MvPolynomial.Basic
import Mathlib.LinearAlgebra.TensorProduct.Basis
import Mathlib.RingTheory.Ideal.GoingDown
import Mathlib.RingTheory.Ideal.KrullsHeightTheorem

/-!
# `DLNFibre.Core.FlatTrivialProductProbe` — the L1-0 `Module.Flat` API-surface contract

**Status: API contract / checkpoint artefact, NOT the L1-0 theorem.** L1-0 (flatness of `mult`
restricted to a rank-`r` chart) was **checkpointed, not proved** (thread 04, 2026-06-23): the
`Module.Flat` *API* is fully viable at Mathlib v4.29 — every lever the local-triviality⟹trivial-
product⟹free⟹flat route needs is present and compiles (the `example`-blocks below are the durable
pins) — but the route is **unreachable this run** because the prerequisite object is missing: there
is no coordinate-ring pullback `A →+* B` of `mult` (the engine carries `mult` only as a *set-level*
function on `Tuple d`, with codim read through `vanishingIdeal`/`Ideal.height`; no `Spec`, no
scheme, no algebra map between the base/total coordinate quotient rings). Building that ring map +
the
determinantal chart localisation + the section-of-the-torsor trivialisation is a from-scratch
affine-AG construction (≈ 8–12 modules), not an API gap. See the thread-04 report for the verdict
and the recommended fallback (the two-inequality dimension sandwich).

This module records the **verified-present API** as `example`-blocks so the next attempt (or the
real L1-0, once the ring map exists) can stand on confirmed contracts rather than re-probing.

**Dependency rule:** `Core` only — never import `DLNFibre.DLN`.
-/

namespace DLNFibre.Core.FlatProbe

open scoped TensorProduct

universe u

/-! ## Free ⟹ flat, and the polynomial / tensor trivial-product shapes -/

/-- Free modules are flat (instance), the base of the route. -/
example (A M : Type u) [CommRing A] [AddCommGroup M] [Module A M] [Module.Free A M] :
    Module.Flat A M := inferInstance

/-- `MvPolynomial (Fin r) A` is free, hence flat, over `A` — the trivial-product model fibre. -/
example (A : Type u) [CommRing A] (r : ℕ) :
    Module.Flat A (MvPolynomial (Fin r) A) := inferInstance

/-- Tensor of frees is free over the base — the `A ⊗ F` trivial-product shape. -/
example (A F : Type u) [CommRing A] [AddCommGroup F] [Module A F] [Module.Free A F] :
    Module.Free A (A ⊗[A] F) := inferInstance

/-! ## Transport flatness across an equivalence (the "B ≃ free" closer) -/

/-- Flatness transports across a linear equivalence. -/
example (A M N : Type u) [CommRing A] [AddCommGroup M] [Module A M] [AddCommGroup N] [Module A N]
    [Module.Flat A M] (e : N ≃ₗ[A] M) : Module.Flat A N :=
  Module.Flat.of_linearEquiv e

/-- Flatness transports across an *algebra* equivalence: `B ≃ₐ[A] (free A-algebra)` gives
`Module.Flat A B` — the one-liner the route ends on, once such an equivalence exists. -/
example (A B : Type u) [CommRing A] [CommRing B] [Algebra A B] (r : ℕ)
    (e : B ≃ₐ[A] MvPolynomial (Fin r) A) : Module.Flat A B :=
  Module.Flat.of_linearEquiv e.toLinearEquiv

/-- Flatness composes along a tower `A → S → M` (`Module.Flat.trans`). -/
example (A S M : Type u) [CommRing A] [CommRing S] [AddCommGroup M] [Algebra A S]
    [Module A M] [Module S M] [IsScalarTower A S M] [Module.Flat A S] [Module.Flat S M] :
    Module.Flat A M := Module.Flat.trans A S M

/-! ## Flat-local-on-base, scheme-free (the local-triviality lever, when the ring map exists)

`mult : Σ^r → Mat^{rk=r}` is Zariski-*locally* (not globally) trivial, so the route needs a
flat-local-on-base lemma. Mathlib v4.29 has it at the **ring/module level, no schemes** — the
levers to glue per-chart freeness into global flatness over the base. They are unusable here only
because no `algebraMap A B` for `mult` exists yet. -/

/-- **Module-level flat-local-on-base.** To prove `Module.Flat R M` it suffices to prove flatness of
`LocalizedModule.Away r M` for each `r` in a spanning set `s ⊆ S` (a principal-open cover) — the
scheme-free local-triviality lever (`Module.flat_of_localized_span`). -/
example (R M : Type u) [CommRing R] [AddCommGroup M] [Module R M]
    (s : Set R) (spn : Ideal.span s = ⊤)
    (h : ∀ r : s, Module.Flat R (LocalizedModule.Away r.1 M)) : Module.Flat R M :=
  Module.flat_of_localized_span (S := R) (M := M) s spn h

/-- **Ring-hom-level flat-local-on-base.** `RingHom.Flat` is a local property: its `propertyIsLocal`
bundles `ofLocalizationSpanTarget`, `ofLocalizationSpan`, composition stability, and iso-respect —
the descent package for gluing per-chart flatness of a ring map. -/
example : RingHom.PropertyIsLocal @RingHom.Flat := RingHom.Flat.propertyIsLocal

/-! ## Downstream levers (NOT in L1-0 scope — confirming they sit on `Module.Flat`)

These belong to L1-1 (a later tide); pinned here only to confirm the flatness fact, once proved,
feeds the height-additivity squeeze with no further hypothesis beyond Noetherianity. -/

/-- Flat ⟹ going-down (instance). -/
example (A B : Type u) [CommRing A] [CommRing B] [Algebra A B] [Module.Flat A B] :
    Algebra.HasGoingDown A B := inferInstance

/-- The height-additivity lemma sits on going-down + Noetherianity (both rings Noetherian). -/
example (A B : Type u) [CommRing A] [CommRing B] [Algebra A B] [IsNoetherianRing A]
    [IsNoetherianRing B] [Algebra.HasGoingDown A B]
    (p : Ideal A) [p.IsPrime] (P : Ideal B) [P.IsPrime] [P.LiesOver p] :
    P.height = p.height + (P.map (Ideal.Quotient.mk (p.map (algebraMap A B)))).height :=
  Ideal.height_eq_height_add_of_liesOver_of_hasGoingDown p P

end DLNFibre.Core.FlatProbe
