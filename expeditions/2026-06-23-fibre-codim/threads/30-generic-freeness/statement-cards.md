# Statement cards — thread 30 (generic freeness, b-build rung 1)

Module: `lean/DLNFibre/Core/GenericFreeness.lean`. Build: green; sorries 0; axioms
`[propext, Classical.choice, Quot.sound]` (Mathlib-standard) on all four theorems.

---

## `Module.FinitePresentation.exists_free_localizedModule_of_isDomain` (primitive core)

```
theorem Module.FinitePresentation.exists_free_localizedModule_of_isDomain
    {R : Type*} [CommRing R] [IsDomain R]
    (M : Type*) [AddCommGroup M] [Module R M] [Module.FinitePresentation R M] :
    ∃ r : R, r ≠ 0 ∧
      Module.Free (Localization (.powers r)) (LocalizedModule (.powers r) M)
```

- **Claim type:** PROVED (engine, network-free; `DLNFibre.Core`).
- **What it says:** generic freeness, module case — a finitely presented module over an integral
  domain is free after inverting one nonzero element. (Weakest-hypothesis core: only
  `[IsDomain]` + `[FinitePresentation]`, no Noetherian.)
- **Proof:** localize at `nonZeroDivisors R`; `FractionRing R` is a field so the localized module
  is `Module.Free` automatically; `Module.FinitePresentation.exists_free_localizedModule_powers`
  (Mathlib) descends freeness to a single `r ∈ nonZeroDivisors R`; `nonZeroDivisors.ne_zero` gives
  `r ≠ 0`.
- **Fidelity note:** `Localization (.powers r) = R[1/r]`; `LocalizedModule (.powers r) M = M[1/r]`.
  The conclusion is exactly "free after inverting one element," and `r ≠ 0` makes `D(r)` nonempty
  (contains the generic point `(0)`) in a domain, so non-vacuous.

## `Module.exists_free_localizedModule_of_isDomain` (Noetherian + finite corollary)

```
theorem Module.exists_free_localizedModule_of_isDomain
    {R : Type*} [CommRing R] [IsNoetherianRing R] [IsDomain R]
    (M : Type*) [AddCommGroup M] [Module R M] [Module.Finite R M] :
    ∃ r : R, r ≠ 0 ∧
      Module.Free (Localization (.powers r)) (LocalizedModule (.powers r) M)
```

- **Claim type:** PROVED. Standard-hypotheses form (Noetherian domain + f.g. module);
  `Module.finitePresentation_of_finite` bridges `Finite → FinitePresentation`.

## `Module.exists_flat_localizedModule_of_isDomain` (flat form — rung-2 interface)

```
theorem Module.exists_flat_localizedModule_of_isDomain
    {R : Type*} [CommRing R] [IsNoetherianRing R] [IsDomain R]
    (M : Type*) [AddCommGroup M] [Module R M] [Module.Finite R M] :
    ∃ r : R, r ≠ 0 ∧
      Module.Flat (Localization (.powers r)) (LocalizedModule (.powers r) M)
```

- **Claim type:** PROVED. `Module.Free ⟹ Module.Flat` (instance). This is the form rung 2 feeds to
  `Algebra.HasGoingDown.of_flat` (where the module IS the localized chart ring).

## `Module.exists_basicOpen_subset_freeLocus_of_isDomain` (freeLocus density form)

```
theorem Module.exists_basicOpen_subset_freeLocus_of_isDomain
    {R : Type*} [CommRing R] [IsNoetherianRing R] [IsDomain R]
    (M : Type*) [AddCommGroup M] [Module R M] [Module.Finite R M] :
    ∃ r : R, r ≠ 0 ∧ (basicOpen r : Set (PrimeSpectrum R)) ⊆ Module.freeLocus R M
```

- **Claim type:** PROVED. The genericity/density content the scout flagged Mathlib was missing:
  `Module.freeLocus R M` contains a nonempty `D(r)` (`r ≠ 0`), hence is dense in the irreducible
  `PrimeSpectrum R`. (Openness alone is the existing `isOpen_freeLocus`; density is new.) Via
  `Module.basicOpen_subset_freeLocus_iff` (Mathlib) + Free ⟹ Projective.

---

## Scope / honest boundary (DO NOT overclaim)

This is the **finite-MODULE** case of Grothendieck generic freeness, NOT the full statement for a
finitely-generated `R`-**algebra** `B` (relative dim possibly > 0, e.g. `B = R[X]`). The algebra
case is strictly stronger (EGA IV 6.9.1: Noether normalization on top of dévissage) and is **absent
from Mathlib** (no `FiniteType`-flat-on-open lemma) — it is a separate, larger build, NOT done here.
The theorem names carry `Module.`/`localizedModule`, not a bare `genericFreeness`, to mark this.

**Consumer caveat (Codex-flagged, load-bearing for rung 2):** these theorems give flatness of a ring
map `R → S` only when `S` is **module-finite** over `R`. If the fibre-codimension chart map is only
finite-type-as-algebra over the base localization, rung 2 needs the algebra-finite-type extension
(roadmapped), not this module case. Whether the chart map is module-finite is a rung-2/rung-3
question (the chart ring is not yet formalised on this branch).

## Rung-2 entry point (precise flat-bridge)

Rung 2 consumes `Module.exists_flat_localizedModule_of_isDomain`. The bridge from this *module*
flatness to the *ring-map* flatness `Algebra.HasGoingDown.of_flat` wants:

- Take `M := S` = the chart ring, as a module over the base `R` (module-finite — see scope caveat).
  The theorem yields `Module.Flat (Localization (.powers r)) (LocalizedModule (.powers r) S)` for a
  nonzero `r` in the base.
- **When the module IS the ring, `Module.Flat = Algebra.Flat`.** Mathlib represents flatness of a
  ring map `A → B` as `Module.Flat A B` (the target ring regarded as an `A`-module). So
  `Module.Flat (R_r) (S_r)` is exactly `Algebra.Flat (R_r) (S_r)` once `S_r` carries the
  `Algebra (R_r)` instance — no conceptual gap. Feed to `Algebra.HasGoingDown.of_flat` → the LANDED
  `Core.FlatQuasiFiniteHeight` (`Ideal.height_eq_under_of_flat_quasiFiniteAt`) /
  `Core.SmoothLocalRelativeDimension`.
- **One Lean pitfall (Codex):** if rung 2's localized chart ring is a *different type* than
  `LocalizedModule (.powers r) S`, transport flatness across the relevant `AlgEquiv`/`LinearEquiv`,
  or define the localized chart via `LocalizedModule` from the start so the instances line up.
- Prefer `Localization (.powers r)` / `Submonoid.powers r` consistently over `Localization.Away r`
  (morally identical, but mixing causes avoidable unification work).

## Non-circularity

Generic freeness is a general commutative-algebra theorem with no reference to the DLN setup, type-A
quivers, or the fibre — it cannot re-enter the R2-3b-4 reducedness circularity (dimension/freeness is
radical-insensitive). It rests only on the Mathlib substrate
(`exists_free_localizedModule_powers` + field-modules-are-free), not on any in-repo result.
