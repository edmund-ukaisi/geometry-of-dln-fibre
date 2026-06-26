# Thread 20 (transport) — generic smoothness FULLY UNCONDITIONAL (#128) — certificate

**Formaliser tide (smooth-c2a, resumed).** New module `Core/FibreComponentOrbitTransport.lean` (225
LoC), wired by the controller; whole library green (3803 jobs); headlines axiom-clean
`[propext, Classical.choice, Quot.sound]` (controller-gated); reviewer PASS + decorrelated Codex.
Commit `a0028ed4`.

## HEADLINE — generic smoothness of the DLN fibre is FULLY UNCONDITIONAL
`isSmoothAt_sweepFibre_topComponent [IsAlgClosed k] (d r hp hq) (I) (hI : I ∈ TopDimMinPrimes
(sweepFibreRing …)) : Algebra.IsSmoothAt k I` — the reduced fibre is smooth at the generic point of
EVERY top-dimensional component. NO open hypothesis. And `exists_isSmoothAt_chartDsig_unconditional` —
the source pivot chart is smooth on a basic open, unconditionally.

## The shortcut — the orbit-iso detour (C2(a)) was UNNECESSARY
The tide first scoped #128 as the ~400–900-LoC labeled chart-localization component `AlgEquiv` (the
fibre≅orbit×A^δ iso), then found a far shorter route that bypasses orbits entirely:
- A fibre top component `sweepFibreRing⧸I` (I a minimal prime) is a finitely-presented **DOMAIN**.
- Over an algebraically closed (hence perfect) field, a finite-presentation domain is **generically
  smooth** — smooth at its generic point `⊥` (`isSmoothAt_bot_of_finitePresentation_domain`, the
  generic-smoothness theorem). NO orbit identification is needed — the component need not *be* an orbit
  closure, only a domain.
- The C1 bridge (`isSmoothAt_minimalPrime_of_isSmoothAt_quotient` + `isSmoothAt_of_ideal_eq` via
  `Ideal.map_quotient_self`) lifts `IsSmoothAt k ⊥` of the component ring to `IsSmoothAt k I` of
  `sweepFibreRing`.
- C3 / thread-17 chart transport (`isSmoothAt_chartDsig_of_isSmoothAt_sweepFibre`) carries it to the
  actual fibre chart `Away chartDsig`.
**Lesson:** the OrbitSmooth machinery (threads 16/17/20-consumer) was a red herring for SMOOTHNESS — the
generic-smoothness-of-a-domain theorem is the direct route. The orbit identification matters for *labeling*
(the bundle / a structural description), not for *smoothness*.

## Supporting lemmas (all axiom-clean)
- `isSmoothAt_bot_of_finitePresentation_domain [IsAlgClosed k]` — fp domain ⟹ `IsSmoothAt k ⊥`.
- `mem_smoothLocus_iff_isSmoothAt`, `specHom_localRingHom_formallySmooth_iff`,
  `comap_algebraMap_specHom_eq_bot` — the smooth-locus / generic-point plumbing.
- `isSmoothAt_sweepFibre_component` — the general (any minimal prime) version; the topComponent headline
  is its specialisation.

## Bonus (still banked, thread 20 #124) — NOT needed for smoothness
`exists_sigma_topComponent_orbitRingEquiv` (the unconditional sigma-side component↔orbit labeling)
remains a genuine standalone result, and the corrected consumer
`isSmoothAt_sweepFibre_of_component_orbitPolyEquiv` — useful for a future structural description, but the
smoothness headline does NOT route through them.

## Net state — SMOOTHNESS CLOSED
Generic smoothness of the DLN fibre is fully unconditional + axiom-clean over `[IsAlgClosed k]`
(+ `[Infinite k]` for the chart form). The scope-3 smoothness deliverable is COMPLETE.

## Artifacts (committed @ a0028ed4)
`threads/20-component-orbit/statement-card-fibreComponentOrbitTransport.md` + codex consults
(construct + redteam). Lean: `Core/FibreComponentOrbitTransport.lean`.
