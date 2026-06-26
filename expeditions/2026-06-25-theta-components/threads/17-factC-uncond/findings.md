# Thread 17 — fact (C) unconditional smoothness (C1+C2+C3) (formaliser, #110) — certificate

**Formaliser tide.** Two new modules, wired by the controller; whole library green (3788 jobs); headlines
axiom-clean `[propext, Classical.choice, Quot.sound]` (controller-gated); reviewer PASS-WITH-NOTES
(actioned). Commits `72b2ed2b` / `e37e3317` / `3e89db24`.

## HEADLINE — generic smoothness is now UNCONDITIONAL except ONE named geometric fact (C2(a))
Thread 16's hypothesis (`IsSmoothAt` of `sweepFibreRing`) is discharged down to a single pure-algebra
identification: the `k`-algebra iso `sweepFibreRing ⧸ I ≃ₐ[k] orbitRing M` for each top-component minimal
prime `I` (fibre-component ↔ orbit-closure). Everything else is unconditional.

## C1 — UNCONDITIONAL (reusable CA, `Core/LocalizationAtComponent.lean`)
- `localizationAtPrimeQuotientAlgEquiv` — for reduced Noetherian `R`, a prime `q` meeting exactly one
  minimal prime `I`: `Loc.AtPrime R q ≃ₐ[k] Loc.AtPrime (R⧸I) (q.map mk)`. **This is thread-16 sub-wall
  (a), now banked.**
- `isSmoothAt_of_isSmoothAt_quotient_unique_minimalPrime`, `…_minimalPrime_of_componentEquiv_domain`
  (the `IsSmoothAt` bridges), the domain generic-point lemma, the AlgEquiv-comap transport.
- **Sub-wall (b) DISSOLVED:** the "q meets exactly one component" hypothesis is FREE for `q = I` by
  minimal-prime incomparability.

## C3 — UNCONDITIONAL (`Core/FibreGenericSmoothUncond.lean`)
- `isSmoothAt_chartDsig_of_isSmoothAt_sweepFibre` + keystones `awayTensorRightAlgEquiv` /
  `schurTensorAwayAlgEquiv` (`S ⊗ Away g ≃ Away (1⊗g)`): transports thread-16's
  `Smooth k (SchurLoc ⊗ Away g)` to `IsSmoothAt k p (Away chartDsig)` across the banked chart iso
  (`reducedFibre_chartDsig_tensorEquiv_reducedVariety`).
- `sweepFibreRing` reduced + Noetherian instances.

## THE SOLE REMAINING OPEN INPUT — C2(a) (the wall, task #119)
`isSmoothAt_sweepFibre_of_component_orbitSmooth` consumes the iso `sweepFibreRing ⧸ I ≃ₐ[k] orbitRing M`
(per top-component minimal prime `I`) and discharges everything else (applies `OrbitSmooth` to the orbit
ring, transports back via C1). Codex (decorrelated ×2) + reviewer confirm: **HONEST reduction —
load-bearing, non-circular, non-vacuous.** C2(a) is a genuine multi-module wall NOT in the harness
(~800–2000 lines): needs a fibre-component ↔ orbit-closure theory
(`topDim_sweepFibre_component_equiv_orbitRing`) — the θ-count chain establishes the *count* but never
*labels a component by an orbit*. Bounded (NOT the months-scale reducedness wall), but real.

## Net smoothness state (controller synthesis)
Generic smoothness = **C1 + C3 unconditional + axiom-clean; the single fact C2(a) (fibre-component ≅
orbit-ring, pen-and-paper-bedrock via thread-14) carried as a named, honest, non-circular hypothesis.**
Tighter than thread-16's conditional (which carried the whole `IsSmoothAt`); the residual is now a pure
algebraic identification with a precisely-costed formalization (~800–2000 lines).

## Artifacts (committed @ 72b2ed2b / e37e3317 / 3e89db24)
`threads/17-factC-uncond/statement-card-*.md` + codex consults. Lean: `Core/LocalizationAtComponent.lean`
(reusable CA, spin-out candidate), `Core/FibreGenericSmoothUncond.lean`. Untouched the B3 tides' files.
