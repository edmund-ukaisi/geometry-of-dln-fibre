# Thread 24 — localized fibre-component↔orbit iso `e` (rung 1) + dead-consumer hygiene (formaliser, #138) — certificate

**Formaliser tide (smooth-c2a).** New module `Core/FibreComponentOrbitIso.lean`, wired by the controller;
whole library green (3805 jobs); headline axiom-clean `[propext, Classical.choice, Quot.sound]`. Commits
`d80407bf` (rung 1), `d6870cce` (hygiene relabel).

## HEADLINE FINDING — the consumer-shaped `e` is globally FALSE; only a LOCALIZED full-d form is reachable
The variety iso in the consumer's shape `sweepFibreRing⧸I ≃ MvPolynomial η (orbitRing M_shifted)` is
**globally false / unreachable** (Codex xhigh, decisive): the chart `e_β` is intrinsically localized
(`gF = detSchurS`, not a unit mod `I`), so it only sees the dense open `D(g_I)`; the reachable object is
the LOCALIZED full-`d`-orbit form (poly wrapper on the FIBRE side, full-`d` orbit), and neither the
un-localized nor the shifted-orbit shape is extractable (cancellation invalid). This is the load-bearing
result of the thread.

## Rung 1 LANDED (axiom-clean) — "the heart"
`schurComponent_chartQuotientEquiv` : `SchurLoc ⊗_k (sweepFibreRing⧸I) ≃ₐ[k] (Away chartDsig)⧸chartComponentIdeal`
— the chart-localization component transport, via `tensorQuotientEquiv` (base change of a quotient) glued
to `reducedFibre_chartDsig_tensorEquiv_reducedVariety` by `Ideal.quotientEquivAlg`. Plus
`chartComponentIdeal` (the fibre component pulled to the localized chart along the keystone).

## Residual (rung 2, precisely costed, NOT built — ~mid-hundreds LoC, multi-tide)
`exists_chartComponent_localizedOrbitEquiv` — descend `(Away chartDsig)⧸chartComponentIdeal` to
`Away Δ (orbitRing (realizerD m))` via (i) the localization round-trip + dsig-avoidance bridge, (ii) the
localization-quotient ring iso inside `TopDimMinPrimesLocalization.ringKrullDim_quotient_map_localizationAway_eq`
(extract as `AlgEquiv`), (iii) the W0 sigma descent. Composing rung 1 + residual = the honest localized
`e`: `SchurLoc ⊗_k (R_F⧸I) ≃ₐ[k] Away Δ (orbitRing (realizerD m))`. Off the critical path (smoothness
fully unconditional; θ-count done); consumed by nothing.

## Hygiene (commit d6870cce) — two dead consumers RELABELED (not deleted; honest record preserved)
- `isSmoothAt_sweepFibre_of_component_orbitSmooth` (FibreGenericSmoothUncond) — ⚠ bare-orbitRing
  hypothesis dimensionally impossible (thread-20); valid-but-vacuous; SUPERSEDED by
  `isSmoothAt_sweepFibre_topComponent`.
- `isSmoothAt_sweepFibre_of_component_orbitPolyEquiv` (FibreComponentOrbit) — ⚠ shifted-orbit-poly
  hypothesis globally false/unreachable (thread-24); only a LOCALIZED iso is chart-supported; SUPERSEDED.
- The `FibreComponentOrbit` module header retitled honestly: its LIVE contribution is
  `exists_sigma_topComponent_orbitRingEquiv` (unconditional sigma-side labeling) + the reusable
  smooth-fp-domain ingredients; the orbit-iso route is superseded.

## Artifacts (committed @ d80407bf / d6870cce)
`threads/24-component-orbit-iso/statement-card.md` + eiso codex consult. Lean:
`Core/FibreComponentOrbitIso.lean`.
