# Brief — `determinantal-atlas` expedition

## Central question

> **Build a Mathlib-grade, network-free `Core` library for determinantal rank geometry and its
> *constructive* pivot-chart atlas — the localization-overlap API, the determinantal rank-stratum
> API, and the per-pivot Schur trivializations with the cocycle-compatibility theorem (+ a
> recon-gated bare `FiberBundle` capstone) — and re-express the DLN rank-locus wrappers as
> instances of it.**

The fourth **build-the-buildable** expedition, on `origin/dev` `a13b11f2` (after #14 + FL-II + FL-III).
Source recommendation: `/tmp/next_foundational_expedition_recommendation.md` (Primary programme). Same
machine as FL-III — autonomous, per-phase stacked PRs, recon-gated capstone, decorrelated review on the
crux rungs.

## Why this is the right bedrock (operator-confirmed)
The chart machinery already exists, scattered through DLN wrappers (`dStratum`, `productRankLocusLE`,
`sigmaIdeal`, `RepCoord`) and fragile ad-hoc double-localizations. This expedition gives that structure its
honest, named, **constructive**, reusable form — standard determinantal algebraic geometry (rank loci, Schur
complements, principal-open localization cocycles), exactly the detail-at-scale the team is strong at. It is
**Core**, network-free; DLN *interfaces* (its rank-loci become instances), the same engine/application split
as the FL-III orbit squeeze. This is foundation-cleanliness/bedrock, not a stuck headline (fibre smoothness
already lands via the fp-domain shortcut without the bundle) — worth it because the math gets clean, uniform,
and computable.

## Constructive emphasis (a deliberate virtue)
The atlas is **explicit, finite, computable**: pivots = (`r`-subset of rows, `r`-subset of columns); each chart
`U_P = D(det A_P)` is a named principal open; each trivialization is the closed-form Schur complement
`D = C A⁻¹ B`; each transition is an explicit rational change of coordinates. Prefer the constructive object
over an abstract existence proof wherever both are available — the payoff is that anyone wanting to *compute*
(explicit sections, transition cocycles, intersection numbers) gets the whole atlas in closed form.

## Scope (layered; recon refines the rung ladder)

- **Phase 1 — foundation.** (1) **Localization-overlap API** (`Core/RingTheory/Localization/…`): double/triple
  principal-open overlaps as localizations at `f·g`, `f·g·h`; canonical `AlgEquiv`s between iterated
  presentations; `refl`/`symm`/`trans`/`algebraMap` transport; cocycle identities. (2) **Determinantal
  rank-stratum API** (`Core/…/Determinantal`): matrix coordinate rings, determinantal ideals, rank-`≤r`
  (closed) and rank-`=r` (open) strata, pivot principal opens, the **cover theorem** (rank-`r` matrices are
  covered by invertible-`r×r`-minor charts), Schur-complement coordinates, localized coordinate-ring isos,
  dimension/height formulas.
- **Phase 2 — the constructive atlas + capstone.** Per-pivot trivialization datum + standard fibre model
  (Schur base ring, fibre coordinate ring, tensor/structure-map/flatness, localization transport);
  transition maps on overlaps; the **cocycle-compatibility theorem** (transitions compose on triple overlaps
  → a coherent atlas). Then the **bare `FiberBundle` capstone** — *recon-gated* on the residue-field-rank
  bridge (see below).
- **Woven throughout — de-DLN-ify.** Re-express `productRankLocusLE`/`sigmaIdeal`/`dStratum`/`RepCoord` as
  instances of the Core determinantal API; keep DLN consumers green, signatures unchanged.

## The one discrimination call (recon-gated)
The **bare `FiberBundle` capstone** (Mathlib's abstract "locally trivial at every point") needs a
**residue-field-rank bridge**: at every prime `p`, rank-over-`κ(p)` `= r` ⟹ an `r`-minor is a unit ⟹ `p ∈`
some `U_P` (so the explicit charts cover *every scheme point*, not only the `k`-rational ones). On reflection
this is most likely **detail-at-scale** (basic-opens `D(fᵢ)` cover where the `fᵢ` generate the unit ideal, +
extend the minor↔rank API over residue fields), not a monument — but the recon confirms. **Build it if
detail-at-scale; if it is genuinely new/deep, the honest ceiling is the explicit atlas-with-cocycle (which is
already the full constructive object) and the bare-bundle leap is roadmapped.** The constructive atlas does not
depend on (b); (b) is abstract repackaging for Mathlib-API interop.

## Execution (operator-confirmed)
Drive Phase 1 → Phase 2 to completion, no pausing for merges; one **PR per phase** (stacked `det-atlas-p1` off
`origin/dev`, `det-atlas-p2` off `-p1`), async operator review. Recon (P0) first → refines the rung ladder +
locks the build-vs-cite boundary. Decorrelated review on the crux rungs (the cocycle compatibility; the
residue-field-rank bridge). Per rung: generalize/re-home, re-gate (L5), name=content, lessons L2–L8.

## Closing criteria
- The Core determinantal/atlas library packaged Mathlib-grade (overlap API + rank-stratum API + constructive
  pivot atlas + cocycle compatibility); green / sorry-free / axiom-clean; DLN rank-loci re-expressed as
  instances, DLN consumers + payoff axioms unchanged. The crux rungs reviewed.
- The bare `FiberBundle` capstone landed — OR, if the recon finds the residue-field-rank bridge is a monument,
  the atlas-with-cocycle ships as the honest ceiling and the bare-bundle leap is roadmapped (honestly recorded).
- The **RLCT generic-foundation programme written into [`ROADMAP.md`](../../ROADMAP.md)** (tracked, not built
  this expedition — operator's scope call).

## Provenance / boundaries
Recommendation `/tmp/next_foundational_expedition_recommendation.md`. Built on #14 + FL-II + FL-III.
**Out of scope:** the RLCT programme (roadmapped this expedition); char-`p` (dropped, scope); the top-dim
minimal-primes-vs-`k`-point-components clarification (lower priority — roadmap/stretch). **Blind** to
`expedition/aoyagi-full`.
