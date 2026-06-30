# Priorities — `determinantal-atlas` (taste ledger)

Controller proposes by VOI; **operator edits this file directly**. Build-the-buildable
([`../../docs/policies/library-building.md`](../../docs/policies/library-building.md)). Scoped against
`origin/dev` `a13b11f2` (post #14 + FL-II + FL-III). **Live status → [`threads.md`](threads.md).** The recon
(P0) refines this ladder + locks the build-vs-cite boundary before Phase 1 dispatch.

## P0 — recon (scout)  ·  branch `det-atlas-p1`
Map, before committing the ladder:
- **Current state:** what the existing DLN rank-chart/bundle machinery already proves (`productRankLocusLE`,
  `sigmaIdeal`, `dStratum`, `RepCoord`, the per-pivot bundle, the existing Schur/localization pieces) — what's
  reusable-as-is vs DLN-fused.
- **Mathlib coverage:** determinantal ideals, `Matrix.rank` / minors API, `Localization.Away` + iterated
  localization isos, `FiberBundle`/local-triviality vocabulary, Schur-complement lemmas. Present vs absent.
- **The build-vs-cite call:** the **residue-field-rank bridge** for the bare-`FiberBundle` capstone — is it
  detail-at-scale (basic-opens-cover + minor↔rank over `κ(p)`) or a genuine monument? Verdict gates Phase 2's
  capstone (build vs roadmap), like FL-III's P2.0 probe.
- Output: the refined P1/P2 rung ladder + the build-vs-cite ledger + the de-DLN-ify target list.

## Phase 1 — foundation (overlap API + determinantal rank-stratum)  ·  `det-atlas-p1`

| rung | item | home (Mathlib-mirror) | risk |
|------|------|------------------------|------|
| P1.a | **Localization-overlap API** — double/triple principal-open overlaps as `Localization.Away (f*g)` / `(f*g*h)`; canonical `AlgEquiv`s between iterated presentations (`R[1/f][1/g] ≃ R[1/(fg)]`); `refl`/`symm`/`trans`/`algebraMap` transport + cocycle identities | `Core/RingTheory/Localization/Overlap.lean` | med — the iterated-localization iso bookkeeping is the known fragile part; standard but fiddly |
| P1.b | **Matrix coordinate ring + determinantal ideals** — `MvPolynomial` coords for `Matrix (Fin m) (Fin n) k`; the ideal of `(r+1)`-minors (rank `≤ r`) | `Core/…/Determinantal/Basic.lean` | low — standard |
| P1.c | **Rank strata** — rank-`≤r` (closed) + rank-`=r` (open = remove rank-`≤r-1`); pivot principal opens `U_P = D(det A_P)`; the **cover theorem** (rank-`r` ⟹ some pivot minor a unit) | `Core/…/Determinantal/Strata.lean` | low–med |
| P1.d | **Schur coordinates** — on `U_P`, `D = C A⁻¹ B`; the explicit trivialization `U_P ≅ GL_r × (B,C)`-space; localized coordinate-ring iso | `Core/…/Determinantal/Schur.lean` | med |
| P1.e | **Dimension / height** of rank strata (from #14 dimension stack) | `Core/…/Determinantal/Dimension.lean` | low |

## Phase 2 — the constructive atlas + capstone  ·  `det-atlas-p2` (off `-p1`)

| rung | item | home | risk |
|------|------|------|------|
| P2.a | **Pivot-chart datum + standard fibre model** — canonical chart datum (drop repeated `s`/`t`/`σ`/`τ` threading); the bundled fibre model (Schur base ring, fibre coord ring, tensor, structure map, flatness, localization transport) | `Core/…/Determinantal/Atlas.lean` | med |
| P2.b | **Transition maps** on overlaps (explicit rational change-of-coords, via the P1.a overlap API) | atlas home | med |
| **P2.c** | **Cocycle-compatibility theorem [CRUX]** — transitions compose on triple overlaps (`g_{P''P} = g_{P''P'} ∘ g_{P'P}`, `g_{PP}=id`) → a coherent atlas | atlas home | **crux** — decorrelated review (the iterated-localization cocycle is the delicate bit) |
| **P2.d** | **bare `FiberBundle` capstone [CRUX, recon-gated]** — the residue-field-rank bridge ⟹ charts cover every scheme point ⟹ Mathlib local-triviality | atlas home | **crux** — build iff P0 says detail-at-scale; else roadmap, atlas+cocycle is the ceiling |

## Woven — de-DLN-ify
Re-express `productRankLocusLE`/`sigmaIdeal`/`dStratum`/`RepCoord` as **instances** of the Core determinantal
API; collapse duplication; keep ALL DLN consumers green + signatures + payoff axioms unchanged. (FL-III pattern:
abstract Core + thin DLN adapter that re-derives the existing headlines.)

## Crux rungs (decorrelated review)
P2.c (cocycle compatibility) · P2.d (residue-field-rank bridge / bare bundle). P0 recon de-risks both first.

## Cross-cutting
- **Constructive-first:** prefer explicit (finite pivot index, Schur formulas, explicit transitions) over
  abstract existence wherever both are available (the computability is the point).
- name=content (object-eq vs `finrank`/dimension-eq; "rank-`=r`" vs "rank-`≤r`" stated precisely; no name hiding
  a cited step). Lessons **L2** (transitive sweep + full-build), **L3** (gate dispatch on completion), **L4**
  (codepoint longLine), **L5** (re-gate at boundaries + crux), **L6** (split severs transitive instance imports),
  **L7** (bare Mathlib-mirror namespaces — NOT `DLNFibre.Core.X`), **L8** (GUARD-first when abstracting).
- Namespace-mirror the eventual Mathlib home so extraction is a file-move.

## Roadmapped (NOT this expedition)
- **RLCT generic-foundation programme** — written into [`ROADMAP.md`](../../ROADMAP.md) this expedition; built later.
- **char-`p` differential-independence criterion** — dropped (scope).
- **top-dim minimal-primes vs `k`-point-components clarification** — lower priority; stretch/roadmap.
