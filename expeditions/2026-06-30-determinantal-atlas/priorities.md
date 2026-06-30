# Priorities — `determinantal-atlas` (taste ledger)

Controller proposes by VOI; **operator edits this file directly**. Build-the-buildable
([`../../docs/policies/library-building.md`](../../docs/policies/library-building.md)). Scoped against
`origin/dev` `a13b11f2`. **Live status → [`threads.md`](threads.md).** The authoritative detailed ladder is
the P0 recon report [`threads/p0-recon/report.md`](threads/p0-recon/report.md).

## P0 — recon ✅ DONE (`787e688f`)
**Verdict (scout + decorrelated Codex xhigh):** the expedition is **overwhelmingly re-home + de-DLN-ify, not
fresh build** — the overlap API (P1.a, *triple cocycle proved*) and the minor↔rank cover (P1.b/c) already exist
DLN-free over arbitrary `CommRing`/field; the residue-field-rank bridge (the P2.d crux) is **already proved**
for the DLN instance (`FibreRankBridge`). **Capstone = BUILD**, with a **framing correction:** NOT Mathlib's
`FiberBundle` (topological-only), NOT over the closure `Σ̄^r` (false — rank-`<r` boundary in no chart) — but a
**bespoke `IsZariskiLocallyTrivialAffineProduct` over the rank-`r` open** (`FibreBundleHeadline` packages all but
the cocycle field). The lone blocker (`AlgEquiv.trans_assoc/refl`, absent v4.29) dissolves by `ext x; rfl`
(scratch-verified) → rung P2.b′. No monument on the path; no fallback expected.

## Phase 1 — overlap API + determinantal rank-stratum  ·  `det-atlas-p1`

| rung | item | home | kind |
|------|------|------|------|
| **P1.a** | overlap API — `awayOverlap`/`awayOverlapTransition` + 3 cocycle laws + restriction + `awayTriple` + **`awayTriple_cocycle`** | `Core/RingTheory/Localization/Overlap.lean` | **[re-home]** — `FibreBundleTransition` §Abstract+§Triple verbatim (general `R`), retarget 2 consumers. **Lowest-risk, already proved → dispatch FIRST** |
| P1.b | matrix coord ring + **determinantal `(r+1)`-minor ideal** (the one genuinely new def; absent in Mathlib) + `detMinorPoly`/`eval_detMinorPoly` | `Core/RingTheory/Determinantal/Basic.lean` | **[generalize]** |
| P1.c | rank strata (`rankLeLocus` closed / `rankEqLocus` open) + pivot `minorChart` + **cover theorem** + minor↔rank criterion | `Core/RingTheory/Determinantal/Strata.lean` (+ `Matrix/RankMinors` mirror re-home) | **[re-home]** — `RankMinorCover`+`Matrix/RankMinors` (i) |
| P1.d | Schur coords — `rank_fromBlocks_zero` (absent Mathlib), `rank_eq_iff_schur_eq`, `pivotRankChartEquiv`, `schurComplement_normal_form` | `Core/RingTheory/Determinantal/Schur.lean` | **[re-home]** — `DeterminantalChart`/`SchurChartIff`/`SchurGauge` |
| P1.e | rank-stratum dimension `r(n+m−r)` / codim `(n−r)(m−r)` | `Core/RingTheory/Determinantal/Dimension.lean` | **[generalize]** — from `DeterminantalStratumDim`; **keep cited Brick A named** (precision — don't fold into the dim theorem name) |

## Phase 2 — constructive atlas + capstone  ·  `det-atlas-p2` (off `-p1`)

| rung | item | home | kind |
|------|------|------|------|
| P2.a | pivot-chart datum + standard fibre model (drop `s/t/σ/τ` threading; bundle base ring + fibre + tensor + structure map + flatness + localization transport) | `Core/RingTheory/Determinantal/Atlas.lean` | **[generalize]** — `FibreOverBaseTriv`+`FibreBundleHeadline` |
| **P2.b′** | **`AlgEquiv` groupoid spin-out** — `trans_assoc`/`trans_refl`/`refl_trans` by `ext x; rfl` (the cocycle-unblocker; network-free, Codex+scratch-vetted) | `Core/Algebra/AlgEquiv/Groupoid.lean` (Mathlib `Algebra/Algebra/Equiv` mirror) | **[build, small]** |
| P2.b | transition maps on overlaps (explicit, via P1.a) | atlas home | **[re-home]** — `FibreBundleTransition`/`FibreTargetOverlap` |
| **P2.c** | **cocycle-compatibility [CRUX]** — base-side DONE; residual = target-side round-trip `(I,J)∘(J,I)=id`, reachable via P2.b′ (+ de-`reducible` `targetChartLoc` if the kernel cost resurfaces) | atlas home | **[crux]** decorrelated review; math LANDED, transport-through-trivialization to finish |
| **P2.d** | **bespoke Zariski local-triviality capstone [CRUX → BUILD]** — `IsZariskiLocallyTrivialAffineProduct` over the rank-`r` open; cover-every-scheme-point via the **de-DLN-ified residue bridge** (already proved `FibreRankBridge`) | atlas home | **[crux, build]** NOT a Mathlib `FiberBundle` |

## Woven — de-DLN-ify (re-express as Core instances; DLN consumers green, signatures + payoff axioms unchanged)
`productRankLocusLE` (22 files) → `rankLeLocus` at the product matrix · `sigmaIdeal` (18) → the `(r+1)`-minor
ideal pulled back along `multComap` (the pullback is the DLN-specific glue, stays) · `dStratum` (8) → `![n,m]`
specialization · `chartDsigAt`/`sweepSigmaRing` (9/24) → pivot open + chart-closure ring. **`RepCoord` (79
files) — DO NOT remove** (pervasive; out of scope).

## Crux rungs (decorrelated review)
P2.c (target-side cocycle round-trip) · P2.d (bespoke Zariski capstone). **Most likely to break:** P2.c's
`@[reducible] targetChartLoc` kernel cost (the predicate P2.d is safe; its cocycle field is the fragile bit).

## Cross-cutting
- **Constructive-first** (explicit pivot index + Schur formulas + explicit transitions over abstract existence).
- name=content; lessons **L2/L3/L4/L5/L6/L7/L8** (see [`lessons.md`](lessons.md)); bare Mathlib-mirror namespaces;
  sibling-clash `rg` per new top-level name; keep cited bricks (Brick A) named, not folded.

## Roadmapped (NOT this expedition)
RLCT generic-foundation programme (in [`ROADMAP.md`](../../ROADMAP.md) Bundle 4b) · char-`p` (dropped) ·
top-dim minimal-primes-vs-`k`-point-components clarification (lower priority).
