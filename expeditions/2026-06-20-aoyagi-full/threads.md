# threads.md — Aoyagi-Full thread ledger

Durable thread-status index. Status ∈ open / in-progress / blocked / review-pending / closed / abandoned.

| NN | type | seat | status | subject |
|----|------|------|--------|---------|
| 01 | design | pp | closed | Rung 0a: foundational defs + goal skeleton → `design-spec.md` |
| 02 | formalisation | fm | review-pending | Rung 0b: encoded `DLNFibre.DLN.RLCT.*` + skeleton + 1 S2 axiom; green; merged `58bc1c3` |
| 03 | design (parallel) | pp | closed | Spine probe: `codim S(t)=Mval` proven general L; θ=a(ℓ−a)+1; stratification R1 architecture |
| 04 | design (parallel) | pp | closed | D1 scope: cite Aoyagi 2013 **Thm 2**; light rung; depends on L2; reuses S1 |
| 05 | design (parallel) | pp | closed | S1 scope: θ-transport linchpin (S1.1 heavy core + 4 corollaries); Jacobian-weight correction; properness amends D1 |
| 06 | review | rv | closed | Rung 0c: fidelity+bedrock audit → **PASS** (5/5 dims; 2 non-blocking flags); foundations are bedrock |
| 07 | design (parallel) | pp | closed | L1/L2 scope: block elim + product reduction + additivity; new S1.5; reg-term=½·stratum-dim fix |
| 08 | formalisation | fm-2 | closed | (1,1,1) gate: arithmetic+coercion sorry-free thru monomial_rlct; rlctAt bridge = 1 named sorry. S2 hygiene fix done. @6e4d505 |
| 09 | review | rv-2 | closed | AUDIT (1,1,1) gate → **PASS 5/5** + green-gate green (2659 jobs). Axiom-use load-bearing, coercion correct, bridge-sorry honest. 3 non-blocking style-lint notes |
| 10 | formalisation | fm-2 | closed | PROBE **ANSWERED YES**: monomial threshold-half provable from Mathlib (Fubini + rpow-iff). `Case111Bridge.lean` axiom-free; (1,1,1) headline dropped monomial_rlct. λ-citation ELIMINABLE (general = labour, no wall). @22f5dfe |
| 11 | formalisation | fm-2 | in-progress | Close the (1,1,1) rlctAt bridge (baby-S1.1: measure-preserving chart + two-sided \|x\|^a integrability + ∃-nbhd) → first FULLY axiom-free+sorry-free end-to-end. Bounded (report if it sprawls) |
| 12 | formalisation | fm-2 | folded | S1 skeleton-refactor probe → folded into the Route A++ measure-architecture decision |
| 13 | formalisation | fm-2 | in-progress | (1,1,1) rlctAt bridge — obstruction was paramsEquivFlat-shaped; resumes as measure-track Unit 2 |
| 14 | formalisation | fm | in-progress | **ALGEBRA track** (Skeleton.lean): A1 `lambdaCore_eq_clean`+`clean_eq_printed` → L1 `block_elimination` → `deepestPoint_exists` |
| 15 | formalisation | fm-2 | in-progress | **MEASURE track**: `paramsEquivFlat` (Route A++ keystone, ParamsFlat.lean) → (1,1,1) bridge close (#13) |
| 16 | design | pp | design-DONE | **R1 design** (the mountain): fixed-M LADDER fully designed ((1,1,1) monomial / (2,1,2) product-MIN / (2,2,2) 24-leaf cover, execution-ready); lower-bound crux SETTLED (centers=admissible strata); G5-abstract BUILD-READY for fm-2 (#52: G5-adapter+G5-step+leaf-sum, exact Mathlib anchors); A-vs-B verdict (B/hybrid general-M, block layer doesn't compound wall); GENERAL-M gated on **G3 alone** (spec'd for roadmap). 3 traps caught (Q4-lct, 0·∞, δ-block). LADDER COMPLETE (3 rungs scoped+handed): (1,1,1) #9/#12 done · (2,1,2) #55 (product-MIN, CERTIFIED min≠sum via c=3/2 test) · (2,2,2) #54 (24-leaf cover) · G5-abstract #52. Cards: `r1-general-atlas-design.md`, `r1-212-product-min-handoff.md` (#55), `r1-222-cover-handoff-split.md` (#54), `g5-abstract-statement.md` (#52), `g3-spec-the-named-wall.md` (roadmap). pp design DONE; residual = fm/fm-2 execution (#55,#54,#52) + G3 tide |

## Seats (reuse across tides; stand down at close)

- `pp` — pen-and-paper (design / fidelity-math / decorrelated Codex). No Lean. On thread 16 (R1 design, the mountain).
- `fm` — formaliser (Lean). ALGEBRA track [thread 14]: A1 → L1 → deepestPoint_exists, in Skeleton.lean.
- `fm-2` — formaliser (Lean). MEASURE track [thread 15]: paramsEquivFlat → (1,1,1) bridge, in ParamsFlat.lean + Case111*.lean.
- `rv-2` — reviewer (fidelity / soundness; decorrelated Codex). Standby; per-rung audit as each closes [delivered the bedrock verdict, thread 16-pre].
- `rv` / `hd` — reviewer / hardener (earlier tides, thread 06). Idle.

## Merge flow (STRUCTURAL PHASE — all in MAIN checkout)

Everyone edits the MAIN checkout (`/home/ubuntu/workspace/geometry-of-dln-fibre`) on `expedition/aoyagi-full`.
**Collision-free by file ownership**, NOT serial-on-everything: `fm` owns Skeleton.lean (algebra rungs);
`fm-2` owns ParamsFlat.lean + Case111*.lean (Skeleton does not import these, so the two tracks' incremental
builds are independent). Teammates iterate with **module-scoped** builds (`lake build DLNFibre.DLN.RLCT.<Module>`)
so an in-flight broken file on one track doesn't fail the other's build. The **controller is the sole committer**:
runs the full `lake build DLNFibre` green-gate, commits + pushes, then pings `rv-2` to audit the closed rung.
Serial only *within* a single file. `pp` runs read-only (no collision). The per-rung modular split of
Skeleton (build-time lesson) is done **opportunistically when a proof gets heavy**, not big-bang.

## Encoded foundations (merged 58bc1c3)
`Foundations/{Loss,Rlct,Lambda}.lean` + `Skeleton.lean`. 9 named-sorry rungs (S1×2, L1, L2, D1, R1,
A1×2, A2) + 1 axiom `monomial_rlct` (S2, narrowed to the bare weighted-monomial-integral fact). Defs
axiom-clean. `aoyagiLambda` = min-over-Adm (ground truth enforced at build). `rlctOrderAt` = honest
`opaque` placeholder (θ-seam). Statement card: `threads/02-rung0b-encode/statement-card.md`.
