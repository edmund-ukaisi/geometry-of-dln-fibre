# threads.md — thread index (core-quiver-engine)

`NN-slug` · type · status · subject. Status ∈ open / in-progress / blocked / review-pending / closed / abandoned.

**Execution mode (from rung 4c on):** Agent Teams — team `core-quiver-engine`, controller = lead/sole-merger;
teammates work in isolated git worktrees (sharing the prebuilt Mathlib `.lake/packages`), commit to their own
branches, and report to the controller, who merges → green-gates → commits on `expedition/core-quiver-engine`.
(Rungs 1–4b were run dispatch-and-integrate; same merge discipline, no parallel worktrees.)

## Rungs 1–3 (closed, reviewed bedrock)

| Thread | Type | Status | Subject |
|---|---|---|---|
| 01-mathlib-recon | explore | closed | Coverage map; rung 4 = build-from-scratch. |
| 02-ambient-objects | formalisation | closed | `Core.Setup` (rung 1). Reviewed. |
| 03-prop31-inversion | formalisation | closed | `Core.RankPattern`: Prop 3.1a inversion (`cumulDiffEquiv`). Reviewed. |
| 04-core-audit | review | closed | Decorrelated audit; SURVIVED; precision fixes. |

## Rung 4 — type-A Gabriel (FULL BUILD)

| Thread | Type | Status | Subject |
|---|---|---|---|
| 06-submult-rankpattern | formalisation | review-pending | **4a:** `Core.Submult` — `submult`/`rankPattern`/bridge. Green, axiom-clean. |
| 07-gabriel-design | pen-and-paper | closed | Peel-one-interval design; no general Gabriel needed; uniqueness free via `diff_cumul`. + `mathlib-levers.md`. |
| 08-interval-modules | formalisation | review-pending | **4b LANDED:** `Core.IntervalModule` — `intervalModule`, `dirSum`, `rank_fromBlocks_zero_zero` (Field), `rankPattern_intervalDirectSum_eq_cumul`. Green, axiom-clean. |
| 09-basechange | formalisation (teammate `basechange`) | review-pending | **4c LANDED** (ran in the shared MAIN checkout, not a worktree — committed `720d298`/`0d319ca`, then controller-wired): `Core.BaseChange` — `baseChange`/`MulAction`, `submult_baseChange` (telescoping conjugation), `rankPattern_baseChange` (invariance), `CommRing`. Green, axiom-clean. |
| 10-barcode | formalisation (teammate `barcode`) | review-pending | **4d CRUX toolkit MERGED + wired** (`Core.Barcode`, green/axiom-clean): splitting FACT + `relSplitting` (relative, recursion-ready) + `finrank_comap_add_one` + `compMap` layer (+`compMap_trans`) + pointwise peel. Full existence theorem NOT yet proved — assembly → thread 13. |
| 13-barcode-assembly | formalisation | open (next, fresh tide) | **4d completion:** wire the toolkit into the full abstract-chain existence theorem — index-finding (least-`s`/last-`j`), global subrep + Finset total-dim strict-drop, `relSplitting` + `Nat.strong_induction` along the bar, Λ-barcode/iso output. (`Tuple` transport may be a further follow-up.) Handoff: `threads/10-barcode/findings.md`. |
| 11-orbits-kostant | formalisation | pending | **4e (≈free):** orbits ↔ Kostant (Cor 2.9) = `cumulDiffEquiv` restricted. After 4d existence (thread 13). |
| 12-rung4-review | review | pending | Decorrelated fidelity/precision audit over 4a/4b/4c/4d/4e before rung 4 closes. |
