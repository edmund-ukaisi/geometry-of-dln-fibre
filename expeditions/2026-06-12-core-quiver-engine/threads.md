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
| 10-barcode | formalisation (teammate `barcode`) | closed | **4d COMPLETE — abstract-chain existence MERGED + AUDITED** (`Core.Barcode`, 722 lines, green/axiom-clean): `hasBarcode_of_isSubrep`/`hasBarcode_top` = existence half of type-A Gabriel. Reviewer (thread 12): **SURVIVED**. `barcode/rung-4d` on origin. |
| 13-assembly | formalisation (teammate `assembly`) | abandoned | Spawned for 4d assembly, then STOOD DOWN — collided with the still-live `barcode` (already ahead on the same work). `assembly` landed in the main checkout and made ZERO writes (git-safety guard caught it). Controller error — premature successor spawn; see `lessons.md`. |
| 11-orbits-kostant | formalisation | pending | **4e (≈free):** orbits ↔ Kostant (Cor 2.9) = `cumulDiffEquiv` restricted. After 4d existence (thread 13). |
| 12-rung4-review | review (`reviewer4`) | closed | **SURVIVED** — all 4a–4d bedrock: gate re-run green/0-sorries/axiom-clean, per-module fidelity vs the paper, adversarial in-Lean **non-vacuity probe** for 4d, Codex-corroborated. One non-defect form-note (the explicit iso object is a corollary still to construct) recorded in the 4d card. |
| 13-tuple-transport | formalisation | open (next) | **rung-4 completion:** construct the explicit `P ≅ ⊕ M^m` iso (corollary of `HasBarcode`) + transport to `Setup.Tuple` (`∃ g ∈ G_d, g·A = ⊕ M_{ij}^{m}`, change-of-basis via 4c); then uniqueness (`m = diff(rankPattern A)`, near-free via `diff_cumul`+4b+4c) and 4e (orbits ↔ Kostant, Cor 2.9). Fresh worktree off the integration tip. |
