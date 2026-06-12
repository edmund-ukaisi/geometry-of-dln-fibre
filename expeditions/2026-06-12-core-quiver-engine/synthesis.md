# synthesis.md — controller's integrative read (core-quiver-engine)

The controller's *internal* integrative ground, flushed every tick (recovery substrate).

## State

- **Branch:** `expedition/core-quiver-engine` (off `dev`), not pushed. Controller mode:
  dispatch-and-integrate (role-typed subagents; controller green-gates + sole committer).
- **Rungs 1–3 — closed, reviewed bedrock:** `Core.Setup` (ambient objects), `Core.RankPattern` (Prop
  3.1a abstract inversion `cumulDiffEquiv`); audited (thread 04), two precision fixes applied.
- **Rung 4 (type-A Gabriel) — FULL BUILD chosen by operator; opened:**
  - **4a landed** (`Core.Submult`): `submult`/`rankPattern`/`rankPattern_self`/`mult_eq_submult`, the
    `Nat.leRec` cast-free route. Green, axiom-clean, controller-checked; reviewer audit batched.
  - **Design done** (thread 07, sympy-certified) — see "the plan" below.
  - **4b landed** (`Core.IntervalModule`): interval modules, `dirSum`, block-rank additivity (Field), headline `rankPattern_intervalDirectSum_eq_cumul`.
  - **4c landed** (`Core.BaseChange`, teammate `basechange`): `MulAction`, `submult_baseChange` (telescoping conjugation), `rankPattern_baseChange` (invariance), `CommRing`. Wired + green-gated (whole lib 1797 jobs).
  - **4d (crux) toolkit MERGED + wired** (`Core.Barcode`, green/axiom-clean on origin): the splitting FACT + the **relative** splitting fact (`relSplitting`, recursion-ready), `finrank_comap_add_one`, the `compMap` abstract-chain layer (+`compMap_trans`), and the pointwise peel lemmas. The **full barcode-basis existence theorem is NOT yet proved** — what remains is module-sized **assembly** (no new crux): index-finding (least-`s`/last-`j`), global subrep + Finset total-dim strict-drop, wiring `relSplitting` + `Nat.strong_induction` along the bar, the Λ-barcode/iso output, and `Tuple` transport. Handoff in `threads/10-barcode/findings.md`. To be done as a **fresh tide** (barcode's earned taste-call: fresh context for the induction wiring).
  - **Team mode:** Agent Teams; `barcode` properly isolated in a worktree, `basechange` landed in the shared main checkout (isolation didn't take — see `lessons.md`).
- Whole lib green (1795 jobs), 0 sorries, axiom-clean. Cosmetic `abel_nf` info at RankPattern.lean:128.

## The plan for rung 4 (from the 07 design — key simplification)

**General Krull–Schmidt and all-Dynkin Gabriel are NOT needed.** The type-A decomposition is proved
directly by a **peel-one-interval-per-step** normal form (total-dimension induction), and **uniqueness is
free**: `rankPattern(⊕ M_{ij}^{m}) = cumul m` + base-change invariance + the already-proven `diff_cumul`
force `m = diff(rankPattern A)`. So "full build" is tractable.

- Prove the crux on an **abstract finite-dim `LinearMap` chain** (mature `ker`/`range`/`comap`/`IsCompl`
  API), transport to `Tuple` via one change-of-basis per vertex.
- **Cite** (don't reprove): `Submodule.exists_isCompl`, `IsCompl` finrank additivity, `rank(P·C·Q)`
  unit-invariance.
- Ladder: **4b** interval modules + direct sums + `rankPattern(⊕)=cumul m` (cheapest, next) ‖ **4c** `G_d`
  base change + rank-pattern invariance → **4d** the peel normal form (CRUX: backward `comap` complement
  chain + threading `IsCompl`; the active/dead-edge `Fin` bookkeeping is the hardest step) → **4e** orbits
  ↔ Kostant (Cor 2.9), ≈free = `cumulDiffEquiv` restricted.

## RESOLUTION (Proved, exact scope)

Ambient objects (`mult`, loci, fibre over fixed `d`); the abstract Prop 3.1a inversion (`cumulDiffEquiv`);
the matrix-side `submult`/`rankPattern` with `r_{ii}=d_i` and `mult = submult 0 (last)`. **Deferred/Cited:**
Prop 3.1b (rank pattern = `cumul` of Gabriel multiplicities) = rung 4d; the `Ext` codimension (Cor 3.5),
QIP (Thm 6.1), explicit formula (Thm 7.10), and the `rlct=½codim` cap — later/other expeditions.

## Drift guard

`Core` imports no `DLN`. Tag Proved/Assumed/Cited/Deferred. No `Core` name asserts Gabriel/tuple content
until 4d proves it. Prefer characterisations + weakest hypotheses shown necessary.
