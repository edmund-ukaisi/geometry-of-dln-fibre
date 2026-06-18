# synthesis.md — controller's integrative read (core-quiver-engine)

The controller's *internal* integrative ground, flushed every tick (recovery substrate).

## CLOSE — the core quiver engine is complete (2026-06-13)

**The §§2–3 quiver-orbit spine is formalized, audited, and on `origin` (`ac40439`):** ambient objects;
Prop 3.1 (both directions); type-A Gabriel existence (Thm 2.5); the complete `G_d`-invariant + the Gabriel
normal-form object; and orbits ↔ Kostant (Cor 2.9) as `orbitKostantEquiv`. 10 `Core` modules, ~2969 lines,
whole library green, **0 sorries, axiom-clean** throughout; `Core` never imports `DLN`. Two decorrelated
audits (threads 12, 15) SURVIVED. **Out of scope (future expeditions, per `ROADMAP.md`):** the `Ext`
codimension (Cor 3.5), the `(C,θ)` computations (§§5–7), the RLCT cap (§8). Close = this synthesis + ROADMAP
+ the close-phase PR into `dev` (operator-gated).

## State

- **Branch:** `expedition/core-quiver-engine` (off `dev`), pushed to `origin` (`ac40439`). Controller mode:
  Agent Teams / dispatch-and-integrate (controller green-gates + sole merger).
- **Rungs 1–3 — closed, reviewed bedrock:** `Core.Setup` (ambient objects), `Core.RankPattern` (Prop
  3.1a abstract inversion `cumulDiffEquiv`); audited (thread 04), two precision fixes applied.
- **Rung 4 (type-A Gabriel) — FULL BUILD chosen by operator; opened:**
  - **4a landed** (`Core.Submult`): `submult`/`rankPattern`/`rankPattern_self`/`mult_eq_submult`, the
    `Nat.leRec` cast-free route. Green, axiom-clean, controller-checked; reviewer audit batched.
  - **Design done** (thread 07, sympy-certified) — see "the plan" below.
  - **4b landed** (`Core.IntervalModule`): interval modules, `dirSum`, block-rank additivity (Field), headline `rankPattern_intervalDirectSum_eq_cumul`.
  - **4c landed** (`Core.BaseChange`, teammate `basechange`): `MulAction`, `submult_baseChange` (telescoping conjugation), `rankPattern_baseChange` (invariance), `CommRing`. Wired + green-gated (whole lib 1797 jobs).
  - **4d (crux) COMPLETE — abstract-chain existence MERGED** (`Core.Barcode`, 722 lines, green/axiom-clean on origin): `hasBarcode_of_isSubrep` / `hasBarcode_top` — every f.d. (sub)representation of an abstract chain `HasBarcode` (a finite family of genuine interval bars — support + nonzero-on-support + identity-edge trajectory + death — forming an internal direct sum `iSupIndep` + `⨆ = Pₜ` at every vertex) = the **existence half of type-A Gabriel (Thm 2.5)**. Full stack sorry-free: splitting facts + `relSplitting`, `compMap`+`compMap_trans`, pointwise peel, `IsSubrep`/`totalDim`, index-finding, `exists_peel`, `Fin.cons` combine helpers, total-dim `Nat.strongRecOn`. Controller-precision-checked (genuine, non-vacuous, name=content: existence only). **Decorrelated rung-4 audit (thread 12, `reviewer4` + Codex): SURVIVED** — all 4a–4d bedrock, gate re-run green/axiom-clean, adversarial in-Lean non-vacuity probe for 4d, one non-defect form-note (the explicit iso object is a corollary to construct in the transport). **The AUDIT gate has PASSED.** `barcode` done (`barcode/rung-4d` on origin).
  - **Tuple transport — LANDED (`Core.Gabriel`, green/axiom-clean on origin, `fea3044`; controller-precision-checked, decorrelated audit due):** `hasBarcode_tuple` (existence on `Tuple`, predicate form) via the `compMap = (submult).mulVecLin` bridge; `finrank_range_compMap_eq_card` (range-rank of a composite = #bars alive across `[i,j]`); **`exists_barcode_rankPattern` = Prop 3.1b COMPLETENESS** (an arbitrary tuple's `r_{ij}` = #bars spanning `[i,j]`, with the Kostant dim constraint — the direction `IntervalModule` disclaimed); **`rankPattern_eq_cumul_barMult` = UNIQUENESS** (`m̄ = diff(rank pattern)` via `diff_cumul`); `barcodeVertexBasis` (the change-of-basis basis object). So the **rank pattern is now a complete invariant determining the Gabriel multiplicities.**
  - **Cor 2.9 LANDED + AUDITED (`Core.Orbit`, green/axiom-clean on origin; decorrelated audit thread 15/`reviewer6` + Codex: `Gabriel` SURVIVED, `Orbit` SURVIVED; one precision finding — `baseChange_normalForm`'s statement now strengthened to carry its docstring's canonicality (the `multiplicityArray L = diff(rankPattern A)` + `p.1≤p.2` conjuncts), fixed `7d15008`. AUDIT GATE PASSED.):** `rankPattern_eq_iff_orbit` — the **complete `G_d`-invariant** (`rankPattern A = rankPattern B ↔ ∃ g, g•A = B`); `orbit_of_rankPattern_eq` — the crux (equal rank patterns ⟹ same orbit, via barcodes → equal `barMult`/`diff_cumul` → relabelling → `Basis.equiv` intertwiner → `P`); `baseChange_normalForm` — the **Gabriel normal-form object** in the literal `intervalDirectSum` form. The block-encoding obstacle was sidestepped by the abstract orbit-equivalence construction. (Controller caught + fixed a docstring overclaim: `orbitKostantEquiv` was advertised but undefined — re-marked deferred.)
  - **Engine core (Bundle 1–2) is essentially complete:** orbits ↔ Kostant ↔ rank patterns, Gabriel existence, Prop 3.1 (both directions), uniqueness, Cor 2.9 — all sorry-free + axiom-clean. **Remaining:** the orbit↔Kostant single-`Equiv` packaging (cosmetic — content in hand); then the **expedition close** (final synthesis + ROADMAP update + the close-phase PR into `dev` — operator-gated, signal-and-wait).
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
