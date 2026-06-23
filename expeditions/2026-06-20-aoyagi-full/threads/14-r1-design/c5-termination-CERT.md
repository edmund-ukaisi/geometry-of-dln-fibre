# C5 per-chart branching — lex-termination CONFIRMED (pp, 2026-06-23)

- **Seat:** `pen-and-paper`. The last de-risk before the controller commissions the hnode-grind.
- **Question:** is the C5 per-chart branching (the `e_i≠0` chart cover + the `e=0` deeper-defect
  sub-branch) `lex(L,ΣM,ncDefect)`-decreasing — and under which measure?
- **Scripts:** `r1-realizability-scripts/c5_termination.py`, `c5_termination_stress.py`,
  `c5_measure_sufficiency.py`, `c5_finite_branching.py`.

## VERDICT

**DECREASING — and the banked `chainRel` (`ΣM`-decrease, `L` fixed) SUFFICES. No `lex(L,ΣM,ncDefect)`
augmentation is needed for the achiever-only route.** Termination is confirmed; the routeStep roadmap
closes its last gap. The bonus: the formaliser's termination obligation is the simplest possible (the
already-banked single-`ℕ` `ΣM` measure), not the `ℕ³` lex.

## 1. The live measure (decl-grounded)

The g138 design proposed `lex(L,ΣM,ncDefect)` (`RouteMState.lean:34`, `routeMeasure`). But that
`RouteState` machinery was REPLACED by the `ChainDimSplit`/`chainRel` rebase (g156): the LIVE
`routeAtlas` recursion (`RouteMRecursion.lean`) descends on `chainRel = ΣM-decrease` ONLY, with `L`
FIXED (`ChainDimSplit` is width-only). `ncDefect` is a stub (`:= 0`). So the check must be against
`ΣM`-decrease, the actual banked `chainRel_wf`.

## 2. Each C5 chart strictly drops `ΣM` (S1, verified)

The C5 partial-drop (`t_{s-1}=a > t_s=b > 0`, complement rank `a−b`) is a SINGLE Schur step clearing
the complement (the `c5_lu_loss` / shear mechanism, C5 hnode cert). It removes one resolved row + col
per complement unit at the active edge `(s, s+1)`, dropping each of `M^s, M^{s+1}` by `a−b`:

    ΣM_red = ΣM − 2·(a−b) < ΣM   (strict, since a−b ≥ 1)

Verified for every active edge & complement rank on `M=(3,3,3,3,3,3)` (`c5_termination.py`: e.g. the
`t=(3,3,2,2,2,0)` C5 step `3→2` drops `ΣM` 18→16). The survivor (rank `b`) STAYS in `S.red` — it is
recursed at LATER drops, each also `ΣM`-decreasing; it is NOT consumed here (no C2-style `L`-drop
needed).

## 3. `e=0` is a DEEPER recursion node, NOT null (CORRECTED, pp2 g222/g223)

**CORRECTION (this supersedes the original "e=0 is null" reading of this section).** pp2 (g222,
`383fded`) verified — and I reproduced (`c5_e0_center.py`) — that the cascade's CENTER (the deepest
point) sits ON `{e=0}`: at `t=(3,3,2,2,2,0)`, the C5 node's downstream `C₆C₅C₄ = diag(0,0,0)` (since
`t₆=0` kills everything), so `e = downstream·(complement) = 0` AT the center. My original "e=0 is
measure-zero, no branch" was WRONG at the center — the deepest point IS on `e=0`. (Reconciliation with
my earlier `0/5000 e≠0`: that sampled RANDOM downstream, which is generically nonzero; the cascade's
SPECIFIC downstream is the most-degenerate point. Both true; the "null" reading was the error.)

**The corrected mechanism (pp2 g223; reproduced `c5_e0_lexdrop.py`) — and #98 still closes:**
- **`e≠0` charts** (a neighbourhood away from the center): the complement survives a few downstream
  layers before its kill ⟹ my Fubini-shear `δ' = δ + (G·q·e)/‖e‖²` applies (`‖e‖²≠0`), the defect is a
  regular ½, the survivor recurses.
- **`e=0` (incl. the center):** the complement's downstream vanishes ⟹ a FURTHER rank-defect on the
  complement sub-block (rank `t_{s-1}−t_s`). This is the recursion DESCENDING into `S.red`: the
  complement's kill is a LATER `ΣM`-dropping step (the rank-`(t_{s-1}−t_s)` complement is a strict
  sub-block, `ΣM` drops). It is a deeper node, NOT a same-node branch and NOT null.

In BOTH cases the recursion descends on `S.red` with `ΣM` dropping ≥2 at every step (the C5 peel, then
the complement's eventual kill — immediate at `e=0`, later at `e≠0`). NO non-`ΣM`-dropping branch is
introduced. So termination's CONCLUSION is unchanged (§2 still holds); only this section's mechanism is
corrected: `e=0` is the recursion's deeper descent, not a null locus. #98 closes.
- `{e=0}` semantically = the downstream ALSO kills the complement = a DEEPER admissible stratum `T'`,
  reached by ANOTHER cascade path (its own branch, smaller `ΣM`), NOT a sub-chart of this node.

## 4. Pass-throughs are gauge, not nodes; branching is finite

- **Full-rank pass-through** (`t_s = t_{s+1}`, no drop): a UNIT GAUGE (det≠0), ABSORBED by the det-1
  reindex `redEmbed` — NOT a recursion step. The recursion branches only at DROPS (`t_s > t_{s+1}`),
  each `ΣM`-decreasing. Between-drop pass-throughs do not threaten termination (they are gauge). This
  is why the `ChainDimSplit` `ΣM`-only measure suffices where the old `RouteState` needed an `L`-drop
  for C2.
- **Finite branching:** rank-1 complement = 1 chart; rank-`(a−b)` = iterate one unit at a time (Codex
  Q4) or the `(a−b)`-chart affine cover of `ℙ^{a−b−1}`; `e=0` null (no branch). Depth is `ΣM`-bounded
  (each step drops `ΣM ≥ 1`). ⟹ finite branching × finite depth ⟹ `Fintype routeMIota` (the banked
  atlas `fintype` field).

## 5. C3/NC-completion does NOT arise on the achiever-only route

`ncDefect` (the C3 NC-completion measure) was needed for the FULL atlas's `threshold_eq` (a globally
normal-crossing divisor arrangement). The achiever-only route (`foldFamily_iInf_eq_half_minAdm`) needs
only the achiever LEAF's codim-list to contain `minAdm`; each cell's `(k,h)=(1,c−1)` is set by
`appendDivisor` directly — NO NC-completion. So C3 is off the live target; `ncDefect` is irrelevant.

## 6. Net + the formaliser recommendation

**Termination CONFIRMED under the banked `chainRel`.** The C5 branching is the last de-risk; it closes.
The full §4 picture is now end-to-end de-risked:
- realizability (pp2 cascade `Adm = RealizableRank`, achiever-only) ✓
- per-node analytic chart (C5 hnode witness) ✓
- termination (this cert: `ΣM`-decrease suffices, finite branching) ✓

**On the Lean route (controller's question — Fubini-shear vs hard-pivot):** the **Codex hard-pivot**
route is the cheaper Lean path — it reuses `schur_straighten_squeeze_exists`'s `hnode` VERBATIM (the
`schur_node_squeeze_unif` squeeze is proven for arbitrary `b,E,SΓ`), so the C5 node is the SAME lemma
call as C1, with the survivor as `SΓ` and `b→0`. The **Fubini-shear** route is conceptually cleaner
(the defect is genuinely regular) but needs a NEW interface (the det-1 shear + spectator-peel
`measurePreserving_coreShear`/`rlct_additive_smooth_block`, which ARE in the library but would be a
second code path). **Recommendation: scope the hnode-grind on the hard-pivot route** (one mechanism for
C1 and C5, reusing the proven squeeze), keeping the Fubini-shear as the fallback / cleaner-redo if the
hard-pivot chart bookkeeping at deep nodes proves fiddlier than expected.

## Most likely thing to break this (RESOLVED, pp2 g222/g223)

The `e≠0` item is now settled (and corrected — see §3). pp2 (g222) verified the cascade's CENTER sits
ON `{e=0}` (the downstream `C₆C₅C₄ = 0` at the deepest point, `t₆=0`), so the cascade does NOT pin
`e≠0` — my earlier hope. But this does NOT open a gap: the C5 cell-cover is
`{e≠0 charts: Fubini-shear, regular ½} ∪ {e=0 sub-locus: recurse on the complement sub-block, ΣM-drops}`,
and BOTH branches descend on `ΣM` (the `e=0` complement-kill is a later `ΣM`-dropping step in `S.red`).
So the cover carries the `e=0` sub-node as a clean deeper recursion, not a wall — the no-stall guard is
the same `ΣM`-descent. The formaliser implements the `e=0` branch as a deeper-recursion cell (not a
stall, not a null skip). This is chart-bookkeeping, formaliser-scale; no termination or mechanism gap
remains. (pp2 banked at `origin/g223-c5-e0-lexterm @ 383fded`; reproduced `c5_e0_{center,lexdrop}.py`.)
