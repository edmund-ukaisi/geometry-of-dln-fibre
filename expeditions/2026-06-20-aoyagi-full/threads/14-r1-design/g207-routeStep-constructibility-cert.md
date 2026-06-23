# routeStep constructibility — codim is ROOT-anchored geometric (not reduced-chain Mval); split.red = schurState (pp-hall, 2026-06-23, #39/#85)

**fm3's PRODUCER-grind constructibility question** (the general-M `routeStep` shape): given that `split.red`
and the `PivotWitness.T` are LOGICALLY DECOUPLED in the type (`branch cells split codim witness`, the value
reads `codim`+`witness`, `routeAtlas` recurses on `split.red`), which `split.red`/`T`/`codim` construction
terminates AND supports both `foldFamily_*` (value) and `cover_le` (geometry)? Two candidates: (1)
flat-branch-over-Adm with arbitrary `split.red`; (2) rank-descent (`split.red = schurState`, g195). **Answer:
(2). split.red is NOT free.**

## THE DECOUPLING TRAP (why candidate 1's arbitrary `split.red` breaks)
`codimsOf` entries are the witness's `codim`, and `PivotWitness M c` is witnessed at the NODE's `M`. If a
child node's `M = split.red` (the reduced chain) and one witnesses `codim = (Mval (split.red) T_local).toNat`,
that UNDERSHOOTS `m₀ = minAdm(ROOT M)`: **`minAdm(schurState M) < minAdm(root M)` in every case** (verified
`g207`): `(2,2,2)` root minAdm 3, `schurState (1,1,2)` minAdm 1; `(3,2,3)` 5 → 2; `(3,3,3)` 7 → 4. A child
cell with `codim = minAdm(child) = 1 < m₀ = 3` ⟹ `foldFamily_threshold_ge` FAILS (a path undershoots `½m₀`).
**So the codim must be the GEOMETRIC codim in the ROOT ambient, not the reduced chain's `Mval`.**

## THE RIGHT READING (g208): codim = Mval(ROOT M, T), the original-space geometric codim
The `(2,2,2)` `codimsOf = [4,3]` is `Mval(ROOT (2,2,2), T)` at BOTH nodes — step-1 `T=(0,0)` →
`Mval((2,2,2),(0,0)) = 4`; step-2 `T=(1,0)` → `Mval((2,2,2),(1,0)) = 3`. **NOT** `Mval(reduced (1,1,2), T)`
(which gives `2, 1` — wrong, undershoots). The codim a node contributes = the GEOMETRIC codim of its blow-up
center = the pivot stratum cardinality = `Mval(ROOT M, T_node)` for the cumulative rank pattern `T_node` the
node resolves (the rank-descent `T_0 ⊃ T_1 ⊃ …`). All `≥ minAdm(ROOT)` (every `Mval(ROOT,T) ≥ minAdm` by def
of the inf) ⟹ `foldFamily_threshold_ge` fires; the achiever path hits `minAdm` ⟹ `foldFamily_achiever`.

## VALUE vs COVER_LE — the tension (g209), and why it forces the geometric tree
- **`foldFamily` (value)** reads `codimsOf` ONLY; the tree SHAPE is irrelevant. Candidate (1) flat-branch
  DOES give the value: `⨅` over `Adm M` of `Mval(ROOT,T)/2 = lambdaCore` (`(2,2,2)`: cells
  `{(0,0)→4,(1,0)→3,(2,0)→4}`, `⨅ = 3/2`, achiever `(1,0) = minAdm 3`).
- **`cover_le` (geometry)** needs REAL charts that cover the loss locus — the iterated `pivotBlowupOn`
  (Case222 step-1 → step-2 → leaf), each landing `monomial·unit` via a c-o-v. A flat branch with ARBITRARY
  `split.red` provides NO charts ⟹ `cover_le` is unprovable.
- In the **UNIFIED `RouteStep`** (one tree feeds both `isCover` + `isValue`), the tree MUST be the GEOMETRIC
  one (the rank-descent `pivotBlowupOn` resolution); the value reads `codimsOf` off it. **`cover_le` forces
  candidate (2).** Candidate (1) is a value-only shortcut that cannot carry the cover.

## RECOMMENDATION (for the build)
1. **DEFINE `schurState` as a Lean def** (reduced widths `M_0−1, M_1−1, M_{s≥2}`). `split.red = schurState`
   (`Σ red < Σ M` via the `hdrops` field — terminates). `split.red` is NOT free.
2. **`codim` = the GEOMETRIC codim in the ORIGINAL ambient** = the pivot stratum cardinality =
   `Mval(ROOT M, T_node)`. NOT `Mval(split.red, T_local)`.
3. **`witness.T`** = the cumulative rank pattern at the node; `hAdm : T ∈ Adm (ROOT M)`; `hCodim : codim =
   (Mval (ROOT M) T).toNat`.

**Two ways to make `codim` root-anchored in the decoupled type:**
- **(A) carry the root `M`** through the `WellFounded.fix` (the recursion knows the original ambient), so
  each node's `PivotWitness` is against `ROOT M`;
- **(B, if root-carry is awkward) `codim` = the pivot stratum CARDINALITY directly** (a `ℕ` read off the
  blow-up center, NOT routed through `Mval`), then prove `codim = Mval(ROOT M, T)` as the `PivotWitness.hCodim`
  obligation (the C1-condition, g183 §2). This decouples `split.red = schurState` (width bookkeeping) from
  `codim` (geometric, root-anchored) cleanly.

## For the (2,2,2) anchor + terminating general skeleton (build NOW)
Rank-descent (candidate 2) with `schurState` defined: `codimsOf = [4,3]` ✓, `cover_le` has the
`pivotBlowupOn` charts ✓, `foldFamily_achiever` fires with `m₀ = 3` ✓. The general recursion terminates on
`chainWidthSum` (the `schurState` `Σ`-drop). The achiever `i₀` (g147/g148) is the rank-descent path resolving
each layer to its `T*`-rank.

## Decorrelation
pp-hall exact algebra (`g207` the undershoot of `minAdm(schurState) < minAdm(root)`; `g208` the
root-vs-reduced codim reading giving `[4,3]`; `g209` the value-vs-`cover_le` tension forcing the geometric
tree). Codex down env-wide (the AISI-wrapper git-ssh hang) — this rests on the exact-algebra + the
foldFamily/`cover_le` structural argument; a decorrelated subagent pass is the substitute channel if wanted.
Builds on g183 §2 (the C1-condition codim=Mval witness), g195 (the (2,2,2) spell-out), RouteMState
(`foldFamily_*`, banked), `block_elimination` (the rank-r normal form / the geometric codim).
