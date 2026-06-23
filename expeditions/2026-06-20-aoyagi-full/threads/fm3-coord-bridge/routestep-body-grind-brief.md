# Brief: the general `routeStep` body — the R1 dispatcher grind (fm3 thread, #85/#39)

You are a **fresh lean-formaliser** on the DLNFibre hero expedition. Invoke the `lean-formalisation`
skill and follow it. Build commands + Mathlib conventions: `lean/CLAUDE.md`. Branch: `fm3/routem`
(work here; push to `origin/fm3/routem` is pre-authorized; do NOT commit to dev/master). **Read the
committed code at HEAD, not any transcript** — verify every signature with `git show
origin/fm3/routem:<file>` before building on it.

## The target (ONE long-pole, decomposed)

Fill the single committed `sorry`: `routeStep {L} (M₀ M : Fin (L+1) → ℕ) : RouteStep M₀ M`
(`lean/DLNFibre/DLN/RLCT/Validate/RouteMRecursion.lean:184`). It is the R1 dispatcher: classify a
node `(root M₀, current M)` into `leaf` or `branch`, producing genuine root-anchored data so the
`routeAtlas` WellFounded.fix (already green around this sorry) builds a `NodeChartFamily` whose `⨅` over
leaves folds to `½·minAdm(M₀)`. ALL design gates are CLEARED (controller green-light 2026-06-23); this
is the transcription grind.

**Do NOT stub it vacuously.** Three green-but-WRONG bodies are catalogued in the `routeStep` docstring
(read it): (i) leaf-everywhere (threshold ⊤), (ii) codim=card (the (4,3,2) trap), (iii) the smuggling
trap (Unit-cells+schurState+codim:=minAdm type-checks via `zero_mem_Adm` but fakes the construction). A
sorry under the correct statement outranks any of these. If you cannot build a sub-target faithfully,
leave its `sorry` with a one-line note and surface to fm3 — do not fake it.

## The committed type (verify @ba71584)

```
inductive RouteStep {L : ℕ} (M₀ M : Fin (L + 1) → ℕ) : Type 1
  | leaf (md : MonoData)
  | branch (cells : Type) (cellsFin : Fintype cells) (cellsNe : Nonempty cells)
      (split : cells → ChainDimSplit M) (codim : cells → ℕ)
      (witness : (c : cells) → PivotWitness M₀ (codim c))
```
`M₀` is the FIXED root (threaded through `routeAtlas (M₀)`); `M` descends to `(split c).red`. The
witness is ROOT-anchored (`PivotWitness M₀`, settled option (A) — do NOT re-restructure the type).

## Banked atoms you CONSUME (all green, sorry-free on fm3/routem — do not rebuild)

- `schurState M hlo : ChainDimSplit M` (`SchurState.lean`) — the C1 reduced-width split
  `(M₀−1, M₁−1, M₂,…)`, `hlo : ∀ s, s.val ≤ 1 → 1 ≤ M s`. `split.red = schurState.red` is the genuine
  reduced chain; `redM_chainRel` gives the ΣM-decrease for the recursive call.
- `PivotWitness M₀ c` (`RouteMState.lean:287`) — a **Type**-structure `⟨T : Fin L → ℕ, hAdm : T ∈ Adm M₀,
  hCodim : c = (Mval M₀ T).toNat⟩`. The root-anchored §2 codim witness. (`Adm`/`Mval` are concrete
  decidable, `Lambda.lean`.)
- `foldFamily_iInf_eq_half_minAdm` (`RouteMState.lean:321`) — the VALUE fold (ACHIEVER-ONLY, no
  surjectivity): given (C≥) every leaf's per-cell `PivotWitness M₀` + (C=∃) ONE achiever leaf `i₀` with
  `minAdm ∈ codimsOf i₀`, `⨅ = ½·minAdm`. This is what the headline consumes.
- `leafMonoData d` / `MonoData.appendDivisor md c` (`RouteMState.lean:54/87`) — the leaf datum (k≡0,
  threshold ⊤) and the pivot-axis append (`(k,h)=(1,c−1)`).
- `NodeChartFamily M = ⟨ι, fintype, nonempty, data : ι → MonoData⟩` — the `routeAtlas` output.
- crux2's per-node hnode primitive (`GeneralR1Recursion.lean`, on `fm2/split-reindex`, imported via the
  toolkit): `schur_straighten_squeeze_exists` (PROVEN cond-on-`hnode`) + `rlctAtOn_reduced_transport` (the
  det-1 reduced-core reindex). **A C5 node is the SAME `schur_straighten_squeeze_exists` call as C1**
  (survivor = SΓ, b→0) — one mechanism C1+C5 (crux2 confirmed).
- cover infra: `S1G5Charts.lean` (the `argmaxCellOn`/`n_cover`/`n_aedisjoint` chart cover over `active`),
  `pivotBlowupOn`, `node_loss_pivot_factor` (`NodeHomogeneity.lean`, the G2 `core∘φ = x_p²·Q`).

## The WORKED PATTERN (the (2,2,2) template — generalize THIS)

`Case222RouteStep.lean` (mine, @9ad72f3, green) is the concrete instance the cascade generalizes:
`case222_routeStep_branch : RouteStep M222route M222route` = `.branch Bool _ _ (fun _ => schurState
M222route _) (fun b => if b then 4 else 3) (witness)`, and `case222_routeStep_value = 3/2` via
`foldFamily_iInf_eq_half_minAdm` (one Unit leaf, codimsOf=[4,3], achiever-only). **Study this first** — it
shows the branch fields jointly inhabited with genuine root-anchored data, folding to lambdaCore.

## pp2's cascade recipe (the classify — confirmed by controller)

- **cells** = the `argmaxCellOn` charts of the node's `pivotBlowupOn` over `active` (the affine charts);
  finite (Fintype), Nonempty.
- **split** = `schurState M` per node (the C1/C5 reduced-width split).
- **T_c achiever-only**: ONE threaded `T*` path (the root minimiser, `Mval M₀ T* = minAdm`); each cell's
  codim = `(Mval M₀ T_c).toNat` for an admissible `T_c` (C≥, the no-undershoot, cardinality-direct
  locally), and the distinguished achiever branch resolves `T*`.
- **leaf** iff `red ≡ 0` / `IsUnit residual` (terminal); `leafMonoData`.
- **termination**: the banked `chainRel` (ΣM-decrease) SUFFICES — no lex augmentation (pp-r1realize
  confirmed; each C5 chart drops ΣM by 2·(complement rank)). e=0 is a DEEPER ΣM-dropping node (recurse on
  complement), NOT a stall: cover = {e≠0 shear} ∪ {e=0 recurse}.

## Suggested decomposition (reachable sub-targets, build IN ORDER, commit each green)

1. **Leaf classifier**: a decidable `isLeafNode M` (red≡0 / unit residual) + the `leaf (leafMonoData …)`
   arm. Smallest piece; validates the terminal case.
2. **Single-node branch constructor**: a `def routeStepBranch (M₀ M) (pivot-data) : RouteStep M₀ M` from
   the argmaxCellOn cells + schurState split + the per-cell codim + the achiever-threaded `PivotWitness
   M₀`. Validate it reproduces `case222_routeStep_branch` on (2,2,2). This is the substantive piece.
3. **Assemble `routeStep`**: classify → leaf | branch (sub-targets 1+2). Then `routeAtlas`/`routeMIota`
   go concrete; wire `foldFamily_iInf_eq_half_minAdm` over `routeMIota` (the value) — confirm it folds to
   ½·minAdm on (2,2,2)/(3,2,3).
4. **Descent wiring** (coordinate with crux2 via fm3): compose `node_loss_pivot_factor` (B, the cover
   CoV) + `rlctAtOn_reduced_transport` (A, crux2's det-1 reindex) INSIDE the cover lintegral — the
   per-node descent. The hnode primitive is crux2's; the fold/iteration is ours.

Build sub-target 1 first, `lake build` to validate the signature, then fill. **Numerically sanity-check**
each codim/Mval against `Lambda.lean`'s `#eval Mval`/`decide Adm` before proving (the (2,2,2):
Mval(0,0)=4, (1,0)=3, minAdm=3 ⟹ 3/2 is the anchor).

## Discipline

- Zero `sorry`/`axiom`/`native_decide`/`#exit` in committed files (`scripts/sorries` before commit).
  `decide +kernel`, not `native_decide`.
- Verify a Mathlib/local lemma EXISTS before building on it (`rg` over `.lake/packages/mathlib/` /
  `lean/`; `scripts/lean-search`). Don't trust recalled signatures.
- Never leave the build broken. Can't fix in 3-4 attempts → `git checkout -- <file>` + a `sorry` with a
  one-line note. Stop on thrash (3 failed attempts at one goal) → consult Codex
  (`local-codex-consult`) or hand back to fm3 with the blocker.
- Do NOT edit `DLNFibre.lean` (single-writer aggregator) or crux2's files (`GeneralR1Recursion.lean`,
  `RouteMBridge.lean`, `RouteMAtlas.lean`, `ResolutionAtlas.lean`) — import them.
- `PivotWitness` is a **Type** (data): a `∀ c ∈ list, PivotWitness M c` fact is a `def` not `theorem`;
  select the witness by a decidable `if`-branch on `c` (rcases on a `Prop`-`Or` fails — `Or.casesOn`
  can't eliminate into a `Type` goal). (Learned building Case222RouteStep.)
- No wall-clock estimates; quote line counts + sub-task lists.
- Report to fm3 (NOT the controller directly): files created, theorems delivered (one line each), sorries
  remaining (with reason), build status, LoC delta, blockers. Coordinate the per-node hnode↔fold boundary
  with crux2 THROUGH fm3 (relay).

## Report cadence

Milestone after each sub-target lands green. Surface a wall (esp. the achiever-threading in sub-target 2,
or deep-node hard-pivot bookkeeping in sub-target 4 — Fubini-shear is the fallback per the controller) the
moment 3 attempts fail. fm3 relays pp2 (cascade) + crux2 (hnode) questions.
