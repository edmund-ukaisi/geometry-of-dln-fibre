# Fold-Jacobian SPECIFY — t11 addendum (findings + re-scope + the invariant statement)

*Author: `architect-t11`. Records the three findings from grinding the PROVE (all team-lead-ACCEPTED,
Codex-corroborated `codex/fold-jacobian-scoping-answer.md`), the re-scoped headline (finding-1), and the
STATEMENT-FIRST design of the finding-2 tree-walk invariant to be gated by team-lead + counter-signed by
coverage-t08 before the maintenance grind. Companion to `fold-jacobian-specify.md` (coverage-t08).*

## Finding-1 — the `∀ t` statement is false at root-leaves (the (1,1,1)-style witness)

**Counterexample.** Take `t = .leaf l` with `l.numDiv = 1`, `l.divExp 0 = 3`. Then
`geometricLeafPaths (dCenterOfNode M) (qNodeOf M) id (.leaf l) = [(l, id)]`, so the composite is `id`:

    |det D(id) w| = |det (ContinuousLinearMap.id ℝ (Params M))| = 1

while the SPECIFY's RHS is `∏_{k} |z_{l.divCoord k}(w)|^{l.divExp k − 1} = |z_{l.divCoord 0}(w)|^2`,
which is `0` at any `w` with `z_{l.divCoord 0}(w) = 0`. So LHS `= 1 ≠ 0 =` RHS. The original `∀ t` quantifier
admits this root-leaf, so the statement is false as written.

**Re-scope (team-lead-APPROVED).** The only consumer (`chartBridge_buildTree`) needs the ROOT build. The
sibling cover SPECIFY `geoAtlas_imageCover` already carries `htree`; the fold SPECIFY omitting it was the
defect. Honest scope:

    t = buildTree M (conOracle M) (conRoot M)

`conRoot` has `numDiv = 0`, so the root-leaf degeneracy cannot occur (an empty analytic ledger ⟹ empty
product `= 1 = |det id|`). Codex sharpened: `buildTree … s` at an *arbitrary* `s` is insufficient (a non-root
`s` already carries divisors the composite does not blow up) — the specialization must be `conRoot`.

## Finding-3 — per-pivot `divCoord`/`divExp` (upstream, co-designed here)

`geoAtlas` currently sets each piece to `{ leaf with chartMap := composite }`, so every fan-out copy of a
leaf shares the leaf's `divCoord`/`divExp`; but the fan-out over `p : Fin (dCenterOfEdge …)` gives each copy
a distinct exceptional coordinate `cNodeOf … (offset+p)` (`cNodeOf` injective). So `LeafJacobian`/`LeafPullback`
(which read the piece's `divCoord`) fail for every non-birth-corner piece. The corrected `ChartBridge` design
already calls for per-pivot `divCoord` (`EngineDefs` clause-(B) note). The fix (in `GeoChart.lean`,
architect-t10's file until its clause-(A) batch lands) must re-derive **each geometric piece's ledger from its
path pivots**:

- `divCoord (piece) = ` the birth-corner flat coords `cNodeOf n_j (pivot_j)` of the divisors born on the piece's
  root→leaf path (one per path level that births/merges a divisor);
- `divExp (piece) = ` the **accumulated** exponents (per `stepUpdate`), NOT a uniform value.

**Design-note-(i) answer (co-design with finding-2):** the per-EDGE Jacobian exponent is *uniform*
(`dCenterOfNode n − 1`, from `geoChartMap_fderiv_det`), but the per-PIVOT `divExp` is *not* uniform — it
accumulates per `stepUpdate` case (see the exponent bookkeeping below). So the finding-3 emission must carry a
per-pivot `divExp` computed from the case, not a single `dCenterOfNode`-derived number.

**Design-note-(ii) (clause C at assembly):** the fix changes ledger FIELDS, not `chartMap`, so t10's cover
proof (images only) is unaffected; but clause (C) (`divExp ∈ terminalExponents t`) must be re-verified for the
per-pivot pieces at assembly (the per-pivot `divExp` values must lie in `terminalExponents`).

## Finding-2 — the tree-walk invariant (the cocycle). STATEMENT to gate.

**Shape: structural induction on `t` at `acc = id`** (mirrors `geometricLeafPaths`' own recursion; the child is
always recursed with `id`, so the motive fixes `acc = id`).

**`acc`-motive robustness (team-lead flag, post-gate).** The `acc = id` motive is clean for the CURRENT
`geometricLeafPaths` (every child recurses at `id`; `acc` is only a same-node prefix, `id` at the root call).
t10's rollover/chartless `id`-passthrough FORWARDS `acc` (does not reset to `id`), so at instantiation VERIFY
(don't assume) that every node reachable from an `id` root call still receives `acc = id`. If that is not
definitionally clean after t10's reshape, GENERALIZE the motive over `acc` with a composition clause:

    Inv(t): ∀ acc, ∀ lc ∈ geometricLeafPaths … acc t, ∀ w,
              |det D(lc.2) w| = |det D(acc) (pathFold t lc w)| · <per-piece monomial>(w)

(the `acc = id` headline is the `|det D(id)| = 1` specialization). This is de-risked: the Phase-2 parametric
fold `abs_det_fderiv_foldr_comp` is ALREADY `acc`-agnostic (it folds an arbitrary map list, so a forwarded
`acc` is just extra leading factors — a rollover's `id`-passthrough contributes `|det D(id)| = 1` via the
off-cone atom), so the fold MECHANICS survive any threading; only the leaf-read STATEMENT needs the `acc`
clause. Decision (id-motive vs acc-generalized) is deferred to the check against t10's landed threading.

Motive `Inv(t)`: for every `lc ∈ geometricLeafPaths (dCenterOfNode M) (qNodeOf M) id t` and every `w`,

    |det D(lc.2) w| = ∏_{k : Fin (pieceLedger lc).numDiv}
                        |z_{pieceLedger lc |>.divCoord k}(w)| ^ ((pieceLedger lc).divExp k − 1)

where `pieceLedger lc` is the finding-3 per-piece ledger (path pivots + accumulated exponents).

- **Base `t = .leaf l`:** `lc = (l, id)`, `lc.2 = id`, LHS `= 1`. The piece's path has NO blow-ups, so
  `pieceLedger` is EMPTY ⟹ RHS `= 1`. ✓ (This is exactly why finding-3's per-piece ledger is load-bearing: the
  leaf's *global* `divExp` would break the base, the *per-path* ledger makes it `1 = 1`.) `J(conRoot)` in the
  team-lead framing = this base.

- **Step `t = .branch n edges`:** a path `lc` factors as `lc.2 = geoChartMap ⟨n, edge, offset+p⟩ ∘ lc'.2` for a
  child path `lc'` of `ch`. Then

      |det D(lc.2) w| = |det D(geoChartMap ⟨n,edge,offset+p⟩) (lc'.2 w)|   -- per-edge atom, banked
                        · |det D(lc'.2) w|                                  -- IH on ch

  The IH gives the child per-piece monomial at `w`; the atom
  (`geoChartMap_fderiv_det` / `_offcone`) gives `|z_{cNodeOf n (offset+p)}(lc'.2 w)| ^ (dCenterOfNode n − 1)` —
  at the INTERMEDIATE point `lc'.2 w`. The step closes iff the atom's intermediate-point factor **regroups**
  onto the source-`w` per-piece ledger delta:

### THE REGROUPING LEMMA (the cert-needed crux, per `stepUpdate` case)

    |z_{cNodeOf n (offset+p)}(lc'.2 w)| ^ (dCenterOfNode n − 1)
      = (the source-w monomial of the ledger delta from parent-of-`ch` to `n`)

matched against `stepUpdate` (`EngineDefs:150-177`). The exponent arithmetic already checks out against my atom:

| case | edge `dCenterOfEdge` | node `dCenterOfNode` | atom exponent (`dCN − 1`) | `stepUpdate` delta | match |
|---|---|---|---|---|---|
| case-2 | `resRows·resCols` | `resRows·resCols` | `resRows·resCols − 1` | new pivot `divExp = resRows·resCols` ⟹ `−1` | **CLEAN** (direct) |
| case-1(1) `u` | `1` | `1 + runLen·resCols` | `runLen·resCols` | `divExp(mergeIdx) += runLen·resCols` | **re-merge** onto ancestor `mergeIdx` |
| case-1(2) `d` | `runLen·resCols` | `1 + runLen·resCols` | `runLen·resCols` | new pivot `divExp = divExp(mergeIdx) + runLen·resCols` | **inherited-threading**: the `divExp(mergeIdx) − 1` "inherited M−1" must come from the intermediate-point substitution |

So the exponent LEDGER matches my atom in all three cases. The OPEN part is the intermediate-point
COORDINATE substitution — which source coordinate `z_{cNodeOf n (offset+p)}(lc'.2 w)` lands on, through the
child fold `lc'.2`, and that the "inherited M−1" (case-1(2)) and the re-merge onto the ancestor birth corner
(case-1(1)) thread correctly. The elder's substitution table (`fold-jacobian-specify.md` §crux;
`cert-psi-mix.md` §R-b confirms per-node exponent-preservation but NOT the fold regrouping) SKETCHES these
(u-chart `u↦u, d_a↦u·d'_a`; d_j-chart `u↦d_j·u', d_a↦d_j·d'_a`) but does not give the formal per-case
intermediate-point identity.

**CERT REQUEST (per team-lead's offer).** Before stating the three regrouping-lemma cases faithfully, commission
a pen-and-paper certificate making the elder's table formal-precise: for each `stepUpdate` case, the exact
identity `z_{cNodeOf n (offset+p)}(childComposite w) = <explicit source-w monomial>` (which coordinates the
child fold `lc'.2` moves the node pivot onto, and that the re-merge/inheritance exponents sum as tabulated).
This is the o5 pattern (cert → build). It is the sole non-mechanical link; the base, the per-edge atom, the
chain rule, and the exponent arithmetic are all in hand.

## Validated fill-target (blocked on finding-3 + the cert)

The elaborating Lean skeleton (a new `Engine/GeoJacobianFold.lean`: the re-scoped headline + `Inv` def + base +
step-via-atom + the sorried regrouping lemma) is deferred to AFTER (a) finding-3's per-piece ledger lands (so
`pieceLedger` is a real def, not a placeholder — the headline cannot elaborate correctly over the current
per-leaf `divCoord`) and (b) the cert pins the regrouping identity. Stating a sorried headline over the current
(false, per-leaf-`divCoord`) `geoAtlas` would be a sorry under a wrong statement. The banked per-edge atom
(`Engine/GeoJacobianSpec.lean`, sorry-free, axiom-clean) is the step's consumed lemma and is construction-stable.
