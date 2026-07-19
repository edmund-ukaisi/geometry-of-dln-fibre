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
(which read the piece's `divCoord`) fail for every non-birth-corner piece.

**#35 IS THE SEAM-FIX UNIFICATION (elder ruling, compass fork 14) — NOT a bolted-on override.** The elder
diagnosed the emission seam as MIS-FACTORED: the ledger (`{lc.1 …}`) and the geometry (`chartMap := lc.2`) are
two structures reconciled after the fact, which is the root of BOTH drift defects (finding-1 falsity and
finding-3 mismatch). The fix is to correct the SEAM itself, not to add a per-pivot `divCoord` override on top
of `{lc.1 with chartMap := lc.2}` (a bolted-on override is GATED-REJECTED at review). Concretely:
`geometricLeafPaths` emits, per path, **ONE record whose `chartMap` AND per-pivot `divCoord`/`divExp` all
derive from the SAME path fold**; `geoAtlas` just reads that record. The payoff is direct: the finding-2
cocycle then becomes **near-definitional maintenance of that one recursion** (each fold step extends `chartMap`
by `geoChartMap` AND the ledger by the step's pivot in lockstep), instead of a reconciliation theorem against a
possible ledger↔geometry mismatch — the wall gets structurally smaller. The co-folded per-path ledger:

- `divCoord (piece) = ` the birth-corner flat coords `cNodeOf n_j (pivot_j)` of the divisors born on the piece's
  root→leaf path (one per path level that births/merges a divisor) — emitted by the SAME recursion that builds
  `chartMap`, so they cannot drift;
- `divExp (piece) = ` the **accumulated** exponents (per `stepUpdate`), NOT a uniform value.

Sequenced: only after t10's countersigned clause-(A) batch lands (`GeoChart.lean` ownership; do NOT edit before).

**Design-note-(i) answer (co-design with finding-2):** the per-EDGE Jacobian exponent is *uniform*
(`dCenterOfNode n − 1`, from `geoChartMap_fderiv_det`), but the per-PIVOT `divExp` is *not* uniform — it
accumulates per `stepUpdate` case (see the exponent bookkeeping below). So the finding-3 emission must carry a
per-pivot `divExp` computed from the case, not a single `dCenterOfNode`-derived number.

**Design-note-(ii) (clause C at assembly):** the fix changes ledger FIELDS, not `chartMap`, so t10's cover
proof (images only) is unaffected; but clause (C) (`divExp ∈ terminalExponents t`) must be re-verified for the
per-pivot pieces at assembly (the per-pivot `divExp` values must lie in `terminalExponents`).

## Finding-2 — the tree-walk invariant (the cocycle). STATEMENT to gate.

**Shape: structural induction on `t`, motive GENERALIZED over `acc`** (elder ruling, ADOPTED now — not
deferred to a post-t10 definitional check). t10's rollover/chartless `id`-passthrough FORWARDS `acc` (does not
reset to `id`), so the `acc = id` motive may not be definitionally clean at every reachable node; discovering
that mid-grind is the entry-9 failure mode the weakest-hypothesis lesson exists to prevent. Since the Phase-2
fold `abs_det_fderiv_foldr_comp` is already `acc`-agnostic (a forwarded `acc` is extra leading factors; a
rollover's `id`-passthrough contributes `|det D(id)| = 1` via the off-cone atom), generalizing costs nothing
and removes the risk. Motive:

    Inv(t): ∀ acc, Differentiable ℝ acc → ∀ lc ∈ geometricLeafPaths … acc t, ∀ w,
              |det D(lc.2) w| = |det D(acc) (pathFold t lc w)| · <per-piece monomial>(w)

where `pathFold t lc` is the geoChartMap composition (so `lc.2 = acc ∘ pathFold t lc`) and `<per-piece
monomial>(w) = ∏_{k : Fin (pieceLedger lc).numDiv} |z_{pieceLedger lc |>.divCoord k}(w)| ^ ((pieceLedger lc).divExp k − 1)`
with `pieceLedger lc` the finding-3 co-folded per-piece ledger.

**The headline** (finding-1 re-scope) is the `acc = id` specialization: `|det D(id) (…)| = 1`, giving
`|det D(lc.2) w| = <per-piece monomial>(w)` for `lc ∈ geometricLeafPaths … id (buildTree M (conOracle M) (conRoot M))`.

- **Base `t = .leaf l`:** `lc = (l, acc)`, `lc.2 = acc`, `pathFold = id`. LHS `= |det D(acc) w|`; RHS `= |det D(acc)(id w)| · <monomial>`. The piece's path has NO blow-ups, so `pieceLedger` is EMPTY ⟹ `<monomial> = 1`, and the identity is `|det D(acc) w| = |det D(acc) w| · 1`. ✓ (Finding-3's per-piece ledger is load-bearing: the leaf's *global* `divExp` would break the base; the *per-path* ledger makes it `1`.) At `acc = id`, `J(root-leaf) = 1`.

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
