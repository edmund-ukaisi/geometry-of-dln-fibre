# Route M index set ι — PINNED (uniform pivotBlowupOn frame, unblocks fm3) (pp-hall, 2026-06-22, #140)

**Unblocks fm3's #27.** fm3's Case222→general map (`threads/fm3-coord-bridge/case222-tree-generalization-map.md`)
pinned the NODE OPERATION (uniform `pivotBlowupOn`; the `(pivot)²` loss factor IS the exceptional divisor
feeding `monomialThreshold`, NOT an additive `nReg/2`; uniform blow-up + recurse (NO step-2 straighten, #35); branch =
pivot choice). This addendum to #138 pins what I own: the **index set ι** + its reconciliation with the
the OFF-PATH squeeze, in fm3's uniform-pivotBlowupOn frame. fm3 is correctly blocked until ι is pinned; it is below.

## The node operation: UNIFORM blow-up + RECURSE (NO step-2 squeeze/straighten)
**(REVISED — controller flag #35: the earlier "two-level reconciliation" put the squeeze back as a step-2
straighten, which is the BLOCKED E→coordinate straightening; removed. C1 defaults to uniform blow-up +
recurse, fm3's frame.)** The C1 node operation is:
1. **`pivotBlowupOn active p`** of the rank-defect center: `core ∘ φ = x_p²·Q`, Jacobian `|x_p|^{card−1}`.
   **The `x_p²` is the EXCEPTIONAL DIVISOR** — `(k,h) = (1, card−1)`, ratio `card/2`, **ACCOUNTED by
   `monomialThreshold`** (`x_p²` vanishes on `{x_p=0}`, NOT a unit, so NOT stripped).
2. **RECURSE on the residual `Q` via the dispatcher** — `Q` is a strictly SMALLER core (singular part = the
   reduced-width Schur chain `S·A2red`; the regular pivot row rides as spectator coords), `ΣM` drops; the
   dispatcher re-classifies `Q` and the next `pivotBlowupOn` fires on its rank-defect. `lex`-terminates.
**NO step-2 straighten.** The E-coupling (the bilinear rank-defect `{r−pq=0}`) is resolved by FURTHER
blow-ups in the recursion, NEVER by straightening E to coordinates. Why this matters (controller flag #35):
- straightening `{r−pq=0}` (a singular quadric) to `{w=0}` (smooth coordinate subspace) IS the
  **E→coordinate straightening crux2 found BLOCKED** — the `(E, SΓ)` Jacobian is rank-deficient at the
  deepest point, so `E` are NOT coordinates there. If one (wrongly) treats them as coordinates, the
  "regular squares" give `rlctAtOn(∑E²) = 1/2`, NOT `nReg/2` — the order-4-vs-order-2 failure fm3 proved.
- The squeeze `flatCore − Φ ∈ ideal(E)` (#131) is a sound analytic FACT but is PARKED off-path: it is NOT
  C1's mechanism (it drops the `x_p²` weight; decision C / g134). The lemma2Fwd det-1 straighten is `(2,2,2)`
  SCAFFOLDING (fm3's map), not a general step.
**The step-2 straighten enters the spec ONLY if fm3 (building C1) + crux2 (vs the rank-deficiency) confirm
it is both NEEDED and CONSTRUCTIBLE** — held pending that check. Until then C1 = uniform blow-up + recurse. **fm3's correction adopted:
every node routes through `pivotBlowupOn`; the δ-branch `![…]` algebra is (2,2,2) scaffolding, not general.**

## ι — PINNED (the formaliser-consumable definition)
`ι M` = the **leaf set of the Route M chart tree** `RouteMTree M`, an inductive type built by the C1/C2/C4/C5
recursion, terminating by `lex(L, ΣM, ncDefect)`:

```text
inductive RouteMTree (M : Fin (L+1) → ℕ) : Type
  | leaf  (hbase : isSmoothLeaf M)                                    -- L=1 / rank-0: F=‖C₁‖² unit≥1
  | nodeC1 (c : PivotChoice M)  (child : RouteMTree (schurReduce M c))     -- coupled: ΣM drops
  | nodeC2 (c : PivotChoice M)  (child : RouteMTree (passThrough M c))     -- full-rank pass: L drops
  | nodeC4 (s : PinchLayer M)   (l : RouteMTree (leftBlock M s))           -- Fubini split: two children
                                (r : RouteMTree (rightBlock M s))
  | nodeC5 (c : MixedChoice M)  (compl : RouteMTree (schurReduce M c.complement))  -- mixed = C1∘C2
                                (surv  : RouteMTree (passThrough M c.survivor))

def ι (M) : Type := { leaves of RouteMTree M }      -- Fintype: finite branching × lex-bounded depth
```
- **`PivotChoice M`** = `(active, p)`: a nonempty coordinate block `active` of the active factor + the argmax
  pivot `p ∈ active` (the `argmaxCellOn_cover` cell — WHICH coordinate attains the max, = which affine chart
  of the blow-up). For a mixed node, `MixedChoice M` additionally carries the rank-`t_s` survivor selector.
- **Each leaf `π` carries `(d_π, k_π, h_π)`:** `d_π` = the ambient (flattened) dimension at the leaf; for each
  node `s` on `π`, ONE exceptional divisor with `(k,h)_s = (1, c_s−1)`, `c_s = Mval(stratum_s)` — from that
  node's `pivotBlowupOn` (Jacobian `u^{card−1}` ⟹ `h = card−1`; loss `u²` ⟹ `k = 1`). NO straighten
  between nodes — the recursion re-finds the next pivot on the residual (uniform blow-up + recurse, #35).
- **C3 (NC-completion) is NOT a tree node** — it is a deterministic POST-PASS on each path's assembled
  divisor arrangement (normal-crossing completion via intersection blow-ups, introducing `k_E ≥ 2`
  intersection divisors whose discrepancy keeps the ratio `codim/2`). It refines a leaf's `(d,k,h)` but does
  NOT branch `ι` — keeping `ι` finite and the branching `{C1,C2,C4,C5}` clean.

## The controller's guess — ι = the rank-defect (squeeze-fails-clean) resolution choices — CONFIRMED
The rank-defect center is where the loss is not yet monomial (pre-blow-up). What fails to be CLEAN (the literal
`u·(ΣE²+G²)`) is exactly at the **rank-defect center** (pre-blow-up, pivot not yet a unit) — which IS the
`pivotBlowupOn` center. So ι is indexed by the SEQUENCE of rank-defect centers resolved = the pivot/minor
choices = the `{C1,C2,C4,C5}` branch tree. **ι enumerates the ways the squeeze-fails-clean gets resolved by
`pivotBlowupOn`.** The controller's guess is right, made precise: `ι ↠ Adm M` (the `(S-min)` surjection — the
path through the minimising stratum's binding divisor is the `(C=∃)` achiever; full surjectivity is the
conceptual statement, `(S-min)` the load-bearing minimum, #134).

## The (2,2,2) banked tree IS `resolution_charts`'s ι for `M=(2,2,2)` (scope, corrected)
`resolution_charts M` is on the reduced-width core `‖∏C‖²` for widths `M` directly (`M = H − r`, `r` the
deepest rank). For the headline `(2,2,2)` r=0: `M = (2,2,2)`, core `= ‖A₁·A₂‖²` (2×2), and **the 24-leaf
banked tree IS `ι` for `M=(2,2,2)`** — `lambdaCore(2,2,2) = ½·minAdm Mval = ½·3 = 3/2`, matching the
24-leaf `⨅ = 3/2` (`g140_scope_check.py`). So fm3's Case222 map is the **direct template**, and the
C1/C2/C4/C5 recursion is its generalization to arbitrary `M`. (The `r=1` reduced core `M=(1,1,1)`,
`(c₁c₂)²`, is a separate smaller instance — already normal-crossing, ι trivial.)

## What fm3 builds (#27), now unblocked
1. **`RouteMTree M`** (the inductive above) + the dispatcher classifying each node C1/C2/C4/C5 (rank read
   RELATIVE to the active prefix image, #138 §1.5). `ι M` = its leaves (Fintype).
2. **Per-node = `pivotBlowupOn active p`** (uniform — NOT the δ-branch `![…]`): `step1A_eq_pivotBlowupOn` /
   `step2E_eq_pivotBlowupOn` are the banked ties; the general node derives `(active, p)` from the
   `PivotChoice`. Jacobian `(x p)^{card−1}`, loss `(pivot)²`. NO straighten between nodes — recurse (uniform, #35).
3. **`(d,k,h)` per leaf** from the path's nodes (`(1, c−1)` each); C3 NC-completion post-pass for `k≥2`.
4. **Value** `⨅ᵢ monomialThreshold = ofReal(lambdaCore M)` via `(C≥)` [`monomialThreshold_ge_of_mult`,
   mult-control, green] + `(C=∃)` [`monomialThreshold_le_regularSeq` at the `(S-min)` achiever, green] +
   `le_antisymm`.
5. **Termination** `lex(L, ΣM, ncDefect)` (#138 §3).

## Most likely thing to break this
The `PivotChoice`/`argmaxCellOn_cover` must be defined so the tree's branching is FINITE at each node (else
`ι` is not a Fintype). The argmax-cell cover (`argmaxCellOn_cover`, `{N}`-generic, banked) gives finitely
many cells per node; the minor-choice (C5 survivor) is a finite Grassmannian-cell choice (finitely many
coordinate-minor selectors). Both finite ⟹ finite branching; lex-bounded depth ⟹ finite tree ⟹ `ι` Fintype.
The one thing to confirm in Lean: the C5 `MixedChoice` survivor-selector set is finite (it is — a choice of
`t_s` columns from `t_{s-1}`, a `Finset`); flagged for the C5 chart construction.

## Decorrelation + provenance
Reconciles fm3's uniform-pivotBlowupOn node frame (`case222-tree-generalization-map.md`) + my #138 taxonomy
+ the #134 `(S-min)`. **The #129/#131 squeeze is PARKED off-path (NOT a step-2 straighten, #35; decision C
/ g134) — its earlier framing here as "step-(2) content" is SUPERSEDED.** The uniform-blow-up-recurse node is the key clarification fm3's
constraint forced. Scripts: `g140_index_set.py`, `g140_iota_inductive.py`, `g140_scope_check.py` in
`g129-scripts/`. A Codex pass on the ι inductive shape is optional (the reconciliation is mechanical given
fm3's frame + #138); the #138 design Codex already stress-tested the taxonomy. Builds on #138 (the
taxonomy), #134 ((S-min)), decision C / g134 (squeeze off-path), fm3's map (the uniform blow-up + recurse node operation).
