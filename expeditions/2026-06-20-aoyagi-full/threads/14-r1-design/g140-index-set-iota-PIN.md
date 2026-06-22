# Route M index set ι — PINNED (uniform pivotBlowupOn frame, unblocks fm3) (pp-hall, 2026-06-22, #140)

**Unblocks fm3's #27.** fm3's Case222→general map (`threads/fm3-coord-bridge/case222-tree-generalization-map.md`)
pinned the NODE OPERATION (uniform `pivotBlowupOn`; the `(pivot)²` loss factor IS the exceptional divisor
feeding `monomialThreshold`, NOT an additive `nReg/2`; node = blow-up (step A, weight) + EXACT Schur-descent (step B, ΣM-drop; #36) + recurse; branch =
pivot choice). This addendum to #138 pins what I own: the **index set ι** + its reconciliation with the
the OFF-PATH squeeze, in fm3's uniform-pivotBlowupOn frame. fm3 is correctly blocked until ι is pinned; it is below.

## The node operation: blow-up (weight) + EXACT Schur-descent (ΣM-drop) + recurse
**(REVISED — controller #35 then refined #36. The squeeze is OFF-PATH; but there ARE two steps: the
blow-up carries the weight, the EXACT Schur-descent carries the `ΣM`-drop. Distinguish THREE things: the
squeeze (off-path bound), the E→coordinate straightening (blocked), and the exact Schur-descent (step B,
the ΣM-drop; its general constructibility = the crux2 check).)** The C1 node operation, two steps:
1. **(A) `pivotBlowupOn active p`** of the rank-defect center: `core ∘ φ = x_p²·Q`, Jacobian `|x_p|^{card−1}`.
   **The `x_p²` is the EXCEPTIONAL DIVISOR** — `(k,h) = (1, card−1)`, ratio `card/2`, **ACCOUNTED by
   `monomialThreshold`** (`x_p²` vanishes on `{x_p=0}`, NOT a unit, so NOT stripped). **Step A does NOT drop
   `ΣM`** — the hard-pivot-normalized residual `Q = ‖Â·A2‖²` has the SAME dimensions `M` (g143).
2. **(B) the EXACT det-unit Schur-descent** (the `lemma2Fwd` generalization — det-`±1` c-o-v, lintegral-level
   splice, NOT a two-sided bound): clears the pivot row+col (`L·Â·R = blockdiag[1, S]`, `S = D − b·a`),
   giving `[regular pivot row] + ‖S·A2red‖²`, `‖S·A2red‖² = dlnLoss M' 0` with `M'_0=M_0−1`, `M'_1=M_1−1`.
   **THE `ΣM`-DROP IS HERE** — `ΣM' = ΣM − 2` (`Σdrop=2>0`, `ChainDimSplit.measure_drops`; g143).
3. **(C) RECURSE** on the smaller core `‖S·A2red‖²` via the dispatcher (`lex`-terminates via step-B's `Σdrop`).

**Three things kept DISTINCT (the controller's flag #35 + refinement #36):**
- **The SQUEEZE** `c₁Φ ≤ F ≤ c₂Φ` (#131) is OFF-PATH — it drops the `x_p²` weight (decision C / g134, g141).
  NOT step B.
- **The E→coordinate straightening** (treating `E` as coordinates, `rlctAtOn(∑E²)=nReg/2`) is BLOCKED — the
  `(E,SΓ)` Jacobian is rank-deficient at the deepest point (crux2); `∑E²` would give `1/2`, not `nReg/2`
  (the order-4-vs-2 failure). C1 does NOT straighten `E` to coordinates.
- **The EXACT Schur-descent** (step B) is the det-`±1` c-o-v clearing the pivot row+col to expose the
  smaller core `‖S·A2red‖²`. It is the intended `ΣM`-drop. **Its general constructibility (vs the
  rank-deficiency that blocked the squeeze/E-straightening) is the crux2 check, held** (#36). If step B
  generalizes, C1 is the both-steps node; if not, C1 falls back to iterated blow-up (the cover handling
  chart-locality). Either way the squeeze is off-path and `E` is never straightened to coordinates.
**fm3's correction adopted:** every node routes through `pivotBlowupOn` (step A); the δ-branch `![…]`
algebra is `(2,2,2)` scaffolding.

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
   `PivotChoice`. Jacobian `(x p)^{card−1}`, loss `(pivot)²`. Step B = EXACT det-unit Schur-descent (ΣM-drop, #36); recurse.
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
+ the #134 `(S-min)`. **The #129/#131 squeeze is PARKED off-path (decision C / g134); the node's ΣM-drop is the EXACT Schur-descent (step B, `lemma2Fwd` generalized, #36), NOT the squeeze and NOT the blocked E→coordinate straightening.** The both-steps node (blow-up + exact Schur-descent + recurse) is the key clarification fm3's
constraint forced. Scripts: `g140_index_set.py`, `g140_iota_inductive.py`, `g140_scope_check.py` in
`g129-scripts/`. A Codex pass on the ι inductive shape is optional (the reconciliation is mechanical given
fm3's frame + #138); the #138 design Codex already stress-tested the taxonomy. Builds on #138 (the
taxonomy), #134 ((S-min)), decision C / g134 (squeeze off-path), #36 (the both-steps node + the crux2 step-B constructibility check), fm3's map (the node operation).
