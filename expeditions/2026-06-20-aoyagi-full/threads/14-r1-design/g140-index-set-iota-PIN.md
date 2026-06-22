# Route M index set ι — PINNED (uniform pivotBlowupOn frame, unblocks fm3) (pp-hall, 2026-06-22, #140)

**Unblocks fm3's #27.** fm3's Case222→general map (`threads/fm3-coord-bridge/case222-tree-generalization-map.md`)
pinned the NODE OPERATION (uniform `pivotBlowupOn`; the `(pivot)²` loss factor IS the exceptional divisor
feeding `monomialThreshold`, NOT an additive `nReg/2`; det-1 Lemma-2 MP straightens interleaved; branch =
pivot choice). This addendum to #138 pins what I own: the **index set ι** + its reconciliation with the
squeeze, in fm3's uniform-pivotBlowupOn frame. fm3 is correctly blocked until ι is pinned; it is below.

## Reconciliation: the squeeze (#129/#131) and fm3's monomial route are the SAME node, two levels
My #138 framed C1 as `(regular squares) + ‖S·A2red‖²` — that is the **squeeze-level** (analytic) view, and
fm3 is right that at the **construction level** it must NOT become an additive `nReg/2` (the squeeze trap we
closed). They are not competing; they are one node seen at two levels. The node operation, reconciled:
1. **unit-pivot chart** — normalize a nonzero pivot minor to a hard unit (post-blow-up `1`, #127).
2. **det-1 Schur straighten (Lemma-2)** — unit-pivot row/col ops, **Jacobian 1 (MP)**, straightens the
   bilinear rank-defect center `{r−pq=0}` to a COORDINATE subspace `{w=0}` (`w := r−pq`). **Contributes NO
   monomial weight.** *This is exactly where my squeeze `flatCore − Φ ∈ ideal(E)` (#131) lives* — it is the
   ANALYTIC identity certifying that this MP straighten is rlct-preserving, NOT a source of weight.
3. **`pivotBlowupOn active p`** of the now-coordinate center `{y₁=…=y_c=0}`, `c = Mval(t)` — chart
   `y_i = u, y_j = u·v_j`, Jacobian `|u|^{c−1}`, loss `F∘π = u²·F_res` (homogeneity/multilinearity). **`(k,h) =
   (1, c−1)`, ratio `c/2` — THE MONOMIAL WEIGHT IS HERE.**
4. recurse on `F_res` until a unit (`≥ 1`, all singular directions blown up).
So: the squeeze is step (2)'s content (MP straighten, weight-free); the `monomialThreshold` weight is step
(3)'s `(pivot)²` exceptional factor. The "regular squares" of the squeeze are NOT an additive `nReg/2` — each
is absorbed into the recursion (a unit-`≥1` leaf factor or a deeper `pivot²`). **fm3's correction adopted:
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
  node's `pivotBlowupOn` (Jacobian `u^{card−1}` ⟹ `h = card−1`; loss `u²` ⟹ `k = 1`). The det-1 Lemma-2
  straightens between nodes (Jacobian 1, no `(k,h)` contribution).
- **C3 (NC-completion) is NOT a tree node** — it is a deterministic POST-PASS on each path's assembled
  divisor arrangement (normal-crossing completion via intersection blow-ups, introducing `k_E ≥ 2`
  intersection divisors whose discrepancy keeps the ratio `codim/2`). It refines a leaf's `(d,k,h)` but does
  NOT branch `ι` — keeping `ι` finite and the branching `{C1,C2,C4,C5}` clean.

## The controller's guess — ι = the squeeze failure mode — CONFIRMED
The squeeze `c₁Φ ≤ F ≤ c₂Φ` holds at EVERY node (the analytic identity). What fails to be CLEAN (the literal
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
   `PivotChoice`. Jacobian `(x p)^{card−1}`, loss `(pivot)²`. Lemma-2 det-1 MP straighten between nodes.
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
+ the #134 `(S-min)` + the #129/#131 squeeze (now correctly placed as step-(2)'s weight-free analytic
content, NOT a competing route). The squeeze-vs-monomial reconciliation is the key clarification fm3's
constraint forced. Scripts: `g140_index_set.py`, `g140_iota_inductive.py`, `g140_scope_check.py` in
`g129-scripts/`. A Codex pass on the ι inductive shape is optional (the reconciliation is mechanical given
fm3's frame + #138); the #138 design Codex already stress-tested the taxonomy. Builds on #138 (the
taxonomy), #134 ((S-min)), #131 (squeeze = step-2 content), fm3's map (the node operation).
