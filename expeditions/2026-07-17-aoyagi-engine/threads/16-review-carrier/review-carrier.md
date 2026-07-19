# Review — t09 QNode carrier package (`QNodeCarrier.lean`)

**Reviewer seat:** rev-carrier (independent audit). **Branch:** `review/carrier`.
**Target:** `lean/DLNFibre/DLN/RLCT/Engine/QNodeCarrier.lean` at merge `9087c2998`
(file content = `95eea41788` on `origin/expedition/aoyagi-engine--t09-qnode`; 708 LoC).
**Verdict:** **PASS-with-notes.** Sound, axiom-clean, sorry-free, non-vacuous; two precision/scope
findings (one case-2 inner-fidelity gap, one docstring over-scope) + minor doc rot + an
integration-state note. None is a soundness or fidelity break of the stated equations.

---

## 0. Integration-state finding (surface to controller FIRST)

The claimed HEADLINE `cNodeOf_eq_realCNode_of_conOracle` is **not on the integration branch.**

- `origin/expedition/aoyagi-engine` tip = `3947d58ac` (tick 258). Its `QNodeCarrier.lean` is the
  `ee9c5934e` "weakest" version: it has `cNodeOf_eq_realCNode` (takes `Function.Injective (realCNode …)`
  directly) and `cNodeOf_eq_realCNode_of_facts` (takes `RealCNodeFacts`), but **NOT** the
  DivBirthInv-instantiated headline.
- The headline was added in `95eea41788` (17:56) on `origin/expedition/aoyagi-engine--t09-qnode`, then
  merged in local commit `9087c2998` (17:57, first parent = `3947d58ac`). `9087c2998` is **not an
  ancestor** of `origin/expedition/aoyagi-engine` and was not pushed — so as of this review the
  integration branch does not carry the seat's claimed capstone.

The review below is of the **target the prompt named** (`9087c2998` / `95eea41788`), i.e. the version
WITH the headline. It builds green and is axiom-clean. The controller should confirm the intended merge
lands on the expedition branch.

---

## A. Fidelity

### A(i) Does `htree` bind `node` to a reachable node? Is `dinv` at that node's state?

The headline

```lean
theorem cNodeOf_eq_realCNode_of_conOracle {M} (s : ConState L)
    (dinv : DivBirthInv M s) (node : StepData M) (edges : List (Edge M))
    (htree : buildTree M (conOracle M) s = ResolutionTree.branch node edges)
    (hd : dCenterOfNode M node ≤ flatDim M) :
    cNodeOf M node hd = realCNode M node hd
```

is a **per-state** lemma. `htree` binds `node` to the *root* node of the subtree built from `s`
(the proof substitutes `node = s.toStepData M rr rc` for the branch's rr/rc via
`ResolutionTree.branch.inj`); `dinv` is `DivBirthInv` **at that same state `s`** whose subtree-root
is `node`. This is honest and correctly scoped — see the scope note in A-scope below.

### A(ii) Non-vacuity — VERIFIED, both by lemma-chain and by a concrete instance

The `DivBirthInv` hypothesis is genuinely inhabited for reachable states:
- `DivBirthInv_conRoot` (DivBirthReach.lean:61) — establishes it at the root (`numDiv=0`, vacuous;
  `#print axioms` = **no axioms**).
- `DivBirthInv_conOracle_stepChildren` (DivBirthReach.lean:136) — maintains it through every
  `conOracle` step-child (axiom-clean).
- `leaves_chart_clauses` (DivBirthReach.lean:299) — the WF-induction that already threads exactly this
  invariant from `conRoot` to every leaf, so the maintenance chain provably composes.

Concrete instantiation (Codex, cross-checked against defs): for `L=2`, `M=(2,2,4)`, `conRoot` emits a
case-2 branch (`dCenterOfNode = 2·2 = 4 > 0`, `flatDim = 12`), and a `case2→case2→rollover` path
reaches a genuine case-1 state (layer 1, cleared 0, target 1, `dCenterOfNode = 1 + 1·4 = 5`). Both
case-1 and case-2 occur under maintained `DivBirthInv`. **Not vacuous.**

### A(iii) Does `realCNode` encode the intended blow-up center?

Geometry checked against `CenterIndices.lean` / `QNodeChart.lean`:
- `flatCoordOf M s i j = equivFin (FlatIdx M) ⟨⟨s,i⟩,j⟩` is the genuine flattening of the
  block-diagonal parameter space (`FlatIdx = Σ s, Fin (M s.castSucc) × Fin (M s.succ)`).
- case-1 center = `Fin.append (uCornerSel)(resBlockOrFallback)` = the merged divisor's immutable birth
  corner `(a,b,b)` ⧺ the `(target−cleared)×resCols` residual block at `(cleared,cleared)`, layer
  `node.layer`; dim `1 + (target−cleared)·resCols` = `dCenterOfNode` case-1. ✓
- case-2 center = the `resRows×resCols` residual block; dim = `dCenterOfNode` case-2. ✓
- The u-corner ⟂ d-block disjointness (`uCornerSel_ne_resBlockOrFallback`) is a **real geometric
  argument**: an assumed coincidence forces (via `flatCoordOf_val_inj`) layer `a=layer` and column
  `b=cleared+r`, then freshness (`a=layer → b<cleared`) contradicts `b ≥ cleared`. Sound; `hfresh f`
  is the correct freshness instance for the merged divisor (`f = chooseMin`, and `toStepData` copies
  its `divBirthCoord`, so `chooseMinData node = chooseMin s`).

### A — FINDING 1 (sharp): case-2 **inner**-fidelity is not certified by the headline

`cNodeOf` has an OUTER classical guard (`if Injective (realCNode) then realCNode else Fin.castLE`).
The headline certifies that guard resolves to `realCNode`. But `realCNode` itself has INNER totality
fallbacks (`resBlockOrFallback`/`uCornerSel` `dite` to `Fin.castLE` off-cone). Whether the equality
also pins those inner selectors onto their **geometric** branches splits by case:

- **case-1: inner-fidelity IS certified.** `centerSelCase_injective`'s `some` branch consumes
  `RealCNodeFacts` and inside `uCornerSel_ne_resBlockOrFallback` does `rw [resBlockOrFallback, dif_pos
  hblk, resBlockCenterIndices]` and `dif_pos hLf` — forcing BOTH inner selectors onto their real
  (geometric) branches. So on-cone, case-1 `realCNode` = u-corner ⧺ residual block, genuinely.
- **case-2: inner-fidelity is NOT certified.** `centerSelCase_injective`'s `none` branch is
  `resBlockOrFallback_injective` — **unconditional**, does not use `RealCNodeFacts`. So `realCNode`
  case-2 is injective (hence `cNodeOf = realCNode`) whether `resBlockOrFallback` chose the geometric
  `resBlockCenterIndices` OR its `Fin.castLE` fallback. The headline discharges case-2 via *vacuous*
  `RealCNodeFacts` (`nodeOccMin = none` ⟹ premise unsatisfiable), never touching the block-fit.

On the reachable cone the case-2 block **does** fit (a case-2 node has `resRows = widthMinUpto layer −
cleared ≤ M^(layer)`, `resCols = M^(layer+1) − cleared ≤ M^(layer+1)`), so the geometric branch is
taken in reality — but that implication is **absent from the theorem**. Consequence: the "names the
intended blow-up coordinates" reading (header lines 37–39) is fully certified only for **case-1**; for
case-2 the headline certifies `cNodeOf = realCNode` but not `realCNode = geometric residual block`.
This matters downstream (the fold-Jacobian blows up whatever coordinates the center names). It is
**Deferred**, owed by the fold/coverage layer as a case-2 analogue of `RealCNodeFacts` —
a lemma `resBlockOrFallback … = resBlockCenterIndices …` under the case-2 block-fit guard.
(Independently surfaced by Codex, §1c/§6.) Report-only — not a soundness break.

### A — scope: subtree-root, not all-internal-nodes

The docstring calls this "**`cNodeOf = realCNode` at every built-tree branch node**" and "the fidelity
capstone, one `conOracle` walk". The theorem as stated gives it at **one** node — the subtree root at
`s`. Lifting to every internal node of the `conRoot` tree needs a WF-induction lemma of shape
`∀ node ∈ ResolutionTree.nodes (buildTree M (conOracle M) conRoot), … cNodeOf = realCNode`, composing
the headline + `DivBirthInv_conOracle_stepChildren` + `DivBirthInv_conRoot`. That machinery exists
(`leaves_chart_clauses` is the leaf-clause analogue) but the internal-node lift is **not in this
package** — a separate coverage obligation. The docstring "every built-tree branch node" slightly
over-scopes the standalone theorem.

### A — name honesty (precision.md)

The theorem NAME `cNodeOf_eq_realCNode_of_conOracle` denotes the equation, which **is** proved — name is
accurate. The over-reach is in the DOCSTRING prose ("every built-tree branch node", "capstone",
header "names the intended blow-up coords") for the case-2 + all-nodes gaps above. Report-only.

---

## B. Soundness spot-check — PASS

- `lake build DLNFibre.DLN.RLCT.Engine.QNodeCarrier` from the review worktree: **green** (2722 jobs),
  only two style-linter warnings (`show`→`change` at :476; a long line) — cosmetic.
- `#print axioms` on all headlines = exactly `[propext, Classical.choice, Quot.sound]`:
  `dCenterOfNode_edgeSum`, `dCenterOfNode_le_flatDim`, `qNodeOf`, `qOfCenter_hasFDerivAt`,
  `qOfCenter_symm_hasFDerivAt`, `qOfCenter_coe_cle`, `realCNode_injective`, `flatCoordOf_val_inj`,
  `uCornerSel_ne_resBlockOrFallback`, `centerSelCase_injective`, `cNodeOf_eq_realCNode`,
  `realCNode_injective_of_dCenterOfNode_zero`, `cNodeOf_eq_realCNode_of_facts`,
  **`cNodeOf_eq_realCNode_of_conOracle`**. `DivBirthInv_conRoot` = no axioms.
- No `sorry`/`admit`/`native_decide`/`axiom` in QNodeCarrier / QNodeChart / DivBirthReach /
  CenterIndices.
- The two "contradiction" discharges in the headline (chooser-fail ⟹ terminal ⟹ leaf ≠ branch;
  terminal ⟹ leaf ≠ branch) are **genuine** structural contradictions, not vacuity-by-false-hyp; the
  case-2 vacuous-`RealCNodeFacts` discharge is legitimate (the premise `nodeOccMin = some target` is
  unsatisfiable when `nodeOccMin = none`) and does not by itself prove case-2 geometric fidelity
  (see Finding 1).
- `"DivBirthInv-ONLY"` (no OracleInv) claim: **legitimate** for this conditional theorem. Chooser
  success is forced by `htree` being a branch (a failed chooser routes `conOracle` to `oracleTerminal`
  ⟹ `buildTree` is a leaf). This proves "*if* a branch was emitted, its chooser succeeded" — it does
  NOT prove global chooser-totality (that stays an `OracleInv`/reachability property), but the theorem
  does not need it. (Codex §3 concurs.)
- `qNodeOf M : QNodeFam M (dCenterOfNode M)` type-checks and composes into `geoChartMap
  (dCenterOfNode M) (qNodeOf M)` — coverage's actual consumer (scratch elaboration, lean exit 0).

---

## C. Codex (decorrelated) — `codex/fidelity-headline-{prompt,answer}.md`

Fired xhigh, read-only. Codex converged **independently** on Finding 1 (case-2 inner-fallback not
certified — its §1c and §6 "sharpest residual doubt": demand a kernel-checked
`resBlockOrFallback = resBlockCenterIndices` case-2 reduction) and on the scope finding (§2: subtree
root only; docstring "every built-tree branch node" overstates). It found the disjointness sound (§4)
and the DivBirthInv-only proof legitimate (§3), matching my read. No new defect beyond mine.

---

## D. Minor doc rot (report-only; no signature impact)

1. Doc line 486 references `realCNode_injective_of_divBirthInv` — **no such theorem exists**; the real
   suppliers are `realCNode_injective_of_facts` and `realCNode_injective_of_dCenterOfNode_zero`.
2. Header line 39 and line 512 list `OracleInv` as part of the `RealCNodeFacts` supply
   ("`DivBirthInv`/`OracleInv`", "`OracleInv` chooser-totality"), but the headline (line 562) proves
   OracleInv is **not** needed. The generic-supply prose predates the headline and over-states the
   requirement.

---

## Verdict by function

- **A. Fidelity — PASS-with-notes.** Statements mean what the equations say; non-vacuous; geometry
  sound. Notes: (1) case-2 inner-block fidelity uncertified (Deferred to fold/coverage); (2) scope is
  subtree-root, docstring "every branch node" over-scopes; (3) doc rot in D.
- **B. Soundness — PASS.** Green build, axioms `[propext, Classical.choice, Quot.sound]` on every
  headline, no sorry, contradictions genuine, DivBirthInv-only legitimate.
- **C. Codex — PASS.** Decorrelated pass confirmed Finding 1 + scope; no additional defect.
- **D. Statement card — delivered** (`statement-card-t09-carrier.md`).
