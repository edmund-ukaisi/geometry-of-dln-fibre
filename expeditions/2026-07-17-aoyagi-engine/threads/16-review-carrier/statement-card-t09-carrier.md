# Statement card — t09 QNode carrier (`QNodeCarrier.lean`)

All theorems: `lean/DLNFibre/DLN/RLCT/Engine/QNodeCarrier.lean` @ `9087c2998`
(file content = `95eea41788`, branch `expedition/aoyagi-engine--t09-qnode`; 708 LoC).
Axioms on every headline below = `[propext, Classical.choice, Quot.sound]` (`#print axioms`, forced
elaboration; no `sorryAx`, no `native_decide`). Build: green (2722 jobs).
**Integration caveat:** the fidelity headline is NOT yet on `origin/expedition/aoyagi-engine`
(tip `3947d58ac`, which carries only the weaker `cNodeOf_eq_realCNode`/`…_of_facts`) — see the review
note §0.

---

## Card 1 — the per-NODE center dimension `dCenterOfNode` + its two obligations

> **Claim.** There is a per-node center dimension `dCenterOfNode M node` (terminal/rollover ⟹ 0;
> case-2 ⟹ `resRows·resCols`; case-1 ⟹ `1 + (target−cleared)·resCols`, `target = occ.min?`) that
> (a) Σ-partitions the per-edge dims over every built-tree branch node, and (b) is `≤ flatDim M` on
> every built-tree branch node.
>
> - **Lean:** `dCenterOfNode` (def), `dCenterOfNode_edgeSum`, `dCenterOfNode_le_flatDim`.
> - **Gloss.** `dCenterOfNode_edgeSum`: for `buildTree M (conOracle M) s = branch node edges`,
>   `(edges.map (dCenterOfEdge node)).sum = dCenterOfNode M node`. `dCenterOfNode_le_flatDim`: same
>   hypothesis ⟹ `dCenterOfNode M node ≤ flatDim M`. The case is *recomputed* at the `StepData`
>   level via the same `conOracle`/`classify` dispatch (`nodeOccMin`), so no new carrier field
>   (option (iv), zero StepData ripple).
> - **Proved.** Both identities, over every branch node of the `conOracle` build. The bound is pure
>   arithmetic (`block_le_flatDim`: the residual block fits inside the layer term
>   `M^(s)·M^(s+1) ≤ flatDim`; case-1 `1 + runLen·rc ≤ rr·rc` via `gcongr`+`omega`). No `DivBirthInv`.
> - **Assumed.** `htree : buildTree M (conOracle M) s = branch node edges` (the node is a built-tree
>   branch node). No reachability invariant.
> - **Cited.** none.
> - **Deferred.** none for these two obligations.
> - **Status.** sorry-free + reviewed (rev-carrier).

---

## Card 2 — `qNodeOf : QNodeFam M dCenterOfNode` (the coverage-consumed family)

> **Claim.** `qNodeOf M` is a total, always-well-formed per-node coordinate-split `Homeomorph`
> family of the shape coverage's `geoChartMap`/`geometricLeafPaths` consume.
>
> - **Lean:** `qNodeOf` (`= qOfCenter M (cNodeOf …) (cNodeOf_injective …)`); supported by
>   `cNodeOf`, `cNodeOf_injective`.
> - **Gloss.** `qNodeOf M node hd : Params M ≃ₜ (Fin (dCenterOfNode M node) → ℝ) × (Fin (flatDim M −
>   dCenterOfNode M node) → ℝ)`. `qNodeOf M : QNodeFam M (dCenterOfNode M)` (verified: elaborates and
>   composes into `geoChartMap (dCenterOfNode M) (qNodeOf M)`).
> - **Proved.** Totality + injectivity for **every** node: `cNodeOf` = `realCNode` when injective,
>   else the canonical `Fin.castLE` (always injective), so `qOfCenter` always yields a Homeomorph.
> - **Assumed.** `hd : dCenterOfNode M node ≤ flatDim M` (the reachable-cone bound; supplied by
>   `dCenterOfNode_le_flatDim` at built-tree nodes).
> - **Cited.** none (Mathlib `Equiv.ofInjective`/`sumCompl`, homeomorph combinators).
> - **Deferred.** The GEOMETRIC content — that these coordinates are the *intended* blow-up center —
>   is Card 3, and only partially certified there (case-2 gap).
> - **Status.** sorry-free + reviewed.

---

## Card 3 — on-cone fidelity: `cNodeOf = realCNode` (`…_of_conOracle`, the headline)

> **Claim.** On the reachable cone (`DivBirthInv M s`), at the subtree-root node of `s`, the
> totality-guarded `cNodeOf` equals the intended selector `realCNode` — DivBirthInv-only (no
> OracleInv), the case-1 chooser supplied by the branch structure itself.
>
> - **Lean:** `cNodeOf_eq_realCNode_of_conOracle` (headline); chain: `flatCoordOf_val_inj`,
>   `uCornerSel_ne_resBlockOrFallback`, `centerSelCase_injective`, `realCNode_injective`,
>   `realCNode_injective_of_facts`, `realCNode_injective_of_dCenterOfNode_zero`,
>   `cNodeOf_eq_realCNode`, `cNodeOf_eq_realCNode_of_facts`, `chooseMinData_toStepData`;
>   predicate `RealCNodeFacts`.
> - **Gloss.** `DivBirthInv M s → buildTree M (conOracle M) s = branch node edges → hd →
>   cNodeOf M node hd = realCNode M node hd`. `realCNode` case-1 = merged divisor's birth corner
>   `(a,b,b)` ⧺ the residual `d`-block; case-2 = the residual block; terminal/rollover = empty.
> - **Proved.** The equation `cNodeOf = realCNode` at the subtree-root node, from `DivBirthInv` alone.
>   Non-vacuous: `DivBirthInv` established at `conRoot` (`DivBirthInv_conRoot`, no axioms) and
>   maintained (`DivBirthInv_conOracle_stepChildren`); a `(2,2,4)` instance exercises both case-1 and
>   case-2. The u-corner ⟂ d-block disjointness is a genuine geometric argument (freshness vs block
>   row). For **case-1**, the proof additionally forces `realCNode`'s inner selectors onto their
>   geometric branches (via `RealCNodeFacts`' corner-validity + block-fit).
> - **Assumed.** `DivBirthInv M s` (the birth-corner reachability invariant: validity + layer-bound +
>   freshness + `divBirthCoord` injective) at the state `s`; `htree`; `hd`.
> - **Cited.** none.
> - **Deferred.**
>   1. **Case-2 inner-block fidelity.** The headline certifies `cNodeOf = realCNode`, but for **case-2**
>      it does NOT certify that `realCNode`'s inner `resBlockOrFallback` takes its geometric branch
>      (`resBlockCenterIndices`) rather than the `Fin.castLE` totality fallback — case-2 injectivity is
>      unconditional and discharges `RealCNodeFacts` vacuously. True on-cone (the case-2 block fits) but
>      owed as a separate lemma `resBlockOrFallback … = resBlockCenterIndices …` under the block-fit
>      guard, by the fold/coverage layer.
>   2. **All-internal-nodes lift.** The headline is per-subtree-root; a WF-induction lemma
>      (`∀ node ∈ ResolutionTree.nodes …, cNodeOf = realCNode`, composing this + the DivBirthInv
>      maintenance chain) is a separate coverage obligation, not in this package.
> - **Structure & ideas observed.** N/A (formaliser package, not a p&p handoff). Note the clean
>   "DivBirthInv-only" mechanism: a failed chooser routes `conOracle` to `oracleTerminal`, so a
>   *branch* output forces chooser success — the branch structure supplies what would otherwise be an
>   OracleInv chooser-totality hypothesis.
> - **Status.** sorry-free + reviewed (PASS-with-notes: Deferred items 1–2 are precision/scope, not
>   soundness; report-only per review.md).

---

## Card 4 — the q-det lemma: `qOfCenter` is a fixed continuous linear equiv

> **Claim.** `qOfCenter` is linear — Fréchet-differentiable with derivative a fixed CLE (fwd + symm),
> the input the downstream fold-Jacobian conjugation step needs.
>
> - **Lean:** `qOfCenterCLE` (def), `qOfCenter_coe_cle`, `qOfCenter_hasFDerivAt`,
>   `qOfCenter_symm_hasFDerivAt`.
> - **Gloss.** `qOfCenterCLE M c hinj : Params M ≃L[ℝ] (Fin d → ℝ) × (Fin (flatDim M − d) → ℝ)` (same
>   underlying map as `qOfCenter`, `qOfCenter_coe_cle` = `rfl`); `HasFDerivAt (qOfCenter …) (qOfCenterCLE
>   … : →L) x` and the symm form.
> - **Proved.** Unconditional linearity of `qOfCenter`/`qOfCenter.symm` (built from `paramsEquivFlatCLE`
>   + `piCongrLeft (centerPerm)` + `sumArrowLequivProdArrow`, all linear).
> - **Assumed.** `hinj : Function.Injective c` (the center selector is injective).
> - **Cited.** none (Mathlib CLE / `HasFDerivAt` API).
> - **Deferred.** The `|det|`-preservation of the conjugation and the fold-Jacobian telescoping (the
>   downstream "wall") consume these but are NOT in this package.
> - **Status.** sorry-free + reviewed.
