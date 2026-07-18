# T2 `buildTree` + chart-producer INTERFACE DESIGN (architect-t02, 2026-07-18)

*Paper/typed-skeleton design pass (NO proof grind). Gates T3: the chart-producer signature below IS
coverage's output contract. Elder to convene on this (coverage-commissioning gate). Builds on the
landed T2a recursion pin (`conStepDepth = WellFounded.fix (conRel_wf M)`, EngineConstruction.lean).*

## 0. The uniform blow-up event (design from this; derive the branches)

Aoyagi's recursion is ONE event, parameterised by the state `s : ConState L` (`layer = S`,
`cleared = J`, `divProfile`/`divExp`/`genDivExp`). At `s` the construction does exactly one of:

- **BLOW-UP at the current level** (`S`, `J`) on the Def-4-minimal eligible divisor `u_{s,k}` (the
  chooser, `IsEligibleMinimalChoice s k runLen`): this emits a NODE whose out-edges are the *charts*
  of that single blow-up — case-1(1) (merge, `stepCase11`) and/or case-1(2) (split,
  `stepAppendAdvance` with the inherited head) — each child `conRel`-smaller.
- **FULL-BLOCK blow-up** (`case-2`, `stepAppendAdvance` with the width-reset head), when no divisor
  is eligible at the level but the residual block is non-trivial: one new pivot per step, `J += 1`.
- **ROLLOVER** (`stepRollover`, `S += 1`, `J := 0`) when the layer is exhausted.
- **TERMINATE** (a LEAF) when fully monomialised: no pending divisor and no residual to blow up.

The "cases" are not four unrelated branches — they are the terminal/step dichotomy of one event, the
step sub-typed by which reduction the level admits. `buildTree` dispatches on that; each non-terminal
child is `conRel`-smaller (the descent lemmas already prove this per case), so `WellFounded.fix
(conRel_wf M)` terminates.

## 1. (a) The per-state DECISION type

The recursion is `WellFounded.fix`-driven; the decision at `s` must carry (i) what node to emit,
(ii) the `conRel`-smaller children to recurse on WITH their descent proofs, (iii) the data to
discharge the structural conjuncts. Proposed:

```
structure StepEmit (M : Fin (L+1) → ℕ) (s : ConState L) where
  node      : StepData M                              -- materialises s's derivable fields (resRows/…)
  hnode     : nodeMatches s node                      -- node.layer = s.layer, .cleared = s.cleared,
                                                       --   .numDiv/.divExp/.divProfile = s's (rfl-class)
  edges     : List (Σ (e : Edge M) (s' : ConState L),
                      conRel M s' s ∧                  -- (ii) descent — from conRel_step* + constraint 1
                      ResolutionTree.rootLedger e.child = stepUpdate node e.case e.subst ∧
                      (e.case = case11 ∨ e.case = case12 →                    -- (iii) StepRel eligibility
                        ∃ h, node.divTilde ⟨e.subst.mergeIdx,h⟩ = node.cleared + e.subst.runLen))
  hlive     : 0 < edges.length ∨ True                 -- (kept loose; PLACEHOLDER — see pivot note)

inductive ConDecision (M) (s : ConState L)
  | terminal (leaf : ChartLeaf M s)                    -- T3 hole (§2): a LeafData + its ChartBridge tuple
  | step     (emit : StepEmit M s)
```

**PIVOT-COMPLETENESS (rev-cov verdict: (a)-generalized CONFIRMED — cert-cov-rungs12, page-verified
×2 + Codex).** The 1(1)/1(2) tags are pivot TYPES of the ONE blow-up, NOT the emission count. The
full per-node chart family has `d_center` edges: for **Case 1**, `d_center = J₁·(M⁽ˢ⁺¹⁾−J) + 1` (the
`u`-pivot + EVERY block-`d` pivot; Aoyagi shows only the corner as representative); for **Case 2**,
the full residual block count. Kill of (b): an omitted pivot direction is UNRECOVERABLE by deeper
branching. AMENDMENT owed in the buildTree body: **replace the loose `hlive` with `pivotComplete`**
— the `edges` list ENUMERATES the center's `d_center` pivots (T3's fold + `buildTree` both consume
it). The `List` arity already accommodates this (the un-baked shape paying off). STEPREL UNAFFECTED
(reviewer-confirmed): every `d`-pivot edge satisfies the SAME 1(2) ledger relation, so the
ledger/descent work stands verbatim — only the emission ARITY changes.

Notes.
- `edges`'s child field is `e.child` = `ResolutionTree.leaf (child-built)` / a branch, produced by the
  recursive call `rec s' (descent-proof)`; so `StepEmit` is really the *pre-recursion* shape and
  `buildTree` closes the loop (the `Σ … conRel M s' s` is exactly what `rec` consumes).
- **Constraint 1 (`layer < L`) lives HERE**: a `step` emit at a case-1(1) edge must supply
  `s.layer < L` (from "we are in a live layer" — `S ∈ 1..L`, i.e. Lean `layer ∈ 0..L−1`). It is NOT
  from `StateInvariant` (which gives `≤ L`). Add it as a field of the case-1(1) edge record (or derive
  from a `hMid : s.layer < L` carried in `StepEmit` for any non-rollover step). This feeds
  `conRel_stepCase11` / `pendingCount_stepCase11_lt`.
- **StepRel discharge shape**: rfl-class. The child's `rootLedger` IS `stepUpdate node e.case e.subst`
  by construction (the child state's ledger fields are the `stepUpdate` output — as `leaf224`/`mergeLeaf`
  already witness), so the equality conjunct is `rfl`; the eligibility conjunct is `IsEligibleMinimalChoice`
  unpacked (in-range + `t̃ = J + runLen`; `runLen ≥ 1` landed).
- **Constraint 3 (case-1(2) parent persistence)**: the split edge's `node` (parent) must be UNCHANGED
  by the split (the parent divisor's `divExp`/`divProfile` persist; the child appends a new pivot). The
  worked example (§4) exercises a real case-1(2) node so this is a positive trace witness, not inferred.

## 2. (b) The chart-producer signature — THE T3 CONTRACT (load-bearing)

For each emitted TERMINAL state `s`, T3 (coverage) must supply a `ChartLeaf M s`:

```
structure ChartLeaf (M : Fin (L+1) → ℕ) (s : ConState L) where
  leaf        : LeafData M
  hledger     : ResolutionTree.rootLedger (ResolutionTree.leaf leaf)
                  = (⟨s.numDiv, s.divExp, s.divProfile, s.cleared⟩ : ResolutionTree.RootLedger L)
                -- ONE RootLedger equality (elder JDI): dodges the dependent-numDiv friction of four
                --   field equations; matches stepUpdate's rfl-class shape.
  -- the ChartBridge per-leaf TUPLE (verbatim the clause region_glue/glue-lane consume):
  hmeas       : MeasurableSet leaf.srcBox
  hbounded    : ∃ R > 0, leaf.srcBox ⊆ paramsEquivFlat M ⁻¹' cubeBox (flatDim M) R
  hdivInj     : Function.Injective leaf.divCoord
  hresInj     : Function.Injective leaf.resCoord
  hdisj       : Disjoint (range leaf.divCoord) (range leaf.resCoord)
  haeInj      : ∃ N, volume N = 0 ∧ Set.InjOn leaf.chartMap (leaf.srcBox \ N)
  hpull       : LeafPullback leaf
  hjac        : LeafJacobian leaf
  hnonempty   : leaf.srcBox.Nonempty                           -- feeds live-attainment (§3)
```

Plus, at the TREE level (not per-leaf), T3 supplies the **image-cover** clause of `ChartBridge`:
`∃ U open, {zero-locus} ⊆ U ⊆ ⋃ leaf, chartMap '' srcBox`, and the leaf-path coherence
`∀ p ∈ leafPaths id t, p.1.chartMap = p.2`. **This is the load-bearing line the probe pinned**: the
cover must instantiate the FULL residual-`d` pivot-chart cover (NOT a fixed-corner chart — the probe's
explicit gap; `cert-atlas-probe` Verdict 1(b)), and it is provably NON-TORIC (a Newton/toric argument
cannot prove it — coverage must run the blow-up construction). `ChartLeaf.leaf.chartMap` must be the
DERIVED root→leaf edge-substitution fold (coherence), so the cover and the per-leaf charts agree.

So T3's contract = `(∀ terminal s emitted, ChartLeaf M s) + the tree-level image-cover + coherence`.
`buildTree` consumes it as a TYPED HOLE (a hypothesis `chartProducer`), leaving ChartBridge unproven
here; when T3 lands, `coverage_theorem` is discharged and `resolutionOf_spec` closes.

## 3. (c) CanonicalResolution conjunct distribution (build vs T3)

`CanonicalResolution t = IsFullMonomialization t ∧ StepRel-all t ∧ base ∧ ChartBridge M t ∧
  (minAdm ≤ terminalExponents ∧ minAdm ∈ terminalExponents) ∧ liveAttainment`.

| conjunct | discharged at | how |
|---|---|---|
| StepRel-all | **BUILD** (GO NOW) | rfl-class per edge via `stepUpdate` + `IsEligibleMinimalChoice` (§1) |
| base (`S=J=0` root) | **BUILD** (GO NOW) | the root `ConState` is the base; `buildTree` starts there |
| liveAttainment — srcBox side | **BUILD** (GO NOW) | `srcBox.Nonempty` is `ChartLeaf.hnonempty` (T3); the leaf-membership is build |
| IsFullMonomialization | **BUILD, GATED** | `divExp = Mval divProfile` = coherence (T-rule maintains it; the (2,2,4)/(3,3,4) traces witness). `divProfile ∈ Adm` is a LEAF property (see below), NOT per-node — GATED on pnp (2,2,3,2) |
| exponent-hooks (`minAdm ≤ e`, `minAdm ∈`) | **BUILD, GATED** | no-undershoot = `Mval T ≥ minAdm` on `Adm` (`Finset.inf'_le`, cert-d3 Check-1) — routes through leaf-Adm, so GATED with IsFullMonomialization |
| ChartBridge | **T3** | the chart-producer contract (§2) |

So the **structural core** — StepRel-all, base, liveAttainment-srcBox — discharges at BUILD NOW (none
touch admissibility). `buildTree` produces `Σ t, (StepRel-all t ∧ base ∧ …)` via `WellFounded.fix`
(Option B — tree + structural certificate carried together, since StepRel-per-edge / terminal-exponent
membership reference the tree's own structure). The IsFullMonomialization + exponent-hook discharge is
GATED (below), and ChartBridge + srcBox-nonempty are the T3 holes.

**ADMISSIBILITY — CORRECTED (elder-gate4 §3a; the predicted THIRD GAP).** `divProfile ∈ Adm` is
**FALSE as a per-node invariant**: a PENDING divisor has `t̃ = min T > 0`, hence its last component
`> 0`, hence `∉ Adm` (clause 3, last-component-zero; `Lambda.lean:54`). WITNESS against the LANDED
carrier: `node334.divProfile = ![1,1] ∉ Adm(3,3,4)` (`CoRank2Spike:83`). The corrected decomposition:
- **per-node invariant = WEAK-DECREASE + BLOCK-BOUND ONLY** (`t⁽¹⁾ ≥ … ≥ t⁽ᴸ⁾`, each `≤ admBound`).
  This IS preserved by the T-rule; rename the brick `stepUpdate_preserves_weakInv` (per case). TRUE and
  needed either way — **build it now, meanwhile.**
- **last-component-zero is a LEAF property**, from post-final-rollover `J = 0` ⟹ no pending divisor ⟹
  every terminal `t̃ = 0` ⟹ last component `= 0`.
- **leaf-Adm = weakInv + leaf-`t̃=0`** — a SEPARATE lemma consuming TERMINATION (that a leaf is reached
  with `J=0` and no pending). This is what feeds no-undershoot; **hbox-critical, not fidelity.**
- **GATE (elder-gate4 §3b): a pen-and-paper truth-value owed BEFORE the build discharges
  IsFullMonomialization / exponent-hooks** — at NON-MONOTONE widths `L≥3`, does the case-2 raw-width
  head-reset (p.20-faithful) reach a leaf with a non-weakly-decreasing profile? And does every emitted
  leaf carry ONLY `t̃=0` divisors (IsFullMonomialization's `∀k` vs the paper's `t̃=0`-only read-off,
  p.22)? KILL-CONDITION: a leaf divisor `∉ Adm` at `M=(2,2,3,2)`. (pnp re-engaged; task tracks it.)

**NEW NAMED OBLIGATION (elder-gate4 §3c): the total-comparability CHAIN CARRIER.** The
invariant→principalization link is T3's (its discharge of the image-cover + per-leaf
LeafPullback/LeafJacobian CONSUMES the total-comparability invariant, `cert-2222 (c)`), but the
build side must MAINTAIN it — a chain invariant (`∀ k k', T_k ≤ T_{k'} ∨ T_{k'} ≤ T_k`, total
comparability of the carried profiles), NOT merely the chooser's LOCAL minimality. Put its TYPE in
with the `buildTree` invariants (`StateInvariant` extension); its preservation proof is a build brick;
T3's cover proof goes THROUGH it, never asserts the cover.

## 4. (d) Worked example — a real case-1(2) node (constraint 3)

At `M = (3,3,4)`, layer `S=1` (Lean `layer=1`), `J=0`, one pending divisor with `divProfile = ![1,1]`,
`divExp = 4 = Mval(1,1)`, run `J₁ = 1` to the next occupied level:

- The blow-up on that divisor emits a NODE with the full pivot family — `d_center = J₁·(M⁽ˢ⁺¹⁾−J) +
  1 = 1·4 + 1 = 5` edges (rev-cov (a)-generalized). The 1(1)/1(2) below are two representative pivot
  TYPES of that family (Aoyagi shows only the corner); all `d_center` edges satisfy the same ledger
  relations, so the analysis of the two types below transfers to the whole family:
  - **case-1(1)** (`stepCase11`): merge → child `divProfile = ![1,0]`, `divExp = 8 = Mval(1,0) = minAdm(3,3,4)`.
    Descent: `conRel_stepCase11` (needs `layer=1 < L=2` ✓ from §1, `runLen=1 ≥ 1` ✓); `pendingCount` drops.
  - **case-1(2)** (`stepAppendAdvance`, inherited head): child APPENDS a new pivot `divProfile = ![1,0]`
    (head `t⁽¹⁾=1` inherited from the parent, tail `:= J`), `divExp = 8`; PARENT persists (its `![1,1]:4`
    unchanged — **constraint-3 witness**); `J += 1`. Descent: `conRel_stepAppendAdvance` (needs `J=0 <
    layerCap` ✓); μ₂ drops.
- Both children are `conRel`-smaller; the parent `node`'s ledger is untouched across the split
  (positive persistence witness). `divExp = Mval(divProfile)` holds at both (coherence, `decide` —
  already witnessed in `CoRank2Spike.node334_*`). This node is the `mixedCaseTree`-shape made faithful.

## 5. Firmest / most-likely-to-break / next

- **Firmest**: the recursion terminates (μ-descent landed, all 4 cases); StepRel/base discharge rfl-class;
  the decision type is a clean sum (terminal / step-with-edges).
- **Most likely to break**: (i) the WEAKENED-INVARIANT preservation (§3) — the case-2 raw-width
  head-reset (`M p.succ`) at NON-MONOTONE widths (`L≥3`) is the exact place weak-decrease could fail;
  this is the pnp (2,2,3,2) gate, KILL = a leaf `∉ Adm`; (ii) the image-cover NON-TORICITY (§2), T3's
  hard part (contract must not admit a corner-only cover).
- **Next (elder-gate4 ratified — execution split)**: (1) **NOW** — implement `buildTree`'s STRUCTURAL
  core (decision type w/ the hledger one-equality fix + layer<L threading; WF.fix producing
  `Σ t, StepRel-all ∧ base ∧ liveAttainment-srcBox`; the case-1(2) witness) + `stepUpdate_preserves_weakInv`
  (true either way) + the total-comparability chain-invariant TYPE; (2) **GATED on pnp (2,2,3,2)** —
  the IsFullMonomialization + exponent-hook discharge (leaf-Adm = weakInv + leaf-`t̃=0`); (3) wire the
  chart-producer hole. T3 coverage commissioned in parallel against §2 (own lane; first rung = the
  per-blow-up local covering lemma at corank≥2).
