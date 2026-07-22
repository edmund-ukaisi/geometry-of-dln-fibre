<task>
Independent soundness check of a Lean 4 theorem STATEMENT (not its proof). I claim the
guard is too weak and the conclusion is false on an admitted edge. Confirm or refute from
the definitions below ONLY. Do not assume any facts not stated here.

## The theorem (guard + conclusion)
```
theorem lastLayer_clear_preserves
    {N : ℕ} (d : Fin (N + 1) → ℕ) (hN : 0 < N) (hpos : ∀ k, 0 < d k)
    (e : ...)
    (p : TreePath d) (ed : TreeEdge d p)
    (hlast : ed.nextState.layer + 1 = N)
    (hinv : LastLayerInv d e (supportAt d p.conState.layer p.conState.cleared) p)
    (hbranch : (p.extend ed).IsRealBranch e) :
    LastLayerInv d e (supportAt d (p.extend ed).conState.layer (p.extend ed).conState.cleared) (p.extend ed)
      ∧ GeneratorCleared d e (p.extend ed)
```
`(p.extend ed).conState = ed.nextState`. States are `ConState N` (so engine `L = N`).

## Relevant definitions (verbatim)
State transitions on `ConState` (fields include `layer`, `cleared`):
- case-2 / case-1(2) — `stepAppendAdvance`: child = ⟨s.layer, s.cleared + 1, …⟩   (layer KEPT, cleared+1)
- case-1(1) (merge) — `stepUpdate case11`: child = ⟨s.layer, s.cleared, …⟩         (layer KEPT, cleared KEPT)
- rollover — `stepRollover`: child = ⟨s.layer + 1, 0, …⟩                            (layer+1, cleared→0)

Oracle (emits the children `IsRealBranch` matches against):
```
conOracle d s :=
  if N ≤ s.layer then terminal
  else if widthMinUpto d (s.layer + 1) ≤ s.cleared then rolloverDecision …   -- a rollover child
  else <case1/case2 decisions>                                                -- clears
```
`widthMinUpto d n ≥ 1` always (widthMinUpto_pos, given hpos).
`edgeδ d p := decide (p.conState.cleared = 0)`.
`IsRealBranch` at a step requires `∃ sc ∈ (conOracle d p.conState).stepChildren, sc.ecase = ed.case ∧ sc.child = ed.nextState ∧ <center/pivot/shear pins>`; the rollover child satisfies the pins (canonCenterOf = ∅, pivot pin vacuous).

`supportAt d S J := if J = 0 then blockCoords d S else if S + 1 < N then blockCoords d (S+1) else ∅`.

`foldResid d e (p.extend ed) j u`, at a NON-terminal step (¬ N ≤ ed.nextState.layer):
- if edgeδ d p (=parent.cleared=0): a "strict transform" of `foldResid d e p (cast j)`;
- else (δ=0): the PURE PULLBACK `foldResid d e p (cast j) (σ u)`, where σ is the step map with σ 0 = 0.

`LastLayerInv d e C p := (∃q, StepInv …) ∧ ∀ j, (Deg1SupportedSlot … j C …) ∨ (∃ unit, ContinuousOn unit region ∧ unit 0 ≠ 0 ∧ ∀ u ∈ region, foldResid d e p j u = unit u)`.
`Deg1SupportedSlot` on support `C` includes `∃ c, ∀ u ∈ region, foldResid d e p j u = ∑_{i ∈ C} c i u * u i` (so if slot j takes the LEFT disjunct, foldResid p j 0 = 0).
`foldStepInvAt_to_lastLayerInv`: an interior node's FoldStepInvAt gives LastLayerInv with EVERY slot in the LEFT disjunct.

`GeneratorCleared d e p := ∃ i₀ q, StepInv … q … ∧ ∑ j, q i₀ j 0 * foldResid d e p j 0 ≠ 0`.

## My argument (verify each step)
1. For N ≥ 2, the FIRST edge reaching layer N−1 must be a rollover (clears keep the layer, only rollover raises it), from a parent p with p.conState.layer = N−2.
2. That rollover edge has ed.nextState.layer = N−1, so hlast : (N−1)+1 = N HOLDS — it is admitted, not excluded.
3. hbranch is satisfiable (rollover is a real oracle child with the canonical pins).
4. Rollover requires widthMinUpto d (layer+1) ≤ cleared, and widthMinUpto ≥ 1, so parent.cleared ≥ 1 ⟹ edgeδ = false (δ=0).
5. Take hinv all-left (foldStepInvAt_to_lastLayerInv on the real interior parent at N−2) ⟹ foldResid p j 0 = 0 for all j.
6. δ=0 ⟹ foldResid(child) j 0 = foldResid p (cast j) (σ 0) = foldResid p (cast j) 0 = 0 for all j.
7. ⟹ ∑ j q i₀ j 0 * foldResid(child) j 0 = 0 for every i₀,q ⟹ GeneratorCleared(child) is FALSE.
8. ⟹ the theorem's conclusion is false on an edge satisfying all hypotheses ⟹ the statement is unsound (unprovable).

Proposed fix: add `hparent : p.conState.layer + 1 = N`; with hlast it forces layer-preserving (parent=child=N−1), i.e. a clear, excluding both rollover-into-N−1 and rollover-out.
</task>

<output_contract>
Three sections, terse.
1. VERDICT: one of {AGREE unsound, DISAGREE sound, CANNOT-DETERMINE} + one sentence.
2. STEP CHECK: for each of my 8 steps, OK / WRONG (+ why if wrong). Flag any step that relies on a fact not in the definitions above.
3. FIX: does `hparent : p.conState.layer + 1 = N` make it sound? Is there a strictly weaker/cleaner guard that also works? Any edge my fix wrongly excludes or wrongly still admits?
</output_contract>

<grounding_rules>
Reason ONLY from the definitions I gave. If a step needs a fact I did not state (e.g. reachability of a state at layer N−2 with cleared ≥ 1, or that case11 can/can't be the first clear), say so explicitly and mark it an assumption rather than asserting it. Distinguish "follows from the given defs" from "plausible but unverified here".
</grounding_rules>
