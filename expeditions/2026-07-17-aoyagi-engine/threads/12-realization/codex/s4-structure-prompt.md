<task>
Lean 4 + Mathlib v4.29. DESIGN REVIEW (not code) for the hardest proof in this engine: the o5 §4
realization. cwd = repo root /home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/aoyagi-engine/t01-r2.

TARGET (in lean/DLNFibre/DLN/RLCT/Engine/O5Realization.lean, currently `sorry`):
  theorem tStar_realized (M : Fin (L+1) → ℕ) (hL : 0 < L) :
    ∃ l ∈ ResolutionTree.leaves (buildTree M (conOracle M) (conRoot : ConState L)),
      ∃ k : Fin l.numDiv, l.divProfile k = tStar M
i.e. the Mval-minimizer tStar M (proven Clearable by clearable_tStar) appears as a t̃=0 analytic
divisor profile at SOME leaf of the built tree.

KEY STRUCTURES (read the files):
- buildTree M oracle s = WellFounded.fix (conRel_wf M) fun s rec => match oracle s with
    | .terminal l _ => .leaf l | .step node children _ _ _ => .branch node (children.map (fun c => Edge.mk c.ecase c.esubst (rec c.child c.hdesc)))  (EngineConstruction.lean).
- conOracle M s dispatches: terminal (L ≤ layer); rollover (widthMinUpto M (layer+1) ≤ cleared);
  else Case-1 (occ.min? = some target, chooseMin s target = some f → case1Decision emitting TWO
  StepChildren: case11 [stepCase11 s f] and case12 [stepAppendAdvance …]) or Case-2 (occ.min? = none →
  case2Decision, one child stepAppendAdvance).  StepChild has .child : ConState L, .hdesc : conRel M child s.
- buildTree_step / buildTree_terminal (EngineConstruction :431,:440); leaves of a branch = union of
  children's leaves.  leaves_isFullMono (EngineConstruction) is the ∀-over-leaves WF-induction TEMPLATE
  (I need the EXISTENTIAL analog — exhibit ONE leaf).
- Banked o4 (reuse index (b), EngineConstruction): LiveHeadDom, chooseMin_spec (returned divisor is
  at target AND componentwise-≤ all same-level), chooserTotalOnChain_of_sameLevel (chooser never
  falls back on a SameLevelChainInv state), step1_dominates (at a case-1 node every level-ℓ divisor
  dominates every level-≤J divisor), OracleInv (the state invariant bundle, holds at every reachable
  state via OracleInv_conOracle_stepChildren).
- cert §4 (threads/12-realization/cert-o5-realization.md §4): the steering rule R(tStar) [at a Case-1
  node in layer S with target level ℓ: take case-1(1) iff ℓ > tStar^S, else 1(2); case-2/rollover
  forced], and the ANCHOR-DESCENT invariant [track one divisor A: born by case-2 at layer b(tStar) with
  coords = tStar prefix + level tStar^b; maintained through clearing layers (plateau: 1(2) freezes;
  descent needs tStar^{S-1} < r_S = Clearable, the pull-ordering brick lands A at exactly tStar^S,
  Def-4-least); termination at layer clear: A becomes t̃=0 = tStar]. The pull-ordering brick reuses
  LiveHeadDom + chooseMin minimality.

I have proven (clean-three): clearable_tStar (tStar is Clearable), all the §3 envelope-splice.
</task>

<output_contract>
Terse, structural. 
1. The cleanest Lean STRUCTURE for the existence proof: what's the top-level induction (WF on the
   state? on a fuel/step count? on the layer?), and how to select+follow the R(tStar) child at each
   step so that `leaves (buildTree child) ⊆ leaves (buildTree s)` chains to the leaf.
2. The anchor-descent INVARIANT as a Lean predicate on ConState (what fields of the anchor to track;
   is it "∃ k, divProfile k = <tStar truncated to layer> ∧ divTilde k = tStar^{layer-1}" or similar?);
   the base/maintenance/termination obligations it factors into.
3. Which banked lemma discharges the pull-ordering brick (the descent case: A lands at EXACTLY tStar^S,
   Def-4-least) — LiveHeadDom? step1_dominates? chooseMin_spec? — and the shape of that step.
4. The single biggest risk / where this design could dead-end (e.g., the R(tStar) child not being
   literally one of conOracle's emitted StepChildren, or the anchor-identity not being stable across
   the case-1(1) exponent bump). Rank by likelihood.
</output_contract>

<grounding_rules>
Read the actual files (buildTree, conOracle, case1Decision/case2Decision, stepCase11/stepAppendAdvance,
leaves_isFullMono, chooseMin_spec, LiveHeadDom, the cert). Ground each structural claim in what you
find; name lemmas exactly (v4.29). Flag inference vs verified-from-file. This is a DESIGN review — do
not write the full proof; give the skeleton + the load-bearing obligations + the risks.
</grounding_rules>
