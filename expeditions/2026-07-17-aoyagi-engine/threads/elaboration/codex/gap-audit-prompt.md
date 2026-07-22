<task>
You are a decorrelated second opinion on a Lean 4 + Mathlib formalisation of Aoyagi's
resolution-of-singularities for deep linear networks. I am the independent "elder" reviewer; I
need you to VERIFY or REFUTE three structural claims I reached, working from the paper's mechanism
and the construction, NOT from my say-so. Reason from first principles and the files; flag every
inference vs observed-fact.

CONTEXT (read these files; all paths absolute):
- Worked mechanism template (built blind from the paper, exact-algebra checked):
  /home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/aoyagi-engine/root/expeditions/2026-07-17-aoyagi-engine/threads/elaboration/fold-recursion-template.md
- The Lean monument (defs foldResid, edgeδ, blockBlowupMap, supportAt, blockCoords, canonCenterOf,
  canonPivotOf, the case1/case2/lastLayer/terminal leaves):
  /home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/aoyagi-engine/root/lean/DLNFibre/DLN/Aoyagi/MonumentAtlas.lean
- The state machine (conOracle, stepCase11/12/2, stepRollover, case1Decision, canon* transitions):
  /home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/aoyagi-engine/root/lean/DLNFibre/DLN/RLCT/Engine/EngineConstruction.lean
- The blow-up algebra (blockBlowupCoordQuot: pivot->1, else identity, NO division):
  /home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/aoyagi-engine/root/lean/DLNFibre/Core/Aoyagi/BlockDivision.lean

BACKGROUND FACTS you can take as given (verified from the Lean):
- edgeδ d p = decide(p.conState.cleared = 0): a step is "δ=1" iff the PARENT's cleared count is 0.
- foldResid at δ=1 does a strict transform via blockBlowupCoordQuot (removes the pivot's u factor);
  at δ=0 it is a pure pullback.
- stepCase11 (merge, case11) keeps cleared UNCHANGED; stepCase12/stepCase2 do cleared+1; rollover
  sets layer+1, cleared:=0.
- canonPivotOf for case11 = cornerToFlat of the REUSED divisor's IMMUTABLE birth corner
  (s.divBirthCoord[mergeIdx]); canonCenterOf for case11 = the current-layer (s.layer) residual block
  only (filter q.1.1 = s.layer ...). TreeEdge carries hpivot : pivot ∈ center.
- The template's (3,3,4) binding trace has state (S=2, J=0) firing "Edge B = Case 1(1) boost":
  δ=1 (cleared=0), NO J-advance, reusing exceptional u_{1,2} which was BORN in layer 1.

CLAIMS TO ADJUDICATE:

CLAIM 1 (the multi-homogeneity invariant, "GAP-3"). The Lean foldResid (root = coreGen = the full
loss generators; steps = strict transform / pullback) is a CROSS-LAYER PRODUCT: degree-1 in each
ACTIVE layer at-or-above the current support layer, with degree-2 legitimately allowed BELOW the
support threshold (the Schur residue γβ of already-cleared layers). This matches the template §3.1
("terminal generator = product one factor per layer") and §3.4 (cleared layer carries degree 2).
Sub-claim 1a: this structure is NOT derivable if the leaves quantify over a FREE parent path p
(arbitrary parent shears break it), so under the current free-edge leaf design it must be a CARRIED
invariant (a def-change to the Deg1SupportedSlot predicate). Sub-claim 1b: if instead the leaves are
conditioned on the branch being a REAL oracle branch (IsRealBranch: center=canonCenterOf,
pivot=canonPivotOf, nextState=oracle child, shear=canonical), then the structure becomes DERIVABLE by
structural induction over the real branch (each real step provably preserves it), so the def-change
DISSOLVES into a derived lemma. QUESTION: are 1, 1a, 1b correct? Is the cross-layer-product form the
right carried object, and does IsRealBranch-conditioning truly make it a derived lemma rather than a
carried invariant?

CLAIM 2 (the case-1(1) boost at cleared=0). Because Edge B (Case 1(1) boost) fires at cleared=0
(δ=1) — the template's (3,3,4) (S=2,J=0) — a naive worry is that a δ=1 step that removes a pivot
would descend the residual one layer while the invariant's support (supportAt(S, cleared=0) = layer-S
block) does NOT descend (case11 keeps cleared=0), breaking the descend. My claim: this worry is VOID
for a REAL boost, because the boost's pivot is the REUSED EXCEPTIONAL coordinate u_{s,k} (born in an
earlier layer), so the strict transform PULLS OUT that u factor (it accumulates into the b-chain /
dominant monomial foldB) and leaves the residual AT THE SAME layer S (no descent) — matching
supportAt(S,0)=layer-S. The free-edge counterexample that breaks the leaf (pivot = a current-layer
c-coordinate, so the strict transform descends the residual) is NOT a real boost and is excluded once
the pivot is pinned to canonPivotOf. QUESTION: is this correct — does the real boost leave the
residual at layer S (no descend), so conjunct-2 holds, PROVIDED the pivot is pinned to the reused
exceptional (canonPivotOf), not a free pivot?

CLAIM 3 (a suspected canonCenterOf/canonPivotOf inconsistency for case11 boosts). For a boost,
canonPivotOf = the reused divisor's birth corner, which lies in an EARLIER layer (birth layer < current
s.layer, e.g. u_{1,2} born in layer 1, boosted at layer 2). But canonCenterOf for case11 filters ONLY
current-layer coords (q.1.1 = s.layer). So the pivot (earlier layer) is NOT in the center (current
layer) — yet TreeEdge requires hpivot : pivot ∈ center. The template §"Edge B" blows up the locus
{ partial current-layer d-block ; u_{s,k} = 0 }, i.e. the center SHOULD include the reused exceptional
u_{s,k}. QUESTION: is this a genuine defect in canonCenterOf (it should include the reused exceptional
coordinate / the pivot), making IsRealBranch currently UNSATISFIABLE for a boost edge? Or is there a
reading under which canonPivotOf for case11 lands in the current-layer block (so pivot ∈ center holds)?
This is the single most important thing to get right — a wrong center def is a correctness defect.

DESIGN QUESTION (depends on 1-3): given the boost complication, should the leaves be (P) kept over
free edges with per-field property hypotheses (center ⊆ blockCoords, a carve-supported shear, a
transition law, plus the CARRIED multi-homogeneity invariant of 1a), or (C) conditioned on IsRealBranch
(one construction hypothesis, per-field constraints derived as canon* lemmas, multi-homogeneity a
derived lemma per 1b) — GIVEN that the boost's pivot/center are cross-layer and the per-field
"within-carve (layer-L)" shear pin and "hpivot ∈ center" are insufficient/wrong for boosts? Which is
the weakest-that-inducts, name=content, bedrock choice?
</task>

<output_contract>
Four sections, in order, terse:
1. CLAIM 1 verdict: TRUE / FALSE / PARTIAL, with the decisive reason; separately rule 1a and 1b.
2. CLAIM 2 verdict: TRUE / FALSE / PARTIAL + the decisive reason (does the real boost descend or not?).
3. CLAIM 3 verdict: DEFECT / NO-DEFECT / CANNOT-DETERMINE-FROM-FILES + the specific evidence
   (quote the canonCenterOf filter and the canonPivotOf birth-corner if you read them).
4. DESIGN: recommend P or C in one paragraph, keyed to your 1-3 verdicts.
For each, mark INFERENCE vs OBSERVED (read-in-file) explicitly.
</output_contract>

<grounding_rules>
Do not trust my claims; check them against the files. If a claim cannot be settled from the files,
say CANNOT-DETERMINE and name exactly what additional fact would settle it. Never emit Lean code to
paste; the diagnosis is what I need. Flag every place you INFER the paper's intent vs OBSERVE a
definition in the Lean.
</grounding_rules>
