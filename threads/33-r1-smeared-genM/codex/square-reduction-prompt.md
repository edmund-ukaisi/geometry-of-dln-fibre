<task>
Confirm a reduction that collapses a Lean formalisation case-split. Same L=2 DLN setup as before:
M=(M0,M1,M2)∈ℕ³, T0∈[0,min(M0,M1)], Mval(T0)=(M0−T0)(M1−T0)+T0·M2, r=argmin T0 ("deepRank"),
minAdm=Mval(r). L=2 derived (transcribed from Lean, proven exclusive+exhaustive):
  InteriorDrop ⟺ M2>0 ∧ r<M0 ∧ r<M1
  BoundaryClean ⟺ ¬InteriorDrop ∧ r=M1
  BoundarySmeared ⟺ ¬InteriorDrop ∧ r<M1

The smeared chart-builder splits on whether the rank block is SQUARE (r=M0) or non-square (r<M0).
The SQUARE case (r=M0) is FULLY BUILT and unconditional in Lean. The non-square case (r<M0) is NOT built.

CLAIM: in the regime the spine actually invokes the smeared branch — 1 ≤ minAdm ∧ BoundarySmeared —
we ALWAYS have r = M0 (so the non-square case NEVER arises and need not be built). Argument:
  - BoundarySmeared gives ¬InteriorDrop ∧ r<M1.
  - ¬InteriorDrop ∧ r<M1 ⟹ ¬(M2>0 ∧ r<M0 ∧ r<M1) with r<M1 known ⟹ (M2=0 ∨ r≥M0).
  - 1≤minAdm forces M2≥1 (else Mval(min(M0,M1))=0 picking T0 to zero a factor). So r≥M0.
  - r = argmin T0 ∈ [0,min(M0,M1)] ⟹ r ≤ M0. Hence r = M0. ∎
A brute sweep over M∈[0,9]³ confirms: 156 smeared minAdm≥1 cases, ALL with r=M0; 0 non-square.
</task>

<output_contract>
1. Is the logical reduction "1≤minAdm ∧ BoundarySmeared ⟹ r=M0" at L=2 SOUND? Scrutinise the step
   "1≤minAdm ⟹ M2≥1" and the step "¬InteriorDrop ∧ r<M1 ∧ M2≥1 ⟹ r≥M0". Counterexample or proof.
2. Any subtlety with minimizer-NONUNIQUENESS: if two argmins exist (one r=M0, one r<M0), and the Lean
   tStar (arbitrary Classical.choose) picks the r<M0 one — does the branch still classify SMEARED, and
   if so does r=M0 still hold for THAT chosen r? (i.e. is the reduction robust to the chosen argmin?)
3. VERDICT: can the non-square smeared chart-builder be SKIPPED entirely (the square case + this
   reduction suffice for the spine's hSmeared at L=2)? BOUNDED (a short reduction lemma) or is there a
   gap?
Concise. Flag inference vs proof.
</output_contract>

<grounding_rules>
The InteriorDrop/Clean/Smeared conditions are GIVEN (Lean, exclusive+exhaustive). The key risk to probe
is (2): the branch predicate AND r=deepRank both read the SAME chosen tStar, so within one M they are
consistent — but state explicitly whether that coupling makes the reduction hold for the ACTUALLY-chosen
r, not just for "some argmin".
</grounding_rules>
