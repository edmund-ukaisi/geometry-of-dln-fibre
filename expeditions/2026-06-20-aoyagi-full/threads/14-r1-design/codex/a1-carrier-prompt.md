<task>
I am formalizing in Lean 4 a per-step bound for a greedy front-loader. I need a clean INDUCTIVE
CARRIER that bridges a GLOBAL definition to a LOCAL recursion, and a check for hidden circularity.

DEFINITIONS (exact, over ℤ):
- M = (M⁰,…,Mᴸ) nonneg integers, L ≥ 1. Mwidths = [M¹,…,Mᴸ] (length L). Ymulti = a fixed multiset of
  L integers (an "achiever pool"), with Dom(Mwidths, Ymulti) GIVEN (equal card; head-count dominance
  cLt(Ymulti,t) ≤ cLt(Mwidths,t) ∀t, where cLt(S,t)=#{s∈S: s<t}).
- forwardMax (b:List ℤ) (R:Multiset ℤ) : List ℤ recurses LEFT to right:
    forwardMax [] R = []
    forwardMax (w::ws) R = maxPick w ws R :: forwardMax ws (R.erase (maxPick w ws R))
  where maxPick w ws R = the LARGEST y∈R with y≥w and Dom(ws, R.erase y) (Dom-preserving feasible pick).
  Green facts: maxPick_spec (maxPick∈R ∧ w≤maxPick ∧ Dom(ws, R.erase maxPick)); le_maxPick (any
  Dom-preserving feasible y≥w has y ≤ maxPick).
- qFM : ℕ → ℤ := fun i ↦ (forwardMax Mwidths Ymulti).getD i 0.   ← GLOBAL definition (full data)
- uTel (q:ℕ→ℤ) : ℕ→ℤ := 0 ↦ M⁰ ; (j+1) ↦ Mseq(j+1) + uTel q j − q j.   (Mseq i = Mᵢ for i<L+1 else 0)
- admBound j = min(M⁰,M¹) if j=0 else M^{j+1}.

GOAL (qFM_uTel_band): ∀ j∈[0,L−1]: uTel qFM (j+1) ≤ admBound j.
Reduces (pure algebra, verified) to the PER-STEP band:
   qFM_j ≥ uTel qFM j   (for j≥1),   qFM_0 ≥ max(M⁰,M¹).

THE PROBLEM: qFM_j = (forwardMax Mwidths Ymulti).getD j 0 is the GLOBAL list element, but the
recursion at depth j operates on the SUFFIX widths (Mwidths.drop j) and a residual pool
R_j = Ymulti after erasing qFM_0,…,qFM_{j−1}. I need to thread an inductive carrier so the global
per-step band follows from a local-recursion invariant.

A CANDIDATE CARRIER (numerically verified 0 failures over 2643 exhaustive cases, L≤5):
- Conservation: uTel qFM i = (∑ R_i) − (∑ Mwidths.drop i).   [R_i = residual pool before pick i]
- Dual-conjunct invariant INV(i): Dom([head'_i] ++ Mwidths.drop(i+1), R_i) ∧ shapeInv(i),
  where head'_i = max(M⁰,M¹) (i=0) else max(uTel qFM i, M^{i+1}), and shapeInv(i) = "the elements of
  R_i that are ≤ b+1 are all in the balanced-block β" (an achiever-structural fact; b=⌊P/c⌋).
- The band from INV(i): the witness y := pick(head'_i, R_i) [smallest R_i-value ≥ head'_i] is in R_i,
  ≥ head'_i ≥ Mwidths[i], and Dom-preserving (from the head'-augmented Dom) ⟹ by le_maxPick,
  qFM_i = maxPick(Mwidths[i], Mwidths.drop(i+1), R_i) ≥ y ≥ head'_i ≥ uTel qFM i.
- INV maintenance i → i+1: the head upgrades from M^{i+2} (cheap) to head'_{i+1}=max(uTel(i+1),M^{i+2});
  the upgrade uses a window head-count ∀τ∈(M^{i+2}, head'_{i+1}]: cLt(R_{i+1},τ) ≤ cLt(Mwidths.drop(i+2),τ),
  proven by a τ-RANGE-SPLIT: τ>head'_{i+1} region free from the pick-step's own Dom output; τ≤head'_{i+1}
  region from shapeInv + the achiever arithmetic good_floor_core (c·aSᵢ ≤ Sprefix(c+1)+(i−1)).
</task>

<output_contract>
1. Is the conservation identity uTel qFM i = (∑R_i) − (∑Mwidths.drop i) the RIGHT bridge between the
   global qFM and the local recursion? Is there a cleaner carrier that avoids referencing R_i (e.g. a
   statement purely about forwardMax (Mwidths.drop i) R_i and its head)?
2. The crux: how should the inductive lemma be STATED so that the GLOBAL qFM_j (= getD j of the full
   forwardMax) is provably equal to the LOCAL recursion's head at depth j? Name the forwardMax
   structural lemma needed (a "drop/suffix" identity: (forwardMax b R).drop k relates to forwardMax
   (b.drop k) (R after k erasures), or getD j relates to the head of the depth-j recursion).
3. Flag any HIDDEN CIRCULARITY: head'_i contains uTel qFM i, and uTel qFM i depends on qFM_0..qFM_{i-1}
   (already-determined picks) — is the INV(i)→band(i)→INV(i+1) induction well-founded (each step uses
   only EARLIER picks), or does head'_i smuggle in the band it is trying to prove?
4. Is the per-step band reduction (qFM_j ≥ uTel j ⟹ uTel(j+1) ≤ admBound_j) the cleanest target, or
   is there a more direct inductive statement?
</output_contract>

<grounding_rules>
- Exact integer arithmetic. Distinguish PROVED from CONJECTURE.
- Focus on the global↔local bridge (point 2) and the circularity check (point 3) — those are the
  subtle parts. The achiever arithmetic (good_floor_core) is established; do not re-derive it.
- The numerics (0/2643) confirm the statements are TRUE; I need the cleanest PROOF STRUCTURE and a
  circularity audit, not a counterexample hunt.
</grounding_rules>
