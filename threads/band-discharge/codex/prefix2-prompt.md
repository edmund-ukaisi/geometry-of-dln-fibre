<task>
Lean4. Prove: prefix_k(forwardMax b R) >= S'_k, where for the SPECIFIC b=Mwidths=[M¹..Mᴸ],
R=Yvec (achiever balanced-split target), S'_k = M⁰+M¹+..+M^{k-1}. forwardMax = front-greedy
(place largest pool value ≥ width keeping Dom). PROVEN: forwardMax_feasible (b[i]≤fm[i]),
forwardMax_perm, forwardMax is prefix-MAX over feasible perms (I can prove this, dual of a
backward suffix-min lemma I have).

VERIFIED FACTS (numerically certain):
- prefix_k(fm) >= S'_k holds (0 fails).
- It is NOT abstract: fails for generic Dom(b,R); needs Yvec achiever structure.
- prefix_k(fm) >= "smallestK_b + excess" and ">= index_b+excess" BOTH FAIL abstractly.
- Have: good_floor_core: c·aSᵢ ≤ Sprefix(c+1)+(i-1), 1≤i≤c=cAch. (aS=sorted widths, Sprefix=their prefix sum)
- Have: S'_k ≤ largestK(Yvec,k) [provable via Yvec_lowerfit: smallestK(Yvec,m)≤Sprefix(m+1)].
- prefix_k(fm) >= largestK(Yvec,k) FAILS (feasibility blocks grabbing the k largest).
- Equivalent suffix form: suffix_k(fm) ≤ tailM_k = M^k+..+M^L (since ∑fm=∑M). And min feasible
  suffix > smallestK(Yvec,L-k) sometimes (feasibility forces larger tail values).
</task>
<output_contract>
ONE proof strategy for prefix_k(fm)≥S'_k. Be concrete: state the exact induction/invariant
(on k? on the list? a potential function combining width-prefix and Yvec structure?) and the
3 key steps. If a constructive feasible witness p with prefix_k(p)≥S'_k exists with a Lean-
computable prefix, give it EXPLICITLY (perm of Yvec). Flag the single riskiest step. ≤40 lines.
</output_contract>
<grounding_rules>Flag guess vs certain. Witnesses must be concrete (I verify numerically).</grounding_rules>
