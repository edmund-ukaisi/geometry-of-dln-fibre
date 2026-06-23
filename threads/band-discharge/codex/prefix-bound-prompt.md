<task>
Lean4/Mathlib. I've built `forwardMax` (front-greedy: at each position place LARGEST pool value ≥ width
keeping remaining Dom) with PROVEN specs: forwardMax_perm (perm of pool), forwardMax_feasible
(b[i] ≤ fm[i]), forwardHead_ge/_dom/_mem, live_le_forwardHead. ALL GREEN.

I need the LAST piece: the prefix lower bound
  forwardMax_prefix_band:  ∀ k, 1 ≤ k → k ≤ L →  S'_k ≤ prefix_k(forwardMax (Mwidths M) (Ymulti M))
where S'_k = ∑_{i<k} Mseq M i = M^0+M^1+...+M^{k-1},  prefix_k(p) = (p.take k).sum,
Mwidths M = [M^1,...,M^L] (M^{i+1} at position i), Ymulti M = the achiever target multiset Yvec.
(This + a separate `fm[0] ≥ max(M^0,M^1)` give the band; that handles j=0 vs j≥1.)

CRITICAL FINDING (numerically, 20000 random Dom pairs): the bound is NOT abstract —
"prefix_k(fm) ≥ (∑R−∑b) + ∑_{i<k-1}b[i]" FAILS for generic Dom(b,R). It holds ONLY using the
SPECIFIC structure of Ymulti=Yvec (the achiever balanced-split). So the proof MUST use the
M-structure / good_floor_core, NOT pure Dom induction.

THE M-STRUCTURE LEMMAS I HAVE (all green, proven):
- good_floor_core: cAch M * aS M i ≤ Sprefix M (cAch M+1) + (i-1)   for 1≤i≤cAch M.
  [aS M i = i-th smallest width (a_0≤a_1≤...); Sprefix M n = a_0+..+a_{n-1}; cAch M = achiever c]
- Yvec M c j = balanced split of P=Sprefix(c+1) into c parts on [0,c), then a_{j+1} on [c,L).
  Yvec is MONOTONE (Yvec_monotone). ∑Yvec = ∑M (sum_Yvec).
- Yvec_lowerfit: smallestK L m (Yvec) ≤ Sprefix M (m+1)   for m ≤ L.  [smallestK = sum of m smallest]
- Yvec_prefix: closed form for ∑_{i<k} Yvec (monotone prefix) — k≤c: k·b+max(0,k+r−c); k>c: Sprefix(k+1).
- aS_le_bp1, count_bp1_le, Sprefix_tail_ge, junction_bound — all available.
- Mwidths_get: Mwidths[j] = M^{j+1}.

The OBSTACLE: forwardMax recursion fm(t::bs)R = w :: fm bs (R.erase w) leaves the M-family —
(bs, R.erase w) is not Mwidths/Ymulti of any M'. So I cannot recurse staying in the structure.

DUAL FORM: prefix_k(fm) ≥ S'_k  ⟺  suffix_k(fm) ≤ ∑_{i=k}^L M^i  (total ∑fm=∑M).
suffix of fm = sum of (L−k) tail values at positions k..L-1 (widths M^{k+1}..M^L).
</task>

<output_contract>
Pick the SINGLE best proof strategy for forwardMax_prefix_band and give a Lean skeleton (≤50 lines).
Address head-on: how to get prefix_k(fm) ≥ S'_k WITHOUT recursing in the M-family. Candidate angles
to evaluate (pick one or propose better):
 (i) Don't bound forwardMax's prefix directly; instead exhibit a DIFFERENT explicit feasible witness
     p_k PER k (depending on Yvec structure) whose prefix = S'_k is computable, then use forwardMax/
     qStar prefix-MAXimality (prefix_k(fm) ≥ prefix_k(p_k)). What explicit p_k? (must be a perm of
     Yvec, feasible Mwidths[i]≤p_k[i], prefix_k ≥ S'_k, and have a Lean-computable prefix.)
 (ii) An abstract prefix lemma with a STRONGER hypothesis than Dom that Ymulti satisfies and that
      IS preserved by the recursion (find the right invariant — excess+prefixWidth failed).
 (iii) sorted-prefix / majorization: relate prefix_k(fm) to smallestK/Yvec_lowerfit.
State which, and the 3-4 key Lean steps + Mathlib lemmas. Flag the riskiest step.
</output_contract>

<grounding_rules>
Assume listed lemmas exist as typed. If you propose witness p_k, it must be CONCRETE (I'll verify
numerically before building). Flag guesses vs certainties.
</grounding_rules>
