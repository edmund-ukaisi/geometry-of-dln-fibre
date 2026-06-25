<task>
A Lean-formalization design decision between two invariants for the SAME greedy maintenance induction.
I need a judgment on which has the CLEANER MAINTENANCE PROOF (not which is true — both verified true over
millions of cases). The key question: does a "strengthen-the-IH" move actually simplify the proof, or does
the case-analysis just relocate inside the maintenance?

SETUP: forwardMax greedy picks left-to-right from pool, q_i = maxPick(w_i, ws_i, R_i) = largest pool elt
>= w_i that keeps Dom(ws_i, R_i.erase y). R_{i+1}=R_i.erase q_i. w_i = M^{i+1} (the i-th width).
ws_i = the suffix widths AFTER position i = [M^{i+2},...,M^L]. cLt(S,t)=#{s<t}. Dom(b,R): |b|=|R| ∧
∀t cLt(R,t)<=cLt(b,t). head'_i = max(u_i, M^{i+1}), u_i a telescoping level (u_{i+1}=M^{i+1}+u_i-q_i).
The GOAL is a per-step band q_i >= u_i (⟹ u_{i+1} <= admBound), proven by an induction carrying an invariant.

TWO CANDIDATE INVARIANTS (both hold + maintain, verified 0 fails over millions):

ROUTE-A "STRONG INV": carry  ∀ t <= head'_i: cLt(R_i, t) <= cLt(ws_i, t)   [head-free, but t-RESTRICTED to <=head'_i].
ROUTE-B "DISSOLVE": carry  Dom(M^{i+1}::ws_i, R_i)  (= the full-width-from-i Dom, ALL t, card-correct
  |R_i|=|M^{i+1}::ws_i|).  Then derive the band via: head-monotonicity gives Dom(head'_i::ws_i, R_i)
  [raising the head M^{i+1}->head'_i only raises cLt]; maxPick_spec on that gives a witness y>=head'_i
  with Dom(ws_i, R_i.erase y); le_maxPick gives q_i >= y >= head'_i >= u_i.

MY NUMERICAL FINDINGS on the MAINTENANCE proofs (exact, exhaustive L<=5):
- ROUTE-A maintenance (STRONG(i) => STRONG(i+1)): I decomposed the target cLt(R_{i+1},t)<=cLt(ws_{i+1},t)
  for t<=head'_{i+1} and it SPLITS into THREE internal regions:
    (i) t<=head'_i, deficit<=0 (M^{i+2}>=t OR q_i<t): free from STRONG(i). [11527 cases]
    (ii) t<=head'_i, deficit=1 (M^{i+2}<t<=q_i): needs STRONG(i) to have SLACK>=1; that slack splits AGAIN
         at b+1 (929 cases t<=b+1 need an achiever arithmetic fact 'good_floor_core'; 112 cases t>b+1
         need a structural argument). [1041 cases]
    (iii) head'_i < t <= head'_{i+1}: STRONG(i) says nothing; needs q_i<t (proven from the telescope
          u_{i+1}=M^{i+1}+u_i-q_i and t>head'_i>=u_i). [2213 cases]
- ROUTE-B maintenance (Dom(M^{i+1}::ws_i,R_i) => Dom(M^{i+2}::ws_{i+1},R_{i+1})): a SINGLE application of
  maxPick_spec (erasing the maxPick from a Dom preserves Dom of the tail). NO t, NO region split, NO
  good_floor_core, NO q_i<t argument. It is literally the standard forwardMax Dom-chain step. [0 fails]
  good_floor_core enters ONLY ONCE, at the base i=0 (Dom(Mwidths, Ymulti), already proven).
</task>

<output_contract>
1. Is my analysis correct that ROUTE-A's maintenance internally re-splits into the same 3 regions
   (so the "strengthen-the-IH" does NOT simplify — the complexity relocates), while ROUTE-B's
   maintenance is a single Dom-erase step? Confirm or correct.
2. Is ROUTE-B genuinely sound — does the band really follow from the head-free Dom + head-monotonicity +
   maxPick_spec + le_maxPick, with NO per-step achiever content (good_floor_core only at the base)? Any
   hidden gap (e.g. does head-monotonicity of Dom actually hold: Dom(a::ws,R) ∧ a<=a' ⟹ Dom(a'::ws,R))?
3. Which invariant gives the cleaner Lean maintenance? Name the deciding factor.
4. Flag any circularity in ROUTE-B (head'_i contains u_i = M0 + Σ_{k<i}(M^{k+1}-q_k), picks <i only).
</output_contract>

<grounding_rules>
- Exact integers. Both invariants are TRUE; the question is PROOF cleanliness, not truth.
- Focus on whether ROUTE-A's case-analysis genuinely vanishes or relocates, and whether ROUTE-B's
  single-step maintenance is sound (esp. the head-monotonicity of Dom and the maxPick witness).
- Distinguish PROVED from CONJECTURE.
