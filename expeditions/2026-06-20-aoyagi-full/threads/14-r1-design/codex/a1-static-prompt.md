<task>
A proposed proof-simplification I suspect is INCOMPLETE; I need adjudication. The bound is TRUE; the
question is whether a specific NON-INDUCTIVE (static) argument suffices, or whether induction is still needed.

SETUP (exact ints): forwardMax greedy picks q_0,q_1,... left-to-right from pool Ymulti (a fixed multiset of
L integers). q_i = maxPick(M^{i+1}, ws_i, R_i) = largest pool elt >= M^{i+1} keeping Dom. R_{i+1}=R_i.erase q_i,
R_0=Ymulti. ws_i = Mwidths.drop(i+1) = [M^{i+2},...,M^L] (suffix widths). cLt(S,t)=#{s<t}. Dom(b,R):|b|=|R| ∧
∀t cLt(R,t)<=cLt(b,t). u_i telescopes u_{i+1}=M^{i+1}+u_i-q_i. head'_i=max(u_i,M^{i+1}). Ymulti has a
balanced β-block (c values in {b,b+1}). good_floor_core (proven achiever fact): c·aS_m<=Sprefix(c+1)+(m-1).

GOAL (per-step band): u_{i+1} <= admBound_i (=M^{i+1} for i>=1). The GREEN consumer proves this FROM the
invariant FMDom(i) := Dom(head'_i :: ws_i, R_i) [a full ∀t Dom statement], via:
  FMDom(i) ⟹ q_i >= head'_i >= u_i ⟹ u_{i+1}=M^{i+1}+u_i-q_i <= M^{i+1}.  [via dom_head_pick + le_maxPick]
So the band needs FMDom(i) for each i.

THE PROPOSED SIMPLIFICATION (which I suspect is incomplete): claim FMDom(i) holds DIRECTLY (no induction)
via two static facts:
  (submultiset)  cLt(R_i, t) <= cLt(Ymulti, t)         [R_i ⊆ Ymulti, removing elements lowers cLt]
  (static_count) cLt(Ymulti, t) <= cLt(ws_i, t)        [from good_floor_core, Ymulti FIXED]
giving cLt(R_i,t) <= cLt(ws_i,t), hence FMDom(i).

MY NUMERICAL FINDINGS (exact, exhaustive L<=6):
- The threshold-restricted static_count cLt(Ymulti,t) <= cLt(Mwidths.drop(i+2),t) for t<=u_{i+1} HOLDS (0 fail).
- BUT FMDom(i) = Dom(head'_i::ws_i, R_i) requires the bound on the WHOLE range t<=head'_i (and the +1 head
  slot above). It splits into: (a) t<=u_i: static_count+submultiset works; (b) GAP u_i<t<=head'_i
  (=u_i<t<=M^{i+1} when M^{i+1}>u_i); (c) t>head'_i: head slot.
- In the GAP (b), the static fact cLt(Ymulti,t) <= cLt(ws_i,t) FAILS (~13900 cases) because ws_i is
  head-free (|ws_i|=L-i-1 < |R_i|=L-i) and Ymulti has MORE small elements than ws_i. Specifically there are
  9258 NON-TRIVIAL gap cases where cLt(R_i,t)>0, cLt(Ymulti,t) > cLt(ws_i,t), yet FMDom holds — and it holds
  ONLY because the erases q_0..q_{i-1} removed small elements, making cLt(R_i,t) < cLt(Ymulti,t). Example:
  M=(0,0,1,0), i=1: R_i={0,1}, cLt(R_i,1)=1=cLt(ws_i,1); but cLt(Ymulti,1)=2. The submultiset bound
  cLt(R_i,1)<=cLt(Ymulti,1)=2 is too weak; the erase of a '0' is what gives cLt(R_i,1)=1.
- So submultiset bounds R_i ABOVE by Ymulti, but the GAP needs R_i to be SMALLER than Ymulti — the WRONG
  direction. Only the inductive erases give the smallness.
</task>

<output_contract>
1. Is my analysis correct that the static "submultiset + static_count" route is INCOMPLETE — that it
   covers t<=u_i but NOT the gap u_i<t<=head'_i, because submultiset is the wrong direction there (R_i
   needs to be smaller than Ymulti, which only the erases provide)? Confirm or refute.
2. If incomplete: is the gap genuinely requiring an INDUCTIVE argument (carrying that the picks removed
   enough small elements), i.e. the same maintenance the simplification was trying to avoid? Or is there a
   DIFFERENT static fact (not submultiset-from-Ymulti) that closes the gap — e.g. a count on R_i directly
   from a prefix-of-picks argument that is still "one-shot"?
3. Is there any way the band could be established WITHOUT full FMDom(i) — a weaker requirement that the
   τ<=u_i static part alone satisfies? (The consumer uses dom_head_pick + le_maxPick which need the full
   Dom(head'_i::ws_i, R_i).)
4. Bottom line: does the static-reduction dissolve the induction, or does the induction (the erases'
   effect on the small-count) remain load-bearing in the gap? Mark PROVED vs CONJECTURE.
</output_contract>

<grounding_rules>
- Exact ints. The band is TRUE. The question is whether the STATIC argument is COMPLETE or whether the
  gap u_i<t<=head'_i still needs the inductive erase-effect.
- submultiset gives cLt(R_i,t)<=cLt(Ymulti,t) (R_i⊆Ymulti) — note the DIRECTION (upper bound by Ymulti).
- Do NOT assume ws_i contains M^{i+1} (it does not; ws_i=Mwidths.drop(i+1)=[M^{i+2},...]).
- Distinguish PROVED from CONJECTURE. The crux: is the gap covered statically, or does it need induction?
