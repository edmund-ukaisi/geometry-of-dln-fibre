<task>
Lean induction-maintenance proof structure. The bound is TRUE (verified millions of cases); I need the
cleanest PROOF for a MULTI-THRESHOLD kernel and whether an achiever lemma (good_floor_core) fires once or
per-step. NO counterexample hunt.

SETUP (exact ints): forwardMax greedy, q_i=maxPick(M^{i+1}, ws_i, R_i)=largest pool elt >=M^{i+1} keeping
Dom. R_{i+1}=R_i.erase q_i. ws_i=Mwidths.drop(i+1)=[M^{i+2},...,M^L]. cLt(S,t)=#{s<t}. Dom(b,R):|b|=|R| ∧
∀t cLt(R,t)<=cLt(b,t). u_i telescopes u_{i+1}=M^{i+1}+u_i-q_i. head'_i=max(u_i,M^{i+1}). Pool R_0=Ymulti=
(balancedSplit: c values in {b,b+1}, r=P mod c copies of b+1, b=⌊P/c⌋) ⊎ (L-c largest sorted widths).
ACHIEVER good_floor_core (proven): c·aS_m <= Sprefix(c+1)+(m-1), 1<=m<=c (aS=sorted widths).

INVARIANT (STRONG INV): STRONG(i) := ∀t<=head'_i, cLt(R_i,t)<=cLt(ws_i,t).
GOAL: STRONG(i) ⟹ STRONG(i+1).

ESTABLISHED (exact, exhaustive):
- STRONG(i) <=> Dom(head'_i::ws_i, R_i) restricted to t<=head'_i <=> SORTED-POINTWISE domination
  R_i[k] >= sorted(head'_i::ws_i)[k] for every rank k (equal cardinality |R_i|=1+|ws_i|).
- The maintenance is MULTI-THRESHOLD: the range (b+1, head'_{i+1}] can have UP TO ~7 tight (binding)
  thresholds; ~16-37% of binding steps have >1. In sorted-pointwise terms these are the binding RANKS.
- blist transition (multiset): blist_{i+1} = blist_i - {head'_i} - {M^{i+2}} + {head'_{i+1}}.
- head'_{i+1} >= M^{i+2} ALWAYS (so the swap never lowers a blist element); when head'_{i+1}>head'_i
  the increase is driven by M^{i+2} (head'_{i+1}=M^{i+2}).
- q_i >= head'_i ALWAYS (the pick is at least the head).
- ABSTRACT INTERLACING IS INSUFFICIENT: I tested "R dom blist pointwise, remove q_i>=head'_i from R,
  apply the blist transition with head'_{i+1}>=M^{i+2}" abstractly — it FAILS ~42% of random instances.
  So good_floor_core does real work; the pointwise reframing does NOT make it abstract.
- STRONG(0) [base] holds: ∀t<=head'_0, cLt(Ymulti,t)<=cLt(ws_0,t). This base IS the achiever majorization
  (good_floor_core content, same family as the proven Dom(Mwidths,Ymulti)).
- The green "tight chain" Dom(Mwidths.drop i, R_i) [for ALL t, card-correct] propagates by maxPick_spec
  with NO good_floor_core per step (good_floor_core only at its base Dom(Mwidths,Ymulti)).
</task>

<output_contract>
1. THE KEY QUESTION: does STRONG(i)⟹STRONG(i+1) need good_floor_core fired AGAIN at each step i, or can
   STRONG propagate from STRONG(0) [base, where good_floor_core fires once] using only the erase chain +
   structural facts (q_i>=head'_i, head'_{i+1}>=M^{i+2}, the tight green chain Dom(Mwidths.drop i,R_i))?
   Given that abstract interlacing fails ~42%, which EXTRA fact (beyond pure interlacing) closes the
   per-step maintenance — is it a fresh good_floor_core invocation, or a propagated consequence of the
   base + the tight chain?
2. For the MULTI-THRESHOLD case (multiple binding ranks at once): give the cleanest uniform argument that
   covers ALL binding ranks/thresholds in one shot (sorted-pointwise, or a sorted-prefix majorization),
   rather than threshold-by-threshold. Name the single inequality.
3. Is there a way to make the maintenance carry the WHOLE Dom(Mwidths.drop i, R_i) [tight green chain,
   no per-step gfc] and DERIVE STRONG(i) at each i from it + a once-proven achiever majorization — so
   good_floor_core fires ONLY at the base? Or is per-step good_floor_core genuinely irreducible? (I earlier
   wrongly claimed a head-monotonicity derivation; it is false — raising a Dom head makes Dom harder. So
   that route is dead. Is there ANOTHER once-only-gfc route, or is per-step gfc the truth?)
4. Flag circularity.
</output_contract>

<grounding_rules>
- Exact ints. The bound is TRUE; I need PROOF STRUCTURE + the once-vs-per-step good_floor_core question.
- Do NOT claim head' monotone (false). Do NOT claim abstract interlacing suffices (it fails ~42%). Do NOT
  claim a head-free β-conjunct (card mismatch, fails). 
- The deciding question: once-only good_floor_core (propagate STRONG from base via the tight chain) vs
  per-step good_floor_core (irreducible). Give your best-supported answer and mark PROVED vs CONJECTURE.
