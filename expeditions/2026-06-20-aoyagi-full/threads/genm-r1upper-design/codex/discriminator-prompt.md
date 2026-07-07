<task>
Adjudicate ONE structural question about a per-step lemma in a deep-linear-network RLCT proof.
Decide: does the boundary-0 peel REDUCE to a black-box use of a single "tail chain" finiteness
result, or does it genuinely require a simultaneous ("joint") resolution of TWO coupled loci?
This decides whether a multi-month formalisation should commit to a joint double-induction build
or hunt for a lighter single-chain recursion. Do NOT rubber-stamp; attack the reduction claim.

SETTING. Widths M=(M0,...,ML), free real matrices A_s : M_s×M_{s+1} in a box around 0.
Product P=A0···A_{L-1}. Frobenius ‖·‖. Target: ∫_box ‖P‖^{-2c'} dA < ∞ for c' < (1/2)minAdm(M),
where minAdm is Aoyagi's exact learning coefficient (=2λ), obeying the proven recursion
minAdm(M0,...,ML)=min_{t≤min(M0,M1)}[(M0-t)(M1-t)+minAdm(t,M2,...,ML)], base minAdm(a,b)=ab.

THE PEEL (boundary 0, cut t). Pivot-chart Schur reduction (Jacobian 1) of A0 exposes its corank
block Γ=(M0-t)×(M1-t); radial blow-up Γ=z·V, Jacobian z^{a-1}dz dσ(V), a=(M0-t)(M1-t). Block
diagonality gives ‖A0·Q‖² ≍ g² + z²h², where Q=A1···A_{L-1} is the tail product,
g=‖(top t rows of the tail product)‖, h=‖V·(bottom M1-t rows of the tail product)‖.

EXACT FACT I DERIVED AND VERIFIED (0 numerical error). Doing the finite z-integral (a=1 case shown,
general a analogous) and using g²+h²=‖A1·A2···A_{L-1}‖² exactly, the per-step integrand collapses to

    J ≍ P_tail^{-(c'-a/2)} · P_full^{-a/2},

where P_tail = ‖(top t rows)·A2···‖² is the REDUCED TAIL CHAIN (t,M2,...,ML) loss, and
      P_full = ‖A1·A2···A_{L-1}‖²    is the FULL REMAINING PRODUCT (M1,...,ML) loss.
The loci are nested: {P_full=0} ⊂ {P_tail=0}, and P_full = P_tail + ‖(bottom rows)·A2···‖² ≥ P_tail.

FURTHER EXACT FACTS.
- At every BINDING cut t (achieving minAdm), the coupling exponent a/2 is ≤ RLCT(P_full)=(1/2)minAdm(M1,...,ML),
  strictly < when a>0. So the binding factor is P_tail (its exponent hits RLCT(P_tail)); P_full is subordinate.
- L=2: P_tail and P_full are DISJOINT ROW-BLOCKS of a single FREE matrix A1 (no deeper factors), hence
  INDEPENDENT; on {P_tail=0} P_full is bounded below. (This case is already fully proved via a corank recursion.)
- L≥3: P_tail and P_full SHARE the deeper factors A2,...,A_{L-1}; both degenerate together when a shared
  factor drops rank. Each further peel introduces ANOTHER P_full^{(k)-a_k/2} on the shared variables
  (matching Aoyagi's diag(b1,...,b_{M(S)}) monomial and his D_J double-induction).
</task>

<grounding_rules>
- Reason from the stated facts. Treat the exact identity J ≍ P_tail^{-(c'-a/2)}·P_full^{-a/2} and the
  order/nesting facts as given (numerically verified). Focus on the reduce-vs-joint judgement.
- Separate inference from assertion. Name any extra assumption you use.
</grounding_rules>

<output_contract>
1. VERDICT (one line): does the per-step lemma REDUCE to a black-box "tail chain finiteness" call, or
   does it REQUIRE a joint/simultaneous resolution of {P_tail=0} and {P_full=0}? And: BOUNDED labour
   (Aoyagi's construction goes through) or a genuine NEW obstruction?
2. The decisive reason, in terms of the coupling factor P_full^{-a/2}: why the subordinate order does or
   does not let it be treated as an independent benign factor at L≥3 (vs the L=2 independent-row-blocks case).
3. Does the ACCUMULATION of P_full^{(k)} coupling factors across successive peels change the answer? i.e.
   even if each is individually subordinate, is their product on shared variables controllable by a black-box
   recursion, or does it force the joint (S,J) bookkeeping?
4. One cheapest exact test that could still overturn your verdict.
