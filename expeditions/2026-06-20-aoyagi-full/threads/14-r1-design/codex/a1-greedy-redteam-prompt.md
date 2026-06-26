<task>
RED-TEAM a claimed IMPOSSIBILITY. I claim that a certain forward-greedy construction CANNOT carry a
checkable, abstractly-inductively-closed loop invariant, and that the right certificate is therefore a
non-greedy (top-level) one. I want you to TRY TO BREAK this claim: either exhibit a checkable coupled
invariant that IS abstractly inductively closed (and sufficient), or independently confirm the
impossibility with a clean argument. Withhold deference — attack it.

THE CONSTRUCTION (forward greedy). We must arrange a multiset Y of L nonneg integers into a tuple
q=(q_0,...,q_{L-1}) (a permutation of Y) satisfying, with widths w_j = M^{j+1}, full prefix sums
S_n = M^0+...+M^n, P_n = q_0+...+q_{n-1}, admBound_0 = min(M^0,M^1), admBound_j = M^{j+1} (j>=1):
  (L)    q_j >= M^{j+1}                  ∀j
  (U)    P_n <= S_n                       ∀n
  (Ladm) P_n >= S_n - admBound_{n-1}      ∀n
  (T)    P_L = S_L
A forward greedy processes positions j=0,1,...; at step j it maintains a running level u_j (u_0=M^0,
u_{j+1}=M^{j+1}+u_j-q_j), picks q_j from the remaining multiset `rem` inside the window
[max(M^{j+1}, u_j+M^{j+1}-admBound_j), u_j+M^{j+1}], removes it, recurses. The greedy is empirically
correct (smallest-in-window picks succeed on all reachable states) but I claim NO checkable local
invariant on the state (rem, u_j, remaining-widths) is BOTH (a) abstractly inductively closed and
(b) sufficient to guarantee completion.

THE CLAIMED STRUCTURAL OBSTRUCTION (attack this). After committing q_0..q_{j-1}, the residual problem
is: arrange `rem` into the remaining slots with the residual corridor. I claim:
  - The residual feasible region IS an integer-polymatroid base polytope: its rank
    ρ_resid(A) = max over feasible completions of ∑_{t∈A} q_t is monotone + submodular (verified
    exhaustively, 0/378 non-submodular over small instances).
  - BUT "is THIS specific multiset `rem` a base-permutation of the residual polymatroid" is STRICTLY
    STRONGER than the residual Gale condition "∀A, sumSmallest(|A|,rem) <= ρ_resid(A)".
  - COUNTEREXAMPLE: rem = {0,2}, u = 1, residual widths W = [0,1] (two slots). Then ρ_resid({0})=1,
    ρ_resid({1})=1, ρ_resid({0,1})=2. The Gale condition HOLDS (0<=1, 0<=1, 2<=2). The base polytope
    is NONEMPTY (the only base point is (1,1)). YET {0,2} is NOT a permutation of any base point, so the
    residual is INFEASIBLE for rem={0,2}. (Direct check: slot 0 has window [max(0,1),1]=[1,1] forcing
    q_0=1, but rem has no 1.)
  - CONCLUSION: any checkable (Gale-style / corridor-majorization) local invariant the greedy carries
    admits states that satisfy it yet dead-end. The clean polymatroid/Gale structure exists at the
    TOP level (start, u=M^0, ρ(A)=∑_{j∈A}M^{j+1}+min{M^0..M^{min A}}) where we only need EXISTENCE of
    SOME base-permutation of Y — never the realisability of an arbitrarily committed `rem`.
</task>

<output_contract>
1. VERDICT: is the impossibility claim CORRECT, or can you exhibit a checkable abstractly-inductively-
   closed sufficient invariant for the forward greedy? If you can, GIVE IT precisely (a closed predicate
   on (rem, u, remaining-widths)) and prove (sketch) it is (a) closed as an abstract hypothesis — assume
   it, take one greedy step from an ARBITRARY predicate-satisfying state, show it holds after — and
   (b) sufficient (implies window-nonempty + completion). If you CANNOT, say so and give the cleanest
   confirmation of the obstruction.
2. Specifically address: is "residual-rem-realisability ⊋ residual-Gale" the right diagnosis? Is the
   {0,2}/u=1/W=[0,1] counterexample sound, and does it generalise (i.e. is the obstruction real, not an
   artefact of one small case)?
3. If the impossibility holds, confirm the alternative: the TOP-LEVEL Rado–Gale existence
   (∀A sumSmallest(|A|,Y)<=ρ(A) ⟹ ∃ assignment) is the correct certificate and does NOT suffer the
   residual gap. Flag any inference vs. fact.
</output_contract>

<grounding_rules>
- This is the achiever (upper-bound) half of an RLCT learning-coefficient theorem; we need ONE feasible
  q (existence), no optimisation. Y is a fixed structured multiset (balanced-split of the c+1 smallest
  widths ⊎ the L-c largest widths, c the achiever); its top-level Gale condition holds unconditionally
  (reduces to an already-proven small-end majorization).
- Lean context: Mathlib has Hall (`Finset.all_card_le_biUnion_card_iff_exists_injective`) but NO
  Gale-Ryser / polymatroid / transportation-feasibility named API. Strong induction on a Multiset is
  clean. An ABSTRACTLY-CLOSED invariant is one provable by assuming it on an arbitrary state (not "the
  reachable ones") and showing one step preserves it — the distinction that matters for a Lean induction.
- "sumSmallest(k,X)" = sum of the k smallest elements of multiset X. ρ_resid submodular verified
  exhaustively; the {0,2} counterexample verified by direct enumeration.
- Withhold deference: I WANT you to find a closed invariant if one exists. If none exists, a crisp
  confirmation of why is equally valuable.
</grounding_rules>
