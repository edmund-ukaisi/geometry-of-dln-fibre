<task>
Decorrelated proof check on ONE lemma of a recursive combinatorial construction. Reason from the
definitions from scratch; try to PROVE it uniformly, or give a minimal counterexample. Exact reasoning.

SETUP. Depth L. Reduced widths M^(1..L+1); running-min M(k)=min(M^(1..k)) (non-increasing). A divisor
is T=(t^1..t^L)∈N^L. tilde(T)=min_j t^j. Componentwise order ≤. The construction proceeds in stages
(S,J): current layer S, cleared count J (0≤J<M(S+1)=min(M(S),M^(S+1))), J resets to 0 when S advances.
It carries a finite set C of divisors, and maintains (all verified as invariants):
  - WeakDec: every T∈C is weakly decreasing (t^1≥...≥t^L).
  - FlatTail(S): every T∈C has t^S=t^{S+1}=...=t^L (tail from the current layer is constant);
    combined with WeakDec, tilde(T)=t^S=t^L (the tail value = the level).
  - WidthBound: every T∈C has t^i ≤ M(i+1) for all i.
Transitions create/mutate divisors so tails are written to the current J (a divisor "at level λ" has
tail = λ). Layer-1 creates (r,...,r) for r=0..M(2)-1.

A "case-1 node" is a stage (S,J) where the least OCCUPIED level ℓ with J+1 ≤ ℓ ≤ M(S)-1 exists (occupied
= some carried divisor has tilde = ℓ), and there is NO occupied level strictly between J and ℓ (the
"run-gap"): {T∈C : J < tilde(T) < ℓ} = ∅.

LEMMA TO CERTIFY (STEP1, verified with 0 counterexamples on 14 instances incl. width-drop bottlenecks):
  At every case-1 node, EVERY divisor x∈C with tilde(x)=ℓ dominates EVERY divisor y∈C with
  tilde(y) ≤ J:  x ≥ y  (componentwise).
The tail part is immediate (x^i=ℓ > J ≥ tilde(y)=y^i for i≥S). The HEAD part (x^i ≥ y^i for i<S) is
the content.

CONTEXT that MAY matter: the ancestry-blind version is FALSE — "for any two carried divisors at
adjacent occupied levels lo<hi, every level-hi divisor ≥ every level-lo divisor" has counterexamples at
width-drop bottlenecks (e.g. after a Case-2 append introduces c=(M(2),M(3),0)=(2,1,0) which is
incomparable to a carried (1,1,1) at M=(2,2,1,1)). So STEP1 must USE that (S,J) is a case-1 node
(ℓ = first occupied above the CURRENT cleared count J, with the run-gap), not merely any adjacent
occupied pair. The carried divisors coexisting at a state come from a single branch of a blow-up tree.

YOUR JOB:
Q1. Prove STEP1 uniformly in L, OR give a minimal counterexample (L, widths, reachable state).
Q2. If the proof needs an auxiliary invariant beyond WeakDec/FlatTail/WidthBound/run-gap (e.g. a
    coexistence/ancestry property saying which divisors can be simultaneously carried), STATE it
    precisely and argue it is maintained. Name the MINIMAL such hypothesis.
Q3. Does STEP1 require the chosen divisor to be the componentwise-MINIMUM of level ℓ, or does it hold
    for EVERY level-ℓ divisor? (Verified: every one. Confirm or refute.)
</task>

<output_contract>
Q1: a uniform proof of the head part, OR a minimal counterexample. Q2: the minimal auxiliary invariant
(precise) + maintenance, if needed. Q3: min-only vs all. End "PROVED uniform in L" or "NEEDS hypothesis
<X>" or "REFUTED at <instance>". Then 3 lines MOST LIKELY WRONG. Flag inference vs proof.
</output_contract>

<grounding_rules>
Reason only from the definitions. Flag INFER vs PROVE. If you need the branch/ancestry structure, say so
and state the weakest form. Actively try to break STEP1 at bottlenecks.
</grounding_rules>
