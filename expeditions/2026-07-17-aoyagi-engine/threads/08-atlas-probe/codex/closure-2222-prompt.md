<task>
Decorrelated second-mathematician check on a resolution-of-singularities construction (Aoyagi 2023,
"learning efficiency of deep linear networks", Section 5) at ONE specific instance. Reason from the
construction below from scratch, exact integer reasoning only; do NOT look anything up.

SETUP. Depth L=3, reduced widths (M^1,M^2,M^3,M^4)=(2,2,2,2). Variable matrices C^(1),C^(2),C^(3),
each 2x2, all entries independent reals, at the origin. Ideal J = entries of the product
P = C^(1)C^(2)C^(3) (2x2). Target: the real log-canonical threshold lambda_0(J) at 0. Known:
minAdm(2,2,2,2) = 3 (so the claim is lambda_0 = 3/2), where
  minAdm(M0)=0; minAdm(M0,M1)=M0*M1;
  minAdm(M0,M1,M2,...) = min over 0<=t<=min(M0,M1) of (M0-t)(M1-t) + minAdm(t,M2,...).

AOYAGI'S CONSTRUCTION (transcribed from pages 14-22; take as given). Double induction on (S,J).
Each exceptional divisor coordinate u carries a FULL vector T=(t^1,...,t^L) in N^L, running min
tilde_t=min_j t^j, and a Jacobian exponent M (its divisor power is M-1). A "total comparability"
invariant (Def 4, p.14/15) holds THROUGHOUT: every pair of T-vectors is comparable (T<=T' or T>=T'
componentwise). Creation/update rules:
  * Layer S=1 produces, for each rank level r, a divisor with T=(r,r,...,r) (all L components r),
    M=(M^1-r)(M^2-r).
  * CASE 1 (partial run of equal b's above J): the b-chain b_i = prod_{tilde_t=i-1} u * b_{i-1}
    (divisibility chain b_1|b_2|...) has b_{J+1}=...=b_{J+J1} != b_{J+J1+1}, with a NONEMPTY set of
    divisors at level tilde_t=J+J1. FIX the divisor u with tilde_t=J+J1 whose FULL T is <= (Def 4)
    every other divisor at that same level (the p.15 minimality tie-break). Then two charts:
      - Case 1(1): mutate that fixed u: set tail t^(S..L):=J (head t^(1..S-1) unchanged), add
        M += J1*(M^{S+1}-J). Does not advance J.
      - Case 1(2): create a NEW u inheriting the fixed parent's head t^(1..S-1), tail t^(S..L):=J,
        M = parentM + J1*(M^{S+1}-J). Advance J (or S).
  * CASE 2 (full run to M(S)): create a new u with head t^(i):=M^{i+1} (i<S, RESET to widths),
    tail t^(S..L):=J, M=(M(S)-J)(M^{S+1}-J). Advance J (or S).  [M(S)=min{M^s:s<=S}]
Terminal (S=L+1): ideal = <diag(b_1,...)>. LCT candidate = (1/2)*min{ M : tilde_t=0 }, with
  M = (M^1-t^1)(M^2-t^1) + sum_{j=2}^L (t^{j-1}-t^j)(M^{j+1}-t^j).

KNOWN (given): at (2,2,2,2) a Case-1 node arises with S=3, J=0, J1=1 whose selected level tilde_t=1
holds TWO divisors: A=(1,1,1) (born at layer 1, rank level 1) and B=(2,1,1) (born at layer 2, Case 2,
head reset to M^2=2, tail=J=1). Both have tilde_t=1; they are distinct and comparable (A<B).

YOUR QUESTIONS:

Q_A (COVERAGE/closure). Run the construction at (2,2,2,2) to termination (following the chart
branches). Enumerate the terminal tilde_t=0 divisors' T-vectors and their M-values. Do the emitted
charts cover a neighbourhood of {P=0} near 0 (every nearby zero has a lift)? Adversarially hunt for a
coverage GAP or an uncovered stratum. Report the terminal atlas and the coverage verdict (scoped).

Q_B (MINIMUM / no undershoot). Is min over emitted tilde_t=0 divisors of M equal to 3? Hunt
adversarially for ANY emitted tilde_t=0 divisor with M < 3 (an undershoot). Report the min, the
achieving profile(s), and whether any undershoot exists.

Q_C (TIE-BREAK LOAD-BEARING — the key question). At the node (S,J,J1)=(3,0,1), Def-4 selects A=(1,1,1)
over B=(2,1,1). Determine the CONSEQUENCE of the choice:
  (c1) If the construction (WRONGLY) fixed B=(2,1,1) instead of A, trace what happens: apply Case 1(1)
       to B (tail t^(3):=0 -> (2,1,0)); the OTHER divisor A=(1,1,1) remains at level 1. Is the
       resulting T-vector set still TOTALLY COMPARABLE (every pair <= or >=)? Compare (2,1,0) with
       the remaining (1,1,1). Then do the same for the CORRECT choice (fix A -> (1,1,0), remaining B).
  (c2) Does the wrong choice change the emitted tilde_t=0 MINIMUM (still 3?), or does it instead break
       the total-comparability invariant / the divisibility chain (i.e. the resolution is no longer a
       valid monomialization)? State precisely WHAT the tie-break protects: the numerical minimum, or
       the structural invariant (and hence coverage).
</task>

<output_contract>
Three sections Q_A, Q_B, Q_C. For Q_C be explicit and show the componentwise comparisons
(2,1,0) vs (1,1,1) and (1,1,0) vs (2,1,1). End with a one-line verdict: "the tie-break protects
X" where X is either "the numerical minimum" or "the comparability invariant / valid principalization
(coverage), with the minimum unchanged either way". Then 3 lines "MOST LIKELY WRONG" naming your least
certain inference per question. Exact arithmetic; flag inference vs computation.
</output_contract>

<grounding_rules>
Reason only from the construction above + elementary exact algebra. Flag where you INFER vs COMPUTE.
If a step (e.g. the S=1->2 boot, or divisor persistence across layers) is not forced by the
transcription, say so rather than invent. Do not appeal to known results for the value.
</grounding_rules>
