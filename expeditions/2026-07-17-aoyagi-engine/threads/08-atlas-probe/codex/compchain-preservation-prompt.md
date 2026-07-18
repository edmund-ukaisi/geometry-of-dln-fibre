<task>
Decorrelated proof check. I am certifying a preservation invariant for a recursive combinatorial
construction (a resolution-of-singularities chooser). Reason from the definitions below from scratch;
exact reasoning; try to PROVE the claim uniformly in the depth L, and if it is false, exhibit a
minimal counterexample. Do NOT look anything up.

OBJECTS. Depth L≥1. Reduced widths M^(1),...,M^(L+1) (positive integers). Running-min
M(k)=min(M^(1),...,M^(k)) (non-increasing in k). A "divisor" is a vector T=(t^1,...,t^L) in N^L.
Componentwise order: T ≤ T' iff t^j ≤ t'^j for all j. A set of divisors is a CHAIN if every pair is
comparable (≤ or ≥). tilde(T) := min_j t^j.

STATE. The construction proceeds in stages indexed (S,J): current layer S∈{1..L}, cleared count
J with 0 ≤ J < M(S+1)=min(M(S),M^(S+1)). It carries a finite multiset C of divisors. J resets to 0
when S advances to S+1.

TRANSITIONS at (S,J), given the carried chain C (write setTail(T,S,J) for the vector equal to T on
components 1..S-1 and equal to J on components S..L):
  * Look at the occupied levels {tilde(T) : T in C}. Let ℓ = the least level with J+1 ≤ ℓ ≤ M(S)-1
    that is occupied (if any). If such ℓ exists (CASE 1): the "eligible set" is E = {T in C :
    tilde(T)=ℓ}. Note ℓ>J. Pick f = a componentwise-minimum of E (assume it exists — part of the
    contract). Then EITHER
      (1a) mutate f in place: replace f by setTail(f,S,J);  (stay at (S,J))
      (1b) append a new divisor setTail(f,S,J), keeping f;  (advance J or S)
  * If no such ℓ (CASE 2): append a new divisor c = (M^(2),...,M^(S), J,...,J) — i.e. head
    c^i = M^(i+1) for i<S (RUNNING-MIN version: c^i = M(i+1)), tail c^i = J for i≥S. (advance J or S)
  Initial divisors (created at layer 1) are (r,r,...,r) for r=0,...,M(2)-1.

CLAIM TO CERTIFY (uniform in L): if C is a chain before the transition, it is a chain after — in
all three transition types (1a),(1b),(2). Equivalently, total comparability is PRESERVED, given that
the chooser picks the componentwise-MINIMUM f of the eligible set.

ALSO relevant (you may use if true, prove if you rely on it): every carried divisor is
weakly-decreasing (t^1 ≥ t^2 ≥ ... ≥ t^L). And the KEY known seed: at (2,2,2,2) with L=3, node
(S,J)=(3,0), eligible level ℓ=1, eligible set {(1,1,1),(2,1,1)}, minimum (1,1,1); mutating the
minimum gives (1,1,0) which stays comparable to (2,1,1), but mutating the NON-minimum (2,1,1) gives
(2,1,0) which is INCOMPARABLE to (1,1,1). So minimality is load-bearing.

YOUR JOB:
Q1. Prove (or refute with a minimal counterexample) that transition (1a) — mutating the eligible
    MINIMUM f to setTail(f,S,J) — preserves the chain. The crux: for a carried g with g ≤ f, why is
    setTail(f,S,J) still comparable to g? Identify the ONE uniform structural reason (do not grind
    cases). If you need an auxiliary invariant on the carried divisors (beyond weak-decrease and the
    chain) to make it go through, STATE that invariant precisely and argue it is maintained.
Q2. Prove (or refute) that the appended divisor in (1b) and (2) is comparable to every carried
    divisor. For (2), the appended c has the running-min head (M(2),...,M(S)) and tail J.
Q3. State the minimal set of auxiliary invariants (if any) the proof consumes, and for each, one line
    on why it is maintained by all three transitions + layer advance.
</task>

<output_contract>
Q1: the uniform reason (one paragraph), the auxiliary invariant if needed (precise statement), and
the proof for the case g ≤ f. Q2: proof for (1b) and (2) (note if (1b) reduces to Q1). Q3: the
auxiliary-invariant list with maintenance one-liners. If any part is FALSE, give the minimal
(L, widths, state) counterexample explicitly. End with "PROVED uniform in L" or "REFUTED at <instance>"
per lemma. Then 3 lines "MOST LIKELY WRONG". Exact; flag inference vs proof.
</output_contract>

<grounding_rules>
Reason only from the definitions above. Flag any step you INFER vs PROVE. If a transition detail is
ambiguous, state the reading you take. Do not assume the claim is true — actively try to break it
(the minimality is load-bearing, so a wrong pick breaks it; the question is whether the RIGHT pick
always works, uniformly in L and at non-monotone widths e.g. M^(3)>M^(2)).
</grounding_rules>
