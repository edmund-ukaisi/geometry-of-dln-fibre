<task>
DLN (deep linear network) RLCT formalisation. We are building an "engine" that resolves the
zero-fibre of the multiplication map mult(A_1,...,A_L) = A_1···A_L to compute the real log-canonical
threshold rlct = (1/2)·minAdm(M), where M=(M_0,...,M_L) are the layer widths and

  minAdm((a)) = 0;  minAdm((a,b)) = a·b;
  minAdm((M_0,M_1,...)) = min_{0<=t<=min(M_0,M_1)} (M_0-t)(M_1-t) + minAdm((t, M_2, ...)).

The resolution is Aoyagi's double induction over layers S=0..L-1 and cleared-pivots J. Each blow-up
step emits one of three CASES on an edge:
- case 1(1): an exponent MERGE into an existing exceptional divisor: its exponent M_{s,k} += J_1·(M^{(S+1)}-J);
- case 1(2): a new pivot SPLIT: new divisor exponent = M_{sk} + J_1·(M^{(S+1)}-J);
- case 2: a new full-block divisor of exponent (M(S)-J)(M^{(S+1)}-J).
The leaf integrand is (product of divisor monomials u_k^{2 M_{s,k}}) × R, where R is a residual that
is EITHER a bounded unit OR a nondegenerate Morse core of transverse rank rho.

DECISION AT HAND (the "L=3 de-risk"). Before we lock the general (S,J) recursion scheme in Lean, we
must know whether the CHART construction for the case-1(1) merge WALLS at depth L>=3, specifically at
M=(2,2,2,2) (minAdm=3). Prior work (a previous expedition, "aoyagi-full") built the per-leaf change
of variables via a "SchurCore front-peel" that is DOCUMENTED as NON-GENERALIZING past depth 2
(the L=2 template does not reach the wall). The current engine instead uses a per-leaf factorization
chartMap = psi ∘ beta, where beta is an EXPLICIT monomial blow-up (|det D beta| = prod |u_k|^{divExp_k - 1})
and psi is a bounded-unit local diffeo, and reads the per-leaf integral via the Mathlib area formula
(needs only the UPPER determinant bound |det D psi| <= hi). A coverage design cert (cert-d3) verified
"no undershoot" for (2,2,2,2) (every admissible rank profile has codim >= minAdm; the recursion's min
= minAdm = 3) and declared coverage "reachable, not walled — a diligent construction via a per-blow-up
LOCAL covering lemma", explicitly NOT via the SchurCore front-peel.

Facts already established this session:
- The TERMINATION side is L-agnostic and proven: a lex measure mu=(L+1-S, layerCap-J, #pending divisors)
  strictly drops on every case (case11 -> component 3, case12/case2 -> component 2, rollover ->
  component 1); no case decreases nothing. So termination does NOT wall at L=3.
- A residual-rank check found the threshold-relevant rho is the TRANSVERSE (on-core) Morse rank, and
  rho >= minAdm held on (2,2,2), (2,2,4), (3,3,4)=8 (tight), and the (2,2,2,2) t=2-reduction leaf (=(2,2,2) core, rho=4>=3).
- At corank>=2 the INTERMEDIATE residual is a coupled recursive DLN core; only a TRUE (fully
  monomialized) leaf has R = ||z||^2 clean.

The specific worry: the genuine NON-reducing L=3 leaf of (2,2,2,2) (the t=1 path: clear 1 pivot in
layer 0, leaving residual (2-1)^2=1 coupled with minAdm(1,2,2)=2) requires resolving a residual that
couples all three layers. Does the case-1(1) merge CHART there wall?
</task>

<output_contract>
1. VERDICT (one line): does the case-1(1) merge chart construction WALL at (2,2,2,2) under the
   psi∘beta + area-formula approach? one of {WALLS / DOES-NOT-WALL / CANNOT-DETERMINE-WITHOUT-X}.
2. The single strongest REASON for that verdict (<=5 sentences), distinguishing what is a KNOWN FACT
   about the SchurCore wall vs your INFERENCE about the new psi∘beta approach.
3. Is the SchurCore front-peel actually NEEDED by the psi∘beta approach, or does the monomial beta +
   area-formula upper-bound sidestep exactly the thing that walled? (<=5 sentences)
4. The single CHEAPEST discriminating test (numeric or 1-chart) that would settle the verdict, stated
   concretely enough to run. Prefer a test on the (2,2,2,2) t=1 leaf.
5. If DOES-NOT-WALL: the one thing most likely to be WRONG about that optimism.
</output_contract>

<grounding_rules>
Flag INFERENCE vs KNOWN FACT explicitly. You do not have the aoyagi-full RR4 source; treat the
"SchurCore non-generalizing past depth 2" as a reported fact, and reason about whether the psi∘beta +
area-formula approach depends on the same mechanism. Do not invent Mathlib lemma names. If the
question cannot be settled without a specific artifact, say so and name the artifact.
</grounding_rules>
