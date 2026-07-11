<task>
Adversarial audit of a corrected proof-architecture for a finiteness integral. HUNT for where it
fails; do not rubber-stamp. Context is self-contained below (no repo needed).

SETUP. For a "chain" M=(M0,M1,...,ML) of positive integers (arity L+1 >= 3), define the layer-peel
minimum
    minAdm(M) = min over 0<=t<=min(M0,M1) of [ (M0-t)(M1-t) + minAdm(redChain(t,M)) ],
    redChain(t,M) = (t, M2, M3, ..., ML),   base cases: minAdm(a)=0, minAdm(a,b)=a*b.
peelCharge(t) = (M0-t)(M1-t) = a*b with a=M0-t, b=M1-t. A "binding cut" is an argmin t*, giving
minAdm(M) = peelCharge(t*) + minAdm(redChain(t*,M)).

The analytic target ("innerCorankDescent"): an integral over a BOUNDED box of variables
(A' the deep matrix tuple, x=(P,B12,C) front blocks, Gamma an a-by-b block ranging over a BOUNDED
box), of freedSchurLoss^{-c'}, where
    freedSchurLoss = |P*Qtp|^2 + |C*Qtp + Gamma*Qb|^2,   Qtp = Qp + P^{-1}B12 Qb,
    Qtild = prod(tailChain M) A'  is M1-by-ML, row-split into Qp (t rows) and Qb (b rows);
    Qp,Qb are row-blocks of A'1 * Z with Z = A'2...A'_{L+1} the deeper product (Qp,Qb SHARE Z).
The claim to certify: this integral is FINITE for every c' < (1/2)minAdm(M).

TWO ROUTES were considered:
 - ATOM-FIRST (REJECTED): integrate Gamma over ALL of R^{ab} first, producing a factor
   det(Qb Qb^T)^{-a/2} times a shifted core, then hand to a plain induction hIH(redChain) at
   exponent c'-ab/2. This was shown FATALLY wrong: the full-space Gamma integral discards the
   bounded-Gamma cutoff and OVER-charges the Qb-degeneration. Concrete: M=(2,2,1,2), a=b=1,
   minAdm=2, c'=3/4<1. With loss ~ alpha^2 + (Gamma*beta)^2: bounded-Gamma integrating alpha first
   gives |Gamma*beta|^{-1/2} (integrable in Gamma and beta); full-space atom gives |beta|^{-1}
   (log-divergent). So the atom route is dead.
 - NATIVE BOUNDED-BOX (S,J) BLOW-UP (the CORRECTED route, to be audited): keep Gamma bounded in
   its box; resolve the coupled corner {w=0}/rank-drop of freedSchurLoss JOINTLY by an iterated
   monomial (toric / Aoyagi (S,J)) blow-up to a normal-crossings form
       loss ~= (monomial in exceptional radii u_i)^2 * (unit U, U>0 bounded below),
   with measure prod|u_i|^{p_i} du; then (only after the decoration is discharged into the u-monomial)
   hand a PLAIN reduced integral to hIH(redChain). The design asserts one native peel suffices
   before plain hIH (no "decorated IH" carrying the determinant).

FACTS I have established by exact algebra (take as given):
 (F1) charges ADD: along the achieving recursion the peelCharges sum to minAdm. Verified for
      (3,3,3,4)=7 [charges 4,3,0], (4,4,4,4)=11 [charges 4,3,4], (2,4,4,5)=7 [3,4,0],
      (3,3,3,3,4)=6 [1,2,3,0], (4,4,4,4,4)=10 [1,2,3,4]. Also every FIRST-LEVEL cut t has
      Mval(t)=peelCharge(t)+minAdm(redChain(t)) >= minAdm(M) (the achiever is the WORST/lowest).
 (F2) the nD corner homogeneous rule: for U_i>0 bounded below,
      INT prod|u_i|^{p_i} (sum_i u_i^2 U_i)^{-c'} du over a box near 0 converges
      <=> c' < (1/2) sum_i (p_i+1). For the (3,3,3,4) front corner p0=3 (Gamma-block dim ab=4),
      p1=2 (deeper dim 3): threshold (3+2+2)/2 = 7/2 = (1/2)minAdm. Independent divisors would
      undershoot: min((p0+1)/2,(p1+1)/2)=3/2. The chart u1=u0*tau and its reciprocal u0=u1*s both
      give 7/2; both are needed to cover the corner.

WHAT TO HUNT (the corrected route's residual risks). Work a DEEP multi-peel chain, e.g. (4,4,4,4)
[minAdm 11, front peel a=b=2 charge 4, then redChain (2,4,4) peel a=1,b=3 charge 3, then NONtrivial
terminal (1,4) charge 4], and/or (4,4,4,4,4). For that chain:

 Q_A. Does the NATIVE layer-by-layer (S,J) blow-up (front peel, then hIH on redChain, recursively)
      actually reproduce a SINGLE normal-crossings monomial whose exponents give sum(p_i+1)=minAdm,
      with ALL units U_i bounded below on a FINITE chart cover? Or is there a chart/branch where a
      deeper exceptional divisor DECOUPLES from the front divisor (so the effective threshold drops
      to a "min" like 3/2, not the coupled sum), because the layer-peel resolves collapses
      SEQUENTIALLY whereas Aoyagi's resolution is SIMULTANEOUS? Give the specific chart if it fails.

 Q_B. Is the reduced integral handed to plain hIH truly PLAIN (loss = redChain-product frobSq only,
      at exponent c'-ab/2, threshold (1/2)minAdm(redChain)), or does a RESIDUAL weight leak from the
      front corner into the reduced integral (a determinant-like factor, a Jacobian power not
      absorbed by the u-monomial), which at the zero-slack binding cut (c'-ab/2 -> (1/2)minAdm(redChain))
      would break plain hIH and force a DECORATED induction? Decide: one native peel + plain hIH, or a
      decorated IH.

 Q_C. Does the native bounded-box corner CoV EXIST as a clean, measurable, finite-cover change of
      variables with explicitly bounded Jacobians (NOT the rejected full-space atom), including the
      reciprocal charts and the rank-deficient (rank Qb = r < b) branches (where Gamma contributes
      only a*r active directions and the missing a(b-r) must come from rank-normal coordinates)? Or
      is there an obstruction (an uncontrolled |det|^{-1} from a pivot inverse with no compensating
      radial variable) that survives into the corrected route?

 Q_D. Is this a genuine FINITENESS obstruction (the integral is actually +infinity somewhere below
      (1/2)minAdm), or only a construction/labour gap (finite, but the clean CoV theorem is unbuilt)?
      The (2,2,1,2) bounded integral converges at c'=3/4, suggesting finiteness holds. Pressure-test
      whether finiteness up to (1/2)minAdm can FAIL for some deeper chain / rank-deficient branch.
</task>

<output_contract>
Answer Q_A, Q_B, Q_C, Q_D in that order. For each: a one-word verdict
(SOUND / GAP / FATAL / UNPROVEN), then the derivation. Mark each bullet [DERIVED] (you computed it),
[INFERRED] (structural argument), or [ASSUMED]. End with: the SINGLE cheapest discriminating
computation that would settle the deepest open risk, and whether you found any genuine finiteness
obstruction (Q_D) vs a labour gap. Be concrete on (4,4,4,4); give the specific failing chart if one exists.
</output_contract>

<grounding_rules>
Do not accept the design's framing as correct; find the failure if there is one. Distinguish a
FINITENESS obstruction (integral = +inf below threshold) from a CONSTRUCTION gap (finite, theorem
unbuilt) — this distinction is load-bearing. Keep facts (F1),(F2) as given but test whether they
IMPLY the corrected route closes. Do not paste code as proof; reason in exact algebra.
</grounding_rules>
