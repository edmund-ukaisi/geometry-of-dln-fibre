<task>
Adjudicate a sharp real-log-canonical-threshold (RLCT) / local-integrability question from a
deep-linear-network fibre-geometry calculation. This is an INDEPENDENT red-team: argue whichever way
the algebra actually goes. No repo access; everything you need is below. Use exact algebra
(codimension / radial-exponent thresholds; a smooth-point Jacobian if useful). Monte-Carlo only as a
guide.

SETUP (L=0 leaf, one width triple M=(M0,M1,M2)):
  M = (3,3,7), and a "cut" index u=2. Define a = M0-u = 1, b = M1-u = 1, d = M2-b = 6.
  - Q_p = z is a u x M2 = 2 x 7 real matrix (a free box, entries in [-1,1]).   ["pivot block"]
  - Q_b = A_cor is a b x M2 = 1 x 7 real matrix (a free box).                    ["corank block"]
  - hsQ := (Q_p ; Q_b) stacked = (u+b) x M2 = 3 x 7 = M1 x M2.
  - Front variables (also free boxes): T = [P | B] an M0 x M1 = 3 x 3 matrix, plus a transverse block.

There is a "shell-j" restriction on the outer variables (Q_p, Q_b): shell-j = { hsQ has exactly j
singular values below a small threshold eps } (weakEigCount = j). Here the shell index is j=2.
NOTE: b=1 < j=2 ("b<j regime"). Since Q_b has only b=1 row, on shell-2 the corank block can account
for at most ~b of the small singular values; the remaining j-b = 1 small singular value is forced
INTO Q_p, i.e. sigma_min(Q_p) -> 0 (Q_p, a 2x7 matrix, drops to rank 1). Equivalently hsQ drops to
rank 1 (corank 2 as a 3-row matrix), with Q_b generically O(1).

TWO CANDIDATE OBJECTS (both arise; please treat both):
 (U)  UNDECORATED shell object:
        I_j(c') = int_{(Q_p,Q_b) box, shell-2}  [ int_{T box} frobSq(T . hsQ)^{-c'} dT ]  d(Q_p,Q_b).
 (D)  DECORATED object (after a change of variables on the chart {rank Q_b = b}: write
        Q_b = D[I_b | X], Q_p = [U | U X + W], W := Q_p . N (u x d) the "incidence coordinate",
        integrate out part of the front producing det(Q_b Q_b^T)^{-a/2} and shifting c' -> q = c' - ab/2):
        G(c') = int_{(U,W,X,D), shell}  det(Q_b Q_b^T)^{-a/2} * [ int_{front} (||H~||^2 + ||Y.W||^2)^{-q} ]
        with H~ in R^{u b}=R^2, Y=(P;C) in R^{M0 x u}=R^{3x2}, W in R^{u x d}=R^{2x6}.
 A comparator "decLoss" = commonDivisor^2 * ||Q_p||^2_F is asserted (by the operator) to stay O(1) on
 the sigma_min(Q_p)->0 locus (only the smallest singular value of Q_p vanishes; ||Q_p||_F stays O(1)).

KNOWN / GIVEN (you may use, but verify if load-bearing):
  - carrierThreshold T1 = minAdm(M)/2, minAdm(M)=min_r[(M0-r)(M1-r)+r M2]. For (3,3,7): minAdm=9, T1=4.5.
  - For a FIXED matrix Q (M1 x M2) of corank k, int_{T box} frobSq(T.Q)^{-c'} dT converges iff
    c' < M0*(M1-k)/2 (the front-vanishing / T->0 locus dominates), and blows up as the small singular
    values of Q shrink.

THE SHARP QUESTIONS:
 1. On the b<j / sigma_min(Q_p)->0 locus of the (3,3,7),u=2,j=2 probe, what is the exact local
    integrability threshold in c' of the inner (front) integral POINTWISE (as a function of the outer
    point), and what is it INTEGRATED (i.e. of the full object I_j / G, integrating the outer
    variables too)? Give both, with the exact radial-exponent / codimension bookkeeping.
 2. Does the object (U and/or D) DIVERGE for some c' in [3, 4.5) (i.e. below T1), or does it stay
    finite up to c' = 4.5? Decide, with a certificate. If it diverges, give the exact threshold and
    the binding stratum. If it stays finite, give the mechanism that absorbs the pointwise blow-up.
 3. Does the shell restriction (which forces sigma_min(Q_p)->0) REMOVE whatever would otherwise absorb
    the blow-up, relative to the off-shell object? Address the role of the singular-value measure /
    Jacobian on the small singular values, and whether a subset-monotonicity argument
    (shell domain is a subset of the full box, same nonnegative integrand) is valid here.
 4. Is the pointwise threshold (if lower than 4.5) actually realized as a divergence of the integrated
    object, or is it a pointwise-only artifact?
</task>

<output_contract>
  Section A: the exact POINTWISE inner threshold on the sigma_min(Q_p)->0 locus (with the codim/exponent).
  Section B: the exact INTEGRATED threshold of I_j (object U) and of G (object D) -- one number each in c',
             with the binding stratum and the radial exponent that certifies it.
  Section C: verdict on Q2/Q3/Q4 -- does it diverge on [3,4.5) or not, and WHY (the absorbing mechanism
             or the divergence certificate). Explicitly rule on the subset-monotonicity argument.
  Keep each section tight. Put a one-line SUMMARY VERDICT at the very top: "FINITE to 4.5" or
  "DIVERGES on [x,4.5)" with x.
</output_contract>

<grounding_rules>
  Flag every step as [FACT] (exact algebra you performed) vs [INFERENCE] (heuristic/expectation).
  Do not assume the answer I want -- I have deliberately withheld my own tentative conclusion.
  If the honest algebra says it diverges below 4.5, say so and give the certificate; if it says finite
  to 4.5, say so and give the absorbing mechanism. Be explicit about where the singular-value measure
  on the small singular values enters, since that is the crux of the pointwise-vs-integrated distinction.
</grounding_rules>
