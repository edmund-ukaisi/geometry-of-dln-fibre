<task>
Adjudicate two exact convergence/RLCT truth-values, decisively, EITHER direction. Exact algebra
(homogeneous-singularity codimension / negative-power integrability). Withhold assuming any desired
answer; I want your independent derivation.

SETUP (a shell in a deep-linear-network RLCT integral; all integrals over boxes [-1,1]^dim).
A "chain" M = (M0, M1, M2, ..., Mlast) of positive integers, length >= 4.
- minAdm(M): minAdm((M0,M1)) = M0*M1; else min over t in [0,min(M0,M1)] of
  (M0-t)(M1-t) + minAdm((t, M2, ..., Mlast)).  bindingCut t* = LEAST achiever.
- a* = M0 - t*, b* = M1 - t*.  Identity at the binding cut:
  minAdm(M) = a*b* + minAdm((t*, M2, ..., Mlast)).
- The "deep factor" Z is the deep-tail matrix product Z = A2 * A3 * ... * A_{last}, of shape
  M2 x Mlast (row dim M2, col dim Mlast).  Its GENERIC rank rho_Z = min(M2, M3, ..., Mlast)
  (product of the deep widths).  NB rho_Z <= Mlast, so if Mlast < M2 then rho_Z < M2 STRICTLY,
  and a M2 x Mlast matrix can have rank AT MOST Mlast < M2.
- At the "sector" (a specific singular shell) the corank residual factor is, for a FIXED generic Z,
  the "corank weight"
      Wenn(Z; a, b) = INT over A_cor in [-1,1]^{b x M2}  of  det( (A_cor * Z)(A_cor * Z)^T )^{-a/2}
  with a = a*, b = b*   (A_cor is b x M2, so A_cor*Z is b x Mlast, and the gram is b x b).
- Separately there is a "pivot energy" scalar factor w = frobSq(prod of the reduced chain
  (t*, M2, ..., Mlast)) > 0 a.e., whose negative-power integral over the reduced parameters converges
  iff its exponent s satisfies s < minAdm((t*, M2, ..., Mlast)) / 2.

CONCRETE INSTANCE for numbers: M = (2, 3, 3, 2).  Then t* = 1, a* = 1, b* = 2, M2 = 3, Mlast = 2,
rho_Z = min(3,2) = 2, minAdm(M) = 4, minAdm((t*,M2,Mlast)) = minAdm((1,3,2)) = 2, a*b* = 2,
a*+b* = 3 = rho_Z + 1.  (Also test M = (2,4,4,3): t*=1,a*=1,b*=3,M2=4,Mlast=3,rho_Z=3,
minAdm=6, minAdm((1,4,3))=3, a*b*=3, a*+b*=4=rho_Z+1.)

QUESTION 1 (decoupled corank weight).  For a FIXED generic deep factor Z of shape M2 x Mlast with
Mlast < M2 (so rank(Z) = rho_Z = Mlast < M2), what is the exact convergence condition on (a,b) for
Wenn(Z; a, b) to be FINITE?  Is it  a + b <= M2  (using the row dimension M2), or  a + b <= rho_Z
(using the true rank)?  In particular, for M=(2,3,3,2) (a=1,b=2,Z is 3x2, rank 2): is Wenn finite or
(log-)divergent?  Give the exact local model at the singular locus and the codimension.

QUESTION 2 (coupled sector convergence to the RLCT threshold).  The full sector integrand couples the
corank weight with the pivot energy w: schematically, on the full-rank set, the freed-corner integral is
bounded by an ATOM  det((A_cor Z)(A_cor Z)^T)^{-a/2} * Cr * w^{-(c' - a b/2)}  AND by a flat BOUNDED
brick  w^{-c'} ; a weighted-geometric-mean (theta in [0,1)) interpolation gives
det^{-theta*a/2} * const * w^{-(c' - theta*a*b/2)}.  Integrating A_cor gives a corank weight at exponent
theta*a, and w at exponent c' - theta*a*b/2 (integrable iff c' - theta*a*b/2 < minAdm(reduced)/2).
   For M=(2,3,3,2) with the rank-deficient Z (rho_Z = 2, a=1,b=2, so a+b = rho_Z + 1):
   (2a) Over what deep DIMENSION does the theta-scaled corank weight INT det^{-theta*a/2} converge --
        is the finiteness condition  theta*a < M2 - b + 1  (row dim), or  theta*a < rho_Z - b + 1
        (true rank)?  With a=1,b=2: rho_Z - b + 1 = 1, M2 - b + 1 = 2.
   (2b) Given (2a), is the COUPLED sector integrand finite for EVERY c' < minAdm(M)/2 = 2 (by choosing
        theta < 1 per c')?  Give the exact interval of admissible theta as a function of c', and whether
        it is nonempty for all c' < 2.  Does the sup over theta<1 of the reachable c'-threshold EQUAL
        minAdm(M)/2, or fall short?

Distinguish clearly: does the convergence key off M2 (the row dimension) or off rho_Z (the true rank of
the deep factor)?  This distinction is the crux.
</task>
<output_contract>
- Q1: VERDICT (finite / divergent for M=(2,3,3,2)) + the exact convergence condition on (a,b) in terms
  of M2 vs rho_Z, with the local model + codimension. FACT vs INFERENCE separated.
- Q2a: the exact theta-scaled corank-weight finiteness condition (M2 vs rho_Z form).
- Q2b: VERDICT whether the coupled sector reaches minAdm(M)/2 for M=(2,3,3,2); the admissible-theta
  interval as a function of c'; whether sup = minAdm/2 or falls short.
- Short exact-arithmetic / symbolic reasoning ok; no floating rank claims as certificates.
</output_contract>
<grounding_rules>
- Exact algebra only for the verdicts (rpow integrability / homogeneous codimension). Rank of an
  M2 x Mlast product is <= min of the widths; do not assume full row rank M2 when Mlast < M2.
- Report the M2-vs-rho_Z distinction explicitly. If you use Monte-Carlo, label it a guide, not a proof.
</grounding_rules>
