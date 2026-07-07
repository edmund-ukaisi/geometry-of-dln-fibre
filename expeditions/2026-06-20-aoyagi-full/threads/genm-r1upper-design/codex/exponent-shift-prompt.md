<task>
Red-team an analytic design for a real-log-canonical-threshold (RLCT) lower bound of a
deep-linear-network zero-product locus. Judge whether the mechanism is SOUND and whether the
from-scratch route is BOUNDED LABOUR or hits a genuine new obstruction. Do NOT rubber-stamp.

SETTING (exact). Widths M = (M_0, ..., M_L), integer >= 0. Free real matrices A_s of size
M_s x M_{s+1}, s=0..L-1, each entry in the box [-1,1] (a neighbourhood of the all-zero tuple).
Product P(A) = A_0 A_1 ... A_{L-1} (size M_0 x M_L). ||.|| = Frobenius norm. We must prove:

   I(c') := ∫_{box} ||P(A)||^{-2c'} dA  <  ∞    for all c' < (1/2) minAdm(M).

Here minAdm(M) is the minimal admissible codimension, PROVEN equal to the layer-peeling recursion
   minAdm(M_0,...,M_L) = min_{0<=t<=min(M_0,M_1)} [ (M_0-t)(M_1-t) + minAdm(t, M_2,...,M_L) ],
   base minAdm(a,b) = a*b.
This is Aoyagi's exact learning coefficient for DLNs (Aoyagi 2023, "learning efficiency of
multiple-layered linear networks"), λ = (1/2) minAdm. So I(c')<∞ for c'<λ IS the RLCT lower bound.

WHAT IS ALREADY BUILT (and its LIMIT). A banked "iterated-fibre" lemma bounds, for FIXED Y,
   ∫_{X in box} ||X Y||^{-2c'} dX  <=  C(p) * ||Y||^{-2c'},   valid only for c' < p/2  (p = rows of X),
and it PRESERVES the exponent c' on Y (same c' on the residual). Iterating over layers therefore caps
the reachable c' at min_s (width_s)/2 — the SINGLE most-binding boundary — undershooting the SUM
(1/2)minAdm by up to a factor of 2. Paradigm failure: M=(3,3,3,3): minAdm=6 so target c'<3, but the
exponent-preserving peel reaches only c'<3/2. This is the wall.

PROPOSED MECHANISM ("shifted-exponent arity peel"). Cover the box by rank-cut charts of the FRONT
factor A_0 (pivot on an invertible t x t block; Schur-reduce A_0 to blockdiag(A0^[t], Γ) via
unit-triangular Jacobian-1 changes of variables Q1 A0 Q2, so Γ = (M_0-t)x(M_1-t) corank block).
Radially blow up Γ = z·V (z>=0, V on the unit sphere), Jacobian z^{a-1} dz dσ(V), a=(M_0-t)(M_1-t).
Block-diagonality gives
   ||A_0 Q||^2  ≍  ||Q_top||^2 + z^2 ||V Q_bot||^2  =: g^2 + z^2 h^2,
where g = ||Q_top|| is the tail chain of widths (t, M_2,...,M_L) (an (L-1)-factor product) and
h = ||V Q_bot|| is a spectator. Do the z-integral EXACTLY:
   ∫_0^∞ (g^2+z^2 h^2)^{-c'} z^{a-1} dz = (1/2)B(a/2, c'-a/2) · h^{-a} · g^{-2(c'-a/2)}   for c' > a/2.
So the tail integrand is g^{-2 c''} with SHIFTED exponent c'' = c' - a/2 = c' - (1/2)(M_0-t)(M_1-t),
times a spectator h^{-a}. Recurse on the tail chain (t,M_2,...,M_L) at the reduced budget c''.
Chart-t converges iff c'' < (1/2)minAdm(t,M_2,...), i.e. c' < (1/2)[(M_0-t)(M_1-t)+minAdm(t,...)];
box = union of charts => converges up to the MIN over t = (1/2)minAdm(M). Base L=1: single free
t x M_L matrix, ∫ ||X||^{-2c'} finite iff c' < (t·M_L)/2 = (1/2)minAdm(t,M_L).

The spectator h = ||V Q_bot||: claimed benign because if Q_bot has full row rank then
h >= σ_min(Q_bot) > 0 on the sphere (so h^{-a} bounded); h→0 only on a deeper tail rank-drop stratum
already inside minAdm(t,M_2,...).
</task>

<grounding_rules>
- Reason from the stated math only. If you need a fact not given, name it as an assumption.
- Keep inference separate from assertion. Flag anything you cannot verify from the setup.
- The 1-D Beta integral, the minAdm recursion, and the reach comparison are given as facts (verified
  by exact algebra by the requester); focus your scrutiny on the MECHANISM's soundness and gaps.
</grounding_rules>

<output_contract>
1. VERDICT: is the shifted-exponent peel a SOUND resolution route (SOUND / SOUND-WITH-GAPS / BROKEN)?
   And is completing it BOUNDED LABOUR or does it hit a genuine NEW obstruction (not mere labour)?
2. The single WEAKEST point in the mechanism. Be concrete: name the step and the exact condition that
   could fail. Candidates to weigh: (i) the spectator h^{-a} at L>=3 where g and h SHARE the deeper
   factors A_2.. (are g,h jointly resolvable without double-counting codim?); (ii) the Q_2 coordinate
   change mixing into the tail measure (is the tail still a clean box/product after Q_2^{-1}?);
   (iii) the covering by rank-cut charts (does the union of charts actually exhaust the box, and is the
   MIN-over-t the correct combination — could a chart the design omits diverge earlier?);
   (iv) whether the two z-integral regimes (c'>a/2 vs c'<a/2) both stay controlled up to (1/2)minAdm.
3. For the weakest point: the single cheapest DISCRIMINATING test (exact-algebra / small case) that
   would confirm-or-kill it.
4. Does this differ from Aoyagi's own recursive-blow-up proof in a way that INTRODUCES risk, or is it
   the same resolution re-organised as an arity recursion? One paragraph.
</output_contract>
