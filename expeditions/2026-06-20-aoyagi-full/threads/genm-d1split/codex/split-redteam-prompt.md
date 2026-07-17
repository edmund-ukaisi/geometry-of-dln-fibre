<task>
Red-team an exact-algebra convergence question about an RLCT (real log canonical threshold) box integral arising in a deep-linear-network fibre computation. I need an INDEPENDENT check of whether a proposed two-branch domain-split covers a specific degeneracy corner, or whether a positive-measure region escapes. Give me your own analysis; do not just agree.
</task>

<setup>
Fix integers u>=1, a>=u, b=1, q>=1 (a "corank-one, a>=u" cell). Real matrices:
  P : u x u, restricted to an invertible box (entries in [-1,1], P invertible).
  B12 : u x 1 ;  C : a x u ;  Gamma : a x 1 (in a fixed finite box).
  A' : deep tail parameters producing a tail product Q (dims (u+1) x q); write
       Q_p = top u rows (u x q), Q_b = bottom row (1 x q).
Define the "pivot"  Qtil := Q_p + P^{-1} B12 Q_b   (u x q).
Define w := frobSq(P * Qtil)   (pivot energy; frobSq = sum of squares of entries).
Define the loss  L := w + frobSq(C*Qtil + Gamma*Q_b).
The target integral (must be finite for every real c' < minAdm(M)/2):
  I = \int_{A'} \int_{P,B12,C} \int_{Gamma}  L^{-c'}  dGamma d(P,B12,C) dA'.
Concrete smallest case: the width vector M=(4,3,2), cut t=2, giving u=2,a=2,b=1,q=2, and the tail is a
SINGLE free layer A1 (3x2) so Q=A1, Q_p (2x2) and Q_b (1x2) are FREE boxes. Here minAdm(M)=6 so the
requirement is finiteness for all c' < 3. Exact-integer fact: minAdm((2,3,2))=4.

Two banked "inner-Gamma" lemmas are available (each bounds the innermost \int_Gamma L^{-c'} dGamma,
pointwise in the outer variables, and each REQUIRES the pivot energy w>0):
  (BOUNDED)  \int_Gamma L^{-c'} dGamma  <=  w^{-c'} * vol(box).   [drops the corank term entirely]
  (PEEL)     \int_Gamma L^{-c'} dGamma  =  ||Q_b||^{-a} * const * (w + frobSq(C*Qtil*(I-Proj_{Q_b})))^{-(c'-a b/2)}
             [gammaAtom: integrates Gamma against Q_b; requires w>0, Q_b != 0, a*b/2 < c'].
A "front-collapse" reduction is available: \int_{P,B12}\int_{A'} frobSq([P|B12]*Q)^{-c'} is finite iff
c' < minAdm((u,M1,M2,...))/2  (it reduces frobSq([P|B12]*Q)=w to a shorter chain; note [P|B12] is u x M1).

The PROPOSED proof splits the outer domain by the conditioning sigma_min(Qtil):
  - sigma_min(Qtil) < delta  ("ill-conditioned")  -> use (BOUNDED), then reduce w via front-collapse.
  - sigma_min(Qtil) >= delta  ("well-conditioned") -> use (PEEL); the emitted Gram is bounded by a
    delta-power constant, and the residual w-power reduces via front-collapse.
</setup>

<questions>
1. For M=(4,3,2), c' in the open interval (2,3): consider the region where Qtil -> 0 with BOTH singular
   values of Qtil comparably small (Qtil ~ eps*V, V a fixed full-rank direction), Q_b ~ O(1). Compute the
   local scaling in eps of: (i) the true inner double integral \int_C \int_Gamma L^{-c'}; (ii) the BOUNDED
   bound w^{-c'}; and then multiply by the measure of the shell {||Qtil|| ~ eps} and integrate radially.
   Which of {true integral, BOUNDED-branch bound} converge as eps->0 for c' in (2,3)?
2. This region has sigma_min(Qtil) small, so the split routes it to the BOUNDED branch. Does that branch's
   contribution converge there for c' in (2,3)? If not, is this a positive-measure region (recall Q_p is a
   FREE 2x2 box for M=(4,3,2), so Qtil is a free coordinate with nonzero density at 0)?
3. If a region escapes both branches, what is the minimal native mechanism that WOULD close it (be specific:
   a radial/polar blow-up in which variable? on the resulting sphere, is the pivot energy w=frobSq(P*Qtil)
   bounded below, and why?), and does that mechanism belong to either of the two branches as dispatched?
</questions>

<output_contract>
For Q1: give the eps-exponents explicitly (inner-integral exponent, shell-measure exponent, net radial
exponent) and the convergence condition on c' for BOTH the true integral and the BOUNDED bound. For Q2:
a yes/no on whether the BOUNDED branch converges on that region for c' in (2,3), with the measure argument.
For Q3: name the blow-up variable and whether w is bounded below on the sphere. Flag any place my setup is
wrong or my framing hides an assumption.
</output_contract>

<grounding_rules>
Exact algebra only for anything load-bearing (radial exponent counting, shell measure dimension). You may
use a scalar/Gaussian toy to guide but state convergence via exponents. Do not assume the split is correct;
find where it breaks if it does. Distinguish what you prove from what you conjecture.
</grounding_rules>
