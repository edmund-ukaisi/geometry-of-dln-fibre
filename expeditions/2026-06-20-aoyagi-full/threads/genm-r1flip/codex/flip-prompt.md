<task>
Adjudicate ONE truth-value in a resolution-of-singularities / real-log-canonical-threshold (RLCT)
computation (Watanabe singular learning theory; Aoyagi's deep-linear-network learning coefficient).
Reason from scratch. I am NOT telling you my current leaning. Distinguish FACT from INFERENCE.

## The concrete object

We want the RLCT of the squared-Frobenius loss of a layer product at its DEEPEST singular point:

    L(C1,...,CL) = || C1 . C2 . ... . CL ||^2   (sum of squares of the entries of the matrix product),

with C^(s) an M^(s) x M^(s+1) real matrix, all near the origin (all C^(s) = 0 is the deepest point;
by a homogeneity + lower-semicontinuity domination the global learning coefficient is realised there).
The zero locus of L is exactly { C1...CL = 0 }. The RLCT is 1/2 * (min over resolution branches of an
explicit integer codimension Mval(t)); the target is finiteness of the box integral
  INT_{box} L^{-c'}  <  infinity   for every real c' < 1/2 * minAdm,
minAdm = min_t Mval(t).

Concrete instance to keep in mind: M = (3,3,3,4), so C1 is 3x3, C2 is 3x3, C3 is 3x4 (L=3), product
3x4. A binding branch is t=(1,0,0) with per-layer codim charges [4,3,0], sum = 7 = minAdm; the front
layer C1 drops to rank 1, freeing a 2x2 "corank" block (corank 2). The tail after the front peel is a
genuine PRODUCT C2.C3 of two free matrices (this is the "corank>=2 with a shared product tail" regime).

## Two candidate ways to establish the finiteness (both target the SAME true RLCT)

Let, after a rank-1 pivot chart on the front layer, the loss split (Schur) into
   L  =  || A . Qtilde ||^2  +  || C . Qtilde + Gamma . Qb ||^2 ,
where Gamma is the freed p x q corank block (here 2x2, FREE parameters), Qb = (nonpivot rows of the
tail product) = W . C2 . C3 is a 2x4 PRODUCT (W a fixed generic 2x3), and A.Qtilde etc. are the pivot
part. So Gamma is multiplied on the RIGHT by the product Qb.

ROUTE 1 ("integrate the corank block out"): treat Gamma as a Gaussian-type block and integrate it out
over ALL of R^{p x q} using a Morse/Gaussian lemma. This requires the isotropic shape ||Delta||^2 + core,
so one substitutes Delta = Gamma . Qb, whose Jacobian is det(Qb Qb^T)^{-p/2}. det(Qb Qb^T) = sum of
squares of the maximal (2x2) minors (Plucker coordinates) of the product Qb; by Cauchy-Binet these are
bilinear in the minors of the factors. So this route produces the maximal-minor ("determinantal")
ideal I_2(Qb) of the matrix product, and one would need to principalise it (make det(Qb Qb^T) a
normal-crossing monomial x unit) on a chart cover.

ROUTE 2 ("keep the block a coordinate, blow up layer by layer"): NEVER integrate Gamma out. Instead
follow the published resolution: blow up the ORIGIN of the current layer's residual block
(center = { the whole residual block = 0 }, a linear/coordinate subspace of that layer's entries; a
single radial u with the block = u * (block')), normalise a pivot, apply det-1 unit (Schur) row/column
transforms depending only on that block's own entries (absorbed into the adjacent factor), which reduce
the residual block to [ 1 (+) smaller-residual ]; the loss factors as u^2 * (pivot energy + smaller
residual coupled to the SAME deeper product); then advance to the next layer and recurse. After the
finite (S,J) staircase the loss becomes SUM of squared monomials in the exceptional coordinates
(normal crossing); finiteness is then a coordinatewise monomial endpoint.

## Facts I have established by exact algebra (sympy, exact rationals)

FACT 1. det(Qb Qb^T) is a 450-term irreducible polynomial, gcd of terms = 1 (not monomial x unit), and
{ rank(Qb) <= 1 } has a point in the DENSE TORUS (all entries nonzero), e.g. Qb* = [[1,1,2,1],[1,1,2,1]].
Such a point lies in NO coordinate-subspace stratum, so no sequence of coordinate/toric blow-ups (centers
inside coordinate strata) can make det(Qb Qb^T) a normal-crossing monomial x unit.

FACT 2. At that same Qb* (rank 1, dense torus), the corank-residual loss || C.Qtilde + Gamma.Qb* ||^2,
for a GENERIC cross term C.Qtilde, has minimum over Gamma equal to 12/7 > 0, and the equation
C.Qtilde + Gamma.Qb* = 0 has NO solution. So Qb* is a POSITIVE-loss point: L > 0 there, i.e. it is NOT
on the zero locus { C1...CL = 0 } of the loss.

FACT 3. In ROUTE 2, each blow-up center is { residual block = 0 } (the block's origin, a coordinate
linear subspace of the current layer's chart entries); the radial u factors from EVERY generator because
the whole block is u*(block'); the det-1 transforms use only that block's entries; det(Qb Qb^T) never
forms; and a depth-k product ideal <B.C....> resolves to monomial generators in k such coordinate peels
(verified end-to-end on a faithful shared-product model). The shared radial (one u per block) gives a
strictly LOWER toric RLCT than a fresh-radial-per-generator ledger.

## The truth-value to adjudicate

Q1. Is the determinantal/Plucker minor ideal I_2(Qb) (equivalently the singular locus {rank Qb <= 1},
which carries the dense-torus point Qb* of FACT 1) something the RLCT resolution of L = ||C1...CL||^2
MUST resolve/principalise? Or is it an object that arises ONLY in ROUTE 1 (integrating Gamma out over
full space) and NOT in ROUTE 2? Use FACT 2 (Qb* is a positive-loss point off the zero locus of L) in
your reasoning.

Q2. Does ROUTE 2 (the published layer-by-layer resolution: blow up residual-block origins, det-1 unit
Schur clears, recurse) genuinely reach normal crossing (sum of squared monomials) for the corank>=2
shared-product tail regime USING ONLY coordinate/smooth centers — or is there a step where it is FORCED
to blow up a NON-coordinate (determinantal / minor / Plucker) center? If forced, name exactly where and
why the layer-by-layer coordinate peels fail to reach normal crossing. Pay specific attention to the
SHARING: the pivot part and the corank part both couple to the SAME deeper product C2.C3.

Q3. VERDICT, one of:
   (a) NON-COORDINATE CENTER FORCED: even the layer-by-layer route must principalise the product-minor
       ideal I_2(Qb) (a genuine resolution-of-singularities theorem, not iterated coordinate blow-ups).
   (b) COORDINATE CENTERS SUFFICE: the layer-by-layer route reaches normal crossing with coordinate/
       smooth centers only; the determinantal ideal I_2(Qb) is a ROUTE-1 artifact that the RLCT
       resolution of L does not need to touch.
   Pick one and defend it. Do not hedge into "it depends" without saying precisely what it depends on.

Q4. Separately: IF coordinate centers suffice (b), is the layer-by-layer resolution nonetheless a
   substantial construction (a finite but multi-step recursion with exceptional-divisor bookkeeping),
   or is it a short/trivial argument? (I want your read on whether "coordinate centers suffice" implies
   "small/easy" or can still be "large but elementary".)
</task>

<output_contract>
Answer Q1, Q2, Q3, Q4 in order, tersely, each with the reasoning that forces it. Mark each key
statement as FACT (mathematically forced) or INFERENCE (your judgement). For Q3 pick exactly one of
(a)/(b). Under ~700 words.
</output_contract>

<grounding_rules>
- Cauchy-Binet: minors of a product AB are bilinear in (minors of A, minors of B).
- The RLCT of a loss ||f||^2 is a LOCAL invariant of the zero locus {f=0} at the point; positive-loss
  points (where ||f||^2 > 0) are smooth points of the loss and contribute nothing to the RLCT there.
- A blow-up with center { a coordinate subspace = 0 } in a chart obtained by prior det-1 (unit) linear
  transforms is a smooth-center blow-up; "coordinate/toric" here means the center is a coordinate
  subspace in the CURRENT chart (after unit transforms), reached without ever writing det(Qb Qb^T).
- Do not assume the answer I want; I have deliberately withheld my leaning. "Route 1 walls" and "Route 2
  is bounded" are DIFFERENT from "the true RLCT is finite" — all three can hold simultaneously.
- Distinguish "the true integral / RLCT" (route-independent) from "what a particular route must resolve".
</grounding_rules>
