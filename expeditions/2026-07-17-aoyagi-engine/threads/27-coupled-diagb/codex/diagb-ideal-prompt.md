<task>
Setting: resolution of singularities for the RLCT (real log-canonical threshold) of the
"deep-linear-network core" loss. Fix reduced widths and matrices of free indeterminates over
the reals:

  (A) M=(3,3,4): C1 a 3x3 matrix, C2 a 3x4 matrix (21 free entries). Core loss
      F = || C1 * C2 ||_Frobenius^2 = sum over (i,j) of (C1 C2)_{ij}^2, resolved at the origin.
  (B) M=(3,3,2,2): C1 3x3, C2 3x2, C3 2x2 (17 free entries). F = || C1 C2 C3 ||^2 at origin.

Aoyagi (2023) claims a resolution g (composition of unit/regular coordinate changes that PRESERVE
the ideal, plus blow-ups of coordinate subspaces) after which, in each deepest chart, the pulled-back
product matrix becomes diag(b_1,...,b_M) (padded with zeros), where each b_i is a MONOMIAL in the
exceptional coordinates, with a divisibility chain b_1 | b_2 | ... | b_M. Equivalently the pulled-back
entry-ideal < (C1...C^L)_{ij} > equals the monomial ideal < b_1,...,b_M >, and the pulled-back loss is
sum_i b_i^2 (normal crossing). The binding exceptional divisor's accumulated exponent equals
Mval(t) = (M1 - t1)(M2 - t1) + sum_{j>=2} (t_{j-1} - t_j)(M_{j+1} - t_j),
and rlct = (1/2) * min over admissible weakly-decreasing profiles t (with t_L = 0) of Mval(t).

Known combinatorial facts (established): min Mval for (A) is 8 at t=(1,0) [layer-1 corank (2,2),
a genuine partial rank drop 0<1<3, the UNIQUE minimizer]; for (B) it is 4, reached at t=(2,1,0)
[layer-1 corank (1,1), scalar] and also at clean t=(3,1,0),(3,2,0).

The genuinely hard step for (A) is that the layer-1 residual after clearing 1 pivot is a free 2x2
block Delta multiplying a free 2x4 block S (a "(2,2,4)" matrix-product sub-core || Delta * S ||^2),
i.e. corank 2 — the b_i then SHARE exceptional divisors and a naive per-row-independent-divisor
"flatten" gives the wrong ideal/value.

Concretely for (A): block-eliminating C1 at rank 1 (an ideal-preserving unit transform) gives the
exact splitting < C1 C2 > = < T , Delta*S >, T a 1x4 clean row (4 free coords, disjoint from the rest),
Delta free 2x2, S free 2x4.

</task>

<subquestions>
1. Give the EXPLICIT sequence of ideal-preserving unit transforms + coordinate blow-ups that fully
   monomializes the (2,2,4) sub-core ideal < Delta * S > (Delta 2x2, S 2x4) into a monomial ideal
   < b_1, ..., b_k > in the deepest chart(s). State, per chart, the exact exceptional coordinates
   introduced, their Jacobian exponents, the exact b-monomials, and the resulting divisor ratios
   (h+1)/(2k). Which chart binds and what is its rlct?

2. For the FULL (3,3,4) core: does Aoyagi's mechanism produce, in the binding chart, a SINGLE
   exceptional divisor whose ACCUMULATED exponent is Mval = 8 (ratio 4), OR does the value 4 arise
   only as a SUM 2+2 of two disjoint pieces (the clean 1x4 row T contributing rlct 2, and the (2,2,4)
   sub-core contributing rlct 2) via disjoint-variable additivity? State precisely whether the
   "single terminal divisor of exponent 8" reading is literally correct in some deepest chart, or
   whether it is only a value-coincidence with the disjoint-sum decomposition. Give the exact b-vector
   (b_1,b_2,b_3) with its divisibility chain, if it exists.

3. Repeat for (3,3,2,2): give the explicit monomialization and b-vector at the coupled branch
   t=(2,1,0) (where the depth-3 factor C3 is SHARED between the "clean" and the "delta-weighted"
   terms, i.e. F ~ ||T C3||^2 + delta^2 ||R C3||^2, T 2x2, R 1x2, C3 free 2x2 shared).

4. Is the ideal identity < (product entries) > = < b_1,...,b_M > in the deepest chart literally an
   equality of ideals in the polynomial ring of that chart's coordinates (verifiable by a Groebner
   basis computation), or does it hold only up to a unit / only for the loss up to a unit factor?
   If the free residual block D_J is not fully monomial at the stage where Aoyagi reads off the
   exponent, say so explicitly.
</subquestions>

<output_contract>
For each subquestion, lead with a one-line VERDICT, then the exact algebra (coordinates, exponents,
b-monomials, ratios). Tag every statement as FACT (you derived/verified it here) or INFERENCE.
Be explicit where the "single binding divisor of exponent 8" reading is or is not literally true.
If a step needs a computation you cannot do by hand, say which and give the setup, do not hand-wave.
Keep it under ~1200 words.
</output_contract>

<grounding_rules>
Work only from the setup above. Do not assume the answer is a clean telescoping; the corank-2 coupling
is real. Show the coordinates. If you cannot fully monomialize a chart by hand, report how far you got
and name the residual precisely. Do not paste long code.
</grounding_rules>
