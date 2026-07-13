<task>
Setting (real analysis / RLCT of a matrix integral, target = FORMALISATION feasibility in Lean+Mathlib v4.29).
For a 3-width "waist" chain (x,s,z) with A0 an x-by-s matrix, A1 an s-by-z matrix (s <= z), we study finiteness of
    I(c) = INT_box  ||A0 A1||_F^{-2c}  dA0 dA1 .
The loss depends on A1 only through the s-by-s Gram G = A1 A1^T, and on A0 only through M = A0^T A0:
    ||A0 A1||_F^2 = tr(M G).
It is a KNOWN fact (Watanabe + Aoyagi, taken as ground truth here) that the finiteness threshold is
    c* = (1/2) * minAdm(x,s,z),   minAdm(x,s,z) = sum_{j=1}^s min(x, z+s+1-2j).

Two established resolution routes:

ROUTE A (transcendental). Rectangular SVD A1 = U Sigma V^T (U in O(s), V in Stiefel V_s(R^z)). Then
    ||A0 A1||^2 = sum_j sigma_j^2 ||A0 u_j||^2 ,
and the Lebesgue measure pushes forward as
    dA1 ~ prod_{i<j}|sigma_i^2 - sigma_j^2| * prod_j sigma_j^{z-s}  d(sigma) dU dV.
On the ordered chamber sigma_1>=...>=sigma_s the Vandermonde factor is bounded by a monomial
    prod_{i<j}|sigma_i^2-sigma_j^2| <= prod_j sigma_j^{2(s-j)},
giving per-mode radial power h_j^{SVD} = (z-s) + 2(s-j) = z+s-2j. Feeding a banked "qPeel" corner integral
(each mode: radial sigma_j power h_j + an R^x "Morse" block ||A0 u_j||^2) gives threshold
(1/2) sum_j min(x, h_j^{SVD}+1) = (1/2) minAdm. This is TIGHT but needs the SVD/Weyl density: an explicit
parametrisation + Jacobian of the map A1 -> (sigma, U, V), i.e. Haar on O(s) and the Stiefel manifold
V_s(R^z). Mathlib v4.29 has NONE of: eigenvalue/SVD Jacobian, Wishart/Weyl density, Haar on O(s),
Stiefel manifold, coarea. Only the general diffeomorphism change-of-variables
(MeasureTheory.Function.Jacobian: image-lintegral = lintegral of |det Dphi| composed) is banked.

ROUTE C (rational, cheaper). A rational triangular chart on A1: peel A1's rows one at a time by
Gram-Schmidt (= Cholesky of G), a rational orthogonal-frame + radial flag with a det-power Jacobian on the
banked general CoV. This gives per-mode radial power h_j^{C} = z-j (the Cholesky/Bartlett staircase),
truncated by the ambient to min(x, z+1-j). Threshold (1/2) sum_j min(x, z+1-j).

The PROBLEM. For s<=2 (all widths, with an orientation choice) route C is TIGHT: sum_j min(x,z+1-j) =
minAdm. But for s>=3 with LARGE x route C UNDERSHOOTS. Exact anchors:
  (x,s,z)=(4,3,4): route C 2c-charge = 9  <  minAdm = 10  (undershoot 1, entirely in mode j=2)
  (x,s,z)=(5,4,6): route C 2c-charge = 17 <  minAdm = 18  (undershoot 1, in mode j=3)
Decomposing the exponents: route C's h_j = (z-s)+(s-j) captures the rectangular part (z-s) AND ONE copy of
the staircase (s-j); the SVD's h_j = (z-s)+2(s-j) has TWO copies. The missing charge is exactly the second
(s-j) per mode = the eigenvalue-vs-Cholesky-pivot repulsion (the "other half" of the Vandermonde
prod_{i<j}|sigma_i^2-sigma_j^2|). At (4,3,4) the ambient cap min(x,.) wastes the repulsion in modes 1,3 but
NOT in mode 2, where it is needed and equals exactly 1.

THE ONE QUESTION. Can this missing repulsion charge be recovered by a construction that stays RATIONAL
(explicit rational/algebraic charts with det-power Jacobians that feed the banked general
MeasureTheory.Function.Jacobian change-of-variables, NO abstract Haar/Stiefel/coarea, per FIXED small s
allowed to be a finite explicit computation) -- so that route C EXTENDS to s>=3-large-x?  OR is the
transcendental orthogonal SVD/Weyl density GENUINELY FORCED there (=> a research-level Mathlib build)?

Consider specifically: (a) a nested sequence of rational blow-ups resolving the eigenvalue-collision /
discriminant locus {sigma_i = sigma_j} = {disc(G)=0}; (b) any OTHER rational device that makes the
eigenvalue repulsion appear as an explicit polynomial/rational Jacobian factor; (c) whether the loss
tr(M G) and the required amplitude can be jointly monomialised rationally. Work the (4,3,4) anchor
concretely: the codim of {sigma_i=sigma_j} in Sym(s), whether a blow-up (or other rational chart) delivers
the missing power-1 in mode 2, and whether any such recursion TERMINATES at finite depth with each level
rational.
</task>

<output_contract>
1. VERDICT (one line): RATIONAL-RECOVERABLE (route C extends, moderate build) / SVD-FORCED (heavy) /
   PARTIAL (recoverable but with named caveats).
2. The single most promising rational device (name it precisely; if a blow-up, give the center and the
   Jacobian power it contributes; if a frame parametrisation, name it and the Jacobian factor).
3. Worked (4,3,4): does your device deliver the missing power-1 repulsion in mode 2 and reach (1/2)minAdm=5?
   Show the charge arithmetic.
4. Termination / atlas: finite depth? finite chart count? any measure-zero locus uncovered and is it benign?
5. The single sharpest reason your verdict could be WRONG, and the cheapest test that would settle it.
Keep it tight. Exact algebra over prose.
</output_contract>

<grounding_rules>
- minAdm and the SVD charge identity sum_j min(x,z+s+1-2j)=minAdm are GROUND TRUTH (do not re-litigate).
- "Rational" means: expressible via polynomial/rational maps whose Jacobian determinant is a
  rational function, usable in the general diffeomorphism CoV; a FINITE explicit computation per fixed small
  s is allowed (s is a fixed small integer in the base case, e.g. 2 or 3). Compact-group Haar as an
  ABSTRACT measure / abstract Stiefel manifold / coarea are NOT available.
- Distinguish clearly what you can PROVE/derive from what you conjecture. If you invoke a classical
  matrix-analysis fact, name it.
- Adjudicate in EITHER direction honestly; do not assume the answer is "recoverable".
</grounding_rules>
