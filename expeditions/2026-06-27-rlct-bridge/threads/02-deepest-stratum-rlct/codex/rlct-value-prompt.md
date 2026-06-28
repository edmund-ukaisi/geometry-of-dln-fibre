<task>
Compute the REAL log canonical threshold (RLCT, Watanabe's "learning coefficient" lambda) at the ORIGIN of the following non-negative analytic function K on R^16, and report your numeric/exact value FIRST before any discussion.

Setup. Let A1, A2, A3, A4 each be a 2x2 real matrix (16 real variables total, the entries). Form the matrix product
    P = A4 * A3 * A2 * A1     (ordinary 2x2 matrix multiplication, in this order).
Define the loss
    K(A1,A2,A3,A4) = sum over the 4 entries (i,j) of P  of  (P_ij)^2
                   = || A4 A3 A2 A1 ||_Frobenius^2 .
This is a homogeneous polynomial of degree 8 in the 16 entries; it is a sum of 4 squares, each square being a degree-4 multilinear "path" form. The deepest point is the origin (all entries 0).

The RLCT lambda is defined (Watanabe, Sumio. "Algebraic Geometry and Statistical Learning Theory") as the smallest pole z = lambda of the zeta function
    zeta(z) = integral over a neighborhood of 0 of  K(x)^{-z} * phi(x) dx ,  phi a smooth cutoff =1 near 0,
equivalently lambda = sup{ z>0 : integral K^{-z} converges near 0 }. (For a sum of c independent squares x_1^2+...+x_c^2 the value is c/2.)
</task>

<output_contract>
1. FIRST LINE: your best value of lambda (the RLCT) as an exact rational if you can, else a decimal to 3 sig figs. State the pole multiplicity m (order of the pole) too if you can.
2. The METHOD you used (toric/Newton-polyhedron resolution with a nondegeneracy verdict; an explicit blow-up / monomialization; a known closed form for deep-linear / matrix-multiplication / reduced-rank-regression models; or a careful numeric zeta/volume estimate with the log-multiplicity correction).
3. If Newton-polyhedron: state whether K is Newton-NONDEGENERATE w.r.t. its Newton boundary, and if not, why the naive Newton bound is not the answer.
4. A second, independent cross-check of the value if at all possible (e.g. a different weight/blow-up, or the c/2-at-a-smooth-point sanity check, or a small analogous case like the 3-layer 2x2 product A2 A1).
5. State your confidence and the single most likely way your value is wrong.
</output_contract>

<grounding_rules>
- This is a genuinely singular point (the four squared entries are NOT independent at the origin — they share the rank degeneracy of the matrix chain), so the answer is NOT simply 4/2 or 16/(2*8). Do not hand-wave the Newton nondegeneracy: a sum of squares of forms is typically DEGENERATE w.r.t. its Newton polyhedron, so the toric/Newton upper bound is usually NOT tight.
- If you run code, actually run it; report what it printed. A float rank at a tolerance is not an exact rank.
- Treat the multiplicity (log-power in the volume asymptotic V(t) ~ c t^lambda (log 1/t)^{m-1}) carefully: a naive log V / log t slope UNDER-estimates lambda when m>1.
- Withhold nothing about your method, but do not assume any particular target value; compute it.
</grounding_rules>

<environment_note>
You are in a read-only sandbox that BLOCKS shell/code execution. Do NOT attempt to run python or any command — those calls will be rejected and waste the budget. Reason analytically (Newton polyhedron, explicit blow-ups/monomialization, known closed forms for deep-linear / matrix-product / reduced-rank-regression models). If you cite a numeric value, derive it by hand or from a known theorem, not by running code.
</environment_note>
