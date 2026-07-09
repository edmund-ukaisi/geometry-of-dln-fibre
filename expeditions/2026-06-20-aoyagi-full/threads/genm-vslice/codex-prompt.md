<task>
Adjudicate the exact exponent accounting of a composed blow-up resolution for a specific
deep-linear-network singularity, and identify where a determinant-inverse would appear in a
Jacobian and how to avoid it natively.

SETTING. Real matrices A0 (3x3), A1 (3x3), A2 (3x4), all entries in the box [-1,1].
Loss F = ||A0 . A1 . A2||_F^2  (squared Frobenius norm of the 3x4 product).
Question is the finiteness of  I(c) = ∫_box F^{-c} dA0 dA1 dA2  as a function of c>0.
The real-log-canonical-threshold theory (Aoyagi 2023; Watanabe) says I(c) < ∞ iff c < lambda,
where 2*lambda = minAdm(3,3,3,4). The combinatorial minimum minAdm is:
  minAdm(M) = min over t in [0..min(M0,M1)] of (M0-t)(M1-t) + minAdm(t, M2, M3, ...),
  minAdm(a,b) = a*b.
For (3,3,3,4) the minimiser is the pivot-rank profile t=(1,0,0): per-boundary "charges"
[(3-1)(3-1), (1-0)(3-0), (0-0)(4-0)] = [4,3,0], summing to minAdm = 7, so lambda = 7/2.
The interesting feature: at boundary 0 the pivot rank is 1, so the corank block is (3-1)x(3-1)=2x2
(a genuine 2x2 residual, "corank 2"), and boundary 1 has a nonzero charge 3 that COUPLES through
the shared deep factor A2.

I want an INDEPENDENT derivation of the resolution and its exponent bookkeeping.

<output_contract>
1. Peel the leftmost factor A0 on the chart where A0 has rank 1 (a 1x1 invertible pivot block,
   WLOG top-left = scalar 'a', with B=1x2, C=2x1, D=2x2 the other blocks). Give the exact
   block/Schur identity for ||A0 . Q||^2 where Q = A1 A2 (3x4), splitting into a pivot term and a
   2x2-corank residual term. State precisely where a^{-1} (the inverse of the pivot minor) appears.
2. Explain the change-of-variables that removes a^{-1} from every JACOBIAN (as opposed to from the
   integrand-expression): which maps are measure-preserving shears (Jacobian determinant = 1) and
   why the pivot inverse never becomes a Jacobian determinant factor. Is there any step where a
   genuine det-inverse is unavoidable?
3. Resolve the 2x2 corank residual by a radial blow-up + unit-triangular (det-1) reductions,
   coupling to the shared downstream A2. Give the Jacobian power of each exceptional divisor and the
   vanishing order of the loss along it. Then CONTINUE to boundary 1 (charge 3) and boundary 2.
4. THE CRUX: the per-boundary charges are [4,3,0]. A naive "resolve each boundary independently"
   gives divisor thresholds ½·4=2 and ½·3=1.5, whose MINIMUM 1.5 is WRONG (it undershoots 7/2=3.5).
   Explain the mechanism by which the successive exceptional divisors COMBINE so that the binding
   terminal divisor accumulates the SUM of charges (4+3+0 = 7, threshold 7/2), not the minimum.
   Be concrete about which exceptional coordinates multiply (the "diag(b)" / b_i = product-of-u
   accumulation) and why the shared deep factor A2 makes the two boundary contributions ADD on the
   same divisor rather than compete.
5. State the general pattern: for a nondegenerate width vector M=(M0,...,ML) and pivot profile t,
   which parts of this are M-generic and which are specific to (3,3,3,4)/corank-2.
Distinguish clearly: FACTS you derive by exact algebra vs INFERENCE/heuristic.
</output_contract>

<grounding_rules>
- Exact algebra only for load-bearing claims (symbolic determinants, Jacobians, Newton polytope /
  toric RLCT rlct(sum of monomials x^a) = min_{w>0} (sum w)/(min_a <w,a>) as an instrument).
- Do NOT trust a single garbled formula; re-derive.
- Frobenius norm squared is a sum of squares; disjoint-variable sum-of-squares RLCTs ADD (Watanabe).
- I have NOT told you my tentative accounting beyond the stated minAdm value; derive the resolution
  structure yourself. If you disagree with any stated number, say so and show the computation.
</grounding_rules>
</task>
