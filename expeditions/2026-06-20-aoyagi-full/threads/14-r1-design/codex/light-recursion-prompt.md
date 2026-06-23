<task>
We are designing a Lean formalisation of a resolution of singularities for the real-log-canonical-
threshold (RLCT) of a "deep-linear-network core" function, and need to decide between a LIGHT and a
HEAVY inductive invariant. Adjudicate, with exact algebra, whether the LIGHT invariant suffices.

SETUP (all established, do not re-derive — these are facts):
- Core function on reduced widths M=(M^1,...,M^{L+1}):  F = || C^1 C^2 ... C^L ||_F^2 , each C^s a
  free real M^s x M^{s+1} matrix, resolved at the origin (the singular point, product = 0).
- The RLCT value is known to equal (1/2) min_t Mval(t), where the min is over weakly-decreasing
  rank profiles t=(t_1,...,t_L), t_L=0, and
    Mval(t) = (M^1-t_1)(M^2-t_1) + sum_{j=2}^{L} (t_{j-1}-t_j)(M^{j+1}-t_j).
- The resolution is recursive in DEPTH. Peeling layer 1 at rank t_1 (block-elimination, a unit
  transform that preserves the ideal/RLCT) gives the EXACT identity (verified in sympy):
    F  ~  || diag(E_{t_1}, Delta) * C2' * C^3 ... C^L ||^2
        =  || T * (C^3...C^L) ||^2  +  weighted terms || Delta-block * (C^3...C^L) ||^2
  where T = the top t_1 output rows (clean), and the bottom (M^1 - t_1) output rows are weighted by
  the residual block Delta (an (M^1-t_1) x (M^2-t_1) matrix of fresh "residual" scalars). When
  Delta is 1x1 = a scalar delta (corank-1 drop), this is exactly
    F ~ || T (C^3...C^L) ||^2 + delta^2 || R (C^3...C^L) ||^2 ,  T,R,C^s all FREE, sharing C^3...C^L.

KEY established fact for the partial-rank case (3,3,2,2), branch t=(2,1,0), Mval=4, target rlct=2:
  G = ||T C3||^2 + delta^2 ||R C3||^2  (T 2x2, R 1x2, C3 2x2, delta scalar, all free).
  Blow up {C3=0} radially (codim 4, radial ratio = 4/2 = 2). On the rank-1 chart of the radial
  divisor, the residual MONOMIAL ideal is (A1, A2, eps*B1, eps*B2, delta*E, delta*eps*F) with
  RLCT 2; so RLCT_0(G)=min(2,2)=2 = (1/2)Mval. The delta-weighted term RAISES the residual
  threshold from 3/2 (the ||TC3||^2-only value) to 2 — the coupling through C3 is load-bearing.

THE DESIGN QUESTION (the one to adjudicate):
  In the recursion's inductive INVARIANT, is it sufficient to carry only
     (residual reduced widths M')  +  (a per-output-row WEIGHT MULTISET: each row carries an
      integer = the number of accumulated divisor scalars weighting it),
  WITHOUT carrying the full matrix Delta / diag(b) data (the actual entries / the actual matrix
  structure of the accumulated weights)?
  Equivalently: is the RLCT of the coupled residual a function ONLY of
     (widths, the per-row weight-multiplicities, the branch t),
  invariant under the actual matrix entries and under WHICH columns are shared?

<output_contract>
1. A yes/no verdict: does a THRESHOLD-ONLY invariant (widths + per-row weight-multiplicities, no
   full Delta matrix) determine RLCT_0 of the coupled residual, for general L and general branch?
2. If YES: state the exact recursion (the per-blow-up threshold accounting, the base case) and a
   proof sketch that the residual monomial ideal — hence its RLCT — depends only on
   (widths, row-weight-multiset, branch).
3. If NO: exhibit the SMALLEST coupled residual where two instances with the SAME (widths, row-weight-
   multiset, branch) but DIFFERENT matrix/column-sharing structure give DIFFERENT RLCT. Characterize
   exactly what extra (diag(b)-like) data is irreducibly needed.
4. Address the specific worry: when Delta is NOT a scalar (corank >= 2, so Delta is a genuine
   matrix block, e.g. 2x2), the bottom rows are weighted by a MATRIX, not independent per-row
   scalars. Does a per-row multiset still capture this, or does the matrix structure of Delta bind?
5. Address the L>=4 worry: the coupling propagates through MULTIPLE shared deep layers
   (||T C3 C4||^2 + delta^2 ||R C3 C4||^2 shares both C3 and C4). Does the per-layer radial cascade
   keep the residual ideal a function of (widths, row-weight-multiset, branch) only?
</output_contract>

<grounding_rules>
- Exact algebra only for any load-bearing claim (symbolic / Newton-polytope / monomial-ideal LCT).
  Monte-Carlo only as a guide, never as a verdict.
- Label every statement FACT (direct algebra from the setup) vs INFERENCE (structural conclusion).
- Do NOT assume the answer. Construct the residual ideals yourself from the setup and read off the RLCT.
- If you find the threshold-only invariant is insufficient, the smallest explicit counterexample is
  worth more than a general argument.
</grounding_rules>
