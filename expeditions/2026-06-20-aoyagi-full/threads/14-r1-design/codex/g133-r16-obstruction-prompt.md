<task>
Independently adjudicate three mathematical questions about a resolution-of-singularities atlas for the
deep-linear-network square-Frobenius loss near 0. Do NOT assume a desired answer; compute / reason from
scratch and report which of the three (if any) FAIL.

SETUP (exact).
- Fix a width vector M = (M[0], M[1], ..., M[L]) of positive integers. A "DLN parameter" is a tuple of
  real matrices A^(s) for s=1..L, where A^(s) has size M[s-1] x M[s]. The loss at the deepest point is
  F(A) = || A^(1) A^(2) ... A^(L) ||_F^2  (squared Frobenius norm of the matrix-chain product, an
  M[0] x M[L] matrix). The zero-locus {F=0} = {A : the chain product = 0}. The base point is A=0.

- The "rank stratification": a stratum is indexed by a vector t = (t_1,...,t_L) of nonnegative integers
  (partial-product ranks / kernel-dim data). The relevant "admissible" strata for this resolution are
  those satisfying: weak-decrease t_1 >= t_2 >= ... >= t_L; the last coordinate t_L = 0; and per-block
  bounds t_1 <= min(M[0],M[1]), t_j <= M[j+1] for j>=2 (1-indexed). For an admissible t define
        Mval(M,t) = (M[0]-t_1)(M[1]-t_1) + sum_{j=2}^{L} (t_{j-1}-t_j)(M[j+1]-t_j).
  (codim of stratum t in the zero-locus picture; over Z.) Define minMval = min over admissible t.

- The RESOLUTION ATLAS (the claim under test): build a finite TREE of charts. At each node, (1) BLOW UP at
  an admissible rank-defect center (the affine pivot cover: pick a nonzero pivot minor; one affine chart
  per pivot choice; charts a.e.-cover); (2) then descend: the per-chart loss F splits as
        F  ~  (nReg unit-coefficient regular squares) + (a strictly smaller reduced-chain core G^2),
  via a two-sided SQUEEZE c1*Phi <= F <= c2*Phi with c1,c2>0 STRUCTURAL constants and
  Phi = (sum of regular squares) + G^2. (This is NOT a change of variables and NOT an orthogonal-Frobenius
  equality; the matrix-chain product is multilinear, F is exactly degree-2 in any single factor under
  scaling.) Leaf: a single smooth block (reduced chain has length 1). The RLCT-threshold of a monomial
  exceptional divisor with Jacobian exponent h and loss-multiplicity k contributes ratio (h+1)/(2k).
</task>

<output_contract>
Adjudicate EACH of the three questions below as FACT / INFERENCE / UNRESOLVED, with an exact reason or a
concrete counterexample chain M + stratum/divisor. Mark every claim as FACT (you can prove it) vs
INFERENCE (your best reasoning, could be wrong). Be adversarial: actively try to find a failure.

(Q1) SURJECTIVITY / EXHAUSTIVENESS. Is every admissible rank stratum t reachable by SOME root-to-leaf path
of the pivot tree? Equivalently: could there exist an admissible stratum t whose codim Mval(M,t) is
STRICTLY SMALLER than the minimum codim over all root-to-leaf paths actually realized by the iterated
pivot blow-up — i.e. an admissible stratum reached by no path? If yes, the atlas infimum OVER-estimates
the RLCT (too-large RLCT). Give a chain M where this is at risk, or argue it cannot happen.

(Q2) MULTIPLICITY. On every exceptional divisor of this tree, is the loss-multiplicity k_E = 1 (so the
binding ratio is (h+1)/2, not (h+1)/(2k) with k>=2)? The trap: x^(2k) has threshold 1/(2k); (x^2+y^2)^2
has threshold 1/2 < 1. Could a chart/divisor arise where the post-squeeze residual is NOT degree-2 in the
exceptional coordinate (k_E >= 2), giving an undershoot (h+1)/(2k) < codim/2? Consider asymmetric chains
like (3,1,3),(2,3,2),(3,2,1) and a depth>=4 chain.

(Q3) TERMINATION. Does the descent always strictly reduce a well-founded measure (e.g. sum of widths
Sigma M, or the total rank defect) at every nonterminal node, so the tree always reaches the smooth
length-1 leaf? Could there be a nonzero singular core where NO admissible minor is available to blow up,
so the descent is stuck and never terminates?
</output_contract>

<grounding_rules>
- Exact algebra only for anything load-bearing; a floating-point rank at a tolerance is not an exact rank.
- A closure/exhaustiveness claim must rule out ALL other strata, not one checked case.
- Keep separate: the abstract rank-stratum statement, the codim (Mval) count, and the RLCT ratio.
- If you build a counterexample, give the exact chain M, the stratum t or divisor, and the exact numbers.
- Do NOT tell me what you think I want to hear. If all three hold, say so and give the load-bearing reason;
  if one fails, give the explicit failing chain.
</grounding_rules>
