<task>
I am deriving the load-bearing geometric step of a resolution-of-singularities RLCT (real
log-canonical threshold) computation for deep linear networks, and I have hit a discrepancy
I need an independent check on. EXACT pen-and-paper / sympy only; no Lean.

SETUP (precise).
- A "matrix chain" has widths M = (M^1, ..., M^{L+1}). The loss at the origin is
  F = ||A . B||_F^2 where A is the first-layer matrix (size m x k, m=M^1, k=M^2) and
  B is the product of the remaining layers (size k x n, n=M^{L+1}); near the origin we
  may treat B as a GENERIC k x n matrix of free coordinates (the deeper layers are the
  recursion's child, handled separately).
- The RLCT at the origin is rlct(F,0) = sup{ c' >= 0 : |F|^{-c'} is locally integrable near 0 }.
  Equivalently the weighted threshold theta(F,1,{0}); under a (not-necessarily measure-preserving)
  resolution map pi the change of variables puts the Jacobian into the integrand as a WEIGHT:
  theta(F,1) = theta(F o pi, |Jac pi|).
- Aoyagi's value: rlct(F,0) = (1/2) minAdm(M), minAdm(M) = min over admissible exponent vectors
  T of Mval(M,T), Mval = sum_j (t^{j-1}-t^j)(M^{j+1}-t^j), t^0:=M^1, t^L=0, t weakly decreasing,
  0<=t^j<=admBound. For L=2, M=(a,b,c): minAdm = min_{0<=t<=min(a,b)} [ (a-t)(b-t) + t c ].

THE PER-NODE RECURSION I am trying to certify (one step).
- "schurState reduction": M^1,M^2 each drop by 1, deeper widths unchanged: red(M)=(M^1-1,M^2-1,M^3,...).
- Define nReg := minAdm(M) - minAdm(red(M)).  (This is a PROVEN arithmetic identity in our system:
  minAdm(red(M)) + nReg = minAdm(M), for non-leaf M.)
- TARGET per-node step:  rlct(F, 0) = nReg/2 + rlct(F_child, 0),  where F_child = ||A' . B'||^2 is
  the loss of the reduced chain red(M), so that iterating gives rlct = (1/2) minAdm by telescoping.

THE BLOW-UP I have (single pivot chart phi_1, pivot = A's (0,0) entry = y0).
  A = y0 * Ahat, Ahat = [[1, u^T],[v, W]] (m x k, top-left entry exactly 1; u is 1x(k-1), v is
  (m-1)x1, W is (m-1)x(k-1)). B passes through. Then (sympy-verified, exact):
    F o phi_1 = y0^2 * core,   core = ||Ahat . B||^2,   |Jac phi_1| = y0^(m k - 1).
  Schur-eliminate the unit pivot block of Ahat:
    Erow = B[0,:] + u . B[1:,:]                 (1 x n; the pivot-row product)
    S    = W - v . u                            ((m-1) x (k-1); Schur complement)
    core = sum_j Erow_j^2 + sum_{i,j} (v_i Erow_j + (S . B[1:,:])_{ij})^2   (sympy-verified exact)
  Near the deepest point v -> 0, so core ~ sum_j Erow_j^2 + ||S . B[1:,:]||^2, i.e. n smooth Morse
  squares (the Erow block) plus a reduced core ||S . Bred||^2.

THE DISCREPANCY (the crux I need checked).
  The single-pivot Schur form gives n = M^{L+1} regular Erow squares. But the recursion needs
  nReg = minAdm(M) - minAdm(red(M)) of them, and I computed (exact, brute force over widths 1..6):
  n != nReg whenever n = M^{L+1} > min(M^1,M^2)-ish. Examples (L=2):
    M=(2,2,2): n=2, nReg=2     (agree)
    M=(2,2,5): n=5, nReg=3     (DISAGREE)
    M=(1,1,4): n=4, nReg=1     (DISAGREE)
    M=(2,1,3): n=3, nReg=2     (DISAGREE)
  Also the single y0 exceptional divisor's own threshold ratio is (h+1)/a = (mk-1+1)/2 = mk/2
  (loss order a=2 in y0, Jacobian order h=mk-1), which is NOT nReg/2 either (e.g. (2,2,2): mk/2=2,
  nReg/2=1).
</task>

<questions>
1. Given the discrepancy, what is the CORRECT local resolution at this node so that the per-node
   step rlct(F,0) = nReg/2 + rlct(F_child,0) holds with the PROVEN value-side nReg = minAdm(M) -
   minAdm(red(M))?  Is a SINGLE pivot blow-up sufficient, or does the sound resolution require
   blowing up the rank locus (a nested sequence) / a different center?  Be concrete about what the
   exceptional divisor is and what monomial-axis power delivers exactly nReg/2 (not n/2, not mk/2).
2. In the regime where the single-pivot Erow block has MORE than nReg smooth squares (n > nReg),
   the extra n - nReg squares are smooth Morse coordinates that should NOT each contribute 1/2 to
   the node and then again to the child -- where do they go? (Hint to probe, not assume: are some
   of the Erow squares actually part of the CHILD's loss F_child = ||S.Bred||^2 rather than fresh
   Morse generators? i.e. is the Erow/child split as clean as the naive Schur form suggests, or
   does part of the n-block get absorbed into rlct(F_child)?)
3. State precisely the Jacobian/monomial power on the exceptional divisor in the SOUND resolution
   and verify its contribution equals nReg/2. If the single chart is not enough, give the center
   sequence and the binding divisor's (k_mon, h) monomial data with (h+1)/(2 k_mon) = nReg/2.
4. If instead you conclude the per-node step CANNOT hold as nReg/2 + child for some node class
   (a genuine obstruction), say so precisely with the smallest witness.
</questions>

<output_contract>
- Distinguish FACT (computed Mval, exhibited resolution data) from INFERENCE.
- Keep all Mval/codim arithmetic explicit; show the binding stratum T for at least (2,2,5),(2,1,3),
  (1,1,4) and contrast n vs nReg.
- If you propose a resolution, give the exceptional-divisor monomial data and the threshold
  contribution explicitly, and confirm it lands on nReg/2.
- Do NOT assume the single-pivot chart is the right one; derive.
</output_contract>

<grounding_rules>
- minAdm/Mval are over the integers; t^0 := M^1; admissibility is all three conditions.
- rlct = (1/2) minAdm is the established value; the per-node nReg/2+child must telescope to it.
- |Jac phi_1| = y0^(mk-1) and F o phi_1 = y0^2 core are sympy-verified facts, not assumptions.
</grounding_rules>
