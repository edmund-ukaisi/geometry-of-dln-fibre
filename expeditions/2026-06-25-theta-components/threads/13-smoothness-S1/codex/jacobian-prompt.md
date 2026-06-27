<task>
Independent analysis of a fibre-Jacobian rank/minor question for deep linear networks.

SETUP (exact). Fix a dimension vector d=(d_0,...,d_N) of nonneg integers, N "arrows".
Rep_d is the affine space of matrix tuples A=(A_1,...,A_N), A_i an (d_i x d_{i-1}) matrix
over an infinite field k. The multiplication map is
    mult(A) = A_N * A_{N-1} * ... * A_1   (an (d_N x d_0) matrix; standard matrix product).
Fix a rank r with 0 <= r <= min_i d_i. Let E_r = diag(I_r, 0) be the (d_N x d_0) matrix
of rank exactly r. The FIBRE is the affine scheme
    Fib = { A : mult(A) = E_r }  in  Rep_d,
cut by the d_N*d_0 polynomial equations  F_{ij}(A) = (mult(A) - E_r)_{ij} = 0.

The fibre Jacobian at a point A is the (d_N*d_0) x (sum_i d_i d_{i-1}) matrix
    J(A) = [ d F_{ij} / d (entry of A) ],
equivalently the matrix of the linear map  Adot |-> sum_i (A_N..A_{i+1}) Adot_i (A_{i-1}..A_1).

KNOWN FACTS (exact, established earlier in this project):
- The fibre top components are in bijection with corner-r Kostant partitions of the shifted
  vector (d_0-r,...,d_N-r); the number of top components is theta = C(m, |delta|) for the
  QIP data (m, delta) of the shifted vector. The codimension of each top component equals a
  fixed integer call it Q (= "C+delta").
- For r close to min_i d_i the codim Q equals d_N*d_0 (the cut equations are independent: complete
  intersection). Example: d=(2,2,2), r=1: Q=4=d_N*d_0; d=(3,3,3), r=2: Q=9=d_N*d_0.
- For smaller r the codim Q is STRICTLY LESS than d_N*d_0 (cut equations dependent). Example:
  d=(2,2,2,2,2), r=0: d_N*d_0=4 but codim Q=3; there are theta=6 top components.
- On the block-triangular chart, A_i = [[I_r, H_i],[0, B_i]] and the fibre is governed by the
  ZERO-PRODUCT condition B_N..B_1 = 0 on the shifted factors plus an affine-linear system in H.
- (Separate result) On the SOURCE side Sigma-bar^r, a single fixed polynomial detDelta (the deep
  top-left r x r minor of the product) is nonzero on every top component simultaneously (a single
  global pivot, not per-component).

QUESTIONS (answer each; distinguish what you can PROVE from what you CONJECTURE):
1. On the generic (top) stratum of Fib, what is the rank of J(A)? Argue it equals the codim Q
   (i.e. Fib is generically smooth of the expected dimension), and identify the precise locus
   where the rank drops below Q.
2. To build a SubmersivePresentation / standard-smooth chart you must choose Q of the cut
   equations and Q of the coordinate variables whose Q x Q Jacobian sub-minor is a UNIT
   (nonvanishing) on an open chart covering the generic locus. Is there a SINGLE FIXED such
   Q x Q minor (one fixed choice of Q rows = equations and Q columns = variables) that is
   nonvanishing on the ENTIRE generic locus of Fib (across all theta top components at once)?
   Or must the witnessing minor be chosen per-component? Give the structural reason. If a single
   global minor exists, describe its canonical form (which equations, which variables); relate it
   to the block-triangular chart and to the row/column structure of dF_A = sum_i L_i Adot_i R_i.
3. When Q < d_N*d_0 (dependent equations), which Q of the d_N*d_0 equations should be selected,
   and is that selection uniform across the generic locus? (E.g. d=(2,2,2,2,2) r=0: which 3 of
   the 4 entry-equations carry the full rank generically?)

OUTPUT CONTRACT:
- A short answer to each of (1),(2),(3).
- For (2): a crisp verdict "single global minor" vs "per-component", with the mechanism.
- Mark every claim PROVEN / CONJECTURE / HEURISTIC. No code unless it is a 5-line exact check.

GROUNDING RULES:
- Reason from the exact algebra (the product-rule differential, ranks of L_i and R_i, the
  block-triangular chart). Monte-Carlo/numeric rank is only a guide, never a certificate.
- Do not assume the answer; derive it. If per-component vs global is genuinely subtle, say which
  small case would decide it.
</task>
