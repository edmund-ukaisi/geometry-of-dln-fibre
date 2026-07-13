<task>
Exact-algebra design review of a change-of-variables (CoV) in a matrix-integral RLCT proof.
No code execution needed; reason with linear algebra + power counting.

SETUP (a "peel" at a binding cut t* of a layer chain M = (M0, M1, M2, ..., ), integers).
At cut t* set a := M0 - t*, b := M1 - t*, r := min(a,b), M2 := the deep-product ambient dim.
The peel frees an a×b "corner" matrix Gamma; a b×M2 "corank" block A_cor; and a deep product
Z (M2 × n, ranges over a bounded box, generically full rank). Q_b := A_cor·Z (b × n).
A Gaussian integral over the corner Gamma (a·b dims) produces, up to bounded box constants:
  (charge) = a·b/2       and    (residual weight)  Wenn(Z) := ∫_{A_cor in box} det(Q_b Q_b^T)^(-a/2) dA_cor,
and a reduced comparator loss  w := frobSq(Gamma'·Z)  on the reduced chain redChain(t*)M.
det(Q_b Q_b^T) is a b×b Gram determinant (product of all b Gram eigenvalues).

STRATIFICATION. The deep Z is stratified by singular-value count-shells with a single threshold eps:
  shell j = { Z : exactly j singular values of Z are < eps ; the other M2-j are >= eps }.
On shell j, write Z = U·Sigma·V^T; the M2-j "strong" columns of U (call U_s, M2×(M2-j)) carry
sigma >= eps, the j "weak" columns carry sigma < eps (-> 0 at the shell boundary).

EXACT FACT (Cauchy–Binet; verified symbolically). With B := A_cor·U (b×M2), D := Sigma^2,
  det(Q_b Q_b^T) = det(B D B^T) = sum_{|S|=b} det(B[:,S])^2 * prod_{k in S} sigma_k^2,
and as the weak sigmas -> 0,  det(Q_b Q_b^T) -> det(B[:,strong])^2 * prod_{k in strong} sigma_k^2,
where B[:,strong] = A_cor·U_s is a b × (M2-j) block.  Hence
  det(Q_b Q_b^T)^(-a/2)  ->  |strong minor|^(-a) * (prod sigma_strong)^(-a),  strong minor = det of a b×(M2-j) block.

CONVERGENCE LEMMA (banked). For X in box(rows × cols),  ∫ det(X X^T)^(-e/2) dX < ∞  iff  e < cols - rows + 1.

DESIGN TARGET (the charge is separately proven in exact integer arithmetic; NOT in question).
The design claims the shell-j integrand is dominated by  const(eps) · (comparator on redChain(t*+j)
at exponent c' - (a-j)(b-j)/2), with total charge C_j = (a-j)(b-j) + minAdm(redChain(t*+j)) >= minAdm(M).
The reduced weight the design needs is  ∫ det(X X^T)^(-(a-j)/2) over box((b-j) × (M2-j)),
which by the lemma converges iff (a-j) < (M2-b+1).

ANCHOR: a = b = 2, M2 = 3, j = 1, so (a-j) = (b-j) = 1, (M2-j) = 2.

BANKED TOOLS available to the CoV:
  (i)   PSD determinant monotonicity: A ⪯ B (both PSD) ⟹ det A ≤ det B.  [det_le_det_of_posSemidef_sub]
  (ii)  the convergence lemma above.  [detGram_lintegral_lt_top]
  (iii) a ONE-STEP bordered-Gram / Schur recursion:
        det Gram(q_1..q_i) = det Gram(q_1..q_{i-1}) · dist(q_i, span(q_1..q_{i-1}))^2.  [borderedGram_det]
  (iv)  a measure-preserving row-reindex of matrix space.  [measurePreserving_rowsEquiv]

A prior design note asserts: "the corner-shrink (a,b) -> (a-j,b-j) is realized by a CoV whose Jacobian is
the |strong (M2-j)-minor| of A_cor·U, supplied by iterating the bordered-Gram recursion det(Q Q^T) = prod ||q_i^perp||^2;
this yields the reduced weight at dims (b-j, M2-j) exponent (a-j)."  I want this claim independently checked.
</task>

<output_contract>
Answer Q1–Q5 in order, each ≤ 6 sentences. End with a one-line VERDICT: "bordered-Gram is load-bearing" OR
"bordered-Gram is NOT load-bearing; the corner-shrink is <X>". Give exact rows/cols/exponents where asked.

Q1. Take the cut-t* residual weight ∫ det(Q_b Q_b^T)^(-a/2) dA_cor (b corank rows, exponent a). Apply the
    weak-direction elimination (M2 -> M2-j) via EITHER the strong-minor factorisation above OR PSD-monotonicity
    (Z Z^T ⪰ eps^2 · P_strong). What are the rows, cols, and exponent of the resulting reduced weight, and does
    it converge at the anchor?  (Compute cols-rows+1 vs exponent.)

Q2. The design NEEDS the reduced weight at dims (b-j, M2-j) exponent (a-j). Compared to Q1's output, which of
    {rows, cols, exponent} must additionally change, and by how much? Can the one-step bordered-Gram recursion
    (iii) — or its iterate det(Q Q^T)=prod||q_i^perp||^2 — change those quantities? (State precisely what the
    row-peel identity does to rows/cols/exponent when you peel one Gram row.)

Q3. Is Wenn(Z) = ∫ det(Q_b Q_b^T)^(-a/2) dA_cor bounded as sigma_min(Z) -> 0 within shell j, or does it blow up?
    Give the blow-up exponent in sigma_min at the anchor (a=b=2, M2=3, j=1). Contrast with the SAME integral but
    with b-corank rows replaced by (b-j) rows and exponent a replaced by (a-j).

Q4. If Q1's weak-elimination alone does NOT reach the design dims, name every distinct reduction still required to
    get from (Q1 output) to (b-j, M2-j, a-j), and attribute each to a mechanism: (weak-direction elimination) /
    (bordered-Gram Jacobian) / (a different choice of peel/cut) / (something else). Be explicit about what shrinks
    the corank-row count b->b-j and the exponent a->a-j.

Q5. Is the one-step bordered-Gram / Schur recursion (iii) the LOAD-BEARING primitive for the corner-shrink, or is
    PSD-monotonicity (i) applied at a re-indexed corank level sufficient? If bordered-Gram is not load-bearing,
    say what its true (if any) role is here.
</output_contract>

<grounding_rules>
Distinguish OBSERVED (an exact identity / a convergence-lemma computation you can carry out) from INFERRED
(a design judgement). Flag each Q's answer as [exact] or [inference]. Do NOT accept the prior design note's
assertion as given — derive the rows/cols/exponents yourself. If a claimed reduction cannot be produced by any
listed banked tool, say so explicitly and name what would be required instead. Do not assume the deep-product Z
has any structure beyond: full rank generically, j singular values < eps on shell j.
</grounding_rules>
