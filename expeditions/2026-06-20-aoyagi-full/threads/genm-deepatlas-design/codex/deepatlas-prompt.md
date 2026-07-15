<task>
I am designing an explicit "stratified-resolution atlas" for a composite-rank locus, to be formalised in
Lean 4 / Mathlib as a change-of-variables + finite-cover finiteness argument. I need you, independently, to
(A) design the cleanest EXPLICIT chart family (coordinate maps + Jacobians), and (B) resolve the one
structural crux (the product-layer reduction). Argue from the definitions; do not assume my framing is right.

SETTING (exact algebra over the reals).
- Deep layers L_0,...,L_{p-1}, with L_i a real matrix of shape v_i x v_{i+1}. Write the composite
  Z = L_0 · L_1 · ... · L_{p-1}  (shape v_0 x v_p). Let rho = min(v_0,...,v_p).
- Target locus in the PARAMETER space  P := prod_i R^{v_i x v_{i+1}}:   S_s := { (L_i) : rank Z <= s },
  for s = rho - k, k = 1,...,rho.
- FACT (verified 3 ways, do not re-derive): the parameter-space codim of S_s is the "composite-rank"
  recursion, NOT the determinantal codim (v_0-s)(v_p-s):
      CR((v_0,...,v_p), s) = min_{0<=r<=min(v_{p-1},v_p)} [ (v_{p-1}-r)(v_p-r) + CR((v_0,...,v_{p-2}, r), s) ],
      base CR((v_0,v_1),s) = (v_0-s)_+ (v_1-s)_+,  inner = 0 when r <= s.
  Mechanism: stratify by r = rank(last layer); restricting the head-composite to a generic r-dim input
  subspace = replacing the last width by r. For a single matrix (p=1) CR = determinantal. For products it is
  strictly smaller (e.g. widths (1,2,1), s=0: CR=1, determinantal would say 2).

WHY (measure context). The eventual integral is  int over P of  (loss)^{-q} * (det charge)^{-a/2} d(params),
where loss vanishes on S_s and the measure near S_s scales like t^{codim-1} dt. I need each chart to
monomialise this so a per-stratum radial integral  int_0^delta r^{C_k - 1 - 2q} dr  is read off, with
C_k = min( u*rho , u*(rho-k) + CR(deep,rho-k) - gamma ) the target exponent. So the atlas must expose the
codim CR(deep,rho-k) as an explicit normal (transverse) coordinate with a monomial (ideally |det|=1 or a
monomial power) Jacobian, covering a neighborhood of S_s up to a null set by FINITELY many charts.

THE TEMPLATE I must mirror (a solved SINGLE-matrix case, p=1). To resolve {rank W <= ell} for one matrix
W (u x d): pick a size-ell invertible pivot minor W11 (block W = [[W11,W12],[W21,W22]]); coordinatise
  W  <->  (W11, W12, W21, E),   E := W22 - W21 · W11^{-1} · W12   (the Schur complement, (u-ell)x(d-ell)).
The map (.,.,.,E) -> W is a TRANSLATION in the W22 block by the constant-in-E shift W21 W11^{-1} W12, so its
Jacobian is identically 1; and rank W = ell + rank E, so {rank W <= ell} = {E = 0} (codim (u-ell)(d-ell)).
Finitely many pivot minors cover {rank W = full-or-less}; the block-LU rank identity is the workhorse.
This single Schur big-cell IS the whole atlas for one matrix.

WHAT I FOUND for the product (verified numerically-exactly):
- rank(head · L_last) = rank(head · A) whenever L_last = A·B with B full row rank (A = the pivot columns).
- The CR minimiser can force SEVERAL layers below generic rank (telescopes): e.g. deep widths (2,2,2), s=0,
  CR=3 decomposes as [E-codim 1 at the last layer reduced to rank 1] + [E-codim 2 at the reduced head chain
  (2,1) at rank 0]. So the resolution looks like a NESTED chain of Schur big-cells, one per recursion level,
  total transverse codim = sum of per-level (reduced-block) Schur-complement dims = CR.

<questions>
Q1. What is the cleanest EXPLICIT chart family for S_s that mirrors the single-matrix Schur big-cell, and
    what is the chart INDEX (finite set)? Is it exactly the CR-recursion tree of (rank r of the current last
    layer, choice of size-r pivot minor) down to termination (r<=s or chain length 2)?

Q2. THE CRUX — the product-layer reduction. After the last-layer chart-5 gives coords (Delta,B,C,E) with
    A := pivot columns of L_last (v_{p-1} x r) and E the transverse Schur block, the reduced chain's "last
    layer" is the PRODUCT  L_{p-2} · A  — a bilinear function of the free L_{p-2} and the chart datum A, NOT
    a free coordinate. How do you make the recursion an honest change of variables / measurable reduction
    despite this product? Concretely: is the right move a right-multiplication coordinate change
    L_{p-2} -> L_{p-2} · G on the free layer L_{p-2} (G an invertible v_{p-1} x v_{p-1} completion [A | A_perp]
    from the chart), splitting L_{p-2}·G = (L_{p-2}·A , L_{p-2}·A_perp) with a constant (chart-dependent)
    Jacobian |det G|^{v_{p-2}}, so the reduced layer L_{p-2}·A becomes a genuine free coordinate and A_perp
    the transverse directions? Or is there a cleaner formulation (e.g. an induction on chain length that
    never forms the product)? Give the exact CoV and its Jacobian.

Q3. Is the whole resolution best organised as an INDUCTION on chain length p (peel the last layer, reduce to
    a length-(p-1) chain), with the base case = the single-matrix Schur big-cell? If so, state the inductive
    step's precise statement (what is assumed for the shorter chain, what is proved for the length-p chain),
    including how the outer det-charge factor det(Q_b Q_b^T)^{-a/2} (Q_b = A_cor · Z, a separate corank
    integral) rides along — does it decouple from the deep reduction or must it be threaded?

Q4. The measure/monomialisation. With several Schur blocks E_1,...,E_m (one per dropped level) as transverse
    coords, the loss near S_s is a sum of squared-scale terms. In the "comparable" regime all E_i scale like
    one radial t (giving t^{CR-1} dt). Do NON-comparable scalings (some E_i << others) ever produce a
    stratum with radial exponent LOWER than CR(deep,rho-k) (which would break the C_k gate), or is CR the
    infimum over all scalings? Argue whether the finite Schur-big-cell atlas EXHAUSTS the degeneration
    (every parameter point near S_s lies in some big-cell up to a null set), i.e. index-completeness.

Q5. Size/feasibility: as a Lean formalisation mirroring a 5-file / ~690 LoC single-block front atlas
    (chart-5 big-cell CoV with |det|=1, a polar H-fibre scaling, an exponent-gate arithmetic lemma, a
    generic finite-cover gluing lemma, and a Schur-complement rank identity already banked), how much extra
    is the multi-layer telescoping — a bounded induction on chain length reusing the single-block pieces, or
    genuinely new machinery? Flag any place where the honest resolution could WALL (not just be laborious).
</questions>
</task>

<output_contract>
- For each of Q1-Q5: label claims [FACT] (provable now), [INFERENCE] (your reasoned judgement), or
  [SPECULATION]. Keep facts vs judgement distinct.
- For Q2 give the EXACT change of variables (matrices, shapes, the completion G, the Jacobian determinant).
- For Q4 give a clean argument (or a counterexample) on whether CR is the infimum radial exponent; if you
  cannot settle it, say what would settle it.
- End with the single most likely place the honest atlas WALLS, and the one check that would de-risk it.
- Do not write code; reason in exact algebra.
</output_contract>

<grounding_rules>
- Everything is over R; ranks are real ranks; "generic" = outside a proper Zariski-closed (measure-zero) set.
- The CR recursion and C_k formula are established facts; do not relitigate them. Focus on the EXPLICIT
  charts, the product-layer reduction, and index-completeness.
- If my telescoping picture is wrong, say so and give the correct structure.
</grounding_rules>
