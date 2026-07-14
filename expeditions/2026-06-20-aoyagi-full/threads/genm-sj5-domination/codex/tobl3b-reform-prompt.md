<task>
You are a measure-theory / random-matrix analyst red-teaming a Lean formalisation plan. A determinant-of-Gram integral must be bounded UNIFORMLY as a deeper matrix degenerates. One proposed route needs a Cauchy–Binet det-Gram identity that is ABSENT from the proof library; a colleague proposes re-expressing the bound via ITERATED SINGLE-DIRECTION spectral peels of an already-built brick. Adjudicate whether the iterated route closes, or whether a b×b determinant identity is genuinely irreducible. Withhold nothing on the analysis; I want your independent derivation.

SETTING (exact objects).
- Deeper product Z : M₂×n real matrix, ranging in a bounded box; rank Z ∈ {0..M₂}, generically full.
  Singular values σ₁≥…≥σ_{M₂}. "Shell j" = exactly j of them are < ε (weak), the top M₂−j are ≥ ε (strong).
- Corank block A ("A_cor") : b×M₂, integrated over a bounded box matBox b M₂ 1.
- Freed corner Γ : a×b, integrated over a bounded box. A pivot energy w = ‖Γ'·Z‖²_F (Frobenius) from a
  DEEPER reduced front block Γ' is a positive constant w.r.t. the (A,Γ) integration.
- The parent off-sector integrand (over A and Γ, at fixed Z) is
      ∫_{A∈box} ∫_{Γ∈box} ( w + ‖Ccross + Γ·(A·Z)‖²_F )^{−c'} dΓ dA.
- Integrating Γ first (a full a×b Gaussian-type corner peel over the b-row block Q := A·Z, b×n) yields,
  for a.e. A (full row rank b), a residual with a determinant-of-Gram divisor:
      ≤ const · det(Q Qᵀ)^{−a/2} · w^{−(c'−ab/2)},   Q = A·Z.
  So the A-integral of the residual is the "corank weight"
      Wenn(Z) := ∫_{A∈box} det((A·Z)(A·Z)ᵀ)^{−a/2} dA.
  Wenn(Z) is FINITE for full-rank Z iff a < M₂−b+1, but sup over degenerating Z is +∞ (blows up as σ_min(Z)→0).

THE BANKED BRICK (call it SPEC). For any r×n "tail" matrix P with 0<sigMin(P)≤B, any m×r "front" F integrated
over its bounded box, and a SECTOR hypothesis "all Gram-eigenvalues of P·Pᵀ except the single smallest are
≥ κ²" (i.e. EXACTLY ONE collapsing singular direction of P), SPEC gives:
      ∫_{F∈box} frobSq(F·P)^{−c'} dF ≤ C · sigMin(P)^{−α'},   with C<∞ σ-independent,
for any α' with max(0, 2c'−m(r−1)) < α' < m. Here frobSq(F·P)=‖F·P‖²_F=trace(F P Pᵀ Fᵀ)=∑_k λ_k·‖(F·U)_{·k}‖²
(λ_k eigenvalues of PPᵀ, U its eigenvectors). SPEC is a SINGLE-collapse, FROBENIUS-trace bound: the integrand
is a trace-loss to a single power, one collapsing direction. A separate "tail tube" then closes
∫ sigMin(P)^{−α'} d(deeper params) < ∞ ⟺ α' < D (a codimension count).

ALSO BANKED: PSD-determinant monotonicity: A⪰0, B−A⪰0 ⟹ det A ≤ det B (for real symmetric PSD). Already used
to prove the shell-0 (all-strong) uniform bound Wenn(Z) ≤ ε^{−ab}·Wenn(I) via ZZᵀ⪰ε²I ⟹ det(AZZᵀAᵀ)≥ε^{2b}det(AAᵀ).

DESIGN TARGET the re-formulation must reproduce (charges, all exact-ℕ, already Lean-verified):
- shell-j reduces to a DEEPER comparator "redChain(t★+j)" with a SHRUNK freed corner (a−j)×(b−j),
  charging ½(a−j)(b−j), plus the deeper minAdm(redChain(t★+j)).
- Total charge C_j = (a−j)(b−j) + minAdm(redChain(t★+j)) ≥ minAdm(M), with the IH firing because
  c' < ½·minAdm(M) ≤ ½·C_j (strict). j saturates at r=min(a,b).
- The reduced det-Gram convergence in the design is (a−j) < (M₂−j)−(b−j)+1 = M₂−b+1 (corner AND ambient both shrink by j).
</task>

<questions>
Q1 (CRUX). Can the shell-j corank weight Wenn(Z) — a b×b det-of-Gram raised to −a/2 — be bounded UNIFORMLY
in the j weak directions of Z by ITERATING SPEC (the single-collapse frobSq bound) once per weak direction,
WITHOUT any b×b Cauchy–Binet / determinant-factorisation identity? Derive it or show where it breaks. Be
explicit about: does SPEC's frobSq(F·P) integrand ever equal / dominate / get dominated by the det-of-Gram
det(QQᵀ)^{−a/2} for b>1? At what b does det(QQᵀ) coincide with a frobSq? If you must first reduce b>1 to a
chain of b=1 problems, what CoV / identity does that reduction require, and is it a determinant identity in disguise?

Q2. If iterating SPEC does NOT directly consume the det-Gram, is there an ALTERNATIVE using ONLY (i) SPEC and
(ii) PSD-determinant monotonicity that reproduces the design's shell-j reduction (corner-shrink to (a−j)(b−j)
+ deeper comparator), with the deeper convergence (a−j)<M₂−b+1? Try: ZZᵀ ⪰ ε²·(projection onto the M₂−j strong
directions); what reduced object does det(A ZZᵀ Aᵀ) ≥ ε^{2b} det(A P_strong Aᵀ) leave, and does its A-box
integral converge at exponent a/2 over a b×(M₂−j) block? Compute the convergence exponent and compare to the
design's (a−j)<M₂−b+1. Does the crude PSD projection (full b×b corner, strong-projected Z) converge, or must
the corner ALSO shrink — and if it must, what mechanism shrinks it in an iterated single-direction scheme?

Q3. The determinant of a Gram matrix factorises as det(QQᵀ)=∏_{i=1}^{b}‖q_i^⊥‖² (Gram–Schmidt/QR: q_i^⊥ = q_i
minus its projection onto q_1..q_{i-1}). Does this row-wise factorisation give a genuine ITERATED single-row
peel of Wenn(Z) into b successive 1-dimensional (b=1-type, frobSq) integrals — i.e. does
∫_{A∈box} ∏_i ‖(A_i·Z)^⊥‖^{−a} dA factor / iterate cleanly, and does each factor match SPEC's frobSq shape?
What is the Jacobian of the Gram–Schmidt CoV on A, and does it reintroduce a determinant?

Q4. NET VERDICT. Does the iterated-single-direction-spectral route CLOSE the uniform shell-j bound reusing only
SPEC + PSD-det-monotonicity (no Cauchy–Binet, no new b×b determinant identity)? Or is a b×b determinant identity
(Cauchy–Binet, OR the Gram–Schmidt/Cholesky determinant product det(QQᵀ)=∏‖q_i^⊥‖²) genuinely IRREDUCIBLE here?
If irreducible, which single identity is the MINIMAL one to build, and is it strictly smaller than full Cauchy–Binet?
State your confidence and the one computation that would flip your verdict.
</questions>

<output_contract>
Answer Q1–Q4 in order. For each: a crisp VERDICT line, then the derivation/where-it-breaks. Give the exact
convergence exponent in Q2. In Q4, name the minimal identity if one is irreducible. Distinguish what you
INFER from what you can DERIVE exactly. Do not rubber-stamp; if the iterated route fails, say so plainly.
</output_contract>

<grounding_rules>
Work from the objects as stated. frobSq = squared Frobenius norm = trace of the Gram. det(QQᵀ) is the FULL
Gram determinant (product of all b eigenvalues), not the smallest. SPEC is single-collapse (ONE small
singular direction, sector hypothesis). The design charges are fixed and correct; only the CoV MECHANISM is
in question. "Box" = a bounded hypercube of matrix entries; integrals are Lebesgue. Do not assume any library
has Cauchy–Binet or a QR/Cholesky determinant lemma (they are absent).
</grounding_rules>
