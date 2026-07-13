<task>
Adjudicate a FORMALIZATION-ROUTE question for a specific box integral. Decide, either way,
whether a proposed change-of-variables route CLOSES the integral at the tight threshold or
hits an obstruction. I want your independent verdict; do not assume my framing is right.

SETTING (all exact, real matrices).
- A0 is a 3x2 matrix (x=3 rows, s=2 cols); A1 is a 2x3 matrix (s=2 rows, z=3 cols).
- Loss  L(A0,A1) = ||A0 A1||_F^2  (squared Frobenius norm of the 3x3 product).
- Box integral  I(c) = ∫_{[-T,T]^{6} x [-T,T]^{6}} L^{-c} dA0 dA1  (each entry in [-T,T]).
- KNOWN FACT (established elsewhere, treat as given): I(c) < ∞  iff  c < 5/2.
  Here 5/2 = (1/2)·minAdm(3,2,3), minAdm(3,2,3)=5. This is the TIGHT threshold to reach.

TOOLBOX AVAILABLE FOR THE FORMAL PROOF (Lean4/Mathlib). This is the binding constraint.
- BANKED "qPeel" engine: it proves finiteness of integrals of the STRICTLY BLOCK-ADDITIVE form
      ∫_{deep boxes} ∫_{[0,1]^q} ( Σ_{i=1}^q u_i^2 · U_i )^{-c} · Π_i |u_i|^{h_i}  du dX  < ∞
  where U_i = ||X_i||^2 (X_i in R^{m_i+1} a "deep block"), for  c < (1/2) Σ_i (h_i + 1),
  UNDER the per-block gate h_i ≤ m_i. Its input MUST be exactly the additive corner Σ u_i^2 U_i
  (no cross terms); it uses a q-ary weighted AM-GM. There is NO version tolerating a cross term.
- BANKED general change-of-variables: Mathlib's `MeasureTheory.Function.Jacobian`
  (lintegral_image_eq_lintegral_abs_det_fderiv_mul): needs an explicit differentiable map with a
  computed Jacobian determinant. Also banked: linear/orthogonal CoV (single fixed orthogonal
  matrix, Jacobian |det|=1), and measure-preserving affine shears (Jacobian 1).
- BANKED front-factor Schur corank atom: integrating a freed corank block Γ against
  ||Ccross + Γ·Qb||^2 gives a det(Qb Qbᵀ)^{-p/2} Jacobian and an exponent shift, BUT ONLY when
  Qb Qbᵀ is positive-definite (full row rank), and it leaves a residual Ccross·(I − P), P a
  projector — a coupled term. On this waist that PosDef hypothesis FAILS ("bottleneck chart").
- Mathlib has NONE of: rectangular-SVD parametrisation/measure, Wishart/eigenvalue (Vandermonde)
  density, Weyl integration, Haar measure on O(s), Stiefel manifold V_s(R^z), coarea formula,
  eigenvalue-map differentiability. Building any of these is a research-level effort ("HEAVY").

THE PROPOSED ROUTE ("route C") TO ADJUDICATE.
  Peel A1's OWN corank by a polynomial/rational Schur-complement chart on A1 itself (pivot an
  invertible k×k block of A1, Schur-complement out the residual), using only the banked Jacobian
  CoV, so as to land on the banked qPeel block-additive form — WITHOUT building any SVD/Wishart/
  Stiefel/Haar density. Terminate a flag recursion at s=1-like leaves.

FACTS I HAVE ALREADY COMPUTED (verified by exact symbolic algebra + numerics; you may re-derive):
  1. L = tr(M G) with M = A0ᵀA0 (2x2 PSD), G = A1 A1ᵀ (2x2 PSD). L depends on A1 only through G,
     and on A0 only through M. Equivalently L = <μ,γ> with μ,γ the vectorized Grams in the PSD
     cone of Sym_2 ≅ R^3.
  2. The rank-1 Schur/LU chart on A1 (pivot the (1,1) entry a, so A1 = L·U,
     L=[[1,0],[d/a,1]], U=[[a,b,c],[0,W1,W2]], W = Schur complement) is MEASURE-PRESERVING
     (Jacobian = 1; it is an affine shear), NOT a det-power. Compensating on A0 gives front
     columns g = a1 + (d/a)a2 and a2, and
        L = ||ρ1||^2 ||g||^2 + ||W||^2 ||a2||^2 + 2 <g,a2>·(b W1 + c W2),
     with ρ1=(a,b,c), the last term a genuine CROSS term = 2<g,a2><ρ1,(0,W)>.
  3. That cross term is SIGN-INDEFINITE, and inf over the box of L / (block-additive part) is not
     bounded below by any positive constant (approaches 0), so the block-additive surrogate is
     NOT a one-sided bound on L.

QUESTIONS (answer independently; re-derive anything you doubt).
 Q1. Can a deep-layer polynomial/rational Schur-flag chart on A1 (any pivot pattern, any
     finite flag recursion, using ONLY the banked Jacobian CoV / affine shears / single fixed
     orthogonal CoV — NO SVD/Wishart/Stiefel/Haar density) transform I(c) into the banked qPeel
     block-additive form Σ u_i^2 U_i and reach the TIGHT threshold c<5/2? If yes, exhibit the
     explicit (3,2,3) chart, its Jacobian, and the resulting h_i / m_i feeding qPeel. If no,
     name the precise obstruction.
 Q2. Is the cross term removable by any polynomial/rational (non-orthogonal-frame) chart, or does
     killing it require diagonalizing the 2x2 deep Gram G (i.e. its eigenvectors / left singular
     vectors of A1)? If diagonalizing G is required, does that force building the SVD/eigenvalue
     density that Mathlib lacks — even in the s=2, r=1, det-power-0 special case of (3,2,3)?
 Q3. Alternatively: does the exact reformulation I(c) ∝ ∫∫_{PSD cone × PSD cone} <μ,γ>^{-c}
     (Sym_2 ≅ R^3) admit a clean elementary/polynomial resolution to c<5/2 — OR does getting FROM
     the A0,A1 box TO the cone integral require the Wishart pushforward (integrating out the
     3-dim Stiefel fibre of A1↦G), i.e. the same missing density?
 Q4. VERDICT for route C, one of: MODERATE (clean, buildable on banked pieces, no new density);
     HEAVY (route C hits friction and forces the literal SVD/eigenvalue density — research-level);
     WALL (route C cannot close even in principle). Give the single most important reason and the
     one cheapest test that could overturn your verdict.
 Q5. Width-general remark: does your (3,2,3) conclusion change for general (x,s,z) with s≥2
     (e.g. does det-power (z-s-1)/2 ≠ 0, or s≥3 multiple small singular directions, matter)?
</task>

<output_contract>
Answer Q1..Q5 in order, each ≤ 12 lines. Lead with a one-word tag per question where applicable
(YES/NO/MODERATE/HEAVY/WALL). If you claim route C closes, you MUST give the explicit chart +
Jacobian + h_i/m_i, not a sketch. End with a 3-line "SINGLE CRUX" summary.
</output_contract>

<grounding_rules>
Distinguish DERIVED-HERE (you computed/verified it) from RECALLED (standard result you assert)
from INFERENCE (plausible but unchecked). Do not trust my facts 1-3 blindly; flag any you find
wrong. The binding constraint is the TOOLBOX (what Mathlib has), not whether the math is true in
principle — the integral's finiteness at c<5/2 is given. "Reaching the threshold" means a valid
one-sided (lower) bound on L feeding the block-additive qPeel, or an equivalently-banked engine.
</grounding_rules>
