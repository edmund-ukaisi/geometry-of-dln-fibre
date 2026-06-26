<task>
Decorrelated fidelity check on a Lean linearisation and its validation. Be terse and adversarial; point out any actual error. Three questions.

CLAIM 1 (linearisation). The "Schur frame" of a network boundary is the matrix-valued map
  S(X,K,N,E) = [[K, K*N],[X*K, X*K*N + E]]
where X is r×t, K is t×t, N is t×c, E is r×c (real matrices). Treating all four arguments as independent variables, its total differential DS applied to increment (dK,dN,dX,dE) is claimed to have four output blocks:
  TL = dK
  TR = K*dN + dK*N
  BL = dX*K + X*dK
  BR = dE + (X*dK*N + X*K*dN + dX*K*N)

Question A: Is this the correct first-order (product-rule, drop 2nd order) linearisation of S? Check BR carefully: S's BR entry is X*K*N + E, so d(X*K*N) by the 3-factor product rule = dX*K*N + X*dK*N + X*K*dN, plus dE. Does the claimed BR match? Any term dropped, duplicated, or mis-grouped? Also verify TR (entry K*N) and BL (entry X*K).

Question B: The determinant argument: DS is block-lower-triangular in the ordering (dK, dN, dX, dE); the diagonal blocks are dK↦dK (det 1), dN↦K*dN (det |det K|^c on the t×c matrix space), dX↦dX*K (det |det K|^r on the r×t matrix space), dE↦dE (det 1); ALL the off-diagonal couplings (dK*N in TR, X*dK in BL, the three BR terms) read only EARLIER-ordered increment slots, so they sit strictly below the block diagonal and do not affect the determinant. Hence |det DS| = |det K|^(r+c). Is this valid? Specifically does every coupling term genuinely read only earlier-ordered slots (dK first, then dN, then dX, then dE), with NO term reading a LATER slot (which would break lower-triangularity)? Note the diagonal-block dets: left-mult by K on the t×c space gives |det K|^c (c columns), right-mult by K on the r×t space gives |det K|^r (r rows) — confirm these exponents.

CLAIM 2 (validation against a hand-computed (3,3,3,3) determinant). The hand-built Jacobian determinant for the (3,3,3,3) deep linear network instance is
  Frame3333Deriv_det = z0^5 * z9^3 * (z1*z4 - z2*z3)^2.
The two network boundaries have dimensions: boundary s=1 has t=2, r=1, c=1; boundary s=2 has t=1, r=1, c=2. The uniform law |det K_s|^(r_s+c_s) gives: s=1 → |det K_1|^2, s=2 → |det K_2|^3, with det K_1 = z1*z4 - z2*z3 (a 2×2 det) and det K_2 = z9 (1×1). So the two K-blocks of the hand det, (z1*z4-z2*z3)^2 and z9^3, equal |det K_1|^2 and |det K_2|^3.

Question C: Is it sound to say the uniform |det K_s|^(r_s+c_s) law "reproduces" these two factors? Is there any risk the exponents (2 and 3) were cherry-picked rather than forced by r_s+c_s = 1+1 = 2 and 1+2 = 3? The remaining z0^5 factor is claimed to be a separate "radial blow-up" factor not part of the Schur frame. Is excluding z0^5 from the Schur-frame validation legitimate, or does it indicate the validation only covers PART of the hand det?
</task>

<output_contract>
Three sections: A, B, C. For each, a one-word verdict (CORRECT / ERROR / PARTIAL) then 2-4 terse sentences. If you find an actual algebraic error, give the exact wrong term and the correction. End with a one-line overall verdict.
</output_contract>

<grounding_rules>
This is pure linear algebra; you can verify by direct computation. Flag any place where you are inferring intent vs computing a fact. Do not invent network-theory context you cannot derive.
</grounding_rules>
