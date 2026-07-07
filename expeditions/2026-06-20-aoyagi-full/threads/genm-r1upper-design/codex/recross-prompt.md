<task>
Design-review the CORRECTED per-chart Γ-bound for a Lean lemma sjBoundaryPeel in a DLN RLCT proof.
A prior design error was caught: schur_cov is a unit-Jacobian reparametrisation, NOT a Frobenius
isometry. Verify the fix and the corrected formalisable spec. Do NOT rubber-stamp.

EXACT (numerically verified to 1e-10). After the schur reparametrisation D↦Γ=D−CA⁻¹B (Jacobian 1) on
the t-pivot chart (A0=[[A,B],[C,D]], A t×t invertible), the box integrand is EXACTLY
   frobSq(A0·Q) = ‖A·Q̃_p‖² + ‖C·Q̃_p + Γ·Q_b‖²,   Q̃_p = Q_p + A⁻¹B·Q_b,
Q=prod(tail)A' (M1×n), Q_p/Q_b = pivot/non-pivot rows, Γ = corank (M0−t)×(M1−t). The corank Γ is
CROSS-COUPLED with C·Q̃_p (not the clean ‖Γ·Q_b‖² a previous design wrongly assumed).

THE FIX (numerically verified to 1e-10). Bound the box Γ-integral by the FULL-SPACE integral (integrand
≥0, box⊆ℝ^{pq}); the full-space integral is translation-invariant, so a FULL-SPACE ANISOTROPIC-SHIFTED
corank atom applies: for R (q×n) FULL ROW RANK, S (p×n), w>0, c'>pq/2 (p=M0−t,q=M1−t,a=pq),
   ∫_{Γ∈ℝ^{p×q}} (w + ‖Γ·R + S‖²)^{−c'} dΓ = Cinf(pq,c')·det(R Rᵀ)^{−p/2}·(w + ‖S(I−P_R)‖²)^{−(c'−pq/2)},
P_R=Rᵀ(RRᵀ)⁻¹R. With R=Q_b, S=C·Q̃_p, w=‖A·Q̃_p‖²: the SHIFT S is absorbed by translation-invariance,
the ANISOTROPY R by the Gram det, giving per-chart residual
   det(Q_b Q_bᵀ)^{−(M0−t)/2} · (‖A·Q̃_p‖² + ‖C·Q̃_p·(I−P_{Q_b})‖²)^{−(c'−a/2)},   core >0 a.e. (A invertible).
This SUPERSEDES the banked isotropic box atom matBox_corank_residual_le (its R=I,S=0 special case; also
box→full-space). Requires Q_b full row rank M1−t; else (deeper-width bottleneck, 750/5440 chains) the
chart RECURSES (Q_b's rank drop is a deeper boundary = the (S,J) coupling).

<grounding_rules>
- The two exact identities (true integrand; full-space anisotropic-shifted atom) are numerically verified;
  judge the DESIGN: is the box→full-space bound sound, the atom the right tool, the split correct?
- Separate inference from assertion; name any extra assumption.
</grounding_rules>

<output_contract>
1. Is the fix SOUND (box→full-space + anisotropic-shifted Gram atom) and does it correctly handle the
   cross-coupling C·Q̃_p (via translation-invariance) and anisotropy Q_b (via Gram det)? BOUNDED or issue?
2. The corrected split: (i) sjBoundaryPeel (piece 3) = cover + schur MP reparametrisation reducing box to
   ∑ gammaPeelIntegral with the TRUE cross-coupled integrand (plumbing?); (ii) gammaPeelIntegral-finiteness
   = the full-space anisotropic-shifted atom + Q_b-rank branch + recursion. Is this the right home for each
   piece, and is piece 3 now genuinely plumbing (given gammaPeelIntegral carries the true integrand)?
3. The corrected ordered lemma list (5–7), dependency order, load-bearing vs plumbing, flagging: (a) the
   full-space anisotropic-shifted atom (new, generalizes matBox_corank_residual_le), (b) the Q_b full-row-rank
   requirement + the a.e./null handling of {det Q_bQ_bᵀ=0}, (c) the box→full-space monotone bound.
4. Biggest remaining risk + cheapest exact check.
</output_contract>
