<task>
Lean-4/Mathlib measure-theory: pick the CLEANEST assembly for a cap-B finiteness lemma, given existing
lemmas. Deep linear network RLCT, depth-2 Schur core.

GOAL lemma (frobSq_capB_inner_lt_top): for an r×r matrix R (r≥3) with pivot R₀₀=1 and |entries|≤1, and
c' < p/2:
    ∫_{S ∈ matBox r p T} frobSq(R·S)^{−c'} < ⊤.
(matBox r p T = box of r×p matrices, entries in [−T,T]; frobSq = squared Frobenius norm; rmatMul = product.)

AVAILABLE (all sorry-free in the repo):
- schur_minorPivot_split {r p} 1 (hj:1≤r): ∃ c₀ c₁, 0<c₀ ∧ 0<c₁ ∧ ∀ R S, (|R|≤1) → (det-dominance) →
  (det M11≠0) → ∃ Sc, [Sc = M22 − M21·M11⁻¹·M12] ∧ [det id] ∧
  c₀·(frobSq(topRow of R·S) + frobSq(Sc·S_bot)) ≤ frobSq(R·S) ≤ c₁·(same).   [the N2b two-sided bound]
- frobSqTopRowP_eq_shearP: frobSq(topRow of R·S) = ∑_{q:Fin p} (S₀q + ∑_a R₀,₁₊ₐ·S₁₊ₐ,q)².
- stepShearP_r (r p) (b:Fin(r-1)→ℝ, |b|≤1) (Sc) (T) (c'):
    ∫_{S∈matBox r p T} ((∑_q (S₀q + ∑_a b_a S₁₊ₐq)²) + frobSq(Sc·S_bot))^{−c'}
      ≤ ∫_{S_bot∈matBox (r-1) p T} ∫_{T'∈morseBox p (r·T)} ((∑_q T'q²) + frobSq(Sc·S_bot))^{−c'}.
- radial_morse_dominates_lt_top {m k} (c') (hc':c'<(m+1)/2) (0≤c') (T) (W:(Fin k→ℝ)→ℝ) (0≤W) (measurable W):
    ∫_{z∈morseBox k T} ∫_{p∈morseBox (m+1) T} (∑_i p_i² + W z)^{−c'} ≤ Kbound·vol(morseBox k T) < ⊤.
- radial_morse_residual_power_le (m) (c'): the per-w shifted Morse bound (needs (m+1)/2 < c', the OPPOSITE
  regime — this is the cap-A peel, NOT cap-B).
- ofReal_rpow_le_const_mul (X F c₀ c'): 0<c'→0<c₀→0≤X→0≤F→ c₀·X≤F → (X=0→F=0) →
    ofReal(F^{−c'}) ≤ ofReal(c₀^{−c'})·ofReal(X^{−c'}).
- The carve route coreSchurGenVal_lt_top exists but uses the IH/recursion (cap-A only) — NOT available cap-B.

THE TENSION: two candidate assemblies, both have a snag:
(A) DROP the residual: from N2b lower bound, c₀·frobSq(topRow) ≤ frobSq(R·S) → ofReal_rpow_le_const_mul →
    frobSq(R·S)^{−c'} ≤ c₀^{−c'}·frobSq(topRow)^{−c'}. Then frobSqTopRowP_eq_shearP makes topRow the shear
    sum, and I want ∫_S (shear sum)^{−c'} < ⊤. BUT stepShearP_r's LHS integrand is (shear + frobSq(Sc·S_bot)),
    not (shear) alone. SNAG: to use stepShearP_r I'd set its Sc:=0 so frobSq(0·S_bot)=0, but then the LHS is
    (shear + 0) = shear — does (shear+frobSq(0·S_bot))^{−c'} = (shear)^{−c'} hold definitionally / by simp?
    And the ofReal_rpow_le_const_mul side-condition (X=0→F=0): when topRow=0, is frobSq(R·S)=0? (needs the
    UPPER N2b bound with the residual, so I can't fully drop it for the side-condition.)
(B) KEEP the residual: N2b gives frobSq(R·S) between c₀·X and c₁·X with X = topRow+frobSq(Sc·S_bot). Use
    ofReal_rpow_le_const_mul on the full X (side-condition X=0→F=0 from the c₁ upper bound — clean). Then
    ∫_S X^{−c'} via stepShearP_r → ∫_{S_bot}∫_{T'∈morseBox p} (∑T'² + frobSq(Sc·S_bot))^{−c'}. Then
    radial_morse_dominates_lt_top with m+1=p, W = frobSq(Sc·S_bot). SNAG: radial_morse_dominates_lt_top wants
    W : (Fin k → ℝ) → ℝ (z over morseBox k T, a FLAT Fin-k vector), but S_bot is matrix-shaped
    (Fin(r-1)→Fin p→ℝ) over matBox (r-1) p T. Need a reshape matBox (r-1) p T ≃ morseBox ((r-1)*p) T (MP)
    + W∘reshape measurable + frobSq(Sc·S_bot) ≥ 0. Is that the intended use, and is the reshape in the repo
    (matToFlat / piCurry style)?

QUESTION: which assembly (A or B) is cleaner/more robust in Lean v4.29, and what's the exact resolution of
its snag? For (B): the matBox→morseBox flat reshape + measurability of W = frobSq(Sc·S_bot)∘reshape — is this
the clean path, and does radial_morse_dominates_lt_top's k-flat shape accept it? For (A): does the
ofReal_rpow_le_const_mul side-condition force me to keep the upper bound anyway (making B no worse)?
</task>

<output_contract>
Terse. 1: pick A or B + the one-line reason. 2: the exact snag-resolution for the chosen one (the missing
sub-lemma(s), named, with shape). 3: the side-condition (X=0→F=0) handling. 4: the ONE highest-risk step.
Mark each [LOW/MED/HIGH]. Flag inference vs known v4.29 fact.
</output_contract>

<grounding_rules>
Design review, no full proofs. If unsure a lemma/reshape exists, say "verify". Mark risks.
</grounding_rules>
