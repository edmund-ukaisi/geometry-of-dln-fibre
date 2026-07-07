<task>
Fidelity check on a Lean 4 / Mathlib matrix-algebra DEFINITION against a banked, already-proven exact identity. All matrices over ℝ. Notation:
- frobSq M = ∑ᵢⱼ (M i j)²  (squared Frobenius norm)
- ⅟A = the ring inverse for [Invertible A]; A⁻¹ = Matrix.nonsing_inv (equals ⅟A when A invertible, equals 0 when A is not a unit)
- M'.toBlocks₁₁ / ₁₂ / ₂₁ / ₂₂ = the four blocks of a Sum-indexed matrix M' : Matrix (t ⊕ a) (t ⊕ b) ℝ
- schurCompl A B C D := D - C * ⅟A * B
- Qp := Q.submatrix Sum.inl id ; Qb := Q.submatrix Sum.inr id (row-block splits of the tail Q)

BANKED exact identity (proven sorry-free, hypothesis [Invertible M'.toBlocks₁₁]):
  frobSq (M' * Q)
    = frobSq (P * (Qp + ⅟P * B₁₂ * Qb))
      + frobSq (C * (Qp + ⅟P * B₁₂ * Qb) + schurCompl P B₁₂ C D * Qb)
  where P = M'.toBlocks₁₁, B₁₂ = M'.toBlocks₁₂, C = M'.toBlocks₂₁, D = M'.toBlocks₂₂.

NEW def under review:
  schurLoss M' Q :=
    frobSq (M'.toBlocks₁₁ * (Qp + M'.toBlocks₁₁⁻¹ * M'.toBlocks₁₂ * Qb))
      + frobSq (M'.toBlocks₂₁ * (Qp + M'.toBlocks₁₁⁻¹ * M'.toBlocks₁₂ * Qb)
          + (M'.toBlocks₂₂ - M'.toBlocks₂₁ * M'.toBlocks₁₁⁻¹ * M'.toBlocks₁₂) * Qb)

NEW theorem (proven): for hU : IsUnit M'.toBlocks₁₁,
  frobSq (M' * Q) = schurLoss M' Q
  proof: haveI : Invertible P := hU.invertible; rw [frobSq_schur_toBlocks_split M' Q, schurLoss]; simp only [schurCompl, invOf_eq_nonsing_inv]

Answer these three questions.
1. Is schurLoss a FAITHFUL transcription of the banked RHS? Check: (a) the shear coordinate Qp + P⁻¹·B₁₂·Qb appears identically in BOTH frobSq terms; (b) the corank block Γ in schurLoss, written D − C·P⁻¹·B₁₂, equals schurCompl P B₁₂ C D = D − C·⅟P·B₁₂ (given ⅟P = P⁻¹); (c) the CROSS-COUPLING term C·(shear) is PRESENT inside the second frobSq (i.e. the second term is frobSq(C·shear + Γ·Qb), NOT the "clean" wrong form frobSq(Γ·Qb) with the C·shear dropped). Left-to-right matrix multiplication associativity: confirm C * P⁻¹ * B₁₂ parses the same as (C*P⁻¹)*B₁₂ and matches C*⅟P*B₁₂ in schurCompl.
2. Is the ⅟ → ⁻¹ substitution legitimate given ONLY IsUnit M'.toBlocks₁₁? Could nonsing_inv (which is 0 on non-units) differ from ⅟ anywhere within the theorem's hypotheses, breaking the equality?
3. Any way this def is subtly-wrong-but-green: vacuity, mis-associated products, a swapped block (e.g. toBlocks₁₂ vs toBlocks₂₁), or the corank block on the wrong side of the cross term?
</task>

<output_contract>
Three numbered answers, each starting with a verdict token FAITHFUL / DISCREPANCY / UNCERTAIN, then one to three sentences. End with a one-line overall verdict.
</output_contract>

<grounding_rules>
This is a math-fidelity read, not a Lean build. Reason from the algebra as given. If a claim depends on a Mathlib lemma behaving a certain way (e.g. invOf_eq_nonsing_inv, associativity of Matrix.mul), state it as an assumption and flag it as inference vs fact.
</grounding_rules>
