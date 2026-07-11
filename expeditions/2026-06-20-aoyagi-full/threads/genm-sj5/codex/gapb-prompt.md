<task>
Lean 4 + Mathlib v4.29 (pinned). I am formalising a finiteness lemma. I need the cleanest
proof ROUTE (exact Mathlib lemma names + proof skeleton) for TWO sub-lemmas. Diagnosis is what
I want — do not write a full proof I can't verify; name the exact API and flag any lemma you are
unsure exists in v4.29.

CONTEXT: real matrices `Matrix (Fin n) (Fin n) ℝ`. Mathlib has (confirmed present, v4.29):
- `Matrix.PosSemidef`, `Matrix.PosDef`
- `Matrix.PosSemidef.eigenvalues_nonneg`, `Matrix.IsHermitian.det_eq_prod_eigenvalues`,
  `Matrix.PosSemidef.det_nonneg`, `Matrix.IsHermitian.posSemidef_iff_eigenvalues_nonneg`
- `Matrix.PosSemidef.mul_mul_conjTranspose_same : A.PosSemidef → (B * A * Bᴴ).PosSemidef`
- `detGram_lintegral_lt_top` (my banked lemma): for `X : Matrix (Fin r) (Fin n) ℝ`, `r ≤ n`,
  `a : ℝ`, `a < n - r + 1`:  `∫⁻ X in matBox r n 1, ENNReal.ofReal ((X * Xᵀ).det ^ (-a/2)) < ⊤`
  where `matBox r n 1 = {X | ∀ i j, X i j ∈ Set.Icc (-1) 1}`, integrated w.r.t. the Pi Lebesgue volume.

<q1>
Sub-lemma A (PSD determinant monotonicity). Real symmetric matrices, prove:
  `A.PosSemidef → (B - A).PosSemidef → A.det ≤ B.det`.
Give the cleanest v4.29 route. Candidate routes I see:
 (i) sqrt route: if A PosDef, B = A^{1/2}(1 + A^{-1/2}(B-A)A^{-1/2})A^{1/2}, det B = det A · det(1+C),
     C PSD, det(1+C) = ∏(1+μ_i) ≥ 1. Handle det A = 0 by `PosSemidef.det_nonneg`.
     — Does Mathlib v4.29 have a PSD square root `Matrix.PosSemidef.sqrt` with
       `sqrt_mul_self`/`posSemidef_sqrt`/`PosDef.sqrt` PosDef+invertible? Exact names?
 (ii) eigenvalue/Weyl route: `A ≼ B ⟹ eigenvalues (sorted) λ_i(A) ≤ λ_i(B)`, then
     `det = ∏ λ_i` with all `λ ≥ 0` ⟹ product monotone. Does v4.29 have Weyl monotonicity of
     sorted eigenvalues (min-max / `Matrix.IsHermitian` eigenvalue monotonicity)? Exact name?
 (iii) a direct `1 ≤ (1 + C).det` for `C.PosSemidef` lemma already in Mathlib?
Rank the routes by v4.29-availability and give the exact lemma names + a proof skeleton for the
best one. If a needed lemma is ABSENT in v4.29, say so explicitly.
</q1>

<q2>
Sub-lemma B (the shrinking-image change-of-variables — the RISK). Prove finiteness:
  `∫⁻ (Y,A) in matBox b m 1 ×ˢ matBox m q 1, ENNReal.ofReal ((Q Qᵀ).det ^ (-a/2)) < ⊤`,  Q = Y * A,
  `Y : b×m`, `A : m×q`, `b ≤ m ≤ q`, `0 ≤ a < m - b + 1`.
The intended route (from a pen-and-paper cert): pointwise Loewner majorant
  `Q Qᵀ = (Y A)(Y A)ᵀ ≽ (Y A_S)(Y A_S)ᵀ`  (A_S = first m columns of A; column-drop + Y-congruence),
then det-monotone (sub-lemma A) ⟹ `(Q Qᵀ).det ≥ ((Y A_S)(Y A_S)ᵀ).det`, so the integrand is
`≤ ((Y A_S)(Y A_S)ᵀ).det ^ (-a/2)`. Then a change of variables `X = Y · A_S` (for fixed A_S) to
reduce to the banked single-matrix `detGram_lintegral_lt_top`.
THE TRAP (cert-flagged): the naive CoV pulls out `|det A_S|^{-b}`, and
`∫ |det A_S|^{-b} dA_S` DIVERGES for `b ≥ 1` (det vanishes to order 1 on a codim-1 set). The cert
says the "shrinking image" `{Y·A_S : Y ∈ box}` has volume `2^{bm}|det A_S|^b` which cancels the
`|det A_S|^{-b}`, but ONLY because the integral over the shrinking image is not bounded by a fixed
box (that reintroduces the divergence).
QUESTIONS:
 (a) Is there a CLEAN Lean route to this finiteness that AVOIDS the delicate shrinking-image
     cancellation entirely — e.g. a different majorant, a Gaussian/Wishart moment bound, or bounding
     `∫_Y det((Y A)(Y A)ᵀ)^{-a/2} dY` for fixed A directly by a constant independent of A (is that
     even true / integrable in A)?
 (b) If the shrinking-image cancellation is unavoidable, how hard is it in Lean (Mathlib v4.29
     `MeasureTheory` + `Matrix`)? Is it a "clean standard" change of variables, or genuinely delicate
     (Jacobian of `Y ↦ Y·A_S`, tracking the image domain, the singular integrand)? Give the honest
     verdict: buildable-in-a-tide, or STOP-and-report-to-controller territory?
 (c) The cleanest single reduction you'd recommend to close it, with exact Mathlib lemma names for
     the linear-map determinant CoV (`MeasureTheory.Measure.map_linearMap_addHaar_eq_smul_addHaar`?
     `lintegral_map`? the Jacobian of right-multiplication `Y ↦ Y·A_S`).
</q2>

<output_contract>
Two sections, Q1 and Q2. For Q1: the ranked routes, the chosen route's exact lemma names, a
proof skeleton. For Q2: answer (a),(b),(c) explicitly; (b) MUST give a clear buildable-vs-STOP
verdict with reasoning. Flag every lemma you are not sure exists in Mathlib v4.29. Be concise;
diagnosis over code.
</output_contract>

<grounding_rules>
Distinguish "this lemma exists in v4.29 (I'm confident)" from "a lemma like this probably exists
(verify)". Do not invent Mathlib lemma names — if unsure, describe the content and say "verify name".
</grounding_rules>
