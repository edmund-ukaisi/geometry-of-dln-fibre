# Consult: cleanest statement + decomposition for the L=2 Schur loss germ (`schur_loss_germ_L2`)

Lean 4 / Mathlib v4.29. This is a FORMALISATION design review, not a math-truth question — the math is
settled. I want your red-team on the STATEMENT SHAPE and the DECOMPOSITION before I write ~400 lines.

## Context (all banked, sorry-free, in `D1L2PhiExpl.lean`)

For `H : Fin 3 → ℕ`, `r : ℕ`, `v : Params H` (= `∀ s, Matrix (Fin (H s.castSucc)) (Fin (H s.succ)) ℝ`),
`B : Matrix (Fin (H 0)) (Fin (H (Fin.last 2))) ℝ`. `flatDim H` = total param count; `paramsEquivFlat H :
Params H ≃ᵐ (Fin (flatDim H) → ℝ)` (measurable), `paramsEquivFlatLinear H` its `≃ₗ[ℝ]` twin (same
function, `paramsEquivFlatLinear_symm_coe`). `prod H A` = layer product (L=2: `= v0 * v1`).

- `dlnLoss H B A = ∑ i, ∑ j, ((prod H A - B) i j)^2`  (squared Frobenius).
- `lossFlatShift H B v w = dlnLoss H B ((paramsEquivFlat H).symm (w + paramsEquivFlat H v))`.
- `BlockParamsL2 H r = Matrix (Fin r ⊕ Fin (H0-r)) (Fin r ⊕ Fin (H1-r)) ℝ × Matrix (Fin r ⊕ Fin (H1-r)) (Fin r ⊕ Fin (H2-r)) ℝ`.
- `blockFlatEquiv_L2 H r I K J … : (Fin (flatDim H) → ℝ) ≃L[ℝ] BlockParamsL2 H r` — a LINEAR reindex:
  `(b x).1 = reindex (sumSplit I).symm (sumSplit K).symm ((paramsEquivFlatLinear H).symm x 0)`, similarly `.2`
  with layer 1. `sumSplit I hI : Fin r ⊕ Fin (H0-r) ≃ Fin (H0)`, `sumSplit_inl : sumSplit I (inl a) = I a`.
- `schurChartRaw H r : BlockParamsL2 → BlockParamsL2`, blocks `A0=[[X,Y],[Z,W]]`, `A1=[[S,T],[Uu,V]]` ↦
  `(fromBlocks X Y (Z*S+W*Uu) (W-Z*X⁻¹*Y), fromBlocks (X*S+Y*Uu) (X*T+Y*V) Uu (V-Uu*M11⁻¹*(X*T+Y*V)))`,
  `M11=X*S+Y*Uu`. 16 `@[simp]` block readbacks all `rfl`.
- `schurChart_global I K J hI hK hJ P₀ (hX : P₀.1.toBlocks₁₁.det ≠ 0)
    (hM11 : (P₀.1.toBlocks₁₁*P₀.2.toBlocks₁₁ + P₀.1.toBlocks₁₂*P₀.2.toBlocks₂₁).det ≠ 0)` gives
    `∃ Φ f', ContDiff ℝ 2 Φ ∧ HasFDerivAt Φ f' 0 ∧ Φ 0 = 0 ∧
      Φ =ᶠ[𝓝 0] fun w => (b).symm (schurChartRaw (b w + P₀) - schurChartRaw P₀)`.
- `Core.schur_product_factor X Y Z W S T Uu V [Invertible X] [Invertible (X*S+Y*Uu)] :
    (Z*T+W*V) - (Z*S+W*Uu)*⅟(X*S+Y*Uu)*(X*T+Y*V) = (W-Z*⅟X*Y)*(V-Uu*⅟(X*S+Y*Uu)*(X*T+Y*V))`.
- `exists_common_pivot_L2_at H r v B hopt hB : ∃ I K J, Inj I ∧ Inj K ∧ Inj J ∧
    ((prod H v).submatrix I J).det ≠ 0 ∧ ((v 0).submatrix I K).det ≠ 0`.
- `dln_hchart_flat H B v F Φ f' (hΦ) (hΦ') (hfix) (hgerm : lossFlatShift H B v =ᶠ[𝓝 0] fun w => F (Φ w)) :
    rlctAt H (dlnLoss H B) v = rlctAtOn F 0`.

Mathlib have: `submatrix_mul_equiv M N e₁ (e₂ : _ ≃ _) e₃ : M.submatrix e₁ e₂ * N.submatrix e₂ e₃ = (M*N).submatrix e₁ e₃`;
`fromBlocks_multiply`; `toBlocks_fromBlocks₁₁…₂₂`; `fromBlocks_toBlocks`; `Equiv.sum_comp`; `Fintype.sum_sum_type`;
`Matrix.invOf_eq_nonsing_inv`; `invertibleOfDetNeZero` (det≠0 → Invertible, `⅟ = ⁻¹`).

## The target `schur_loss_germ_L2` and my plan

GOAL: near the flat origin, `lossFlatShift H B v =ᶠ[𝓝 0] fun w => F (Φ w)` with `Φ` from
`schurChart_global` and `F` the sum-of-squares readout `∑ p² + ∑ qₑ²` (`p` = the M11,M12,M21 regular
blocks; `qₑ` = M22-B22 = product bottom-right minus B, reconstructed from chart output).

Plan:
1. Take `I K J` from `exists_common_pivot_L2_at`; set `b := blockFlatEquiv_L2 …`, `P₀ := b (paramsEquivFlat H v)`.
   Then `b w + P₀ = b (w + flat v)` (b linear). Verify the two det conditions for `schurChart_global`:
   `P₀.1.toBlocks₁₁ = (v 0).submatrix I K` (banked readback) → `hX` from common pivot; and the product-pivot
   `M11(P₀) = (submatrix (prod v) sI sJ).toBlocks₁₁ = (prod v).submatrix I J` → `hM11` from common pivot.
2. `recoverProduct Q := fromBlocks Q.2₁₁ Q.2₁₂ Q.1₂₁ (Q.1₂₁ * Q.2₁₁⁻¹ * Q.2₁₂ + Q.1₂₂ * Q.2₂₂)`. Prove
   `recoverProduct (schurChartRaw P) = P.1 * P.2` on `{det X≠0, det M11≠0}` (fromBlocks_multiply for the 3
   regular blocks + schur_product_factor for the ₂₂ corner, ⅟↔⁻¹ bridge).
3. Reindex-product identity: `(b x).1 * (b x).2 = (prod H (flatSymm x)).submatrix (sumSplit I) (sumSplit J)`
   via `submatrix_mul_equiv` (middle equiv `sumSplit K`).
4. `F(x) := ∑ (a : Fin r ⊕ Fin(H0-r)), ∑ (bb : Fin r ⊕ Fin(H2-r)),
        ((recoverProduct (b x + schurChartRaw P₀) - B.submatrix (sumSplit I) (sumSplit J)) a bb)^2`.
   Frobenius reindex: `∑ i j ((M-B) i j)² = ∑ a bb ((submatrix (M) sI sJ - submatrix B sI sJ) a bb)²` (Equiv.sum_comp ×2).
5. Germ: near 0, `Φ w = b.symm(schurChartRaw(b w + P₀) - C)`, so `b (Φ w) + C = schurChartRaw (b (w+flat v))`,
   so `recoverProduct (b (Φ w) + C) = (b(w+flat v)).1 * (b(w+flat v)).2 = submatrix (prod (flatSymm(w+flat v))) sI sJ`
   (needs dets ≠ 0 at `w + flat v`, holds near 0 by continuity — same `eventually_ne` pattern as `schurChart_global`'s
   `hdom1..4`). Then `F (Φ w) = ∑ ((submatrix prod sI sJ - submatrix B sI sJ) a bb)² = loss = lossFlatShift w`.

## Questions

1. **Statement shape.** Is `∃ Φ f' F, ContDiff ℝ 2 Φ ∧ HasFDerivAt Φ (f':…) 0 ∧ Φ 0 = 0 ∧
   lossFlatShift H B v =ᶠ[𝓝 0] fun w => F (Φ w)` the right deliverable? Or should I ALSO chain
   `dln_hchart_flat` and conclude `rlctAt H (dlnLoss H B) v = rlctAtOn F 0`? (Next tide reindexes F into the
   consumer's `(Fin nReg → ℝ) × Y ↦ ∑p²+∑qₑ²`.) Should F already be block-split into `(∑ regular²)+(∑ ₂₂²)`
   (three fromBlocks blocks + the ₂₂ block), or is the single `∑_{a,bb} residual²` form better for the germ (defer
   the split to the reindex tide)?
2. **The `recoverProduct` route** vs alternatives. Is reconstructing M22 via `schur_product_factor` inside a
   total `recoverProduct` the cleanest, or is there a slicker identity? Any trap making `recoverProduct∘schurChartRaw
   = P.1*P.2` painful (the ⅟ vs ⁻¹ instance juggling, `Invertible` synthesis on `X*S+Y*Uu`)?
3. **Reindex-product step 3.** `(b x).1 = reindex (sumSplit I).symm (sumSplit K).symm (layer0)`. Is
   `reindex e₁ e₂ M = M.submatrix e₁.symm e₂.symm` the reliable rewrite, and does `submatrix_mul_equiv` fire with
   `e₂ = (sumSplit K).symm.symm = sumSplit K` cleanly, or is there a `reindex`-vs-`submatrix` defeq snag?
4. **Pitfalls** in the flat/flatLinear bridge (`paramsEquivFlat` in lossFlatShift vs `paramsEquivFlatLinear` in b),
   and in `H (Fin.last 2)` vs `H 2` for the `B` column index / `sumSplit J`.
5. Anything that makes this LESS than ~400 lines, or any hidden wall.

Answer concisely, focused on statement shape + decomposition risks. Flag the single biggest risk.
