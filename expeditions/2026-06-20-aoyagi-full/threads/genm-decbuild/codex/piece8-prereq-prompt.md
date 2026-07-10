<task>
Lean/Mathlib formalisation design question. I need to close a per-chart finiteness for a rank-flag
peel; the question is the MINIMAL prerequisite for the "good stratum," to avoid building an absent
Mathlib primitive.

SETTING. `gammaPeelIntegral` (a chart integral) rewrites (banked, exact) to the freed-Γ triple integral
∫_{A'} ∫_{x=(P,B₁₂,C), P invertible} ∫_{Γ over a FINITE box} freedSchurLoss(x,Γ,Q̃)^{−c'}, where
freedSchurLoss = frobSq(B₀) + frobSq(C'·B₀ + Γ·Q_b), B₀ = P·Q̃ₚ (the reduced leading product), Q_b the
b×q corank tail block, c' < ½·minAdm(M). Goal per chart: this triple integral < ⊤, GIVEN the one-shorter
IH `RouteMBoxThresholdFinite (redChain t M)` (box-finiteness of the reduced chain, threshold ½·minAdm(redChain)).

BANKED Lean facts (verified):
- Regime A `freedSchurLoss_inner_peel_lt_top`: inner-Γ integral < ⊤ GIVEN (i) c' > ab/2, (ii)
  (Q_b Q_bᵀ).PosDef, (iii) core positivity 0<frobSq(B₀). Emits the shift c''=c'−ab/2 and the Gram
  weight det(Q_bQ_bᵀ)^{−a/2}. (a=M₀−t, b=M₁−t.)
- Regime B `freedSchurLoss_inner_bounded_lt_top`: inner-Γ < ⊤ GIVEN 0<frobSq(B₀) + FINITE Γ-domain,
  any c'≥0. NO Gram, NO Q_b condition. But its crude bound freedSchurLoss^{−c'} ≤ frobSq(B₀)^{−c'}
  loses the ab/2 shift.
- Gram normaliser `exists_gram_normalizer`: for PosDef G, ∃ M=G^{−1/2} with |det M|=(det G)^{−1/2}, via
  CFC.sqrt (functional calculus). (So det(Q_bQ_bᵀ)^{−a/2} is handled by CFC, NOT Cauchy-Binet.)
- `posSemidef_self_mul_conjTranspose`: A·Aᵀ is always PosSemidef.
- pivot cover `pivotLocus_eq_iUnion b`: {rank Q_b ≥ b} = ⋃ over b×b minor charts (banked).
- Cauchy-Binet (det(MMᵀ)=Σ_S (det M[:,S])²) is ABSENT from Mathlib v4.29.

MY CLAIM to red-team: the good stratum is {rank Q_b = b} (full row rank), and its closure needs
Regime A (which supplies the ab/2 shift), whose hypothesis (ii) (Q_b Q_bᵀ).PosDef follows from full row
rank — a lemma buildable from `posSemidef_self_mul_conjTranspose` + `posDef_iff_dotProduct_mulVec` +
"Aᵀx≠0 for x≠0 when A has full row rank" (~20 lines). So the MINIMAL prerequisite is
"rank Q_b = b ⟹ (Q_b Q_bᵀ).PosDef", NOT Cauchy-Binet. The complement {rank Q_b < b} splits into
{rank=b−1} (a certified leaf) + {rank≤b−2} (a separately-gated residual).
</task>

<output_contract>
Three short sections.
1. VERDICT on my claim (CORRECT / INCORRECT / PARTIAL) + ≤5 sentences: is "rank=b ⟹ Gram PosDef" the
   minimal prerequisite for the good-stratum closure, and is Cauchy-Binet genuinely AVOIDED?
2. The ONE thing most likely to still force Cauchy-Binet (or another absent primitive), if any — e.g.
   does routing {rank Q_b = b} as a measurable chart of the A'-domain need det(Q_bQ_bᵀ)≥minor² (a
   Cauchy-Binet ≥-corollary) to even DEFINE/measure the stratum, vs. just `0 < det(Q_bQ_bᵀ)` (PosDef)?
3. The shift-source: confirm the ab/2 shift comes from the Γ-peel (Regime A), NOT the radial
   (radial = u-scale finiteness, α=M₁M₂−1−2c', non-binding). YES/NO + one sentence.
Keep under 350 words. Flag inference vs. derivation.
</output_contract>

<grounding_rules>
Reason from the banked facts as given. Do NOT assume Mathlib has Cauchy-Binet, compound matrices, or GMT.
Flag any step that needs a fact I did not list. The key discriminator: PosDef needs 0<det (strict), which
full row rank gives directly (Gram of independent rows) — does anything downstream need the STRONGER
Σ-minors² decomposition rather than just strict positivity?
</grounding_rules>
