<task>
Lean 4 / Mathlib v4.29 formalisation. I must CLOSE a crux `d1ge_L2_hAtV_explicit` by
assembling data to feed a BANKED reduction lemma `d1ge_L2_hAtV_of_explicit_chart`. This is the
L=2 headline of a research project (RLCT of deep linear networks). I want a red-team of my
worked-out architecture BEFORE I write ~400 lines, especially the two subtle points (global
smoothness of `qₑ`, and whether a coordinate "shear" is needed).

## What I HAVE (banked, sorry-free)

GERM (`schur_loss_germ_L2_rlct`): at optimal `v` with `prod H v = B`, `B.rank = r`, produces
common pivots `I : Fin r → Fin (H 0)`, `K : Fin r → Fin (H 1)`, `J : Fin r → Fin (H 2)`
(injective) and gives:

    rlctAt H (dlnLoss H B) v = rlctAtOn F (0 : Fin (flatDim H) → ℝ)

where F = schurReadoutF_L2 (a function on the flat space `Fin (flatDim H) → ℝ`), defined as:

    F(x) = ∑ (a : Fin r ⊕ Fin(H0-r)) ∑ (bb : Fin r ⊕ Fin(H2-r))
              ((recoverProduct (blockFlatEquiv_L2 x + C) - Br) a bb)^2

  - blockFlatEquiv_L2 : (Fin (flatDim H) → ℝ) ≃L[ℝ] BlockParamsL2 H r  (a CONTINUOUS LINEAR equiv;
    BlockParamsL2 = Matrix (Fin r ⊕ Fin(H0-r)) (Fin r ⊕ Fin(H1-r)) ℝ  ×  Matrix (Fin r ⊕ Fin(H1-r)) (Fin r ⊕ Fin(H2-r)) ℝ).
    So blockFlatEquiv_L2 x = (A0blocks, A1blocks): first layer blocks X=₁₁,Y=₁₂,Z=₂₁,W=₂₂ ;
    second layer blocks S=₁₁,T=₁₂,U=₂₁,V=₂₂.
  - C = schurChartRaw (blockFlatEquiv_L2 (flat v)) is a CONSTANT (BlockParamsL2). Key readbacks:
    C.2.₁₁ = M11(P₀) (product pivot, invertible), C.2.₁₂ = M12, C.1.₂₁ = M21, and
    recoverProduct C = P₀.1 * P₀.2 = (prod v).submatrix I J = Br (the reindexed target).
  - Br = B.submatrix (sumSplit I) (sumSplit J). Since prod v = B, Br = (prod v).submatrix I J, rank ≤ r.
    Its ₁₁ block Br.₁₁ = the invertible pivot minor.
  - recoverProduct Q = fromBlocks Q.2.₁₁ Q.2.₁₂ Q.1.₂₁ (Q.1.₂₁ Q.2.₁₁⁻¹ Q.2.₁₂ + Q.1.₂₂ Q.2.₂₂).
    (Matrix.inv = Mathlib nonsingular inverse.)

So with Q = blockFlatEquiv_L2 x + C, the four blocks of (recoverProduct Q - Br):
  ₁₁ = (S(x)+C.2.₁₁) - Br.₁₁ = S(x)     [C.2.₁₁=Br.₁₁]
  ₁₂ = (T(x)+C.2.₁₂) - Br.₁₂ = T(x)
  ₂₁ = (Z(x)+C.1.₂₁) - Br.₂₁ = Z(x)
  ₂₂ = (Z(x)+Br.₂₁)(S(x)+Br.₁₁)⁻¹(T(x)+Br.₁₂) + (W(x)+C.1.₂₂)(V(x)+C.2.₂₂) - Br.₂₂
(all block reads are LINEAR coords of x via blockFlatEquiv_L2.)

nRegL2 H r = r*(H0+H2-r) = #entries of (S,T,Z blocks) = r² + r(H2-r) + (H0-r)r.  flatDim(H-r) = (H0-r)(H1-r)+(H1-r)(H2-r) = #entries(W,V). specDim := #entries(X,Y,U) = r² + 2r(H1-r). Total = flatDim H. Verified numerically at (4,4,4)/r=1: 7+18+7=32.

I also have: rlctAtOn_congr_germ (rlctAtOn f x = rlctAtOn g x if f =ᶠ[𝓝 x] g); rlctAtOn_comp_homeomorph
(MP homeomorph transports rlctAtOn); Core.schur_complement_zero_of_rank_le (Invertible B11, rank(fromBlocks B11 B12 B21 B22) ≤ r ⟹ B22 = B21 ⅟B11 B12); exists_contDiff_eventuallyEq_of_contDiffOn (bump-globalise a ContDiffOn map to a global ContDiff one agreeing near a point); Matrix.inv is ContDiffOn on the invertible locus (via ContDiffOn.inv / Cramer).

## What I must PRODUCE for the banked consumer `d1ge_L2_hAtV_of_explicit_chart`

It needs (Option A = the intended packaging): a free finite-dim normed measure space `Y`, and
  - qₑ : (Fin (nRegL2 H r) → ℝ) × Y → EuclideanSpace ℝ (Fin n)  with  n = (H0-r)(H2-r),  hq : ContDiff ℝ 1 qₑ  (GLOBAL)
  - t0 : Y
  - hchart : rlctAt H (dlnLoss H B) v = rlctAtOn (fun p => (∑ i, p.1 i^2) + (∑ i, qₑ p i^2)) ((0), t0)
  - hRne : ∃ U ∈ 𝓝 t0, ∀ᵐ z ∂(volume.restrict U), (∑ i, qₑ ((0),z) i^2) ≠ 0
  - e : Y ≃ₜ ((Fin (flatDim(H-r)) → ℝ) × (Fin specDim → ℝ)), measure-preserving + measurable embedding
  - u : Y → ℝ measurable, ua ub with 0<ua, bound ua≤|u w|≤ub near t0
  - hfact : ∀ t:Y, (∑ i, qₑ ((0),t) i^2) = u t * dlnLoss (H-r) 0 ((paramsEquivFlat (H-r)).symm (e t).1)
Option A: e = Homeomorph.refl (so Y = (Fin (flatDim(H-r)) → ℝ) × (Fin specDim → ℝ)), u ≡ 1.

## My worked-out plan (RED-TEAM THIS)

1. Choose Y = (Fin (flatDim(H-r)) → ℝ) × (Fin specDim → ℝ). Build a MEASURE-PRESERVING linear
   homeomorphism ρ : (Fin (flatDim H) → ℝ) ≃ₜ (Fin nReg → ℝ) × Y that reindexes the flat coords into
   ( p=(S,T,Z) | reduced=(W,V) shifted by C | spectators=(X,Y,U) ). It factors as blockFlatEquiv_L2
   (linear equiv to BlockParamsL2) ∘ a block/coordinate permutation ∘ a translation on the (W,V) part.
   CLAIM: NO SHEAR is needed — the reduced core factor is literally (W+C.1.₂₂)(V+C.2.₂₂), a pure
   translation, because recoverProduct reads Q.1.₂₂·Q.2.₂₂ (the ₂₂ CORNERS of the raw layer blocks)
   directly, NOT the chart's Schur-adjusted A1red = V - U·M11⁻¹·M12. Is this right?

2. Regular part: under ρ, ∑ over regular blocks (S,T,Z)² = ∑ p.1². Clean (they're distinct coords).

3. Global qₑ: define qₑ(p,t) := (Z(p)+Br.₂₁)·G(S(p)+Br.₁₁)·(T(p)+Br.₁₂) + A0red(t)·A1red(t) - Br.₂₂,
   flattened to EuclideanSpace ℝ (Fin (H0-r)(H2-r)), where G is a GLOBALLY ContDiff matrix function
   agreeing with Matrix.inv on a nbhd of Br.₁₁ (bump-globalise Matrix.inv near the invertible Br.₁₁ via
   exists_contDiff_eventuallyEq_of_contDiffOn), and A0red(t)=W(t)+C.1.₂₂, A1red(t)=V(t)+C.2.₂₂ read from t.1.
   - Global ContDiff ℝ 1: yes (G global smooth, rest polynomial).
   - On slice p=0 (S=T=Z=0): qₑ(0,t) = Br.₂₁·G(Br.₁₁)·Br.₁₂ + A0red·A1red - Br.₂₂
     = Br.₂₁·Br.₁₁⁻¹·Br.₁₂ + A0red·A1red - Br.₂₂ = A0red·A1red  [G(Br.₁₁)=Br.₁₁⁻¹; Schur-of-Br=0 by rank≤r].
     So ∑qₑ(0,t)² = ‖A0red·A1red‖² = dlnLoss(H-r) 0 (A0red,A1red) = dlnLoss(H-r) 0 ((paramsEquivFlat(H-r)).symm t.1).
     hfact holds GLOBALLY with u≡1.  Is the Schur-of-Br=0 step correct (rank(Br)≤r, Br.₁₁ invertible)?
   - Near ρ(0)=(0,t0): S(p) small ⟹ S(p)+Br.₁₁ near Br.₁₁ ⟹ G = inv ⟹ qₑ = raw ₂₂ block. So
     (∑p²+∑qₑ²) ∘ ρ⁻¹  =ᶠ[𝓝(0,t0)]  F ∘ ρ⁻¹. hchart via rlctAtOn_comp_homeomorph(ρ) + rlctAtOn_congr_germ.

4. hRne: slice residual ∑qₑ(0,t)² = ‖A0red·A1red‖² is a nonzero polynomial in t (generic), a.e. ≠ 0
   near t0 (needs hpos : r < H s so the reduced widths are positive; use a MvPolynomial ae_ne_zero style).

## Questions
Q1. Is the "NO SHEAR" claim correct (reduced factor = raw ₂₂ corners (W+c)(V+c), pure translation)?
Q2. Is defining qₑ via a bump-globalised matrix-inverse G the cleanest route to GLOBAL ContDiff ℝ 1
    while keeping qₑ(0,·) a global polynomial for hfact? Any pitfall (e.g. G ContDiff but qₑ mixing
    matrix mul + reindex to EuclideanSpace vector — order of smoothness, EuclideanSpace vs Pi)?
Q3. Is the hchart route (MP homeomorph ρ, then germ-congruence to swap F for ∑p²+∑qₑ² near the base
    point) sound, given rlctAtOn is a pure germ invariant? Any measurability/finite-measure snag with ρ
    being merely linear (det ±1 ⟹ MP)?
Q4. Biggest risk / cheapest thing to verify first before writing 400 lines? Rank the sub-pieces by risk.
</task>

<output_contract>
Answer Q1–Q4 in order, terse. For Q1/Q3 give a definite YES/NO + the one-line reason. For Q2 name the
cleanest construction + the single most likely Lean pitfall. For Q4 rank the 3-4 riskiest sub-pieces and
the cheapest discriminating check for the top one. Total under ~450 words. Flag any place my math is WRONG.
</output_contract>

<grounding_rules>
This is pure math + Lean-architecture reasoning; no repo access needed. Distinguish "your math is correct"
(you can verify) from "this Lean lemma exists" (you cannot verify — flag as needs-check). Do not invent
Mathlib lemma names as if confirmed.
</grounding_rules>
