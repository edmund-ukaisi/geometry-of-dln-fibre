<task>
Lean 4 / Mathlib v4.29 RLCT proof. Goal: rlctAtOn myF222 0 ≤ 3/2 (the ≤ half of the (2,2,2) DLN
resolution). myF222 (x : Fin 8 → ℝ) = (x0x4+x1x6)²+(x0x5+x1x7)²+(x2x4+x3x6)²+(x2x5+x3x7)² = ‖AB‖²
(A=[[x0,x1],[x2,x3]], B=[[x4,x5],[x6,x7]]).

PROVEN (sorry-free, available):
- rlctAtOn_le_of_box_diverges (F : (Fin N→ℝ)→ℝ) (t) (hdiv : ∀ c':NNReal, t<c' → ∀ ε>0,
    ∫⁻_{cubeBox N ε} ENNReal.ofReal(|F x|^(-c')) = ⊤) : rlctAtOn F 0 ≤ t.   (cubeBox N ε = univ.pi(Icc -ε ε))
- monomialIntegrand_lintegral_box_eq_top (d)(k h:Fin d→ℕ)(hk:∃j,k j≠0)(c':ℝ)
    (hc':monomialThreshold d k h ≤ ofReal c')(hc'0:0<c'){ε}(hε:0<ε) :
    ∫⁻_{univ.pi(fun _:Fin d => Icc 0 ε)} ofReal(|monomialIntegrand d k h c' u|) = ⊤.
    monomialIntegrand d k h c u = (∏j |u j|^(h j))·(∏j |u j|^(2 k j))^(-c).
- integrableOn_monomial_mul_unit_iff (strip a unit factor |unit|∈[a,b], 0<a, from a leaf integrand).
- Chart factorizations (ring-proven): myF222(step1A y)=y0²·step1Residual y ;
    step1Residual v = resolvedForm(lemma2Fwd v) ; resolvedForm(step2E z)=z1²·(unit U≥1).
    step1A y = ![y0, y0 y1, y0 y2, y0 y3, y4,y5,y6,y7] (Jac y0³). step2E on Fin 7.
    lemma2Fwd a measure-preserving homeomorph (det -1). g5_pivotNode (full cover) + the c-o-v
    lemma2 lintegral_image_eq_lintegral_abs_det_fderiv_mul are available.
- CONFIRMED: naive low-dim slices give the WRONG RLCT (3/2 is a JOINT 8-dim degeneration) — a real
    chart change-of-variables is required, no slice shortcut.

For rlctAtOn_le_of_box_diverges I must show ∫⁻_{cubeBox 8 ε} ofReal(|myF222|^{-c'}) = ⊤ for c'>3/2.
The plan: lower-bound by ONE composite binding-leaf chart φ:
  ∫⁻_{cubeBox 8 ε} g ≥ ∫⁻_{φ''V} g = ∫⁻_V |det Dφ|·(g∘φ) = ⊤,  g = ofReal|myF222|^{-c'},
where V is a box in chart coords, φ''V ⊆ cubeBox 8 ε, φ InjOn V, and the V-integral diverges on the
binding z1-axis (exponent 2-2c' ≤ -1 for c'≥3/2).
</task>

<output_contract>
Answer these, shortest sound route, concrete v4.29 lemma names, ≤ ~500 words:
1. Compose step1A∘(Lemma-2 ext, y0 spectator)∘step2E into ONE φ:Fin8→Fin8 and compute |det Dφ| once,
   OR iterate the single-node c-o-v (chain 2-3 nodes, multiply Jacobians)? Which is shorter in Lean?
2. For the LOWER bound (one direction into a sub-region) can I avoid the full composite det — e.g.
   lower-bound |det Dφ| by a monomial, or use lintegral_image c-o-v per node and chain? What exactly
   does lintegral_image_eq_lintegral_abs_det_fderiv_mul give for the ≥ direction (it's an equality;
   the ≥ comes from φ''V ⊆ cubeBox + lintegral_mono_set)?
3. After c-o-v the V-integrand is y0^{3-2c'}·z1^{2-2c'}·U^{-c'} (U≥1). To feed
   monomialIntegrand_lintegral_box_eq_top (d=2,(y0,z1),k=(1,1),h=(3,2)) I must strip U^{-c'} via
   integrableOn_monomial_mul_unit_iff and match the |det|·... to the monomialIntegrand form
   ∏|u|^h·(∏|u|^{2k})^{-c}. Give the exact rewriting: how |det|=y0³z1² (the ∏|u|^h with h=(3,2)) times
   (y0²z1²)^{-c'} (the (∏|u|^{2k})^{-c} with k=(1,1)) times U^{-c'} equals the leaf integrand, and how
   the box-divergence atom closes it. Flag any soundness issue (InjOn, the spectator coords in φ, that
   the box V's image is genuinely ⊆ cubeBox, the 6 non-(y0,z1) coords as a Fubini-spectator product).
</output_contract>

<grounding_rules>
Distinguish lemmas you are SURE exist in Mathlib v4.29 from ones you INFER. Flag any step that needs a
lemma not named above. If the composite-chart route has a hidden trap (the spectator dimension count,
the det of the composite, the InjOn of the composite), say so explicitly.
</grounding_rules>
