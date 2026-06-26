<task>
Lean 4 / Mathlib v4.29. (2,2,2) RLCT ≥-direction: prove rlctAtOn myF222 0 ≥ 3/2.
myF222 (x:Fin 8→ℝ) = ‖AB‖² (A,B 2×2 in flat coords). The ≤-direction (≤ 3/2) is DONE.

GATED tools:
- rlctAtOn_ge_of_integral_lt (F)(hFm)(U open ∋0)(t)(∀c'<t, ∫⁻_U ofReal(|F|^{-c'}) < ⊤) : t ≤ rlctAtOn F 0.
- g5_pivotNode (active : Finset (Fin N))(U)(hUcov : U =ᵐ ⋃_{p∈active} argmaxCellOn active p)(g) :
    ∫⁻_U g = Σ_{p∈active} ∫⁻_{chartDomOn p \ pivotZeroOn p} ofReal|det φ_p'|·g∘φ_p. (One pivot-blowup node.)
- The composite chart phiUnit = step1A ∘ Lemma2 ∘ step2E (1 unit leaf); phiUnit_cov (its c-o-v). I built
  the ≤ via ONE binding leaf (phiUnit) + box-divergence.
- step1A = pivotBlowupOn {0,1,2,3} 0 (|det|=y0³); step2E = pivotBlowupOn {1,2,3} 1 (|det|=z1²);
  Lemma-2 m.p.; the leaf factorizations myF222∘φ = monomial·unit (unit≥1) for unit + block leaves.
- monomialIntegrand_integrable_of_lt (c'<threshold ⟹ monomial integrable on unit box);
  integrableOn_monomial_mul_unit_iff (strip the unit). monomialThreshold (unit leaf)=monomialThreshold (block leaf)=3/2.
- ENNReal.sum_lt_top (cover_integral_lt_top_iff): Σ finite ⟺ all summands finite.

For ≥ I need: ∃ open U∋0, ∀c'<3/2, ∫⁻_U ofReal(|myF222|^{-c'}) < ⊤.
</task>

<output_contract>
≤ ~450 words, concrete v4.29 lemma names. The SHORTEST sound route. Decide:
1. Is the FULL 3-deep g5_pivotNode cover (step1 4-way ∘ step2 3-way ∘ step3 4-way = 24 leaves, each
   finite below 3/2) REQUIRED for ≥, or is there a shorter finiteness argument? E.g. — can I bound
   ∫⁻_U |myF222|^{-c'} above by a FINITE quantity WITHOUT the exact 24-leaf cover (some direct
   integrability of |myF222|^{-c'} on a box for c'<3/2, via a coarser estimate)?
2. If the cover is needed: the recursion. g5_pivotNode step-1 gives ∫⁻_U = Σ_{4 A-pivots} ∫⁻_{chart}
   |y0³|·g∘φ₁. Each chart integral = ∫⁻ over (chartDomOn\pivotZero) — is THIS again a cover-integral
   I recurse on (apply g5_pivotNode for step-2 inside), or does the Lemma-2 splice + the chart-domain
   structure let me reduce each of the 4 charts to the SAME unit/block leaf finiteness I have? How many
   distinct leaf-finiteness lemmas do I actually need (the 4 A-charts are symmetric; 8 unit + 16 block
   leaves but only 2 distinct (d,k,h) types)?
3. The cover hypothesis hUcov (U =ᵐ ⋃ argmaxCellOn): for the TOP node (step1, active {0,1,2,3}), what's
   the cleanest U and the cover proof? The argmaxCellOn cells tile {y≠0} up to null hyperplanes (the
   gated argmaxCellOn_cover); is U = a nbhd of 0 with U =ᵐ ⋃cells provable from argmaxCellOn_cover +
   {0} null?
ASSESS: is ≥ a "mechanical composition" (~1-2 days, reuse gated nodes) or a GENUINE long serial pole
(needs much new machinery)? Be concrete — this decides whether I parallelize it out.
</output_contract>

<grounding_rules>
SURE vs INFERRED v4.29 / project lemma names. If the recursion (g5_pivotNode inside a chart) needs the
chart-domain to itself be a ⋃argmaxCellOn (the recursion's cover hyp), flag whether that's provable or a
gap. If a coarser direct-integrability estimate (route 1) exists, that's the win — say so explicitly.
</grounding_rules>
