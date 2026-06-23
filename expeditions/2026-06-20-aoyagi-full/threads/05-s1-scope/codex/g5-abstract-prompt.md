<task>
Decorrelated soundness check of a Lean measure-theory cover-gluing lemma (the engine a 24-leaf
change-of-variables cover will instantiate). Confirm the statements faithfully express the intended
change-of-variables-over-a-cover, and the null-exceptional handling is sound.

CONTEXT: RLCT threshold integrals are computed as ∫⁻_U g (g = |F|^{-c}, ℝ≥0∞-valued, so `lintegral`
with NO integrability side-conditions — the ∞-above-the-rlct value is fine). A resolution expresses
∫⁻_U g as a sum over chart leaves. Measure μ is additive-Haar (Lebesgue) on a finite-dim real E.

LEMMA 1 `perChart` (per-chart c-o-v with null-exceptional drop):
Hyps: φ C¹ on V\N (HasFDerivWithinAt φ (φ' x) (V\N) at x∈V\N); InjOn φ (V\N); μ(φ''N)=0; V,N measurable.
Concl: `∫⁻ x in φ''V, g x ∂μ = ∫⁻ x in V\N, ofReal|det(φ' x)| · g(φ x) ∂μ`.
Proof: apply Mathlib `lintegral_image_eq_lintegral_abs_det_fderiv_mul` on V\N (gives ∫⁻_{φ''(V\N)} g =
RHS), then `φ''V =ᵐ φ''(V\N)` (their symmetric difference: φ''V\φ''(V\N) ⊆ φ''N which is null; and
φ''(V\N)\φ''V = ∅ since V\N⊆V).

LEMMA 2 `g5_step` (the cover consumer): s a Finset of leaves, φ i C¹+InjOn on V_i\Z_i, U =ᵐ ⋃_{i∈s}
φ_i''(V_i\Z_i), `hdisj` = Pairwise AEDisjoint over (φ_i''(V_i\Z_i)), hmeas NullMeasurableSet.
Concl: `∫⁻_U g = Σ_{i∈s} ∫⁻_{V_i\Z_i} ofReal|det φ_i'| · g(φ_i)`.
Proof: setLIntegral_congr hcover, then `lintegral_biUnion_finset₀ hdisj hmeas g`, then per-leaf c-o-v.

QUESTIONS:
1. perChart: is the null-drop `∫⁻_{φ''V} g = ∫⁻_{φ''(V\N)} g` SOUND? Specifically: does `μ(φ''N)=0`
   (Luzin-N, on the IMAGE) genuinely suffice (a) for the two integrals to agree, and (b) is it the RIGHT
   obligation (vs, say, μ(N)=0 on the domain, which would NOT suffice without the area-formula)? Confirm
   the c-o-v is applied where φ is injective (V\N) and the drop only adds a null image-set.
2. g5_step: is `Pairwise AEDisjoint over the IMAGES φ_i''(V_i\Z_i)` the correct disjointness contract for
   `lintegral_biUnion_finset₀` (sum over an a.e.-disjoint cover)? Is requiring disjointness of the IMAGE
   leaves (not the domain V_i\Z_i) the right thing — i.e. the burden that overlapping cover regions would
   double-count is correctly placed on the caller's hdisj?
3. Any GAP between the stated hyps and the conclusion — e.g. a missing measurability/finiteness hyp, or a
   case where U =ᵐ ⋃ images but the sum still wouldn't equal ∫⁻_U g? Is the lemma faithful to "∫⁻_U g =
   Σ chart integrals" with no smuggled assumption or hidden over-/under-claim?
</task>

<output_contract>
Three numbered verdicts, terse: SOUND/FLAG + reason. For Q1 confirm μ(φ''N)=0 is the right image-side
Luzin-N obligation. For Q2 confirm image-disjointness is correct. For Q3 flag any gap or "faithful".
</output_contract>

<grounding_rules>
The Mathlib lintegral change-of-variables (image = ∫ |det fderiv|·g∘φ, InjOn+C¹, no integrability over
ℝ≥0∞) and lintegral over a.e.-disjoint finite unions are standard; use them. Flag inferences. Don't
invent Mathlib lemma names.
</grounding_rules>
