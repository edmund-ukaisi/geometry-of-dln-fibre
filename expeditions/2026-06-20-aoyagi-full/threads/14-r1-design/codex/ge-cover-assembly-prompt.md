<task>
I am formalising in Lean 4 + Mathlib the ≥-direction of an RLCT (real log-canonical threshold) lower bound for a (2,2,2) deep-linear-network loss. I need an INDEPENDENT red-team of the cover-assembly DESIGN before I sink ~150-250 lines of Lean into it. Diagnose the soundness risks; do NOT write Lean code.

THE TARGET (≥-half):
  rlctAtOn myF222 0 ≥ ⨅ᵢ monomialThreshold (dᵢ)(kᵢ)(hᵢ) = 3/2
where myF222 : (Fin 8 → ℝ) → ℝ is ‖A·B‖² for 2×2 matrices A (slots 0-3), B (slots 4-7).

THE GATED ≥-SPINE (Lean signatures, already proven, I must USE these as-is):
  rlctAtOn_ge_of_integral_lt (F)(hFm)(U : Set E)(hU : IsOpen U)(h0 : 0 ∈ U)(t : ℝ≥0∞)
    (hfin : ∀ c' : NNReal, (c':ℝ≥0∞) < t → ∫⁻ x in U, ENNReal.ofReal (|F x|^(-(c':ℝ))) < ⊤) : t ≤ rlctAtOn F 0
  cover_integral_lt_top_iff (s : Finset ι)(μ)(U)(leafSet : ι → Set E)(g : E → ℝ≥0∞)(w : ι → E → ℝ≥0∞)
    (hcov : ∫⁻ x in U, g x ∂μ = ∑ i ∈ s, ∫⁻ x in leafSet i, w i x ∂μ) :
    (∫⁻ x in U, g x ∂μ < ⊤) ↔ ∀ i ∈ s, ∫⁻ x in leafSet i, w i x ∂μ < ⊤
  NOTE: cover_integral_lt_top_iff's hcov is an EQUALITY (∫_U = ∑ leaf), not a ≤. So I apparently need an EXACT additive decomposition, not just a covering.

GATED ae-DISJOINT COVER MACHINERY (proven, reusable):
  argmaxCellOn (active : Finset (Fin N))(p : Fin N) : Set (Fin N→ℝ) := {y | y p ≠ 0 ∧ ∀ j ∈ active, |y j| ≤ |y p|}
  argmaxCellOn_cover : {y | ∃ j ∈ active, y j ≠ 0} = ⋃ p ∈ active, argmaxCellOn active p   (EXACT cover of the "some active coord ≠0" set)
  argmaxCellOn_aedisjoint (p≠q in active) : AEDisjoint volume (argmaxCellOn active p) (argmaxCellOn active q)
  argmaxCellOn_measurableSet : MeasurableSet (argmaxCellOn active p)

GATED CHANGE-OF-VARIABLES NODES (proven; each: ∫_{φ '' (V \ {pivot=0})} g = ∫_{V\{pivot=0}} |det Dφ|·(g∘φ)):
  step1A_lintegral_image  (step1A = pivotBlowupOn {0,1,2,3} 0,  |det| = x0³)
  step2E_lintegral_image  (step2E = pivotBlowupOn {1,2,3} 1,    |det| = z1²)
  measurePreserving_lemma2Hom (the Lemma-2 regular change-of-vars, det ±1, measure-preserving)

THE CHART TREE (24 leaves): step1A (A-pivot blow-up, |det|=x0³) → Lemma-2 splice (m.p.) → step2E (E-pivot, |det|=z1²; 8 UNIT leaves, residual U≥1) OR step2D (δ-pivot) → step3 (4-block blow-up, |det|=u³; 16 BLOCK leaves, residual res≥1). Each leaf integrand pulls back to a monomial·unit with the unit bounded below by 1. Per-leaf finiteness: integrableOn_monomial_mul_unit_iff (gated) gives ∫_leaf < ⊤ for c' < that leaf's monomialThreshold. All 24 leaf thresholds are ≥ 3/2 (binding leaf = 3/2).

MY PLAN: for each c' < 3/2, show ∫_U |myF222|^{-c'} < ⊤ by: (1) decompose U into 24 leaf-images via the chart tree, the active-coord argmaxCellOn cells at each pivot node giving the cover; (2) on each leaf, change-of-variables (the gated nodes) turns ∫_leaf into ∫ of a monomial·unit; (3) each is finite since c' < 3/2 ≤ leaf threshold (integrableOn_monomial_mul_unit_iff); (4) cover_integral_lt_top_iff assembles ∑ finite ⟹ ∫_U finite; (5) rlctAtOn_ge_of_integral_lt ⟹ ≥ 3/2.

THE TWO PROBES (the controller's specific soundness concerns):
(a) COVER vs PARTITION: cover_integral_lt_top_iff wants the EQUALITY ∫_U = ∑ leaf. With argmaxCellOn_cover (exact cover) + argmaxCellOn_aedisjoint (ae-disjoint), is the equality ∫_U g = ∑_p ∫_{cell p} g sound (ae-disjoint ⟹ no double-count ⟹ exact additivity over a finite cover)? What is the EXACT Mathlib lemma chain (lintegral over a finite ae-disjoint union = sum of lintegrals)? Or does the equality need genuine disjointness (not just ae)? If ae-disjoint suffices, is there a subtlety at the NESTED tree (cover-of-covers: step1's cells, then within each, step2's cells, then step3's) — does ae-disjointness compose through the change-of-variables (does φ map null sets to null sets / is the pullback of an ae-disjoint cover ae-disjoint)?
(b) DO THE 24 LEAVES COVER U WITH NO GAP? The exceptional loci {pivot=0} are removed at each c-o-v step (the gated nodes are stated on V \ {pivot=0}). Across the whole tree, the removed loci are a finite union of coordinate hyperplanes (measure zero) — so the 24 leaf-images cover U UP TO a null set. Is "cover up to null" sufficient for the ∫_U equality (∫ over a null set = 0), or is there a gap where the singularity of |myF222|^{-c'} sits exactly ON a removed hyperplane and contributes ⊤ that the cover misses? (This is the silent-gap risk: the integrand BLOWS UP on the coordinate hyperplanes, which are exactly the removed loci.)

</task>

<output_contract>
Four sections, terse:
1. PROBE (a) verdict: is the ae-disjoint-cover ⟹ exact-sum-equality sound for cover_integral_lt_top_iff? Name the Mathlib lemma chain (or the gap). Address nested-tree ae-disjointness composition through c-o-v.
2. PROBE (b) verdict: do the 24 leaves cover U up to null, AND is cover-up-to-null sufficient here GIVEN the integrand blows up exactly on the removed hyperplanes? This is the soundness crux — be adversarial. If the singularity-on-removed-locus is a real gap, say so loudly + the fix.
3. The SINGLE most likely place this design has a silent hole, and the cheapest Lean probe to expose it before sinking the 150-250 lines.
4. Any reordering of my 5-step plan that reduces risk (e.g. handle the hyperplane-singularity FIRST).
</output_contract>

<grounding_rules>
Distinguish what FOLLOWS from the cited Lean signatures (observed) vs what you INFER about Mathlib lemma availability (flag as inference — I will verify lemma names locally before trusting them). Do NOT invent Mathlib lemma names with confidence; if you propose one, mark it "likely exists, verify". The diagnosis (where the risk is) is what I need; the lemma recipe is illustrative only.
</grounding_rules>
