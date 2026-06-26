<task>
I am formalising in Lean 4 + Mathlib v4.29 a change-of-variables "cover" identity for a threshold
(lintegral) integral over a finite atlas of blow-up charts. I have a PROVEN abstract one-step lemma
and PROVEN per-node chart atoms; I need the cleanest STRUCTURE to assemble the 3-deep composition.
Give me a structural plan, NOT code I will paste blindly (I will write/run the Lean myself).

## What I have (proven, axiom-clean, green)

ABSTRACT ONE-STEP GLUING (call it `g5_step`), over E = finite-dim real Haar space (e.g. `Fin N → ℝ`):
  g5_step (μ) (s : Finset ι) (φ : ι → E → E) (φ' : ι → E → E →L[ℝ] E) (V Z : ι → Set E) (U : Set E)
    (hVZ : ∀ i∈s, MeasurableSet (V i \ Z i))
    (hφ' : ∀ i∈s, ∀ x∈ V i \ Z i, HasFDerivWithinAt (φ i) (φ' i x) (V i \ Z i) x)
    (hinj : ∀ i∈s, InjOn (φ i) (V i \ Z i))
    (hcover : U =ᵐ[μ] ⋃ i∈s, φ i '' (V i \ Z i))
    (hdisj : Set.Pairwise s (AEDisjoint μ on (fun i => φ i '' (V i \ Z i))))
    (hmeas : ∀ i∈s, NullMeasurableSet (φ i '' (V i \ Z i)) μ)
    (g : E → ℝ≥0∞) :
    ∫⁻ x in U, g x ∂μ = ∑ i∈s, ∫⁻ x in V i \ Z i, ENNReal.ofReal |(φ' i x).det| * g (φ i x) ∂μ

PER-NODE ATOM (proven, parametric in n): the pivot blow-up `pivotBlowup n : (Fin(n+1)→ℝ) → (Fin(n+1)→ℝ)`,
`x ↦ (x₀, x₀x₁, …, x₀xₙ)`, with `pivotBlowup_hasFDerivWithinAt`, `pivotBlowupDeriv_det = (x 0)^n`,
`pivotBlowup_injOn` (InjOn off `{x | x 0 = 0}`).

ALSO PROVEN: `rlctAtOn_comp_homeomorph` (rlctAtOn transports under a measure-preserving homeomorphism).
Mathlib has `lintegral_image_eq_lintegral_abs_det_fderiv_mul` (the single c-o-v), `lintegral_biUnion_finset₀`
(cover-additivity), `map_linearMap_addHaar_eq_smul_addHaar` (det-1 linear map preserves volume).

## The concrete target (the (2,2,2) DLN resolution cover, 24 leaves)

The atlas is a 4-NODE tree on E = Fin 8 → ℝ (coords: A=4 entries, B=4 entries; F = ‖A·B‖²):
  NODE 1 (step1): 4 charts, pivot blow-up on the A-block, |det|=x³, exceptional {x=0}.
  NODE 2 (Lemma-2): a SINGLE homeomorphism (polynomial, det = −1) — a regular coordinate change, NOT a cover.
  NODE 3 (step2): 3 charts, pivot blow-up on a 3-coord sub-block (E,F0,δ), |det|=s², exceptional {s=0}.
  NODE 4 (step3): 4 charts (only on the δ-branch of node 3), pivot blow-up on a 4-coord block, |det|=u³.
Result: 8 "unit" leaves (node1×node3-{E,F0 pivots}) + 16 "block" leaves (node1×node3-δ×node4) = 24.
Composite Jacobians: unit leaves |det|=x³s²; block leaves |det|=x³s²u³.
Per chart, cover is the standard affine-chart cover of a coordinate-subspace blow-up (pivots = argmax
regions, a.e.-disjoint; the all-zero slice {block=0} is the only uncovered set = Lebesgue-null).

Goal (my measure deliverable): `∫⁻_U |F|^{-c} = Σ_{24 leaves} ∫⁻_{leaf} |det Dφ_leaf|·|F∘φ_leaf|^{-c}`,
i.e. g5_step composed: node1 (4-way) then within each, node3 (3-way) then within the δ-one, node4 (4-way),
with node2 (homeomorph) spliced between node1 and node3.

## The specific structural questions

1. COMPOSITION SHAPE: g5_step gives `∫⁻_U = Σ_i ∫⁻_{Vᵢ\Zᵢ} wᵢ·(g∘φᵢ)`. To go 3-deep I must apply g5_step
   again to EACH inner `∫⁻_{Vᵢ\Zᵢ} wᵢ·(g∘φᵢ)` — but that inner integral has an EXTRA weight factor wᵢ and
   the integrand is `g∘φᵢ`, not bare g. Is the cleanest move: (a) fold the weight+pullback into a new `g' :=
   wᵢ·(g∘φᵢ)` and recurse g5_step on g' over the SAME E, composing the φ's by `φᵢ ∘ φⱼ` and multiplying
   Jacobians? Or (b) prove a bespoke "2-level g5" / "n-level g5" lemma once and instantiate? Or (c) a
   `List`/tree-indexed leaf type with a single flat g5_step over the 24 composite charts? Rank these for a
   ONE-OFF (2,2,2) build that should also not be horrible to reuse for a future general-M atlas.

2. THE HOMEOMORPH NODE (Lemma-2, det −1): it's not a cover, just a regular change. In the lintegral cover
   language, is the cleanest treatment to (i) treat it as a 1-element g5_step (s = {*}, V=univ, Z=∅, the
   single chart = the homeomorph, |det|=1), so it slots uniformly into the composition? Or (ii) handle it by
   a direct `lintegral_image` / measure-preserving rewrite OUTSIDE the g5_step chain? Which keeps the
   composite-Jacobian bookkeeping (x³·1·s²·u³) cleanest?

3. THE COVER OBLIGATION (hcover + hdisj) — the genuinely heavy part. For the pivot blow-up on a coordinate
   block, the charts are the argmax regions `Vᵢ = {pivot i is (weakly) max-magnitude}`. What is the
   lowest-pain Lean formulation of (a) `U =ᵐ ⋃ φᵢ''(Vᵢ\Zᵢ)` and (b) pairwise AEDisjoint? Concretely: is it
   better to define the chart images directly as sets (e.g. `{A | a_pq ≠ 0 ∧ |a_pq| ≥ |a_others|}`) and prove
   the cover by a pointwise argmax argument, or to push everything through the φ-domain side? Any Mathlib
   lemma for "argmax over a Finset gives an a.e.-disjoint cover up to ties (a null set)"?

4. SCOPE CHECK: is there a materially SIMPLER honest target than the full 24-leaf `∫⁻=Σ∫⁻` that still serves
   as the measure half (the fm assembly side then evaluates per-leaf monomial thresholds = 3/2)? E.g. is the
   per-step `∫⁻=Σ∫⁻` (three separate one-level identities) a cleaner deliverable than the fully-composed
   24-term sum, given the consumer just needs each leaf's `∫⁻_{leaf} |det|·|F∘φ|^{-c}` finiteness threshold?
</task>

<output_contract>
Four numbered sections matching Q1–Q4. For Q1 and Q2: a ranked recommendation with the single decisive
reason for the top choice (≤4 sentences each). For Q3: the lowest-pain formulation + name any Mathlib lemma
you are CONFIDENT exists (mark uncertain ones "unverified"). For Q4: a yes/no on whether the per-step form
is the cleaner deliverable, with one reason. Be concrete and terse; no Lean code blocks longer than a
signature.
</output_contract>

<grounding_rules>
Distinguish Mathlib lemmas you are confident exist (v4.29) from ones you infer should exist (mark
"unverified — I will grep"). Do not invent lemma names. If a step is genuinely hard with no clean Mathlib
support, say so plainly rather than papering over it — I would rather know the cover proof is the wall.
</grounding_rules>
