<task>
Lean 4 / Mathlib v4.29. (2,2,2) RLCT ≤-direction, FINAL structural decision. I need to realize a
change-of-variables ∫⁻_{phiUnit '' V} g = ∫⁻_V ofReal|det Dφ|·(g∘φ) for the composite chart
phiUnit : (Fin 8→ℝ)→(Fin 8→ℝ), then show the RHS = ⊤ (binding-axis divergence).

I have, ALL GATED + sorry-free:
- step1A_lintegral_image: ∫⁻_{step1A''(W\{x0=0})} g = ∫⁻_{W\{x0=0}} ofReal|det₁|·g∘step1A  (step1A = pivotBlowupOn {0,1,2,3} 0, |det₁|=x0³).
- step2E_lintegral_image: ∫⁻_{step2E''(V\{z1=0})} g = ∫⁻_{V\{z1=0}} ofReal|det₂|·g∘step2E  (step2E = pivotBlowupOn {1,2,3} 1, |det₂|=z1², on Fin 7).
- measurePreserving_lemma2Hom: lemma2Hom (Fin 7→ℝ ≃ₜ, det ±1) measure-preserving. lemma2Inv its inverse.
- phiUnit u = step1A (Fin.cons (u 0) (lemma2Inv (step2E (Fin.tail u)))).
- myF222_phiUnit_monomial: myF222(phiUnit u) = u0²·(tail u)1²·U, U≥1 (U a poly, bounded on a box).
- composite det D(phiUnit) = −u0³·u2² (sympy-verified; u2=(tail u)1).
- monomialIntegrand_lintegral_box_eq_top (the d=8 box-divergence atom), unitMonomialThreshold_le (≤3/2), monomialIntegrand_eq_prod_rpow, integrableOn_monomial_mul_unit_iff.
- HasFDerivWithinAt.comp + (f.comp g).det = f.det·g.det (LinearMap.det_comp) — both verified to compile.
- phiUnit_image_subset_cubeBox (∃δ, phiUnit''(cubeBox 8 δ)⊆cubeBox 8 ε), continuous_phiUnit, phiUnit_zero.
</task>

<output_contract>
≤ ~400 words. ONE recommendation + the exact Lean skeleton. Decide between:
(A) ONE composite c-o-v: build HasFDerivWithinAt phiUnit φ' V x with φ' = step1A'.comp innerLift', and
    |φ'.det| = u0³·z1². I'd need innerLift' (the derivative of u ↦ cons u0 (lemma2Inv(step2E(tail u)))).
    How do I get innerLift' + its det WITHOUT a manual 8×8 matrix det? Can I (a) chain HasFDerivWithinAt
    through Fin.cons (HasFDerivAt.finCons?), lemma2Inv (it's a poly — fun_prop / explicit?), step2E
    (pivotBlowupOn_hasFDerivWithinAt, gated), Fin.tail; and (b) get the composite det as a PRODUCT
    step1A_det · (lemma2Inv det = ±1) · step2E_det via det_comp — but the maps are on Fin 8 vs Fin 7
    (the cons/tail change dimension), so how does det_comp apply across the dimension-changing cons/tail?
(B) NESTED-image chaining: ∫⁻_{phiUnit''V} = ∫⁻_{step1A''(innerLift''V)} =[step1A_lintegral_image]
    ∫⁻_{innerLift''V} |x0³|·g∘step1A, then recurse on innerLift''V (= cons∘lemma2Inv∘step2E∘tail image).
    Does the Fin.cons/Fin.tail spectator structure let me peel the u0-spectator (piFinSuccAbove) and
    apply step2E_lintegral_image + the lemma2Hom m.p. splice on the Fin-7 tail? Give the exact
    set-image + integrand chaining.
Which is SHORTER and avoids the dimension-change det trap? Give the concrete lemma sequence.
</output_contract>

<grounding_rules>
Distinguish SURE v4.29 lemmas from INFERRED. The det_comp dimension issue (Fin 8 outer, Fin 7 inner via
cons/tail) is the crux — be explicit whether (A)'s det-product even typechecks (the inner map is
Fin8→Fin8 as a whole, so its derivative IS Fin8→Fin8; the cons/tail is internal). Flag if HasFDerivAt
for Fin.cons / Fin.tail has a clean Mathlib lemma (HasFDerivAt.finCons? Continuous.finCons exists). If
(B)'s nested-image needs a non-obvious set identity (step1A''(innerLift''V) vs phiUnit''V), say so.
</grounding_rules>
