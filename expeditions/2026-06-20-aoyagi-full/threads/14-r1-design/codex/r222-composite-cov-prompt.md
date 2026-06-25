<task>
Lean 4 / Mathlib v4.29. (2,2,2) RLCT ≤-direction. I need the cleanest way to realize a COMPOSITE
change-of-variables lower bound. Goal: ∫⁻_{cubeBox 8 ε} ofReal(|myF222 x|^{-c'}) = ⊤ for c'>3/2.

The composite leaf chart φ = phiUnit (Fin 8 → Fin 8):
  phiUnit u = step1A (Fin.cons (u 0) (lemma2Inv (step2E (Fin.tail u))))
where:
- step1A = pivotBlowupOn {0,1,2,3} 0  (a blow-up; |det Dstep1A| = (x0)³; PROVEN: step1A_lintegral_image
  gives ∫⁻_{step1A''(V\{x0=0})} g = ∫⁻_{V\{x0=0}} ofReal|det|·g∘step1A via the gated pivotBlowupOn
  infra: pivotBlowupOn_hasFDerivWithinAt, pivotBlowupOn_injOn).
- lemma2Inv : a polynomial bijection on Fin 7, the inverse of a measure-preserving homeomorph
  lemma2Hom (PROVEN measurePreserving_lemma2Hom, det ±1).
- step2E : Fin 7 → Fin 7, ALSO a pivot-blow-up (E-pivot), |det| = z1² (= (the pivot coord)²).
- PROVEN factorization: myF222 (phiUnit u) = (u0)²·(z1)²·U,  z1 = (Fin.tail u) 1,  U ≥ 1 (and U is a
  polynomial, bounded on any bounded box).
- PROVEN atom: monomialIntegrand_lintegral_box_eq_top — ∫⁻_{[0,ε]^d} ofReal|monomial| = ⊤ when
  monomialThreshold ≤ c'. And monomialThreshold(d=8, k=1 on axes 0,2; h=3,2; zeros) ≤ 3/2 (PROVEN).
- PROVEN: integrableOn_monomial_mul_unit_iff (strip a unit factor |unit|∈[a,b], 0<a).

The c-o-v lemma: lintegral_image_eq_lintegral_abs_det_fderiv_mul μ (hs:MeasurableSet s)
  (∀x∈s, HasFDerivWithinAt f (f' x) s x) (InjOn f s) g :
  ∫⁻_{f''s} g = ∫⁻_s ofReal|（f' x).det|·g(f x).
</task>

<output_contract>
≤ ~450 words, concrete v4.29 lemma names. Answer:
1. For the composite φ = phiUnit, is it cleaner to (a) build ONE HasFDerivWithinAt for the composite
   via HasFDerivWithinAt.comp (chain rule) + det-of-composite = product (ContinuousLinearMap.det of a
   comp = product of dets?), giving |det Dφ| = x0³·(±1)·z1² in one c-o-v; OR (b) ITERATE: apply step1A
   c-o-v, then handle the inner (lemma2Inv∘step2E on the tail) as a SEPARATE c-o-v / measure-preserving
   step — but the integrand after step1A is on Fin 8 and the inner map acts on the Fin-7 tail with u0 a
   spectator. Which is shorter and what's the Fin.cons/Fin.tail spectator bookkeeping for (b)?
2. The Lemma-2 splice: lemma2Hom is measure-preserving on Fin 7. To insert it inside the Fin-8
   integral with u0 spectator, do I lift it to Fin 8 (id × lemma2Hom via a prod/cons equiv) and use
   MeasurePreserving.lintegral_comp / setLIntegral? Or fold it into the composite derivative (its det
   is ±1 so it just multiplies |det| by 1)? Give the exact lemma for "measure-preserving map ⟹ ∫⁻
   transports" at the set-restricted level.
3. The ≥ lower-bound mechanics: I want ∫⁻_{cubeBox} g ≥ ∫⁻_{φ''V} g (via lintegral_mono_set, needs
   φ''V ⊆ cubeBox) then = ∫⁻_V |det|·g∘φ (c-o-v) then = ∫⁻_V monomialIntegrand·U^{-c'} (factorization)
   then = ⊤ (strip U via integrableOn_monomial_mul_unit_iff contrapositive + box-divergence atom). Is
   this chain sound, and what's the cleanest way to get φ''V ⊆ cubeBox 8 ε for a small box V (the
   polynomial-image bound — V radius δ ⟹ φ''V radius ≤ poly(δ))?
</output_contract>

<grounding_rules>
Distinguish SURE Mathlib v4.29 lemmas from INFERRED. Flag if the composite HasFDerivWithinAt.comp has a
within-set domain trap (the inner map's range vs the outer's domain set). Flag if det-of-composite needs
the maps to be differentiable at the point (chain rule) vs my blow-up being only piecewise nice. Be
explicit if (a) or (b) hides more work.
</grounding_rules>
