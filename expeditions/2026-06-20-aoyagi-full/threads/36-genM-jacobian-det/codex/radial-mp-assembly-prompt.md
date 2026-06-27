<task>
Lean 4 + Mathlib v4.29. I'm extending a smeared-chart box-divergence atom from minAdm=1 (done) to
minAdm≥2. The minAdm=1 case was MEASURE-PRESERVING (weight 1) and used a clean reusable lemma. For
minAdm≥2 the chart has a RADIAL blow-up with det |z|^{minAdm−1} ≠ 1 — NOT measure-preserving. I need the
cleanest reusable generalized-assembly shape. The chart is also RATIONAL (unbounded near a null pole),
so the final step must use a preimage sub-box (NOT image-containment).

THE DONE minAdm=1 LEMMA (reusable, landed sorry-free):
  routeMCore_box_diverges_of_MPChart (M phi) (hmp : MeasurePreserving phi volume volume)
    (hemb : MeasurableEmbedding phi) (c' ε) (hsrc : ∃ S, MeasurableSet S ∧ S ⊆ phi⁻¹(cubeBox N ε) ∧
      ∫_S (loss∘phi)^{-c'} = ⊤) : ∫_{cubeBox N ε} (loss)^{-c'} = ⊤
  proof: setLIntegral_comp_preimage_emb (∫_{cubeBox} = ∫_{phi⁻¹(cubeBox)} (loss∘phi)) + lintegral_mono_set hsrc.

THE minAdm≥2 SMEARED CHART (validated 46/46, e.g. (2,3,1): r=2,c=1,s=1,minAdm=2,N=9):
  φ_sm = Q ∘ radial ∘ shear, where:
  - Q = paramsEquivFlat ∘ pack : measure-preserving LINEAR reshape (det ±1).
  - radial = pivotBlowupOn (the r·c = minAdm kept-block coords) at pivot z : POLYNOMIAL, det |z|^{minAdm−1},
    differentiable EVERYWHERE (banked pivotBlowupOnDeriv_det / pivotBlowupOn_hasFDerivWithinAt).
  - shear = the rational Λ₀-shear (det 1, MEASURE-PRESERVING via skew_product, UNBOUNDED near pole {a=0}).
  Rate: loss∘φ = z²·U (U z-free polynomial). leafH = (minAdm−1 on z, 0 else). Off-pole.
  EXISTING banked pieces I can reuse: routeMCore_box_diverges_of_nodeChart (the achiever assembly) takes
  a NodeAchieverChart with a `cov` field
    ∫_{phi''(V\{z=0})} g = ∫_{V\{z=0}} ofReal(∏|u_j|^{leafH j})·g(phi u)
  discharged (for POLYNOMIAL charts) via lintegral_image_eq_lintegral_abs_det_fderiv_mul (needs all-x∈s
  differentiability + InjOn + |det|=∏|u_j|^{leafH j}) + uses image_subset for the final step. The rational
  chart breaks BOTH the all-x∈s differentiability (pole) AND image_subset (unbounded).

QUESTIONS:
1. The cleanest REUSABLE generalized assembly for "(measure-preserving) ∘ (radial blow-up)" charts with
   det |z|^{minAdm−1}, rational/unbounded pole. Candidate: a lemma
   `routeMCore_box_diverges_of_RadialMPChart` with hypotheses: the MP shear+Q part (MeasurePreserving +
   MeasurableEmbedding of the NON-radial composite `Q∘shear`), the radial Jacobian fact, and an
   `hsrc`-style preimage sub-box certificate. Or: decompose φ_sm = (Q∘shear) ∘ radial, push the radial
   Jacobian via lintegral_image_eq_lintegral_abs_det_fderiv_mul (radial is polynomial, diff everywhere,
   det |z|^{minAdm−1}) on the SUB-BOX (where InjOn holds), then the MP part via setLIntegral_comp_preimage_emb.
   Which composition order makes the c-o-v cleanest? Give the exact reusable hypothesis set + the final calc.
2. KEY: can I AVOID a bespoke radial-Jacobian assembly by folding the radial into the source divergence?
   I.e. instead of carrying |z|^{minAdm−1} as a c-o-v weight, note: on the sub-box S, the integrand
   (loss∘φ)^{-c'} = (z²U)^{-c'} = |z|^{-2c'}·U^{-c'}, and the z-axis divergence ∫₀ᵟ z^{-2c'} = ⊤ already
   handles the BINDING axis. The radial blow-up's role is geometric (it makes φ a diffeo onto the rank-r
   locus), but for the DIVERGENCE (∫_{cubeBox}=⊤), do I even need the radial Jacobian, or can I use the
   SAME routeMCore_box_diverges_of_MPChart if I prove φ_sm is measure-preserving AFTER ALL? Specifically:
   is φ_sm = Q∘radial∘shear measure-preserving? NO (radial det |z|^{minAdm−1}≠1). But: does the box-
   divergence ∫_{cubeBox}=⊤ actually NEED φ_sm measure-preserving, or just the EXISTENCE of a sub-box S of
   φ_sm⁻¹(cubeBox) where ∫_S (loss∘φ)^{-c'} = ⊤ AND a c-o-v relating ∫_S to ∫_{cubeBox}? Re-examine:
   routeMCore_box_diverges_of_MPChart needs MP for the setLIntegral_comp_preimage_emb step
   (∫_{cubeBox} g = ∫_{φ⁻¹(cubeBox)} g∘φ). For NON-MP φ, this c-o-v has the Jacobian:
   ∫_{cubeBox} g = ∫_{φ⁻¹(cubeBox)} g∘φ · |det Dφ| — so I'd LOWER-bound ∫_{cubeBox} g ≥ ∫_S g∘φ·|det Dφ|
   (over S ⊆ φ⁻¹(cubeBox), via lintegral_image_eq...). Then ∫_S (g∘φ)·|z|^{minAdm−1} = ⊤ needs the z-axis
   divergence with the EXTRA |z|^{minAdm−1} factor: ∫₀ᵟ z^{-2c'}·z^{minAdm−1} dz — is this STILL ⊤ for
   c' ≥ minAdm/2? Compute: exponent = minAdm−1 − 2c' ≤ minAdm−1 − minAdm = −1, so YES ⊤. Confirm this is
   the right structure: the radial Jacobian z^{minAdm−1} is ABSORBED into the binding-axis divergence
   (the threshold minAdm/2 is exactly calibrated so z^{minAdm−1−2c'} ≤ z^{−1}). So the generalized
   assembly is lintegral_image_eq_lintegral_abs_det_fderiv_mul (radial part) ∘ MP (shear+Q), with the
   z-axis divergence now at exponent minAdm−1−2c' ≤ −1. Assess.
3. Given Q2: the cleanest is likely: φ_sm = (Q∘shear) ∘ radial where radial is the ONLY non-MP piece
   (polynomial, diff everywhere, InjOn off {z=0}, det |z|^{minAdm−1}). Then on a sub-box S:
   ∫_{cubeBox} g ≥ ∫_{radial '' (S' \ {z=0})} g∘(Q∘shear)  [Q∘shear MP, preimage]
              = ∫_{S' \ {z=0}} g∘(Q∘shear)∘radial · |det D radial|  [lintegral_image_eq, radial poly]
              = ∫_{S'\{z=0}} (loss∘φ)^{-c'} · |z|^{minAdm−1} = ⊤  [z-axis, exp ≤ −1].
   Is this the right factorization? What's the exact reusable hypothesis set (the MP+emb of Q∘shear, the
   radial HasFDerivWithinAt + InjOn + det, the sub-box S')? Give the lemma signature + calc skeleton.
</task>

<output_contract>
Answer Q1 (the reusable assembly options), Q2 (yes/no: is the radial Jacobian absorbed into the binding-
axis divergence at exponent minAdm−1−2c' ≤ −1? + the right c-o-v structure), Q3 (the exact factorization
+ reusable lemma signature + calc). End with "RECOMMEND:" — the single cleanest reusable generalized-
assembly shape for the minAdm≥2 smeared charts (and whether it subsumes the minAdm=1 MP lemma). Flag any
Mathlib v4.29 lemma name you're unsure of (esp. the lintegral_image_eq_lintegral_abs_det_fderiv_mul ∘ MP
composition, and whether abs_rpow_lintegral_Ioo with exponent minAdm−1−2c' is the right 1D atom).
</output_contract>

<grounding_rules>
Distinguish certain-Mathlib-facts from inference. Load-bearing: Q2 (the radial Jacobian z^{minAdm−1}
absorbed into the z-axis divergence — the exponent arithmetic minAdm−1−2c' ≤ −1 from c'≥minAdm/2) and Q3
(the c-o-v factorization order: MP-preimage then radial-Jacobian-image, or vice versa). Be concrete about
which piece carries the Jacobian.
