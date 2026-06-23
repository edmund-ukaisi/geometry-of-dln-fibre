<task>
Decorrelated soundness check of a Lean composite change-of-variables lemma — the core of a 24-leaf
resolution-cover RLCT bound. Confirm the chaining + the null-set handling are sound; this infra will be
reused by a ~400-600 LoC ≥-direction grind, so a subtle flaw must be caught now.

CONTEXT: RLCT threshold integrals ∫⁻_U g (g = |F|^{-c}, ℝ≥0∞-valued, lintegral — no integrability hyps).
On ℝ^8 (Lebesgue). A composite chart φ = step1A ∘ Lemma2⁻¹ ∘ step2E resolves the (2,2,2) singular core.

THE COMPOSITE C-O-V LEMMA (`phiUnit_cov`): for W = (V \ {u2=0}) \ {u0=0} (off the two pivot loci),
  `∫⁻_{φ '' W} g = ∫⁻_W ofReal(|u0|³·|u2|²) · g(φ u)`.
Built by chaining three transports through the set-image identity φ''W = step1A''(Lemma2⁻¹''(step2E''W)):
  - step1A is a pivot blow-up (pivot coord 0, active {0,1,2,3}): C¹, InjOn off {x0=0}, |det Dstep1A| = x0³.
    The Mathlib Jacobian c-o-v (lintegral_image_eq…abs_det_fderiv_mul) needs InjOn on the SOURCE set. Here
    the source is Lemma2⁻¹''(step2E''W); the proof shows this set is ⊆ {x0≠0} (coord 0 is PRESERVED through
    Lemma2⁻¹∘step2E, established by a lemma coord0_L2S2: (Lemma2⁻¹(step2E u)) 0 = u 0), so the {x0=0}
    restriction is a no-op (disjoint), and InjOn holds.
  - Lemma2⁻¹ is a MEASURE-PRESERVING HOMEOMORPHISM (det ±1, transvections, Jacobian 1) — pure m.p.
    transport, NO Jacobian factor.
  - step2E is a pivot blow-up (pivot coord 1 of the Fin-7 tail = coord 2 of Fin 8, active {1,2,3}): |det| =
    z1² ; InjOn off {u2=0} (the W-restriction), again a no-op on W.
  - Final |det| product = |u0|³·|u2|² (the binding-monomial weight); pivot loci {u0=0},{u2=0} are null
    (coordinate hyperplanes, addHaar_submodule).

THE ≤-CONCLUSION (`rlctAtOn_myF222_le ≤ 3/2`): for every c'>3/2, ε>0, the cube integral ∫⁻_{[-ε,ε]^8}
|myF222|^{-c'} = ⊤, shown by: ⊤ = ∫⁻_P monomialIntegrand·Uval^{-c'} (one leaf box P=[0,δ]^8 diverges,
since c' > monomialThreshold=3/2 and Uval∈[1,B] a bounded unit) = ∫⁻_P |u0|³|u2|²·|myF∘φ|^{-c'} (a per-
leaf integrand EQUALITY) = ∫⁻_W … (drop null pivot loci) = ∫⁻_{φ''W} |myF|^{-c'} (the composite c-o-v,
backwards) ≤ ∫⁻_{cubeBox ε} |myF|^{-c'} (φ''W ⊆ the cube box, lintegral_mono_set). So the cube integral
≥ ⊤.

QUESTIONS:
1. Is the composite c-o-v SOUND — specifically, is it legitimate to chain the two Jacobian blow-up c-o-v's
   with the m.p. homeomorph splice in between, and to treat the {x0=0}/{u2=0} pivot-zero restrictions as
   no-ops via the coord-preservation argument (coord 0 preserved through Lemma2⁻¹∘step2E)? Any gap where the
   InjOn-on-source hypothesis of the middle/outer blow-up c-o-v could fail?
2. Is the ≤-direction localization SOUND — does ONE binding leaf's box diverging (∫⁻_P = ⊤, P ⊆ cube via
   φ) genuinely force the cube integral = ⊤, hence c' inadmissible, hence rlctAtOn ≤ 3/2? Any quantifier slip
   (e.g. needing ALL leaves, or the leaf box not actually inside the cube)?
3. Is the unit-handling sound — the per-leaf integrand is an EQUALITY |u0|³|u2|²·|myF∘φ|^{-c} =
   monomialIntegrand·Uval^{-c} with Uval∈[1,B] a genuine bounded-away-from-0 unit, so the leaf's
   monomialThreshold (3/2) IS the leaf's RLCT (the unit doesn't move the threshold)? Or could the unit Uval
   secretly vanish / blow up and shift it?
</task>

<output_contract>
Three numbered verdicts, terse: SOUND/FLAG + reason. Flag any gap in the chaining, the no-op restriction
argument, the one-leaf localization, or the unit-handling. Distinguish fact from inference.
</output_contract>

<grounding_rules>
The Mathlib Jacobian lintegral c-o-v (image = ∫|det|·g∘φ, InjOn+C¹ on the source, over ℝ≥0∞), m.p.-
homeomorph lintegral transport, addHaar-null coordinate hyperplanes, and "∫⁻ over a superset ≥ ∫⁻ over a
subset" are standard. Flag inferences. Don't invent Mathlib lemma names.
</grounding_rules>
