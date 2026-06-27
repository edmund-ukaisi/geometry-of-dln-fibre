<task>
Lean 4 + Mathlib (v4.29) formalisation. I am about to formalise the BOUNDARY-SMEARED achiever
chart for a deep-linear-network RLCT box-divergence atom. I need a sharp judgement on ONE gating
question BEFORE I write any Lean: can the rational chart discharge the EXISTING (fixed) chart
structure's change-of-variables field, or is there a genuine interface gap?

CONTEXT — the existing structure (cannot be changed for one instance):

  structure NodeAchieverChart (M) where
    ...
    phi : (Fin N → ℝ) → (Fin N → ℝ)          -- the chart map (N = flatDim)
    p   : Fin N                               -- the binding pivot axis
    leafH : Fin N → ℕ                         -- Jacobian exponents
    cov : ∀ (V : Set (Fin N → ℝ)), MeasurableSet V → ∀ (g : (Fin N → ℝ) → ℝ≥0∞),
        ∫⁻ x in phi '' (V \ {x | x p = 0}), g x
          = ∫⁻ u in V \ {x | x p = 0}, ENNReal.ofReal (∏ j, |u j| ^ (leafH j)) * g (phi u)
    ...

The banked POLYNOMIAL charts (phi4422, phi334) discharge `cov` via Mathlib's
  lintegral_image_eq_lintegral_abs_det_fderiv_mul (hs : MeasurableSet s)
      (hf' : ∀ x ∈ s, HasFDerivWithinAt f (f' x) s x)   -- ALL x in s, NOT a.e.
      (hf : InjOn f s) (g) :
    ∫⁻ x in f '' s, g x = ∫⁻ x in s, ENNReal.ofReal |(f' x).det| * g (f x)
applied with s = V \ {x p = 0}, then rewriting |det Dφ u| = ∏ |u j|^{leafH j}. The polynomial charts
are differentiable EVERYWHERE (HasFDerivAt phi u for all u); their extra null slice (e.g. {u 1 = 0}
for phi334) is only for InjOn, not differentiability.

THE SMEARED CHART (φ_sm), validated exact 46/46:
  - Coords (a reparam of all N flat coords): front factors A0..A_{L-2} (IDENTITY block); a radial
    pivot z + angular H̄ (r×c block, (0,0)=z-pivoted); residual S_bot (s×c, free). s = m1 − r > 0.
  - P := A0···A_{L-2} (the front product, M0 × m1). P_1 := first r columns (M0×r, full col rank r
    generically), P_2 := remaining s columns.
  - Λ_0 := (P_1ᵀ P_1)⁻¹ P_1ᵀ P_2   (RATIONAL in the front coords — divides by the r×r Gram minor).
  - A_{L-1} := [ z·H̄ − Λ_0·S_bot ; S_bot ].
  - φ_sm : (front, z, H̄-ang, S_bot) ↦ (front, A_{L-1}).
  - Telescopes: P·A_{L-1} = z·P_1 H̄, so F = ‖P A_{L-1}‖² = z²·U, U = ‖P_1 H̄‖² a POLYNOMIAL
    (the rational Λ_0 cancels out of F).
  - |det Dφ_sm| = |z|^{minAdm−1} EXACTLY (block-triangular: identity front + unit-triangular det-1
    rational shear + radial pivotBlowup), OFF the null pole set N0 := {det(P_1ᵀ P_1) = 0}.
  - The chart is a genuine diffeo onto its image only on (V \ {z=0}) \ N0; on N0, Λ_0 is undefined
    (blows up) so φ_sm is not even continuous there (under any extension).

The pivot axis for the cov field is z, so the cov set is V \ {z = 0}. N0 is a proper algebraic
hypersurface in the FRONT coords (codim ≥ 1, Lebesgue-null), NOT contained in {z = 0}.

THE GATING QUESTION:
The cov field removes ONLY {z = 0}. The Mathlib c-o-v lemma needs HasFDerivWithinAt φ_sm on ALL of
s = V \ {z=0}. But φ_sm is NOT differentiable on N0 ⊆ s (the pole). So the banked route fails as-is.

I considered: there is NO a.e. version of lintegral_image_eq_lintegral_abs_det_fderiv_mul in
Mathlib v4.29 (only the all-x∈s version). The threshold-transport lemma S1.1
(weightedThreshold_le_transport / _transport_aux) DOES allow differentiability only off a null set
E (hderiv : ∀ m ∈ Eᶜ, HasFDerivAt π (Dπ m) m), but it produces an inequality/equality of
weightedThreshold (an RLCT sSup), NOT the raw lintegral identity the cov field demands.

</task>

<questions>
1. Is my reading correct that the EXISTING cov field (Mathlib all-x∈s c-o-v on s = V\{z=0}) CANNOT
   be discharged by the rational φ_sm, because the pole N0 ⊆ s is a genuine non-differentiability
   that is null but not inside the removed {z=0}? Or is there a route I am missing?

2. Can I PROVE the existing cov identity for φ_sm by splitting s = (s \ N0) ∪ (s ∩ N0): apply the
   Mathlib lemma on s \ N0 (where φ_sm is C¹, InjOn, |det|=∏|u_j|^{leafH j}), and argue the s ∩ N0
   contributions vanish on BOTH sides because N0 is null? Concretely:
   - RHS: ∫⁻ over (s ∩ N0) of ofReal(∏|u_j|^h)·g(φ u) — is zero since N0 is null (volume-null set,
     integrand finite-ish). YES?
   - LHS: ∫⁻ over φ_sm '' (s ∩ N0) of g — needs volume(φ_sm '' (s ∩ N0)) = 0 (a Luzin-N / image-of-
     null-is-null fact). φ_sm is undefined on N0; but if I extend φ_sm arbitrarily-measurably on N0,
     is φ_sm '' (s ∩ N0) null? This needs the image of a null set to be null, which requires φ_sm
     Lipschitz / differentiable ON N0 too (Luzin-N) — which fails. So is the LHS the real obstruction?
   Assess this split route precisely. Does it close, or does the LHS φ_sm''(s∩N0) image-null
   requirement re-introduce exactly the differentiability-on-N0 that fails?

3. If the existing cov field genuinely cannot be discharged, what is the MINIMAL honest fix, ranked
   by Lean cost: (a) a NEW structure field/variant `cov'` that removes {z=0} ∪ N0 and a matching
   M-agnostic divergence assembly that drops the extra null slice (mirroring how phi334 already
   removes a 2nd slice {u 1=0} but only inside InjOn, NOT inside the cov set) — i.e. generalise the
   cov set to remove an EXTRA null measurable set; (b) prove the LHS image-null via some other
   structure; (c) something else. For (a): does dropping an EXTRA null set from the cov set keep the
   downstream `routeMCore_box_diverges_of_nodeChart` assembly sound (it currently argues {z=0} is
   null to restore V; removing a 2nd null set N0 is the same kind of argument — the box-divergence
   LOWER bound only needs the lintegral over the smaller set, monotone, so removing more null mass
   is harmless for a LOWER bound)?

4. Sanity-check the divergence-direction soundness of (a): the atom is a box-divergence (the
   integral = ⊤). The chart supplies a LOWER bound chain (calc ending in ≤ cubeBox integral). If I
   compute the leaf divergence on the SMALLER set s \ ({z=0} ∪ N0) and the cov pushes it to
   φ_sm''(s\({z=0}∪N0)) ⊆ cubeBox, then by lintegral_mono_set the cubeBox integral ≥ ⊤, done. Does
   removing N0 from the source set WEAKEN the lower bound to the point it no longer diverges? (The
   leaf integral ∫ monomialIntegrand·U^{-c} over [0,δ]^N minus a null set is still ⊤ since the
   divergence is from {z→0}, and N0 is null — confirm the box-divergence survives deleting a null
   set that does NOT contain the singular locus {z=0}.)
</questions>

<output_contract>
Answer Q1–Q4 in order, each ≤ 8 sentences. For Q1 give a yes/no verdict on whether the existing cov
is dischargeable. For Q2 give a yes/no on whether the split route closes and name the precise
blocking sub-fact if not. For Q3 rank the fixes and pick the cheapest sound one. For Q4 give a
yes/no on whether the box-divergence survives, with the one-line reason. End with a single
"VERDICT:" line: either "EXISTING cov dischargeable via <route>" or "GAP: need <minimal fix>".
Flag explicitly any claim that is inference vs. a Mathlib fact you are certain of.
</output_contract>

<grounding_rules>
Distinguish: (i) Mathlib v4.29 facts you are confident exist, (ii) standard measure-theory facts
(image of null under Lipschitz is null; null sets don't affect lintegral), (iii) inference about
this specific construction. Do NOT assert a Mathlib lemma name exists unless you are confident; if
unsure, say "a lemma of this shape should exist / may need proving". The key uncertainty is the LHS
image-null requirement in Q2 — be precise there.
</grounding_rules>
