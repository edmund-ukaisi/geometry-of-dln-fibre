<task>
I am formalising a measure-theoretic change-of-variables (c-o-v) lemma in Lean 4 + Mathlib v4.29.
The target theorem has a FROZEN signature I cannot change (it is a structure field consumed elsewhere).
I need you to adjudicate ONE truth-value: is the target provable sorry-free given ONLY the resources
I list, or does it intrinsically require differentiability + injectivity facts that are NOT among my
given resources (i.e. it is a WALL — I should surface it rather than fake-close it)?

FROZEN TARGET (`interiorLDU_cov`), schematically over an opaque ambient dimension N = routeMAmbient M:

  theorem interiorLDU_cov (M ...) (V : Set (Fin N → ℝ)) (hV : MeasurableSet V)
      (g : (Fin N → ℝ) → ℝ≥0∞) :
    ∫⁻ x in φ '' (V \ {x | x p = 0}), g x
      = ∫⁻ u in V \ {x | x p = 0}, ENNReal.ofReal (∏ j, |u j| ^ (leafH j)) * g (φ u)

where φ = interiorLDUphi M ... : (Fin N → ℝ) → (Fin N → ℝ), p = structPivot M (a fixed coordinate),
leafH = interiorLDU_leafH M ... : Fin N → ℕ (the per-axis Jacobian exponents).

RESOURCES I AM GIVEN (the brief says: consume `interiorLDU_abs_det` as a BLACK BOX, do NOT re-derive it):

  (R1) interiorLDU_abs_det : ∀ u, |LinearMap.det (fderiv ℝ φ u).toLinearMap| = ∏ j, |u j| ^ (leafH j)
       -- the absolute Jacobian determinant VALUE only. NOTE: `fderiv` returns 0 for non-differentiable
       -- maps, so this statement ALONE does NOT entail differentiability of φ.

  (R2) coordZero_null : ∀ (q : Fin N), volume {x | x q = 0} = 0   -- a single coordinate hyperplane is null.

  (R3) Standard Mathlib measure theory (lintegral, MeasurableSet algebra, addHaar image-null lemmas).

RESOURCES I DO NOT HAVE (verified by grep over the whole Lean library):
  - NO sorry-free `Differentiable ℝ φ` or `HasFDerivAt φ` fact. (The only route is via a factor-list
    decomposition `composeFold fs = φ`, but `fs` (= interiorLDU_factors) and that map-equality
    (interiorLDU_map_eq) are themselves OPEN sorries owned by a sibling sub-task H1, which I must NOT
    consume or re-prove.)
  - NO injectivity fact: no `Set.InjOn φ S` for any S. The worked 4-dim template (`phi3333_cov`, a
    concrete (3,3,3,3) instance) proved InjOn by a bespoke triangular coordinate-recovery argument
    specific to that dimension; there is no general-M analogue, banked or derivable from R1-R3.

THE WORKED TEMPLATE (`phi3333_cov`) that the brief says to "generalize" used Mathlib's
`lintegral_image_eq_lintegral_abs_det_fderiv_mul volume hSgmeas hderivWithin hInjOn g`, whose
hypotheses are EXACTLY: (a) `∀ x ∈ S, HasFDerivWithinAt φ (D' x) S x` (differentiability), and
(b) `Set.InjOn φ S` (injectivity off the weighted axes). The template SUPPLIED both from
`differentiable_phi3333` and `phi3333_injOn`, neither of which has a general-M analogue available to me.

<output_contract>
Answer in 3 short sections, decisive:
1. VERDICT: Is `interiorLDU_cov` provable sorry-free from {R1, R2, R3} ALONE (no diff, no injectivity)?
   YES or NO, one line.
2. WHY: The load-bearing reason. In particular: does the RHS term `g (φ u)` (a genuine geometric
   pushforward, g arbitrary nonneg measurable) force the use of an injective-c-o-v lemma, hence force
   BOTH differentiability and injectivity as genuine inputs? Is there ANY Mathlib route to this exact
   image-pushforward identity that needs NEITHER? (e.g. a trick using only the determinant value, or a
   measure-theoretic argument that sidesteps injectivity — be concrete about whether it exists in v4.29.)
3. RECOMMENDATION: Given the brief froze the signature WITHOUT diff/injectivity hypotheses and forbade
   consuming H1's factor-list sorries, is the honest move to (a) surface a WALL (the frozen signature is
   under-resourced — it needs diff+injectivity threaded in, which only H1/another sub-task can supply),
   or (b) is there a legitimate sorry-free close I am missing? Pick one.
</output_contract>

<grounding_rules>
Distinguish Mathlib facts you are CERTAIN exist at v4.29 from ones you INFER. If you propose a
sorry-free route, name the exact Mathlib lemma and its hypothesis list; if you cannot name it, say so
and treat the route as unavailable. Do not hand-wave "it should be possible".
</grounding_rules>
</task>
