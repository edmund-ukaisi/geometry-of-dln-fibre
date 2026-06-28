<task>
Lean 4 + Mathlib v4.29, DLNFibre harness. FINAL piece of the (1,1)-smeared RLCT lower-bound atom: the
subBox source certificate feeding a LANDED divergence lemma. Everything else is sorry-free.

LANDED (sorry-free) I consume:
- routeMCore_phiSm_offpole : for off-pole u (hc : ∑ i, (frontMat M hL u i ⟨0,hm1⟩)² ≠ 0),
    routeMCore M (phiSm u) = (u (smPivotCoord))² · (∑ i, (frontMat M hL u i ⟨0,hm1⟩)²).
  [smPivotCoord : Fin (routeMAmbient M) is the deepest-(0,0) flat coord; phiSm is the flat chart.]
- measurePreserving_phiSm, measurableEmbedding_phiSm.
- routeMCore_box_diverges_of_MPChart M phi hmp hemb c' ε (hsrc) : the divergence lemma. hsrc =
    ∃ S, MeasurableSet S ∧ S ⊆ phi ⁻¹' (cubeBox (routeMAmbient M) ε) ∧
      (∫⁻ u in S, ENNReal.ofReal (|routeMCore M (phi u)| ^ (-c'))) = ⊤.
  cubeBox N ε := Set.univ.pi (fun _ => Set.Icc (-ε) ε).
- frontMat M hL u : Matrix (Fin (M 0)) (Fin (M⟨L-1⟩)) ℝ = prodAux M ((paramsEquivFlat).symm u) (L-1);
  CONTINUOUS in u (continuous_prodAux ∘ continuous_paramsEquivFlat_symm).
- abs_rpow_lintegral_Ioo_eq_top : ∫⁻ over Ioo 0 δ of |x|^p = ⊤ when p ≤ -1 (verify exact name/shape).

GOAL: routeMsm_box_diverges (the atom): for c' ≥ minAdm M / 2 (= 1/2, since minAdm=1 for (1,1)) and ε>0,
  ∫⁻ x in cubeBox (routeMAmbient M) ε, ENNReal.ofReal (|routeMCore M x|^(-c')) = ⊤.
via routeMCore_box_diverges_of_MPChart with a source box S.

THE VALIDATE-SMALL (RouteM121Smeared.subBox121_diverges, fixed (1,2,1)) did this with U = a² (a SINGLE
coordinate u 0), peeling TWO axes (z = u2 the divergence axis, a = u0 bounded away), integrand factoring
as |u2|^{-2c'}·|u0|^{-2c'}. For the GENERIC chart U = ∑ᵢ (frontMat i ⟨0⟩)² is a POLYNOMIAL in MANY front
coords (degree 2(L-1)), NOT a single coord — so that factoring does NOT transfer.

THE KEY NEW DIFFICULTY: I need a positive-measure source box S where (i) U > 0 (off the pole {U=0}),
(ii) the rate = u_p²·U so the integrand = |u_p|^{-2c'}·U^{-c'}, (iii) ∫_S diverges. The natural S:
pivot coord u_p ∈ (0,δ) [divergence axis], all OTHER coords (incl. the front coords) in [−δ,δ] or a
bounded-away set. The ∫|u_p|^{-2c'} over (0,δ) = ⊤; the rest ∫ U^{-c'} over the bounded box must be
> 0 (so ⊤·(>0)=⊤). But U^{-c'} can BLOW UP where U→0 inside the box (so ∫U^{-c'} could itself be ⊤ —
fine, still >0) OR U=0 on a null set (U^{-c'}=+∞ there, measure 0 — fine). The rest factor just needs
to be > 0, which holds as long as U > 0 on a positive-measure subset of the box.
</task>

<output_contract>
1. The cleanest source box S definition + the c-o-v factoring. Do I peel ONLY the u_p axis (Tonelli /
   piFinSuccAbove at smPivotCoord), leaving the rest as ONE block integral ∫ U^{-c'}? Then S =
   {u_p ∈ (0,δ)} × {rest ∈ box}, integrand = |u_p|^{-2c'} · U(rest-and-up... wait U depends on front
   coords which are in the rest block, NOT u_p — confirm U is independent of u_p [it is: U = ∑frontMat²,
   frontMat reads layers 0..L-2, smPivotCoord is the deepest (0,0); frontMat_update_pivot is LANDED]}.
   So U is a function of the REST coords only ⟹ Tonelli gives (∫|u_p|^{-2c'})·(∫_rest U^{-c'}) = ⊤·(>0).
2. How to prove ∫_rest U^{-c'} > 0 (the rest factor positive): the cleanest. U > 0 on a positive-measure
   subset of the rest box (U is a nonzero polynomial — frontMat at a point where all front layers = I /
   generic is nonzero). Is `MeasureTheory.setLIntegral_pos_iff` + a single witness point enough, or do I
   need U bounded-away? (Only > 0 is needed, not bounded-away — ⊤·c = ⊤ for any c > 0.)
3. The containment S ⊆ phiSm⁻¹(cubeBox ε): each flat coord of phiSm u is bounded by ε on S. phiSm only
   changes coord smPivotCoord (to u_p − smearShift); the others are u's coords ∈ [−δ,δ]. Need δ small +
   the smeared pivot coord bounded. The smearShift is unbounded near the pole — does S need to bound it?
   (The validate-small's subBox121 bounded a away from 0 so b/a is controlled.) How to handle generically.
4. The single biggest risk / likely wall (the U>0 non-vacuity? the smearShift-boundedness for containment?
   the Tonelli peel at the opaque smPivotCoord?). Be concrete.
</output_contract>

<grounding_rules>
Mark Mathlib lemmas unsure at v4.29 as "verify". Prefer reusing routeMCore_phiSm_offpole +
routeMCore_box_diverges_of_MPChart + the landed frontMat continuity. The rate identity is OFF-POLE only
(the cov sees it a.e.); S must stay off the pole {U=0} (a null set). minAdm=1 ⟹ NO radial Jacobian
weight (weight 1), so routeMCore_box_diverges_of_MPChart [not the RadialMPChart variant] is the target.
</grounding_rules>
