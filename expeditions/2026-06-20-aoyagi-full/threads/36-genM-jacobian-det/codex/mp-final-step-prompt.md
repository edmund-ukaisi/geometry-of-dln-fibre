<task>
Lean 4 + Mathlib v4.29. I need the cleanest concrete formulation of a box-divergence via a
MeasurePreserving change-of-variables, for a RATIONAL chart that is UNBOUNDED near its pole (so the
usual "image ⊆ cubeBox" route fails). I have all the MP pieces; I need the right final-step shape.

GOAL (the atom for M=(1,2,1), N=4 flat coords):
  theorem routeM121sm_box_diverges (c' : NNReal) (hc' : (minAdm M121 : ℝ≥0∞)/2 ≤ (c':ℝ≥0∞))
      (ε : ℝ) (hε : 0 < ε) :
    ∫⁻ x in cubeBox 4 ε, ENNReal.ofReal (|routeMCore M121 x| ^ (-(c':ℝ))) = ⊤
where `cubeBox 4 ε = Set.univ.pi (fun _ => Set.Icc (-ε) ε)` (the symmetric cube around 0).

I HAVE (sorry-free, banked):
- `measurePreserving_phi121sm : MeasurePreserving phi121sm volume volume`  (phi121sm : (Fin 4→ℝ)→(Fin 4→ℝ))
- `measurableEmbedding_phi121sm : MeasurableEmbedding phi121sm`
- `MeasurePreserving.setLIntegral_comp_preimage_emb (hg) (hge) (f) (s) :
    ∫⁻ a in g ⁻¹' s, f (g a) ∂μ = ∫⁻ b in s, f b ∂ν`   (Mathlib)
- the RATE OFF-POLE: `routeMCore M121 (phi121sm u) = (u 2)^2 * (u 0)^2`  for `u 0 ≠ 0`
  (`routeMCore_phi121sm_offpole`); pivot is z = coord 2, U = a² = (u 0)², minAdm=1, leafH≡0.
- the a.e. leaf_integrand and the bare-monomial box-divergence:
  `monomialIntegrand_lintegral_box_eq_top (d k h) (hk : ∃j, k j≠0) (c') (hc') (hc'0) (hε) :
     ∫⁻ u in univ.pi (fun _:Fin d => Icc 0 ε), ofReal |monomialIntegrand d k h c' u| = ⊤`
  (over the FULL positive box [0,ε]^d; here monomialIntegrand for k=δ_z, h≡0 is |z|²^{-c'}).
- φ_sm is UNBOUNDED near its pole {a=u 0=0} (flat coord z−(b/a)sb → ∞), so φ_sm '' (box) ⊄ cubeBox.

THE OBSTRUCTION: the existing image_subset-based assembly needs φ_sm '' P ⊆ cubeBox, which FAILS.
The MP route: ∫_{cubeBox ε} g = ∫_{φ_sm⁻¹(cubeBox ε)} g∘φ_sm (setLIntegral_comp_preimage_emb). I then
want to lower-bound ∫_{φ_sm⁻¹(cubeBox)} (loss∘φ)^{-c} ≥ ⊤ using the rate z²a² and the monomial box-div.

QUESTIONS:
1. What is the cleanest concrete SOURCE SUB-BOX `P_sub ⊆ φ_sm⁻¹(cubeBox ε)` on which (i) the rate
   loss∘φ = z²a² holds (a≠0), (ii) `monomialIntegrand`-style divergence `∫_{P_sub} (z²a²)^{-c} = ⊤`
   survives, and (iii) `P_sub ⊆ φ_sm⁻¹(cubeBox)` is provable (φ_sm bounded on P_sub)? My candidate:
   `P_sub = {u : u 0 ∈ Icc δ' δ ∧ u 1 ∈ Icc (-δ) δ ∧ u 2 ∈ Icc 0 δ ∧ u 3 ∈ Icc (-δ) δ}` with `a=u 0`
   bounded away from 0 (so φ_sm bounded ⊆ cubeBox for small δ) AND z=u 2 ∈ [0,δ] still hitting z→0 (the
   divergence axis). Is the divergence ∫_{P_sub} (z²·a²)^{-c} = ⊤ derivable from the FULL-box
   `monomialIntegrand_lintegral_box_eq_top`, or do I need a Fubini-over-z restricted-box divergence
   lemma? The full-box lemma is over [0,ε]^d (a∈[0,ε] includes a=0); I need a∈[δ',δ]. Is there a
   restricted-box monomial divergence in the codebase, or is the clean move: factor the integral as
   (∫_{a,b,sb sub-box} U^{-c} da db dsb) × (∫_{z∈[0,δ]} |z|^{-2c} dz) by Fubini/Tonelli, the z-factor = ⊤
   for c ≥ minAdm/2 = 1/2 (∫₀ᵟ z^{-1} = ⊤), the other factor > 0?
2. Is there a SLICKER route avoiding the sub-box entirely: since I already PROVED the leaf-box
   divergence over the FULL box `[0,δ]^4` in the form `∫_{[0,δ]^4} monomialIntegrand·U^{-c} = ⊤`
   (`nodeLeaf_box_div`, which I have via the bundle), can I push THAT through MP directly? I.e. is
   `∫_{[0,δ]^4} (∏|u_j|^{leafH_j})·|loss∘φ|^{-c} = ⊤` (a.e. leaf_integrand, on [0,δ]^4\{z=0}) related to
   `∫_{cubeBox} |loss|^{-c}` via MP WITHOUT needing φ([0,δ]^4) ⊆ cubeBox — e.g. by
   `∫_{[0,δ]^4 ∩ φ⁻¹(cubeBox)} ≤ ∫_{φ⁻¹(cubeBox)} = ∫_{cubeBox}` and showing the FIRST integral is still
   ⊤ (the divergence at z→0 with a bounded-away region is inside φ⁻¹(cubeBox))? Assess whether
   `[0,δ]^4 ∩ φ⁻¹(cubeBox)` retains the ⊤ divergence (the z→0 mass with a bounded away from 0 sits in
   φ⁻¹(cubeBox) for small δ).
3. Concretely, for the REUSABLE lemma `routeMCore_box_diverges_of_MPChart` (params: rate-off-pole +
   a.e. leaf_integrand + cov-via-MP `phi_cov` + Ubound + MeasurableEmbedding + MeasurePreserving, NO
   image_subset), what is the minimal additional HYPOTHESIS I should add to make the final step clean?
   (e.g. a hypothesis `hbox_pre : ∃ δ>0, (the divergence sub-box) ⊆ φ⁻¹(cubeBox ε)` — a bounded-region
   containment that IS provable for the rational chart, unlike the full image_subset). Propose the exact
   reusable hypothesis + the final calc.
</task>

<output_contract>
Answer Q1 (the sub-box + whether full-box lemma suffices or need Fubini-z), Q2 (the slicker
intersect-route, yes/no + reason), Q3 (the minimal reusable hypothesis + the final calc skeleton). End
with "RECOMMEND:" — the single cleanest path to `∫_{cubeBox} = ⊤` for the rational MP chart, and the
exact reusable-lemma hypothesis that replaces image_subset. Flag any Mathlib lemma name you're unsure
exists in v4.29 (esp. Fubini/Tonelli for the z-axis factorization, `lintegral_prod`/`Measure.prod`).
</output_contract>

<grounding_rules>
Distinguish certain-Mathlib-v4.29-facts from inference. The load-bearing uncertainty: whether the
full-box monomial divergence (a∈[0,ε]) can be restricted to a∈[δ',δ] (Q1), and whether the
intersect-route (Q2) keeps ⊤. Be concrete about the Fubini/Tonelli lemma names if that's the route.
