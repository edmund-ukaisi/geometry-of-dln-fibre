<task>
Lean 4 / Mathlib v4.29. I must prove ONE locked theorem (the "atlas change-of-variables for the
local RLCT"). I have a concrete architecture; I want your judgement on soundness/provability, the
single riskiest step, and any subtle statement problem. Distinguish "Mathlib definitely has X"
(name it) from inference.

FRAMEWORK (all defined, cite-free):
- negPow K c := fun x => (K x)^(-c)   (Real.rpow; 0^(neg)=0).
- localAdmissibleExponents K x := {c | 0 ≤ c ∧ IntegrableAtFilter (negPow K c) (𝓝 x)}.
- rlctAt K x := sSup (localAdmissibleExponents K x).
- wLocalAdmissibleExponents W K x := {c | 0 ≤ c ∧ IntegrableAtFilter (fun w=>W w*negPow K c w) (𝓝 x)}.
- wrlctAt W K x := sSup (wLocalAdmissibleExponents W K x).
- sumSqFam F := fun w => ∑ i, (F i w)^2   (F : Fin M → (Fin D→ℝ)→ℝ).
- monomialFam e := fun k u => ∏ d, (u d)^(e k d)   (e : Fin M → Fin D → ℕ).
- jacWeight h u := ∏ d, |u d|^(h d)   (h : Fin D → ℕ).
- monomialThreshold (kexp h : Fin D→ℕ) (hbind) := (bindingAxes kexp).inf' hbind (fun d=>(h d+1)/(2*kexp d)).
  bindingAxes kexp = {d | 0 < kexp d}.
- Chart F x₀ : record with g:(Fin D→ℝ)→(Fin D→ℝ), hg0: g 0 = x₀, hg_cont, hg_analytic (AnalyticOnNhd ℝ g univ),
  dom (COMPACT, 0∈dom), nbhd (OPEN, dom⊆nbhd), excep (measurable, volume excep=0),
  hg_inj: InjOn g (nbhd\excep), bexp: Fin M'→Fin D→ℕ, k₀, jac: Fin D→ℕ, unit,
  hchain: ∀ k d, bexp k₀ d ≤ bexp k d, hbind: (bindingAxes (bexp k₀)).Nonempty,
  hunit_cont: ContinuousOn unit nbhd, hunit_ne: ∀ u∈nbhd, unit u≠0,
  hjac: ∀ u∈nbhd, |det (fderiv ℝ g u)| = jacWeight jac u * |unit u|,
  hideal_fwd: RegionRepresents (F∘g) (monomialFam bexp) nbhd,
  hideal_bwd: RegionRepresents (monomialFam bexp) (F∘g) nbhd.
  jacWeightFn := fun u => |det (fderiv ℝ g u)| (proven Continuous).
- Resolution F x₀ : numCharts, charts:Fin numCharts→Chart F x₀, hne (univ nonempty),
  U:Set _, hU: U∈𝓝 x₀, hcover: volume (U \ ⋃ c, (charts c).g '' (charts c).dom) = 0.

ALREADY PROVED & usable:
- Object A (germ ideal invariance, weighted, SET form, at ANY base point x):
  wLocalAdmissibleExponents_sumSqFam_eq_of_germ_eq: with W,F,G measurable, W≥0 near x,
  LocallyNullZeros (sumSqFam G) x, LocallyNullZeros (sumSqFam F) x,
  GermRepresents G F x, GermRepresents F G x  ⟹
  wLocalAdmissibleExponents W (sumSqFam G) x = wLocalAdmissibleExponents W (sumSqFam F) x.
- RegionRepresents.germRepresents_of_isOpen (region rep on open V ⟹ GermRepresents at any x∈V).
- Object C origin VALUE: monomialSumSq_wrlctAt_eq: under hchain,hbind, unit ContinuousAt 0, unit 0≠0,
  Measurable unit, W =ᶠ[𝓝 0] jacWeight h · unit  ⟹
  wrlctAt W (sumSqFam (monomialFam e)) 0 = monomialThreshold (e k₀) h hbind.
  Its proof internally establishes hset: wLocalAdmissibleExponents W (sumSqFam(monomialFam e)) 0 = Ico 0 T,
  and hexp_iff: (∀ d, -1 < (h d - 2*(e k₀ d)*c)) ↔ c < T. I can refactor to expose the SET form.
- MonomialBox lemmas (network-free, over box (−ε,ε)^D): prodRpow_lintegral_box_lt_top (per-axis interval I
  same for all axes; each axis lintegral of |x|^{e_j} finite ⟹ product finite), prodRpow_boxSymm_lt_top,
  prodRpow_boxSymm_eq_top, boxSymm_mem_nhds, exists_boxSymm_subset.
- Chart.two_mul_wrlctAt_eq_chartMin: per chart, 2*wrlctAt jacWeightFn (sumSqFam (F∘g)) 0 = chartMin
  (= inf' binding (jac d+1)); its proof does Object-A-at-0 to swap sumSqFam(F∘g)↔sumSqFam(monomial bexp).
- Mathlib area formula (E=Fin D→ℝ, μ=volume): lintegral_image_eq_lintegral_abs_det_fderiv_mul
  (InjOn f s, hs meas, HasFDerivWithinAt): ∫⁻_{f''s} g = ∫⁻_s ofReal|det f'| * g(f x);
  addHaar_image_eq_zero_of_differentiableOn_of_addHaar_eq_zero (DifferentiableOn f s, μ s=0 ⟹ μ(f''s)=0);
  addHaar_image_le_lintegral_abs_det_fderiv (non-inj measure bound).
  LocallyIntegrableOn.integrableOn_isCompact (LocallyIntegrableOn f s + IsCompact s ⟹ IntegrableOn f s).
  LocallyIntegrableOn f s = ∀ x∈s, IntegrableAtFilter f (𝓝[s] x).

TARGET (statement LOCKED):
  rlctAt (sumSqFam F) x₀
    = Finset.univ.inf' res.hne (fun c => wrlctAt (res.charts c).jacWeightFn
        (sumSqFam (fun i => F i ∘ (res.charts c).g)) 0).

KEY IDENTITY I'll use: sumSqFam (fun i=>F i ∘ g) u = (sumSqFam F)(g u) = K(g u),
so negPow (sumSqFam(F∘g)) c u = (negPow K c)(g u), i.e. the chart weighted integrand
jacWeightFn u * negPow Kc c u = |det Dg u| * (negPow K c)(g u) = the area-formula RHS integrand with h=negPow K c.

MY ARCHITECTURE:
Let K = sumSqFam F (measurable, ≥0). Let T_c := monomialThreshold ((charts c).bexp k₀) jac hbind.
STEP 0 (per-chart set form): wLA_c := wLocalAdmissibleExponents jacWeightFn (sumSqFam(F∘g_c)) 0 = Ico 0 T_c,
  T_c > 0, wrlctAt_c = T_c. [Object-A-at-0 (as in Chart.two_mul...) ∘ exposed monomial SET form.]
  Gives BddAbove wLA_c and "c<T_c ⟺ c∈wLA_c (for c≥0)".

INFRA PIECE 1 (InjOn-off-null area equality, per chart, for measurable h:E→ℝ≥0∞):
  ∫⁻_{g''s} h = ∫⁻_s ofReal|det Dg|*(h∘g), when s measurable, g analytic(so HasFDerivWithinAt & DifferentiableOn),
  InjOn g (s\excep), volume excep=0.
  Proof: g''s and g''(s\excep) differ by g''(s∩excep) which is null (null-image lemma, DifferentiableOn);
  s and s\excep differ by null; apply Mathlib InjOn equality on s\excep. QUESTION: any obstruction?

LEG A (rlctAt ≤ inf'): Finset.le_inf' ⟸ ∀ c', rlctAt K x₀ ≤ wrlctAt_c'.
  Prove localAdmissibleExponents K x₀ ⊆ wLA_c' (then csSup_le_csSup with BddAbove wLA_c').
  Given c∈localAdmissible: ∃ s₀∈𝓝 x₀, IntegrableOn(negPow K c) s₀. Pick measurable nbhd s∋0 with g''s⊆s₀
  (continuity of g, g 0=x₀). Then ∫⁻_s ofReal(jacWeightFn·negPow Kc c) = ∫⁻_s ofReal|det Dg|·((negPow K c)∘g)
  = ∫⁻_{g''s}(negPow K c) [piece 1] ≤ ∫⁻_{s₀}(negPow K c) < ⊤. So integrable on s ⟹ c∈wLA_c'.

LEG B (inf' ≤ rlctAt): R := inf'_c T_c. Show Ico 0 R ⊆ localAdmissible K x₀, then
  R = sSup(Ico 0 R) ≤ sSup localAdmissible = rlctAt (BddAbove localAdmissible from Leg A subset + BddAbove wLA_c).
  Take 0≤c<R. Want IntegrableOn (negPow K c) U (U∈𝓝 x₀). Since U\⋃g_c''dom_c null:
  ∫⁻_U ofReal(negPow K c) = ∫⁻_{U∩⋃ g_c''dom_c} ≤ ∑_c ∫⁻_{g_c''dom_c}(negPow K c)
  = ∑_c ∫⁻_{dom_c} ofReal|det Dg_c|·((negPow K c)∘g_c) [piece 1]. Each term < ⊤ via:
    IntegrableOn (jacWeightFn·negPow Kc c) dom_c, from LocallyIntegrableOn+compact (piece 3), from
    for each p∈dom_c: IntegrableAtFilter (jacWeightFn·negPow Kc c) (𝓝 p), from
      Object-A-at-p (germ ideal eq at p via RegionRepresents.germRepresents_of_isOpen, both dirs;
      null guards discharge as in Chart proof but at p) reducing to monomial,
      then PIECE 2 (off-origin convergence): c<T_c ⟹ c∈wLocalAdmissible jacWeightFn (sumSqFam(monomial bexp)) p.

INFRA PIECE 2 (off-origin monomial convergence): for base point p, exponents e chain k₀, weight W with
  W =ᶠ[𝓝 p] jacWeight jac·unit (unit ContinuousAt p, unit p≠0, Measurable unit), and 0≤c<monomialThreshold(e k₀,jac):
  IntegrableAtFilter (fun u=>W u*negPow (sumSqFam(monomialFam e)) c u) (𝓝 p).
  PLAN: mirror monomialSumSq_wrlctAt_eq's ⊇ branch but BOX CENTERED AT p (∏_d (p_d-ε,p_d+ε)):
  chain-collapse sumSqFam(monomial e)=(monomial e k₀)²·U (U cont, U≥1>0 everywhere via 0^0=1);
  off axes integrand = V·∏|u_d|^{β_d}, β_d=jac_d-2c·(e k₀ d), all β_d>-1 (from c<T via hexp_iff, ALL axes);
  V=unit·U^{-c} bounded near p. Per-axis box lintegral: p_d≠0 axis interval avoids 0 (|x|^β cont on compact
  ⟹ finite); p_d=0 axis is (−ε,ε) (finite iff β_d>-1, TRUE). Needs a per-axis-interval box lemma
  (generalize prodRpow_lintegral_box_lt_top to I:Fin D→Set ℝ) + a "|x|^s integrable on interval avoiding 0".

INFRA PIECE 3: LocallyIntegrableOn.integrableOn_isCompact (Mathlib), fed by piece 2 at each p (𝓝[dom]p≤𝓝 p).
</task>

<output_contract>
1. VERDICT: is this architecture SOUND and provable-as-stated? Any leg that cannot close from the given
   fields? (Especially: is the LOCKED statement right, and does Leg B genuinely close via pieces 2+3?)
2. The SINGLE riskiest / least-mechanical step, and whether it needs new math or is engineering.
3. Piece 1 (InjOn-off-null equality): correct & buildable from the named Mathlib lemmas? Any gap
   (e.g. HasFDerivWithinAt from AnalyticOnNhd on univ; g''(s∩excep) null needs DifferentiableOn on s∩excep only)?
4. Piece 2 (off-origin, box at p, NO translation): is "box at p + per-axis interval convergence" the
   cleanest, or is translation-to-0 cleaner? Any landmine in V being only ContinuousAt p (measurability
   on a nbhd for AEStronglyMeasurable — I have Measurable unit + U polynomial)? Confirm β_d>-1 for ALL d
   (not just p-zero axes) suffices and follows from c<origin-threshold.
5. Any place a nonneg-measurable ⟹ (IntegrableOn ↔ ∫⁻ ofReal < ⊤) step needs care (the integrand
   jacWeightFn·negPow Kc c is nonneg & measurable; negPow K c nonneg & measurable).
6. Rough line-count estimate per piece; is the whole thing ~600-900 lines?
</output_contract>

<grounding_rules>
If a leg genuinely cannot close from the Resolution/Chart fields as given, SAY SO and name the minimal
missing field — do not invent one. Mark inference vs certainty. Do not paste large proofs; give the
decomposition and the risks.
</grounding_rules>
