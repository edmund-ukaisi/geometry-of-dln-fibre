<task>
Lean 4 / Mathlib v4.29 formalisation. I must prove ONE theorem (the "atlas change-of-variables
for the local RLCT"). I want your judgement on the CLEANEST bounded proof decomposition, and an
honest verdict on whether it is ~1 focused effort or a multi-hundred-line monument, plus the single
riskiest step.

FRAMEWORK (all already defined, cite-free):
- `negPow K c := fun x => (K x) ^ (-c)`  (Real.rpow; note 0^(neg) = 0).
- `localAdmissibleExponents K x := {c | 0 ≤ c ∧ IntegrableAtFilter (negPow K c) (𝓝 x)}`.
- `rlctAt K x := sSup (localAdmissibleExponents K x)`.
- `wLocalAdmissibleExponents W K x := {c | 0 ≤ c ∧ IntegrableAtFilter (fun w => W w * negPow K c w) (𝓝 x)}`.
- `wrlctAt W K x := sSup (wLocalAdmissibleExponents W K x)`.
- `sumSqFam F := fun w => ∑ i, (F i w)^2`  (F : Fin M → (Fin D → ℝ) → ℝ).
- A `Chart F x₀` structure carries: `g : (Fin D→ℝ)→(Fin D→ℝ)`, `hg0 : g 0 = x₀`, `hg_cont`,
  `hg_analytic : AnalyticOnNhd ℝ g univ`, `dom` (COMPACT, `0 ∈ dom`), `nbhd` (OPEN, `dom ⊆ nbhd`),
  `excep` (measurable, `volume excep = 0`), `hg_inj : InjOn g (nbhd \ excep)`,
  and its Jacobian weight `jacWeightFn := fun u => |det (fderiv ℝ g u)|` (proven Continuous).
- A `Resolution F x₀` carries: `numCharts`, `charts : Fin numCharts → Chart F x₀`, `hne` (univ nonempty),
  `U : Set _`, `hU : U ∈ 𝓝 x₀`, `hcover : volume (U \ ⋃ c, (charts c).g '' (charts c).dom) = 0`.

ALREADY PROVED (usable):
- `Chart.two_mul_wrlctAt_eq_chartMin`: per chart, `2 * wrlctAt jacWeightFn (sumSqFam (F∘g)) 0 = chartMin`
  (a finite value). In its proof I established that the chart's weighted admissible set EQUALS a
  concrete `Set.Ico 0 T_c` (via Object A ideal-invariance + Object C monomial rule); so each chart's
  `wLocalAdmissibleExponents (charts c).jacWeightFn (sumSqFam (F∘(charts c).g)) 0 = Ico 0 T_c`, downward-closed.
- Mathlib area formula pinned & available:
  `lintegral_image_eq_lintegral_abs_det_fderiv_mul μ hs (hf' : ∀ x∈s, HasFDerivWithinAt f (f' x) s x)
     (hf : InjOn f s) g : ∫⁻ x in f''s, g x ∂μ = ∫⁻ x in s, ENNReal.ofReal |(f' x).det| * g (f x) ∂μ`
  and `addHaar_image_le_lintegral_abs_det_fderiv` (no-injectivity `≤`, g≡1).
- `IntegrableAtFilter` = `∃ s ∈ filter, IntegrableOn f s`.

TARGET THEOREM (statement locked):
`rlctAt (sumSqFam F) x₀ = Finset.univ.inf' res.hne (fun c => wrlctAt (res.charts c).jacWeightFn
   (sumSqFam (fun i => F i ∘ (res.charts c).g)) 0)`.

The intended math: local integrability of `(sumSqFam F)^(-c)` near x₀ holds  ⟺  for EVERY chart,
`jacWeightFn · (sumSqFam(F∘g))^(-c)` is integrable near 0. Then the global admissible set = the
intersection of the per-chart weighted admissible sets = ⋂ Ico 0 T_c = Ico 0 (min T_c), whose sSup
is min_c T_c = the RHS inf'.

The two legs I foresee:
- (≤ / "some chart binds", i.e. global admissible ⊆ each chart's): change variables through a single
  chart g_c on a small source box B ⊆ nbhd \ (nbhd around excep); area-formula EQUALITY (InjOn off
  the null excep) turns `∫_{g_c '' B}(K)^(-c)` into `∫_B jacWeightFn·(K∘g_c)^(-c)`; and `g_c '' B ⊆ U`
  by continuity so it is dominated by the global integral. Gives: c globally-admissible ⟹ c
  chart-admissible.  RISK: the area-formula needs InjOn on ALL of B and B must avoid excep; the source
  neighbourhood-of-0 vs the compact dom mismatch.
- (≥ / "min suffices": each chart admissible ⟹ global admissible): use `hcover` to bound
  `∫_U K^(-c) ≤ Σ_c ∫_{g_c '' dom_c} K^(-c) ≤ Σ_c ∫_{dom_c} jacWeightFn·(K∘g_c)^(-c)` (subadditive,
  non-injective `≤`). RISK: chart-admissible gives integrability only NEAR 0, but dom_c is a fixed
  COMPACT set; need "integrable near 0 ⟹ integrable on all of dom_c" (the pulled-back integrand's
  only bad locus is the coordinate hyperplanes, worst at 0). This seems to need re-deriving the
  monomial structure on all of dom_c, not just near 0.
</task>

<output_contract>
1. VERDICT (one line): is this a bounded ~single-effort Lean proof given the above, or a
   multi-hundred-line development? State which.
2. The cleanest decomposition into named sub-lemmas (≤5), each with its one-line Lean-level content
   and which Mathlib lemma it rides. Order them.
3. The SINGLE riskiest / least-mechanical step, and whether it needs new math or is pure engineering.
4. Any place where the LOCKED statement is subtly wrong or unprovable as stated (e.g. the "near 0"
   vs "compact dom" mismatch making the ≥ leg need an extra hypothesis the structure lacks) — if so,
   name the minimal missing field/hypothesis. Flag inference vs certainty.
</output_contract>

<grounding_rules>
Distinguish "Mathlib definitely has X" (name it) from "there should be an X" (mark as inference).
If the ≥ leg genuinely cannot close from the `Resolution` fields as given, SAY SO plainly rather
than inventing a field — the point is to know whether the statement is landable or needs a
structure change.
</grounding_rules>
