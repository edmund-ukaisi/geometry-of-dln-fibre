<task>
Confirm or refute a claimed FALSITY in an RLCT lemma statement (the 11th in a series of fidelity gaps).

THE LEMMA (claimed FALSE as stated): `rlct_unit_invariant`
`rlctAt (fun w => u w * F w) wstar = rlctAt F wstar`
where `rlctAt G wstar := sSup { c' : NNReal-coerced-to-ℝ≥0∞ | ∃ U ∈ 𝓝 wstar, IntegrableOn (fun w => |G w|^(-(c':ℝ))) U volume }` (threshold of exponents for which |G|^{-c'} is locally Lebesgue-integrable near wstar).
HYPOTHESES: `0 < a`, and `∃ U ∈ 𝓝 wstar, ∀ w ∈ U, a ≤ |u w| ∧ |u w| ≤ b` (u bounded away from 0 and ∞ near wstar). **NO measurability hypothesis on u.**

CLAIM: false without `Measurable u`. Counterexample chain:
1. u = a·𝟙_V + b·𝟙_{Vᶜ} for V a NON-measurable set (Vitali) inside a nbhd of wstar — satisfies a≤|u|≤b (the only hypothesis), but u is non-measurable.
2. F ≡ 1 near wstar (real-analytic, nonzero) ⟹ rlctAt F wstar = ⊤ (|1|^{-c'}=1 integrable on bounded U for all c').
3. u·F = u, non-measurable. |u·F|^{-c'} = u^{-c'} takes two values on V / Vᶜ ⟹ non-measurable.
4. IntegrableOn requires AEStronglyMeasurable; a function non-measurable on positive-measure V (and Vᶜ) is not a.e.-equal to any measurable function ⟹ |u·F|^{-c'} not Integrable for any c'>0 ⟹ the admissible set is {0} (c'=0 gives |·|^0=1, integrable) ⟹ rlctAt(u·F) = sSup{0} = 0.
5. rlctAt F = ⊤ ≠ 0 = rlctAt(u·F) ⟹ equality FALSE. Fix: add `Measurable u`.

QUESTIONS:
1. Is the chain correct — does a non-measurable bounded u (Vitali-type) make u·F non-measurable, hence |u·F|^{-c'} non-integrable for c'>0, hence rlctAt(u·F)=0 while rlctAt F>0? CONFIRM/REFUTE.
2. Is the `Integrable ⟹ AEStronglyMeasurable` step (step 4) the rigorous crux, and does it genuinely fail for a function differing on a non-measurable positive-measure set? Any subtlety (e.g. could |u·F|^{-c'} be a.e. equal to a measurable function despite V non-measurable)?
3. Is `Measurable u` the right minimal fix, or is something weaker (AEMeasurable u) or stronger needed? At the use-site, u is an analytic unit (the resolution's nonvanishing chart factor) — is that measurable?
</task>

<output_contract>
Three numbered verdicts, terse: CONFIRMED/REFUTED + one-line reason each. For Q2 note any subtlety about AEStronglyMeasurable vs the non-measurable set. For Q3, the minimal correct hypothesis + whether the use-site (analytic unit) satisfies it.
</output_contract>

<grounding_rules>
Separate rigorous fact from inference (flag inferences). The Vitali-set non-measurability and Integrable⟹AEStronglyMeasurable are standard; use them. Don't invent Mathlib lemma names.
</grounding_rules>
