<task>
You are an independent reviewer of a Lean 4 + Mathlib formalisation. I need a decorrelated
judgement on ONE question: is a cited axiom genuinely LOAD-BEARING in a theorem, or is its
dependency cosmetic on a statement that is "really 1/2 = 1/2"?

SETUP (definitions, paraphrased from Lean):
- `axisRatio (h k : ℕ) : ℝ≥0∞ := (h+1) / (2*k)`  (division in extended-nonneg-reals; k=0 gives ⊤).
- `monomialIntegrand d k h c u := (∏ⱼ |uⱼ|^{hⱼ}) * (∏ⱼ |uⱼ|^{2kⱼ})^{-c}`.
- `unitBox d := [0,1]^d`.
- `monomialThreshold d k h : ℝ≥0∞ := sSup { c | ∃ c':NNReal, c = c' ∧ IntegrableOn (monomialIntegrand d k h c') (unitBox d) volume }`.
  This is an honest measure-theoretic object: a supremum over the set of real exponents for which a
  Lebesgue integral converges. There is NO decidability/kernel evaluation route to its value.
- `monomial_rlct` is the SINGLE cited axiom (Watanabe/Hironaka normal-crossing extraction). Its
  threshold-half states, unconditionally: `monomialThreshold d k h = ⨅ⱼ axisRatio (hⱼ) (kⱼ)`.

THE THEOREM UNDER AUDIT:
  `case111_monomialThreshold : monomialThreshold 2 ![1,1] ![0,0] = ENNReal.ofReal (aoyagiLambda ![1,1,1] 0)`
PROOF (verbatim shape):
  rw [(monomial_rlct 2 ![1,1] ![0,0]).1, case111_axisRatio_inf, ofReal_aoyagiLambda_case111]
where `case111_axisRatio_inf : ⨅ⱼ axisRatio (![0,0] j) (![1,1] j) = 1/2` (sorry-free, arithmetic)
and `ofReal_aoyagiLambda_case111 : ENNReal.ofReal (aoyagiLambda ![1,1,1] 0) = 1/2` (sorry-free, kernel-eval).
`#print axioms case111_monomialThreshold` = [propext, Classical.choice, Quot.sound, monomial_rlct].

QUESTIONS:
1. Is `monomial_rlct` LOAD-BEARING here, i.e. is it the only bridge from the integral object
   `monomialThreshold` to the arithmetic value 1/2? Or could `monomialThreshold 2 ![1,1] ![0,0]`
   be reduced to 1/2 by computation/defeq WITHOUT the axiom (making the dependency cosmetic)?
2. State plainly what this theorem DOES validate and what it does NOT. In particular: does it,
   by itself, establish `rlctAt (dlnLoss) = aoyagiLambda` (the RLCT-headline)? Or only the
   agreement of the monomial-model threshold value with the closed-form citation value?
3. Any subtle soundness concern with the axiom's threshold-half being UNCONDITIONAL while its
   order-half is scoped to `∃ j, kⱼ ≠ 0`?
</task>

<output_contract>
Three numbered answers, terse. For Q1 a yes/no + one-sentence reason. For Q2 a two-line
"validates / does-not-validate". For Q3 one short paragraph.
</output_contract>

<grounding_rules>
Distinguish what you can deduce from the given definitions (fact) from what you infer about
Lean/Mathlib behaviour you cannot see (inference). Flag any inference explicitly. Do not invent
Mathlib lemma names.
</grounding_rules>
