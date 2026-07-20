1. **VERDICT = harmless-caveat.** For the DLN loss `K ≥ 0`, restricting to `0 ≤ c` is faithful: negative exponents cannot increase the supremum once `c = 0` is admissible. Negative `s` may be admissible, but they lie below `0`, so they do not affect the RLCT value in the paper setting.

2. **VERDICT = harmless-caveat.** For `K ≥ 0`, `K^(-c)` agrees with `|K|^(-c)` away from `K = 0`, so this is faithful for the DLN loss modulo the value assigned exactly on the zero locus. Lean’s `Real.rpow 0 (neg) = 0` is harmless for nonzero analytic/polynomial losses with Lebesgue-type measure, because the zero locus has measure zero; it would be a genuine gap for signed `F`, atomic measures, or positive-measure zero sets.

3. **VERDICT = harmless-caveat.** Yes: with the junk-`0` encoding, the honest finite-value reading of Prop. 8.3(iii) is the infimum over `{x | K x = 0}`, since paper-regular points contribute `+∞`, not `0`. The caveat is that the no-zero case is not faithfully represented: the paper gives `+∞`, while your ℝ-valued `sSup` gives junk `0`.

4. **VERDICT = faithful.** “Locally integrable” as a global property means locally integrable at every point for the fixed exponent, so `∀ x, IntegrableAtFilter ... (𝓝 x)` matches Def. 8.1(i). There is no noncompactness or paracompactness gap here; noncompactness affects whether the infimum is attained, not the meaning of local integrability.

Overall: `rlctGlobal` is faithful for the `F = K ≥ 0` DLN use-case with a nonempty zero locus and Lebesgue-type measure, provided the junk-`0` cases are kept explicitly out of scope.