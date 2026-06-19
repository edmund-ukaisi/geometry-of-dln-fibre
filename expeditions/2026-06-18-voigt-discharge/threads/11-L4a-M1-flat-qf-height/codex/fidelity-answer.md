1. **FAITHFUL**  
`Q.under R` is exactly `Q.comap (algebraMap R S)`, i.e. the contraction `Q ∩ R`. The only subtlety is terminological: `Q.LiesOver (Q.under R)` is tautological, not an extra lying-over theorem.

2. **FAITHFUL**  
Mathlib’s `QuasiFiniteAt R Q` means `QuasiFinite R (Localization.AtPrime Q)`, and Mathlib’s `QuasiFinite` deliberately does **not** include finite type. So this is not literally the Stacks/EGA quasi-finite-at-a-point definition unless finite/essential finite type is also present. But it is strong enough for the lemma: it implies `QuasiFiniteAt.eq_of_le_of_under_eq`, so primes below `Q` in the same fibre collapse. I do not see a counterexample under the exact Lean hypotheses.

3. **FAITHFUL**  
The informal claim says “Noetherian rings”, so assuming both `R` and `S` Noetherian is not a mismatch. From the Mathlib source, `R` Noetherian is a file-level section variable for the cited height formula, even though the lemma’s visible binders emphasize `S`. As a minimal theorem, `R` Noetherian may be removable by a direct chain/going-down argument, but it is an expected Noetherian dimension-formula hypothesis.

4. **FAITHFUL**  
Yes: Mathlib’s `Etale` gives finite presentation and formal étaleness; formal étale gives formal unramified and smooth, hence flat, and with essential finite type + formally unramified Mathlib supplies quasi-finiteness. No extra hidden hypotheses beyond the corollary’s stated Noetherian assumptions are needed.

5. **FAITHFUL**  
The name accurately says what the theorem proves: height equality with the contraction under flatness and `QuasiFiniteAt`. It does not claim finite type, so it tracks Mathlib’s broadened quasi-finite convention. The geometric “fibre contributes nothing” is captured through the fibre-height-zero auxiliary argument, even if not in the theorem name.

Overall verdict: **FAITHFUL-WITH-CAVEAT**