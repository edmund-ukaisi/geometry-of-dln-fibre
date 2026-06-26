<task>
Lean 4 + Mathlib v4.29. A generic-smoothness chart-transport lemma currently DROPS component
incidence; I must strengthen it honestly (or land the cheapest genuine strengthening + correct the
docstring).

CURRENT (weak) lemma `exists_isSmoothAt_chartDsig_unconditional`:
  input: a top-dim minimal prime `I` of `sweepFibreRing` (a reduced fp k-algebra, k alg-closed).
  output: ∃ h : Away(chartDsig), ∀ p prime, h ∉ p → IsSmoothAt k p.
The output does NOT certify that D(h) (the basic open {h ≠ 0}) meets the chart-image of I's generic
point — i.e. it doesn't tie `h` to the chosen component `I` at all.

The chain producing `h`:
1. `isSmoothAt_sweepFibre_topComponent I hI : IsSmoothAt k I`  (per-component, LANDED).
2. `smooth_schurLoc_tensor_away_of_isSmoothAt_sweepFibre I (IsSmoothAt k I)` :
   ∃ g ∉ I, Smooth k (SchurLoc ⊗_k Away g)   -- g ∈ sweepFibreRing, g ∉ I is the load-bearing fact.
3. chart iso `e : Away(chartDsig) ≃ₐ[k] SchurLoc ⊗_k sweepFibreRing`; the chart element is
   `h = e.symm (includeRight g)`  where `includeRight : sweepFibreRing → SchurLoc ⊗_k sweepFibreRing`.
4. `isSmoothAt_of_smooth_localizationAway : h ∉ p → IsSmoothAt k p`.

WHAT I WANT: carry the incidence so the conclusion certifies "smooth at the chart generic point of the
chosen top component I", not merely "smooth on some basic open". Concretely I'd like a prime P of
Away(chartDsig) with h ∉ P and P corresponding to I across e (i.e. the prime e.map P =: Q of
SchurLoc ⊗ sweepFibreRing has Q.comap includeRight = I, and includeRight g ∉ Q).

KEY FACTS available cheaply: g ∉ I (from step 2). SchurLoc is a smooth NONZERO k-algebra (a
localization of a polynomial ring); includeRight is the base-change map sweepFibreRing →
SchurLoc ⊗_k sweepFibreRing.
</task>

<output_contract>
Rank these candidate C4 deliverables by COST (cheap → heavy) and for the top one give the exact
Mathlib lemma names (flag guesses):
(A) Just certify D(h) ≠ ∅ / h non-nilpotent (kills vacuity; uses includeRight g ≠ 0 since g ∉ I in a
    reduced ring + e.symm injective). Is this clean?
(B) Certify there EXISTS a prime Q of SchurLoc ⊗ sweepFibreRing with Q.comap includeRight = I and
    includeRight g ∉ Q (lying-over for the base-change map), then pull back P := e.map Q's preimage,
    h ∉ P. Which Mathlib lying-over / going-up / faithfully-flat lemma applies to includeRight
    (base change by a nonzero/faithfully-flat k-algebra)? Is `Ideal.exists_minimalPrimes_comap_eq`,
    `PrimeSpectrum.comap` surjectivity, or a faithfully-flat lemma the right tool? How heavy?
(C) Full "P is THE chart prime of I's generic point" (exact correspondence). Worth it or overkill?
Then: if (B)/(C) are heavy (multi-lemma), confirm (A) + a corrected docstring is the honest
minimal close, and state precisely what (A) does and does NOT claim.
Be terse.
</output_contract>

<grounding_rules>
Flag inference vs certainty. If a Mathlib lemma name is a guess, mark it [guess].
</grounding_rules>
