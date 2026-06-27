<task>
Lean 4 + Mathlib v4.29 (pin 8a178386). I need to PROVE one commutative-algebra lemma,
sorry-free and axiom-clean ([propext, Classical.choice, Quot.sound]). I want the SHORTEST
robust assembly route from EXISTING Mathlib lemmas (names below), and the one or two steps
most likely to bite.

GOAL LEMMA (the only thing I must prove):
  For a NONTRIVIAL Noetherian commutative ring `A`, the set
    TopDimMinPrimes A := { p | p ∈ minimalPrimes A ∧ ringKrullDim (A ⧸ p) = ringKrullDim A }
  is NONEMPTY.

Equivalently it suffices to prove the structural fact:
  ∃ p ∈ minimalPrimes A, ringKrullDim (A ⧸ p) = ringKrullDim A.
(Then nonemptiness of TopDimMinPrimes is immediate by unfolding its def.)

My intended math route (verify or replace with something shorter):
  (1) ringKrullDim A = Order.krullDim (PrimeSpectrum A); PrimeSpectrum A is Nonempty (A nontrivial),
      so ringKrullDim A = ⨆ (x : PrimeSpectrum A), ↑(Order.coheight x).
  (2) For each prime x, coheight x = ringKrullDim (A ⧸ x.asIdeal)
      [via coheight_eq_krullDim_Ici + Ideal.primeSpectrumQuotientOrderIsoZeroLocus + ringKrullDim_quotient,
       since zeroLocus {x} as a subtype is order-iso to Set.Ici x in PrimeSpectrum A].
  (3) Going-down: every prime x dominates some minimal prime q ≤ x with coheight q ≥ coheight x
      (Set.Ici x ⊆ Set.Ici q gives krullDim Ici x ≤ krullDim Ici q, i.e. coheight x ≤ coheight q).
      So  ⨆ over all primes coheight  =  ⨆ over minimalPrimes coheight.
  (4) minimalPrimes A is FINITE (minimalPrimes.finite_of_isNoetherianRing) and NONEMPTY
      (Ideal.nonempty_minimalPrimes for ⊥ ≠ ⊤, i.e. A nontrivial). A finite nonempty sup in
      WithBot ℕ∞ / ℕ∞ is ACHIEVED — so some minimal prime q has coheight q = ⨆ = ringKrullDim A,
      i.e. ringKrullDim (A ⧸ q) = ringKrullDim A.

CONFIRMED-EXISTING Mathlib lemmas (names verified by grep at this pin):
  - `Order.coheight_bot_eq_krullDim [OrderBot α] : coheight (⊥ : α) = krullDim α`
  - `Order.coheight_eq_krullDim_Ici (x : α) : (coheight x : ℕ∞) = krullDim (Set.Ici x)`
  - `Order.krullDim_eq_iSup_coheight_of_nonempty [Nonempty α] : krullDim α = ↑(⨆ a, coheight a)`
  - `Order.krullDim_eq_iSup_coheight : krullDim α = ⨆ a, ↑(coheight a)`
  - `ringKrullDim_quotient (I : Ideal R) : ringKrullDim (R ⧸ I) = Order.krullDim (PrimeSpectrum.zeroLocus I)`
  - `Ideal.primeSpectrumQuotientOrderIsoZeroLocus (I : Ideal R) : PrimeSpectrum (R⧸I) ≃o (zeroLocus I subtype)`
  - `minimalPrimes.finite_of_isNoetherianRing : (minimalPrimes R).Finite`  (R Noetherian)
  - `Ideal.nonempty_minimalPrimes (h : I ≠ ⊤) : Nonempty I.minimalPrimes`
  - `Ideal.exists_minimalPrimes_le [J.IsPrime] (e : I ≤ J) : ∃ p ∈ I.minimalPrimes, p ≤ J`
  - `ringKrullDim` is `Order.krullDim (PrimeSpectrum R)` by def.
  - `minimalPrimes A = (⊥ : Ideal A).minimalPrimes` by def.

QUESTIONS:
  Q1. Is step (2) — coheight (x : PrimeSpectrum A) = ringKrullDim (A ⧸ x.asIdeal) — the
      load-bearing friction? Is there a SHORTER way to get it (a direct Mathlib lemma
      `coheight_eq_ringKrullDim_quotient` or via `PrimeSpectrum.zeroLocus_singleton` order-iso),
      OR should I avoid coheight entirely?
  Q2. ALTERNATIVE route to consider and rank vs the above: stay entirely in `WithBot ℕ∞` with
      `ringKrullDim (A⧸p) ≤ ringKrullDim A` (Mathlib `ringKrullDim_quotient_le`) for the ≤ side,
      and for the ≥ / achieved side use a maximal LTSeries in PrimeSpectrum A whose head is pushed
      to a minimal prime. Could that be shorter than the iSup-achieved bookkeeping?
  Q3. For step (4): what is the cleanest Mathlib idiom for "finite nonempty sup over a Set is
      achieved by a member"? (`Set.Finite.exists_maximal_wrt`? `Set.exists_max_image`? a
      `iSup`-attained lemma?) Give the exact lemma name at v4.29 if you know it, and whether it
      works in `WithBot ℕ∞` vs needing me to drop to `ℕ` / `ℕ∞`.
  Q4. The `⊥`-might-not-be-prime subtlety: A need NOT be a domain, so `⊥ : PrimeSpectrum A` does
      not exist. Confirm my route never secretly assumes a global bottom prime. Where could that
      bite?
  Q5. Anything in this chain that is FALSE or needs an extra hypothesis I omitted (e.g. does the
      sup-achieved step need finite Krull dimension, which I get from finite-type-over-field but
      NOT from bare Noetherian — is "Noetherian + nontrivial" actually enough, or must I also
      assume `ringKrullDim A ≠ ⊤`)? This is the most important question — flag any gap.
</task>

<output_contract>
  Section A (≤6 lines): verdict on the overall route — does it close with Noetherian+nontrivial
    alone, or is an extra finiteness hypothesis genuinely required? Answer Q5 first and bluntly.
  Section B: rank route-1 (coheight iSup) vs route-2 (LTSeries push-down) by total Lean friction;
    pick one and say why.
  Section C: for the chosen route, a numbered skeleton (Lean-shaped, lemma names at each step),
    flagging each step as [mechanical] / [friction] / [risk].
  Section D: answers to Q1, Q3, Q4 with exact lemma names where you are confident; mark any
    name you are NOT sure exists at v4.29 as "GUESS — verify".
</output_contract>

<grounding_rules>
  Distinguish lemmas you are CONFIDENT exist at Mathlib v4.29 from GUESSES. I will grep-verify
  every name before use; do not invent signatures. If a step needs a fact not in my list and you
  are unsure Mathlib has it, say so explicitly rather than asserting a lemma name.
</grounding_rules>
