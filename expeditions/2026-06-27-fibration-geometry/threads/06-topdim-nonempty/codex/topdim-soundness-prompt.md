<task>
I am red-teaming a Lean 4 / Mathlib proof of a pure commutative-algebra lemma, for SOUNDNESS of the
mathematical argument (not Lean syntax). Verify the math is correct, or find a gap.

CLAIM: For a nontrivial Noetherian commutative ring A, the set
  TopDimMinPrimes A := { p | p ∈ minimalPrimes A ∧ ringKrullDim (A ⧸ p) = ringKrullDim A }
is nonempty. (ringKrullDim valued in WithBot ℕ∞; coheight of a prime x = krull dim of the closed
subset V(x) = sup of lengths of chains of primes ABOVE x; equivalently ringKrullDim (A ⧸ p) = coheight p.)

THE PROOF STRATEGY (as implemented):
1. minimalPrimes A is finite (Noetherian) and nonempty (since ⊥ ≠ ⊤ in a nontrivial ring, ⊥ has a
   minimal prime over it).
2. Choose a minimal prime p maximising q ↦ ringKrullDim (A ⧸ q) over the FINITE nonempty set
   minimalPrimes A (max attained: Set.exists_max_image).
3. Claim that this max value EQUALS ringKrullDim A, by le_antisymm:
   (≤ direction) ringKrullDim (A ⧸ p) ≤ ringKrullDim A: the quotient bound (surjection A ↠ A/p),
                 i.e. ringKrullDim_quotient_le.
   (≥ direction) ringKrullDim A ≤ ringKrullDim (A ⧸ p): using
                 ringKrullDim A = ⨆ x : Spec A, coheight x  (krullDim_eq_iSup_coheight),
                 then for each prime x, pick a minimal prime q ≤ x (exists_minimalPrimes_le, since ⊥ ≤ x.asIdeal),
                 and bound:
                    coheight x ≤ coheight q        [coheight_anti, since q ≤ x and coheight is ANTITONE]
                              = ringKrullDim (A ⧸ q) [ringKrullDim_quotient_eq_coheight]
                              ≤ ringKrullDim (A ⧸ p) [p maximises over minimal primes, q is minimal].
                 Hence ⨆_x coheight x ≤ ringKrullDim (A ⧸ p).

THE SPECIFIC SOUNDNESS QUESTIONS:
(Q1) Is "coheight is ANTITONE" correct? i.e. for primes q ≤ x, is coheight x ≤ coheight q? Coheight =
     sup of chain-lengths going UP from the prime. A smaller prime q has at least as many primes above
     it as the larger x, so its coheight should be ≥. Confirm the direction is coheight x ≤ coheight q
     (NOT the reverse), and that this is exactly a "going-down"-free monotonicity (no integral/flatness
     hypothesis needed — pure order theory on Spec, since {primes ≥ x} ⊆ {primes ≥ q}).
(Q2) Is it legitimate to bound coheight x by going through SOME minimal prime q ≤ x, rather than needing
     the chain to start at a minimal prime? The argument only needs: every prime x has a minimal prime
     q ≤ x, and coheight x ≤ coheight q. Is there any subtlety with WithBot ℕ∞ (e.g. ⊥, ⊤, or the sup
     being over an empty/infinite family) that could make the inequality fail at the boundary?
(Q3) Does this argument genuinely prove the EQUALITY ringKrullDim (A ⧸ p) = ringKrullDim A, and not
     merely ≤? In particular is the ≥ direction (the iSup_le over all primes x) airtight, given that
     p itself is a minimal prime so coheight p = ringKrullDim (A ⧸ p) is one of the terms — but the
     proof does NOT rely on p being a specific x, it bounds EVERY x's coheight by ringKrullDim(A⧸p).
(Q4) Any hidden requirement that A be finite-dimensional? The claim asserts NO finite-dimensionality
     hypothesis. Does the WithBot ℕ∞ valuation make the sup/antisymmetry work even if ringKrullDim A = ⊤?
</task>

<output_contract>
For each of Q1–Q4: a one-word verdict (SOUND / GAP / SUBTLE) followed by 2-4 sentences of justification.
Then a final overall line: "OVERALL: <SOUND|GAP-at-Qn>". Be terse. If you find a genuine gap, give the
minimal counterexample or the missing hypothesis.
</output_contract>

<grounding_rules>
This is a math-soundness review. State plainly which claims are standard theorems (cite the standard
name, e.g. "coheight antitone is order-dual of height monotone") vs which are your inference. Do NOT
assume the Lean lemma names are correctly applied — reason from the MATH. If a step is correct math but
the named lemma might have a different direction/hypothesis, flag that as SUBTLE.
</grounding_rules>
