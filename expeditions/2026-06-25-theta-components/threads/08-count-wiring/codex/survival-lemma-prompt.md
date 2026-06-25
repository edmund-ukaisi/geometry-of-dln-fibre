<task>
Lean 4 + Mathlib v4.29 (pin). Commutative algebra. I am building a REUSABLE lemma:
"localization at a single element survives the top-dimensional-minimal-prime count."

DEFINITION (already in the codebase):
  TopDimMinPrimes (A) := {p ∈ minimalPrimes A | ringKrullDim (A ⧸ p) = ringKrullDim A}
i.e. the minimal primes whose quotient carries the full Krull dimension.

GOAL LEMMA: Let A be a CommRing, f : A, and S = Localization.Away f A
(M = Submonoid.powers f, IsLocalization M S, S a CommRing A-algebra). Want:
  comap (algebraMap A S) is a Set.BijOn from TopDimMinPrimes S onto TopDimMinPrimes A,
hence (TopDimMinPrimes S).ncard = (TopDimMinPrimes A).ncard.

FACTS I HAVE / KNOW:
1. Minimal-prime correspondence (Mathlib): IsLocalization.minimalPrimes_map M S (⊥) gives
   ((⊥).map (algebraMap A S)).minimalPrimes = comap (algebraMap A S) ⁻¹' (⊥).minimalPrimes.
   With Ideal.map_bot and minimalPrimes = Ideal.minimalPrimes ⊥, this reads:
   minimalPrimes S = comap (algebraMap A S) ⁻¹' minimalPrimes A.
   Standard: comap (algebraMap A S) is an order-iso of Spec S onto {p ∈ Spec A | p ∩ M = ∅}
   = {p ∈ Spec A | f ∉ p} (for M = powers f). So comap restricts to a bijection
   minimalPrimes S ≃ {p ∈ minimalPrimes A | f ∉ p}, inverse p ↦ map (algebraMap A S) p.
2. Ambient no-drop: I can supply ringKrullDim S = ringKrullDim A as a hypothesis (call it hdim),
   or prove it from an avoidance witness.
3. For the per-prime top-dimensionality, I need, for each surviving prime P of S:
   ringKrullDim (S ⧸ P) = ringKrullDim (A ⧸ comap P).
   The standard reason: S ⧸ P is a localization of the domain A ⧸ comap P at the image of M
   (away-localization of the quotient). I have a per-domain no-drop available specialized to
   f.g. k-domains: ringKrullDim_localizationAway_eq_of_fg_domain (D fg k-domain, g≠0 ⟹
   dim (Localization.Away g D) = dim D), and ringKrullDim_localizationAway_eq_of_avoids_top_prime.
4. KEY HAZARD (reviewer + Codex flagged earlier): the per-prime / componentwise no-drop
   dim((A⧸comap P)[1/f̄]) = dim(A⧸comap P) does NOT follow from the ambient no-drop + avoidance
   (a domain localized at a non-unit can drop dimension, e.g. DVR at a uniformizer). It must be
   invoked PER surviving prime, and holds in our application because A⧸comap P is an f.g. k-domain
   with f̄ ≠ 0.

DESIGN QUESTION. I want the cleanest, most reusable ABSTRACT statement that:
 (a) does NOT bake in "f.g. k-domain" (so it is reusable), but
 (b) lets the two call sites (W1: A = O(Σ^r) the source ring with f = detΔ; W2:
     A = O(F)[SchurVar] with f = detSchurS) discharge their obligations from the f.g.-domain
     no-drop with minimal friction.

Specifically: should the abstract lemma take as a hypothesis
  (H_perprime) : ∀ P ∈ TopDimMinPrimes S, ringKrullDim (S ⧸ P) = ringKrullDim (A ⧸ comap P)
or rather, since the bijection needs to go the OTHER way (from A to S to establish surjectivity
onto TopDimMinPrimes A), is it cleaner to phrase the per-prime obligation over A:
  (H_perprime') : ∀ p ∈ TopDimMinPrimes A, ringKrullDim (Localization.Away (the image of f in A⧸p))
                    = ringKrullDim (A ⧸ p)     [the per-component no-drop, A-side]
combined with havoid : ∀ p ∈ TopDimMinPrimes A, f ∉ p, and the ambient hdim?

I am unsure whether to drive the bijection from the S side (comap, needs per-prime dim on S quotients)
or assemble it from the A side (map, needs per-prime dim on A quotients). Which orientation makes the
Set.BijOn cleanest given Mathlib's IsLocalization.minimalPrimes_map gives the S-minimal-primes as a
preimage under comap? And how do I get ringKrullDim (S ⧸ P) = ringKrullDim (A ⧸ comap P) into a usable
form — is there a Mathlib lemma that S ⧸ (P) ≅ localization of A⧸comap P, or do I build the away-map
quotient iso by hand (Localization.awayMap of Ideal.Quotient.mk (comap P), with surjectivity +
the right kernel) the way ringKrullDim_localizationAway_eq_of_avoids_top_prime already does?
</task>

<output_contract>
1. RECOMMENDED ABSTRACT STATEMENT (Lean signature sketch): the exact hypotheses to take, in the
   orientation that minimizes proof friction. Be explicit about whether per-prime dim is a hypothesis
   or derived, and on which side (A or S).
2. THE BIJECTION PROOF SKELETON: how comap (or map) gives Set.BijOn TopDimMinPrimes S → TopDimMinPrimes A,
   citing the Mathlib lemmas for (i) minimalPrimes correspondence, (ii) the inverse map, (iii) the
   dim-equality transport. Flag any Mathlib lemma name you are NOT sure exists at v4.29.
3. THE PER-PRIME DIM EQUALITY: cleanest route to ringKrullDim (S ⧸ P) = ringKrullDim (A ⧸ comap P).
   Either name a Mathlib lemma (S⧸P ≅ away-localization of A⧸comap P) or give the by-hand awayMap
   construction (surjectivity + ringKrullDim_le_of_surjective both ways, or an actual ring iso).
4. PITFALLS specific to v4.29 (instance issues with Localization.Away over a quotient, IsLocalization
   of the quotient map, comap vs map direction on minimalPrimes).
</output_contract>

<grounding_rules>
You may reason from standard commutative-algebra facts. For any Mathlib lemma you cite, mark it
[CONFIDENT exists] or [UNSURE - verify] explicitly; v4.29 names may differ. Distinguish
"this is the clean math" from "this exact Lean lemma exists".
</grounding_rules>
