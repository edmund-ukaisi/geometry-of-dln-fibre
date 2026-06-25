<task>
Lean 4 / Mathlib v4.29 formalisation. I am computing varietyDim of an algebraic locus.

DEFINITIONS:
- varietyDim Z := (ringKrullDim (MvPolynomial σ k ⧸ vanishingIdeal k Z)).unbotD 0, i.e. the Krull
  dimension of the coordinate ring of the ZARISKI CLOSURE of Z (vanishingIdeal is closure-based, radical).
- Σ^r ⊆ (RepCoord d → k) is the exact-rank locus (reducible, θ top-dim components).
- U_Δ = {detΔ ≠ 0} is a principal-open chart; chart := Σ^r ∩ U_Δ.
- F = a fibre; O(F) = MvPolynomial σ k ⧸ vanishingIdeal F is the (reducible, Noetherian) fibre coord ring.

LANDED:
- A regular retraction φ : chart → F and section, giving a SET bijection chart ≅ Mat^{=r}_Δ × F.
- varietyDim_eq_of_polyExtensionAlgEquiv: if O(W) [the closure coord ring of W] ≃ₐ[k] MvPolynomial ι O(F)
  (UN-localized free poly ring), then varietyDim W = varietyDim F + card ι.  [domain-free]
- card SchurVar = δ.
- The geometric fact (rung-3 cert, sympy-verified): the chart's RING OF REGULAR FUNCTIONS is
  O(F)[SchurVar]_{detΔ} — a LOCALIZED free poly ring (localized at detΔ).

THE MISMATCH I need to resolve:
varietyDim(chart) reads the coord ring of the CLOSURE of chart, which (chart dense in Σ^r) is O(Σ^r) —
NOT the localized regular-function ring O(F)[SchurVar]_{detΔ}. So my un-localized rung-3 lemma does NOT
directly apply to the chart: O(Σ^r) is not literally MvPolynomial ι O(F).

QUESTION: what is the cleanest Lean route, given these landed pieces, to
  varietyDim Σ^r = δ + varietyDim F  (= varietyDim(chart) by density)?
Specifically, which of these is cheapest and correct:
(1) Build a LOCALIZED rung-3: ringKrullDim(Localization.Away f (MvPolynomial ι A)) = ringKrullDim A + card ι
    for Noetherian A, when f avoids the top minimal primes — i.e. fold the no-drop into a localized
    poly-extension Krull-dim lemma. Then need: O(Σ^r) [closure ring] vs O(F)[SchurVar]_{detΔ}
    [regular-function ring] — are these the SAME ring up to the AlgEquiv, or is there still a gap because
    closure-coord-ring ≠ ring-of-regular-functions-on-the-open?
(2) Avoid the localized ring entirely: find a DIRECT AlgEquiv O(closure(chart)) = O(Σ^r) ≃ₐ
    MvPolynomial ι O(F)? (This seems FALSE: Σ^r is globally NOT a product, only on the chart.)
(3) Some other structural route.

CRITICAL sub-question: for a principal-open D(f) ⊆ X with X irreducible (or: f avoids top components),
is the relationship  ringKrullDim O(X) = ringKrullDim (O(X)[1/f])  [= ringKrullDim O(D(f)) as a SCHEME,
the localized ring]  the right bridge? I.e. is "varietyDim(chart) computed via the closure" EQUAL to
"ringKrullDim of the localized regular-function ring O(X)[1/f]"? In scheme terms: dim of an open dense
subscheme = dim of the whole. Confirm whether varietyDim(Σ^r∩U_Δ) [closure-based] equals
ringKrullDim(O(Σ^r)[1/detΔ]) [localized], and under what hypothesis.

Be concrete about Mathlib v4.29 lemma names where they exist; mark [believe-present]/[must-verify]/
[ABSENT]. Terse.
</task>

<output_contract>
1. The mismatch verdict: is the closure-coord-ring O(Σ^r) related to the localized regular-function ring
   O(F)[SchurVar]_{detΔ}, and how (the precise ring identity / no-drop). One paragraph.
2. The cheapest correct route (pick 1/2/3), as an ordered list of sub-lemmas, each LANDED/MUST-BUILD/ABSENT.
3. The single sharpest risk + the Mathlib lemma to verify first.
</output_contract>

<grounding_rules>
Distinguish a mathematical claim from a Lean-availability claim. Flag explicitly if the
closure-coord-ring vs regular-function-ring distinction introduces a gap I have not accounted for.
</grounding_rules>
