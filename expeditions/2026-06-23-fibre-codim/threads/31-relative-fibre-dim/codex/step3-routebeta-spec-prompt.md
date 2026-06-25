<task>
Lean 4 + Mathlib v4.29 formalisation STRATEGY/STRUCTURE de-risk (this is the single biggest-risk
rung of a larger proof; I want the cleanest realization pinned BEFORE a multi-module grind).

CONTEXT. I am proving the "homogeneous sweep" dimension identity for deep-linear-network fibres:
  hSweep : varietyDim Σ^r = (δ : ℕ∞) + varietyDim F
where (over an alg-closed char-0 field k):
 - Σ^r = productRankLocus d r ⊆ (τ → k) is the EXACT-rank-r product locus (a possibly REDUCIBLE
   affine variety; θ top-dimensional components),
 - F = fibre d E is a fixed fibre (also possibly reducible),
 - δ = r(d_N + d_0 − r),
 - varietyDim Z := (ringKrullDim (MvPolynomial τ k ⧸ vanishingIdeal Z)).unbotD 0  -- CLOSURE-based.

I HAVE LANDED (sorry-free), reusable:
 (A) varietyDim_eq_of_polyExtensionAlgEquiv : given a k-AlgEquiv
       e : (MvPolynomial τ k ⧸ vanishingIdeal W) ≃ₐ[k] MvPolynomial ι (MvPolynomial σ k ⧸ vanishingIdeal F)
     and Finite ι, Finite σ, vanishingIdeal F ≠ ⊤, concludes varietyDim W = varietyDim F + card ι.
     [Domain-free, via MvPolynomial.ringKrullDim_of_isNoetherianRing.] NOTE: the LHS ring is the
     UN-LOCALIZED closure coordinate ring O(W); the RHS is a FREE (un-localized) poly ring over O(F).
 (B) A SHARED no-drop: for a f.g. k-algebra R (Noetherian, reducible OK) and g : R, if g avoids a
     TOP-dimensional minimal prime p₀ of R (ringKrullDim (R⧸p₀) = ringKrullDim R ∧ g ∉ p₀), then
     ringKrullDim (Localization.Away g R) = ringKrullDim R. (Built on dim=trdeg for affine domains +
     the surjection R[1/g] ↠ (R⧸p₀)[1/ḡ].)
 (C) A set-level chart trivialization bijection (over the principal open U_Δ = {detΔ ≠ 0}, detΔ the
     top-left r×r minor of the product mult(A)): Φ(A) = (mult A, chartGauge(mult A)•A), with the
     retraction landing in F, and Ψ(M,B) = chartGauge(M)⁻¹•B inverse. Round-trips proved.
     The gauge entries involve Δ⁻¹, so the maps are regular only AFTER localizing at detΔ.
 (D) A pen-and-paper certificate: detΔ AVOIDS every top-dimensional minimal prime of O(Σ^r)
     (one-chart density), and the δ Schur coordinates (Δ, B12, B21 entries) are FREE polynomial
     generators over O(F) on the chart, with B22 Schur-determined: O(Σ^r ∩ U_Δ) ≅ O(F)[δ vars]_{detΔ}.

THE TENSION I NEED RESOLVED. Brick (A) consumes the UN-LOCALIZED O(W). The chart trivialization (C)+(D)
naturally produces a LOCALIZED iso O(Σ^r ∩ U_Δ)_{detΔ} ≅ O(F)[δ vars]_{detΔ}. These differ by the
detΔ-localization. So I CANNOT feed (A) directly with W = Σ^r (or W = chart) unless I bridge the
localization.

QUESTION (the structure decision, give a concrete Lean-shaped plan):
Which of these is the cleanest at v4.29, and what is the exact intermediate-lemma chain?

 ROUTE-1 ("localize both sides, then no-drop twice"):
   - Build the LOCALIZED AlgEquiv  Localization.Away (mk detΔ) O(Σ^r) ≃ₐ[k]
     Localization.Away g' (MvPolynomial SchurVar O(F))  (g' = detSchurS image).
   - ringKrullDim both sides; LHS = dim O(Σ^r) by no-drop (B) (detΔ avoids a top min prime, cert D);
     RHS = dim (MvPolynomial SchurVar O(F)) by no-drop (B) (g' a nonzero k-coeff poly, avoids every
     component) = dim O(F) + δ by ringKrullDim_of_isNoetherianRing.
   - Never uses brick (A); uses (B) twice + the LOCALIZED AlgEquiv. The localized AlgEquiv is built
     from the set-level Ψ comorphism (aeval) descended through vanishingIdeal + IsLocalization.algEquivOfAlgEquiv.

 ROUTE-2 ("un-localized poly-ext directly"):
   - Somehow present O(Σ^r) (un-localized closure ring) directly as a free poly extension to feed (A).
   - I suspect this is WRONG: O(Σ^r) is NOT a free poly ring over O(F) (only its detΔ-localization is),
     so (A) cannot apply to W = Σ^r. Confirm/deny.

 ROUTE-3 (a localized variant of brick A): build a localized analogue of
   varietyDim_eq_of_polyExtensionAlgEquiv that consumes a localized AlgEquiv and folds in no-drop (B)
   on both sides — i.e. package ROUTE-1 as one reusable lemma.

For the chosen route, give the EXACT Lean intermediate lemma statements and the v4.29 API names for:
 - descending a k-algebra map MvPolynomial τ k → (target) through vanishingIdeal to a quotient map
   (Ideal.quotientMap / Ideal.quotientMapₐ / Ideal.Quotient.liftₐ — which, and the kernel-containment
   obligation shape);
 - building the comorphism of the regular map Ψ as an `aeval` substitution (MvPolynomial.aeval) and
   proving it descends (the vanishingIdeal image-pushforward — I have FibreNormalForm.vanishingIdeal_image_smul
   for FIXED k-gauges; the chart gauge is detΔ-VARIABLE, so flag if that lemma is reusable or if I need
   IsLocalization-level comorphism);
 - IsLocalization.algEquivOfAlgEquiv exact signature + the submonoid-correspondence obligation;
 - the localized-AlgEquiv → ringKrullDim equality (ringKrullDim_eq_of_ringEquiv on the localized rings).

Tell me the SINGLE cleanest route and the ~module count, and the ONE place most likely to re-incur a
"generator-ideal strict-inclusion" wall (the route MUST stay vanishingIdeal-side / radical, never the
fibreGenIdeal/IadDeep generator route).
</task>

<output_contract>
1. VERDICT: which route (1/2/3), one line.
2. Confirm or deny ROUTE-2's wrongness (is O(Σ^r) un-localized a free poly ext? yes/no + why).
3. The chosen route's intermediate-lemma CHAIN: 3-6 numbered Lean-shaped statements (with the v4.29
   API name each step uses). Be name-precise; mark any name "uncertain at v4.29 — grep <term>".
4. The single most-likely wall + the mitigation.
5. Module-count estimate for the chosen route.
Terse. This is structure validation, not exposition.
</output_contract>

<grounding_rules>
Reason about Mathlib v4.29.0. If unsure a name exists at that pin, say "uncertain — grep <term>"
rather than assert. Distinguish confident names from inferred ones. Do not invent lemma names.
</grounding_rules>
