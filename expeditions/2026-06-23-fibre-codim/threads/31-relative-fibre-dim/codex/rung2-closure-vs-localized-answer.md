**Mismatch Verdict**

`O(Σ^r)` and the chart regular-function ring are **not the same ring**. The correct identity is
`Γ(D(detΔ), O_{Σ^r}) = O(Σ^r)[1/detΔ]`, and your rung-3 ring is an isomorphic localized ring
`O(F)[SchurVar][1/g]`. Thus `varietyDim(chart)` uses `O(closure chart) = O(Σ^r)` if the chart is dense, while the regular chart ring is `O(Σ^r)[1/detΔ]`. The bridge is **dimension no-drop**, not ring equality:
`ringKrullDim O(Σ^r) = ringKrullDim O(Σ^r)[1/detΔ]`.
For affine finite-type `k`-algebras this holds if `detΔ` meets a top-dimensional component; density needs avoidance of all minimal components, but dimension equality only needs a top one. For arbitrary irreducible Noetherian schemes, dense open need not preserve dimension.

**Cheapest Route**

Pick **(3): localized bridge with two no-drop lemmas**. Route (1) is only half of this; route (2) is false globally.

1. `vanishingIdeal chart = vanishingIdeal Σ^r`, or directly `varietyDim chart = varietyDim Σ^r`.
   Status: **LANDED if your density theorem is formal; otherwise MUST-BUILD**.

2. Identify the principal-open regular ring:
   `O(Σ^r)[1/detΔ] := Localization.Away (Ideal.Quotient.mk IΣ detΔ)`.
   If your concrete ring is `(Localization.Away detΔ) ⧸ IΣ.map`, bridge it by localization-through-quotient.
   Status: **MUST-BUILD** unless already in `Sred`.
   Mathlib: `IsLocalization.of_surjective` [believe-present], `IsLocalization.algEquiv` [believe-present], `PrimeSpectrum.localization_away_comap_range` [believe-present].

3. State the rung-3 equivalence with the correct left side:
   `Localization.Away detΣ O(Σ^r) ≃ₐ[k] Localization.Away g (MvPolynomial SchurVar O(F))`.
   Status: **MUST-BUILD / verify exact statement**. A bare “regular functions are ...” certificate is not enough unless its left side is literally this localization.

4. Prove no-drop on the source:
   `ringKrullDim O(Σ^r) = ringKrullDim (Localization.Away detΣ O(Σ^r))`.
   Status: **MUST-BUILD; canned lemma ABSENT**.
   Ingredients: `IsLocalization.height_comap` [believe-present], `IsLocalization.height_map_of_disjoint` [believe-present], `IsLocalization.isMaximal_of_isMaximal_disjoint` [believe-present].

5. Prove localized polynomial no-drop:
   `ringKrullDim (Localization.Away g (MvPolynomial ι O(F))) =
    ringKrullDim (MvPolynomial ι O(F))`.
   Status: **MUST-BUILD; canned localized rung-3 ABSENT**.

6. Finish with the landed polynomial dimension:
   `ringKrullDim (MvPolynomial ι O(F)) = ringKrullDim O(F) + Nat.card ι`.
   Status: **LANDED** via `MvPolynomial.ringKrullDim_of_isNoetherianRing` [believe-present].
   Then use `card SchurVar = δ` **LANDED**.

**Sharpest Risk**

The main risk is that the rung-3 equivalence is not tied to `Localization.Away (Ideal.Quotient.mk IΣ detΔ)`. Verify first: `IsLocalization.of_surjective` [believe-present], since it gives the quotient-localization bridge from `(Localization.Away detΔ) ⧸ IΣ.map` to `O(Σ^r)[1/detΔ]`.