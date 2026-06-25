**CHOSEN SUBSTRATE:** **(iv) pivot-chart trivialization + `MvPolynomial.ringKrullDim_of_isNoetherianRing`**; none of the four is already a complete v4.29 theorem, but (iv) is the cleanest because the only dimension-addition step is Mathlib-present and works for reducible rings.

**Adjudication**
- **(i) Order/Krull chains:** primitives present: `Order.krullDim`, `ringKrullDim`, `IsLocalization.orderIsoOfPrime`, `Algebra.HasGoingDown.of_flat`, `Algebra.HasGoingDown.iff_generalizingMap_primeSpectrumComap`. Missing: a relative chain theorem giving `dim X = dim Y + dim fibre`. Homogeneity of closed fibres does not itself give going-down or flatness.
- **(ii) Trdeg tower:** `trdeg_add_eq` is present, but it needs a domain top ring. Component-wise use is possible only after serious component/dominance/generic-fibre bookkeeping. Homogeneity of closed fibres does **not** identify relative trdeg with fibre dimension without either generic-fibre machinery or an explicit local trivialization.
- **(iii) Spec/localization/going-down:** useful lemmas are present: `IsLocalization.orderIsoOfPrime`, `IsLocalization.height_map_of_disjoint`, `IsLocalization.AtPrime.ringKrullDim_eq_height`, `Algebra.HasGoingDown.of_flat`. Missing: packaged `ringKrullDim_localization` and a global flatness/relative-dimension theorem. Cleaner only after reducing to (iv).
- **(iv) Chart polynomial-extension route:** Mathlib substrate present: `MvPolynomial.ringKrullDim_of_isNoetherianRing`. Must build the pivot chart trivialization and a tailored localization-no-drop lemma. This is the route that actually exploits constant-isomorphic fibres.

**Proof Strategy**
1. **LANDED:** Use `productRankLocus_eq_iUnion_smul_fibre`, `mult_smul`, `image_smul_fibre`, and `codimRepCanonical_fibre_eq_of_rank_eq` as the homogeneity input.
   This is where the fibre theorem becomes special: over a rank-`r` pivot chart, we explicitly choose endpoint gauges sending the base matrix to the normal form `E`.

2. **MUST-BUILD:** For each nonzero `r × r` minor chart on `Mat^{=r}`, construct the regular Schur-complement chart:
   `Mat^{=r}_Δ ≃ Spec k[δ variables][detΔ⁻¹]`.
   The coordinate count is `δ = r(p+q-r)`.

3. **MUST-BUILD:** Build the chart trivialization
   `Σ^r_Δ ≃ Mat^{=r}_Δ × F`
   by
   `A ↦ (mult A, P(mult A) • A)`,
   where `P(mult A)` is the regular endpoint gauge on the chart. The inverse is `(M, B) ↦ P(M)⁻¹ • B`.
   This uses `mult_smul` and `image_smul_fibre`, not Chevalley or upper semicontinuity.

4. **MUST-BUILD + LANDED:** Convert that set-level isomorphism into a coordinate-ring `AlgEquiv`, then use `varietyDim_eq_of_coordRingAlgEquiv` and radical-insensitivity from `VarietyDimRadical`.

5. **Mathlib-present:** Compute the polynomial part:
   `ringKrullDim (MvPolynomial BaseVars O(F)) = ringKrullDim O(F) + δ`
   by `MvPolynomial.ringKrullDim_of_isNoetherianRing`.
   This is the main reason (iv) wins: `O(F)` may have zero divisors, but this lemma only needs Noetherianity, not domain hypotheses.

6. **MUST-BUILD:** Prove localization by `detΔ` does not drop top dimension for `O(F)[BaseVars]`.
   Use `IsLocalization.orderIsoOfPrime` for `≤`; for `≥`, pass to a top minimal prime of `O(F)`, then use the domain closed-point argument with `IsLocalization.height_map_of_disjoint`, `IsLocalization.AtPrime.ringKrullDim_eq_height`, and the engine’s affine-domain equidimensionality such as `height_eq_ringKrullDim_of_isMaximal`.

7. **MUST-BUILD:** Prove finite chart gluing:
   `varietyDim (⋃ finite charts) = max chart dimensions`.
   Then every chart has dimension `δ + varietyDim F`, and the finite pivot charts cover `Σ^r`.

**Reducibility Handling**
Do **not** apply trdeg to `O(Σ^r)` or `O(F)`. The chart ring is a localized polynomial ring over the possibly reducible `O(F)`, and `MvPolynomial.ringKrullDim_of_isNoetherianRing` handles that directly. Reducibility appears only as a max over top minimal primes of `O(F)` in the localization-no-drop lemma; locally, top pieces contribute `δ + dim F_i`, hence the max is `δ + max_i dim F_i`.

**Localization Top-Dim Lemma**
It sits after the chart `AlgEquiv`, before the chart dimension conclusion. Cheapest v4.29 route: prove a tailored lemma for `Localization.Away detΔ (MvPolynomial BaseVars A)` with `A = O(F)`, not a general localization theorem. Use prime correspondence for the upper bound and a top component plus a maximal ideal avoiding `detΔ` for the lower bound.

**Biggest Risk**
The riskiest step is the set-level chart trivialization to coordinate-ring `AlgEquiv`, including the saturation/localized-coordinate bridge for the principal open. If that gets messy, it can recreate much of the missing localization/product infrastructure.

**Sublemma Count**
About **7** serious sublemmas: Schur chart, endpoint gauge regularity, total chart trivialization, coordinate-ring transport, localized polynomial dimension no-drop, finite-union dimension max, and chart cover/nonemptiness bookkeeping.