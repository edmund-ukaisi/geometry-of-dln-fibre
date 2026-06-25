**(A)**

Verdict: **yes**, the chart `AlgEquiv` is necessary.

The landed sweep and constant-fibre facts do not give `+δ`. They only prove
`Σ^r = ⋃ P, P • F` and `varietyDim (P • F) = varietyDim F`; an infinite union of equal-dimensional sets can have larger dimension.

The missing theorem would be a finite-type morphism result:
`dim total = dim base + dim fibre`
for `mult : Σ^r → Mat^{rk=r}` with constant fibre dimension. That is mathematically valid only with real AG hypotheses, and in Lean it would require generic-fibre/Chevalley/flatness-style infrastructure. Treat this as **[MATHLIB-ABSENT-RISK]**. Global `mult` over `rank ≤ r` is not usable because fibres jump at lower ranks.

Cheapest Lean route: prove the rank-chart trivialization and get dimension from the chart coordinate ring.

**(B)**

Verdict: **yes**, use **(i)**: explicit `aeval` substitutions with inverse substitutions.

Use the reduced fibre coordinate ring, not the generator quotient:
```lean
F₀ := MvPolynomial (RepCoord d) k ⧸
        vanishingIdeal k (canonicalCoord d '' fibre d E)

Rprod := Localization.Away
  (MvPolynomial.map (algebraMap k F₀) (detSchurS (d 0) (d (Fin.last N)) r))
-- morally O(F)[SchurVar]_{det}
```

Use `Rchart := Sred d r hp hq` or an equivalent vanishing-ideal principal-open chart. On the pivot chart, `rank ≤ r` plus `det Δ ≠ 0` is exact rank.

Build two maps by `aeval`:

`Θ^* : Rprod →ₐ[k] Rchart` from  
`A ↦ (Schur coordinates of mult A, φ(A) = s(mult A)⁻¹ • A)`.

`Λ^* : Rchart →ₐ[k] Rprod` from  
`(schur, F) ↦ s(schur) • F`.

Then prove inverse by generator extensionality.

Use:
- `MvPolynomial.algHom_ext` **[believe-present]**
- `AlgEquiv.ofAlgHom` **[believe-present]**
- `IsLocalization.Away.mapₐ`, `IsLocalization.Away.lift`, `IsLocalization.Away.algebraMap_isUnit` **[believe-present]**
- `Ideal.quotientMapₐ`, `Ideal.quotientEquivAlg` **[believe-present]**
- `IsLocalization.algEquivOfAlgEquiv`, `MvPolynomial.isLocalization` **[believe-present]**
- LANDED `basePresentationEquiv`, `Sred`, `IadDeep_isRadical`, Schur chart criterion.

Do not use the fixed-`P` base-change `AlgEquiv` as the main construction. The gauge here is variable, `P = s(M)`, so reusing the landed constant-gauge transport means rebuilding it over `SchurLoc` anyway.

Critical subtlety: the set-level section/retraction does **not** itself give the coordinate-ring `AlgEquiv`. You must prove regularity and descent through `vanishingIdeal`. If you descend through `fibreGenIdeal`, you hit the reducedness wall again.

**(C)**

Verdict: **cheaper-route-exists**.

One chart suffices if you prove a no-drop/density lemma for the top-left pivot:
```lean
vanishingIdeal k (canonicalCoord d '' (Σ^r ∩ D ΔPdeep))
  = vanishingIdeal k (canonicalCoord d '' Σ^r)
```
This full density condition is stronger than needed. For dimension only, it suffices that `ΔPdeep` avoids every top-dimensional minimal prime of `O(Σ^r)`. If `Σ^r` is irreducible, `ΔPdeep ∉ vanishingIdeal Σ^r` is enough. If reducible, nonempty is not enough; the chart must meet every top-dimensional component.

In this setting, prove density directly by endpoint-GL orbit density: for any `A ∈ Σ^r`, the function
`P ↦ det Δ(mult(P • A))` is nonzero because some endpoint base change puts `mult A` in the chosen pivot chart. If `f` vanishes on the chart, then `P ↦ f(P • A)` vanishes on a nonempty principal open in the group; use the `groupRing_isDomain` / localization argument from `vanishingIdeal_range_orbitMap_eq_ker` to get vanishing at `P = 1`.

Use:
- LANDED `exists_baseChange_of_rank_eq`, `rank_endpoint_conj`, `mult_smul`
- LANDED orbit-ring pattern `groupRing_isDomain`, `vanishingIdeal_range_orbitMap_eq_ker`
- `IsLocalization.Away.surj`, `MvPolynomial.funext` **[believe-present]**

You still need a principal-open no-drop lemma
`ringKrullDim O(Σ^r) = ringKrullDim O(Σ^r)[1/Δ]`; general Mathlib support is **[MATHLIB-ABSENT-RISK]**, but the GL-density proof is the clean custom route. Finite pivot-cover union-max is avoidable if this is built.

Cheapest overall route to `hSweep`: **[MUST-BUILD]** one-chart density/no-drop for `ΔPdeep`; **[MUST-BUILD]** explicit Schur chart `AlgEquiv` `Rchart ≃ₐ[k] O(F)[SchurVar]_{det}` using `vanishingIdeal`, not `fibreGenIdeal`; **[MUST-BUILD]** target localization no-drop plus `ringKrullDim Rprod = varietyDim F + δ`, using `MvPolynomial.ringKrullDim_of_isNoetherianRing` **[believe-present]** and `card_SchurVar` **[LANDED]**; avoid the global fibration theorem and finite union-max, both **[MATHLIB-ABSENT-RISK]**.