**Route A:** NEEDS bridging lemma X.
Real lemmas:

`Algebra.H1Cotangent.exact_map_δ` [CONFIRMED-recalled]
`Algebra.H1Cotangent.exact_δ_mapBaseChange` [CONFIRMED-recalled]
`KaehlerDifferential.exact_kerCotangentToTensor_mapBaseChange` [CONFIRMED-recalled]

Missing bridge X: a packaged comparison saying, for `P : Algebra.Extension k κ` with `P.Ring = R` and `P.algebraMap_surjective = residue_surjective`, the JZ connecting map
`Algebra.H1Cotangent.δ k R κ`
corresponds under `P.equivH1CotangentOfFormallySmooth` to
`(KaehlerDifferential.kerCotangentToTensor k R κ).extendScalarsOfSurjective hsurj`.

Mathlib has the ingredients `Algebra.Extension.Cotangent` [CONFIRMED-recalled], `Algebra.Extension.cotangentComplex` [CONFIRMED-recalled], and low-level `Generators.H1Cotangent.δ_eq` [CONFIRMED-recalled], but I do not see that comparison lemma packaged. So JZ-as-stated does not cleanly land.

**Route B:** DEAD as stated with `Generators.self k κ`.
That presentation gives the cotangent complex of the self-presentation of `κ/k`, not the conormal map for `R ↠ κ`.

Nearby usable theorem: if you set `P := R`, not `Generators.self`, then
`Algebra.FormallySmooth.iff_split_injection` [CONFIRMED-recalled] applies directly:
`[Algebra.FormallySmooth k R]`, `hsurj : Function.Surjective (algebraMap R κ)`, and `[Algebra.FormallySmooth k κ]` give a retraction of
`KaehlerDifferential.kerCotangentToTensor k R κ`.

**Route C:** LANDS at v4.29. Cleanest.
Lemma chain:

`IsLocalRing.ResidueField.algebraMap_eq` [CONFIRMED-recalled]
`IsLocalRing.ker_residue` [CONFIRMED-recalled]
`IsLocalRing.CotangentSpace` is abbrev `(maximalIdeal R).Cotangent` [CONFIRMED-recalled]

so
`RingHom.ker (algebraMap R κ) = maximalIdeal R`.

Then:

`IsLocalRing.residue_surjective` [CONFIRMED-recalled] gives
`hsurj : Function.Surjective (algebraMap R κ)`.

Main injection:

`Algebra.FormallySmooth.kerCotangentToTensor_injective_iff` [CONFIRMED-recalled]
with `(R := k) (P := R) (A := κ)` gives
```lean
Function.Injective (KaehlerDifferential.kerCotangentToTensor k R κ)
  ↔ Subsingleton (Algebra.H1Cotangent k κ)
```

`Algebra.FormallySmooth.subsingleton_h1Cotangent` [CONFIRMED-recalled] supplies the RHS from `[Algebra.FormallySmooth k κ]`.

For `[Algebra.FormallySmooth k κ]`, usable sources are:
`Algebra.FormallyEtale.of_isSeparable` [CONFIRMED-recalled] plus the instance `FormallyEtale → FormallySmooth` [CONFIRMED-recalled], or
`Algebra.FormallySmooth.of_perfectField` [CONFIRMED-recalled] using `PerfectField k`; `IsAlgClosed k` gives `perfectField` [CONFIRMED-recalled].

**Route D:** DEAD.
I found no v4.29 direct theorem of the form smooth local `⇒ m/m² ≃ κ ⊗[R] Ω[R⁄k]`, nor a smooth `⇒` regular-parameters lemma giving this finrank bound without the conormal injection.

After Route C, the dimension step is standard:
`LinearMap.extendScalarsOfSurjective` [CONFIRMED-recalled] makes the map κ-linear, then
`LinearMap.finrank_le_finrank_of_injective` [CONFIRMED-recalled], and your target rank via `Module.finrank_baseChange` [CONFIRMED-recalled].

RECOMMENDED ROUTE = C. LoC for injection step: ~8 if `[Algebra.FormallySmooth k κ]` is already available, ~12-15 if deriving it from separability/ess-finite-type. BOUNDED.
