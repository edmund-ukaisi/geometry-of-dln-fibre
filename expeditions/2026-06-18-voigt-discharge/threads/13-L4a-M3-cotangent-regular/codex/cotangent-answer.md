**Q1.** The reduction to `finrank κ (m_R/m_R²) ≤ n` is sound. No injectivity is needed by the regularity criterion itself.

But your proposed conormal-surjectivity proof is wrong-direction: a surjection
`m_R/m_R² → κ ⊗[R] Ω[R⁄k]`
gives `finrank (κ ⊗ Ω) ≤ finrank (m_R/m_R²)`, not the desired upper bound. To get `finrank (m_R/m_R²) ≤ n`, you need an injection/split injection into `κ ⊗[R] Ω[R⁄k]`.

Load-bearing:
`[CONFIRMED-recalled] IsRegularLocalRing.of_spanFinrank_maximalIdeal_le`
`[CONFIRMED-recalled] IsLocalRing.spanFinrank_maximalIdeal_eq_finrank_cotangentSpace`
`[CONFIRMED-recalled] ringKrullDim_le_spanFinrank_maximalIdeal`

**Q2.** The scalar issue is real but bounded. Raw
`KaehlerDifferential.kerCotangentToTensor k R κ`
is `R`-linear. Since `R → κ` is surjective, use
`[CONFIRMED-recalled] LinearMap.extendScalarsOfSurjective`
to view it as `κ`-linear, after rewriting
`RingHom.ker (algebraMap R κ) = maximalIdeal R` via:
`[CONFIRMED-recalled] IsLocalRing.ResidueField.algebraMap_eq`
`[CONFIRMED-recalled] IsLocalRing.ker_residue`
`[CONFIRMED-recalled] IsLocalRing.residue_surjective`

Cleanest route: use the extension wrapper:
`[CONFIRMED-recalled] Algebra.Extension.formallySmooth_iff_split_injection`
roughly:
```lean
(P : Algebra.Extension k κ) [Algebra.FormallySmooth k P.Ring] :
  Algebra.FormallySmooth k κ ↔ ∃ l, l ∘ₗ P.cotangentComplex = LinearMap.id
```
This gives a `κ`-linear split injection
`P.cotangentComplex : P.Cotangent →ₗ[κ] κ ⊗[R] Ω[R⁄k]`.
Then use:
`[CONFIRMED-recalled] LinearMap.finrank_le_finrank_of_injective`.

**Q3.** `finrank κ (κ ⊗[R] Ω[R⁄k]) = n` should assemble, but this is the bookkeeping-heavy part.

Skeleton:
`S := Localization.Away f`; M2 gives `IsStandardSmoothOfRelativeDimension n k S`.
Then:
`[CONFIRMED-recalled] Algebra.IsStandardSmooth.free_kaehlerDifferential`
`[CONFIRMED-recalled] Algebra.IsStandardSmoothOfRelativeDimension.rank_kaehlerDifferential`
give `Ω[S⁄k]` free of rank `n`.

Localize from `S` to `R = Localization.AtPrime m` using:
`[CONFIRMED-recalled] IsLocalizedModule.iso _ (KaehlerDifferential.map k k S R)`
`[CONFIRMED-recalled] IsLocalizedModule.extendScalarsOfIsLocalization`
as used in `RingTheory/Smooth/Locus.lean`.

Then base-change a finite basis:
`[CONFIRMED-recalled] Module.Basis.baseChange`
`[CONFIRMED-recalled] Module.finrank_eq_card_basis`
or directly:
`[CONFIRMED-recalled] Module.finrank_baseChange`
when its typeclass hypotheses line up.

The likely local-ring equivalence/bookkeeping lemma is:
`[GUESS] Localization/LocalizationLocalization API: Localization.AtPrime m` as localization of `Localization.Away f` at the mapped prime. Content: since `f ∉ m`, `A_m ≃ (A_f)_{mA_f}`.

**Q4.** You do not need `κ ≅ k` for the proof. You need `κ` formally smooth over `k` to get the conormal split injection.

Use:
`[CONFIRMED-recalled] IsAlgClosed.perfectField`
`[CONFIRMED-recalled] Algebra.FormallySmooth.of_perfectField`
roughly:
```lean
[Field K] [Field L] [Algebra K L] [PerfectField K]
[Algebra.EssFiniteType K L] : Algebra.FormallySmooth K L
```
and:
`[CONFIRMED-recalled] Ideal.ResidueField` is definitionally `ResidueField (Localization.AtPrime I)`
`[CONFIRMED-recalled] Algebra.EssFiniteType.comp`
`[CONFIRMED-recalled] instance (p : Ideal R) [p.IsPrime] :
  Algebra.EssFiniteType R p.ResidueField`

If you specifically want `Ω[κ⁄k]=0`, then prove `k → κ` surjective and use:
`[CONFIRMED-recalled] KaehlerDifferential.subsingleton_of_surjective`.
For surjectivity/bijectivity over alg closed:
`[CONFIRMED-recalled] IsAlgClosed.algebraMap_bijective_of_isIntegral`
but the one-shot finite-type maximal-residue lemma is `[GUESS]`; likely you prove it via Zariski/Nullstellensatz API.

**Q5.** Present API is enough; no conormal/left-exactness kill. The proposed surjectivity-only route is mathematically dead, but the split-injection route is in Mathlib.

Estimated size: ~250-400 LoC if you package the chart-to-local Ω-rank and residue formal-smoothness lemmas; ~150-250 LoC if you already have localization bookkeeping from M2 reusable.

Main risks are not missing theory, just coercions:
`CotangentSpace R` versus `(RingHom.ker (algebraMap R κ)).Cotangent`;
`R`-linear versus `κ`-linear conormal map;
`Away f` to `AtPrime m` localization equivalence.

**Q6.** I found no direct v4.29 producer `smooth local ⇒ regular local`, nor a direct lemma “Ω free rank n + residue field condition ⇒ regular”. Shortest route is:

M2 dimension `dim R = n`;
formal smoothness of `R` and `κ` gives split conormal injection;
Kähler localization gives `finrank κ (κ ⊗[R] Ω[R⁄k]) = n`;
regularity follows from `IsRegularLocalRing.of_spanFinrank_maximalIdeal_le`.
The companion `finrank_cotangentSpace = n` follows from `IsRegularLocalRing.iff_finrank_cotangentSpace` plus M2, or by combining both inequalities.

VERDICT: BOUNDED (~250-400 LoC, route = M2 dimension + formally-smooth split conormal injection + Kähler localization/base-change + regularity criterion).