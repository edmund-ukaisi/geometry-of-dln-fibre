**Bottom Line**

Your obstacle is real. At Mathlib `v4.29.0`, `IsRegularLocalRing` gives regularity and cotangent/Krull dimension control, but there is no available theorem:

- `IsRegularLocalRing R → IsDomain R`
- `IsRegularLocalRing R → IsReduced R`
- `Algebra.Smooth k A → IsReduced A`
- `Algebra.IsStandardSmooth k A → IsReduced A`

The only regular-local-ring file is `Mathlib/RingTheory/RegularLocalRing/Defs.lean`, with the converse-style instance
`[IsLocalRing R] [IsDomain R] [IsPrincipalIdealRing R] : IsRegularLocalRing R`.

**Ranked Recommendation**

1. **Most reachable: height-direct, dodging reducedness.**

   Work toward:
   ```lean
   (fibreGenIdeal d E).height = C + δ
   ```
   not first toward:
   ```lean
   vanishingIdeal k (canonicalCoord d '' fibre d E) = fibreGenIdeal d E
   ```

   The key point is that height is radical-insensitive. I did not find a named theorem, but it is essentially a two-line lemma from:
   - `Ideal.radical_minimalPrimes`
   - `Ideal.height`

   Sketch:
   ```lean
   lemma Ideal.height_radical (I : Ideal R) :
       I.radical.height = I.height := by
     rw [Ideal.height, Ideal.height, Ideal.radical_minimalPrimes]
   ```

   Then the landed theorem
   ```lean
   vanishingIdeal_image_fibre_eq_radical
   ```
   gives codimension from `height (fibreGenIdeal d E)` without proving `fibreGenIdeal` radical.

   This dodges reducedness. It does **not** dodge the actual height computation.

2. **Second: Jacobian/submersive-presentation smoothness, but only as a local tool.**

   Mathlib does not have a high-level theorem “Jacobian has constant full rank on a chart implies smooth.” What it has is the lower-level standard-smooth API:

   - `Algebra.PreSubmersivePresentation.naive`
   - `Algebra.PreSubmersivePresentation.jacobiMatrix_naive`
   - `Algebra.SubmersivePresentation`
   - `Algebra.SubmersivePresentation.isStandardSmooth`
   - `Algebra.SubmersivePresentation.isStandardSmoothOfRelativeDimension`
   - `Algebra.IsStandardSmoothOfRelativeDimension.exists_etale_mvPolynomial`
   - `Algebra.IsSmoothAt.exists_notMem_isStandardSmooth`

   So a Jacobian criterion is reachable only by explicitly packaging a presentation and an invertible square minor. `CotangentJacobian` alone gives tangent = Jacobian-kernel at a rational point; it is not a smoothness criterion.

3. **Not recommended: generic smoothness for the fibre.**

   `Scheme.Hom.dense_smoothLocus_of_perfectField` needs a reduced source. You can apply it to the reduction `R ⧸ I.radical`, but then it proves smoothness of the reduced fibre, not of `R ⧸ I`. More importantly, unlike the orbit case, the fibre has no dense single orbit and no transport mechanism to move an existential smooth point to a computable normal form point. It will not give the explicit height `C + δ` without a separate component/dimension analysis.

4. **Not recommended: prove regular local implies domain/reduced first.**

   At v4.29 this is a serious commutative algebra subproject, not a short proof. The standard routes need associated graded / regular sequences / Cohen-Macaulay-style machinery that is not present in the local regular ring API. You do have:
   ```lean
   isReduced_ofLocalizationMaximal
   ```
   so if you had reducedness of all maximal localizations, global reducedness would follow. But getting that from `IsRegularLocalRing` is the missing hard theorem.

**Submersion Route**

A clean “smooth/submersion ⇒ fibre codim” route is not currently turnkey. Mathlib has `Algebra.Smooth.flat`, and `SmoothOfRelativeDimension` definitions, but I do not see a ready fibre-height formula giving codimension of a closed fibre from relative dimension. `AlgebraicGeometry.Morphisms.SmoothFiber` is the opposite direction: flat + smooth fibres imply smooth.

So the likely reachable path is not generic smoothness, but an explicit rank-chart height computation: prove enough of the deep Schur/pivot chart presentation to identify the localized fibre ideal with a graph/coordinate ideal and use existing height tools such as `height_graphIdeal_localization_eq`, `IsLocalization.height_map_of_disjoint`, `RingEquiv.height_map`, and the landed `sigmaIdeal` codimension.

**Module Estimate**

For the height-direct route: about **4-6 new modules**.

The hardest rung is the **deep localized rank-chart/fibre presentation**: a weaker replacement for the full product iso `Sred ≃ₐ[k] SchurLoc ⊗ FibreAlg E`, sufficient to compute height. The `IsRegularLocalRing → IsDomain` gap should not be on the critical path.