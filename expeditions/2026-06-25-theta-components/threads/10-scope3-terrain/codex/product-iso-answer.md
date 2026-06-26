**Verdict:** for `FibreAlg` itself, the product iso is not a Mathlib packaging problem. The hard point is exactly the radicality/reducedness wall. For the reduced fibre coordinate ring `O(F) = k[Rep]/vanishingIdeal(F)`, the existing `chartLocalizedAlgEquiv` is already the right object and can probably be tensor-packaged. Replacing `O(F)` by `FibreAlg` is the nontrivial AG content.

**A. Product Iso**
The clean split is:

1. **Reduced chart product, tractable:** use `chartLocalizedAlgEquiv`
   ```lean
   Localization.Away chartDsig ≃ₐ[k] Localization.Away chartGfib
   ```
   and rewrite the RHS as roughly
   ```lean
   SchurLoc ⊗[k] sweepFibreRing
   ```
   using `MvPolynomial.algebraTensorAlgEquiv` / `scalarRTensorAlgEquiv` plus localization base-change. This gives a genuine local product chart for the reduced variety.

2. **Strict scheme product with `FibreAlg`, hard:** build a cut presentation `Scut` and endpoint-normalize
   ```lean
   Scut ≃ₐ[SchurLoc] SchurLoc ⊗[k] FibreAlg d E
   ```
   then prove `Scut ≃ Sred`. That last identification is equivalent to proving the cut ideal radical.

The hardest sublemma is:
```lean
sigmaIdeal ≤ ker (normalized map to SchurLoc ⊗ FibreAlg)
```
or equivalently the localized equality between the reduced rank-locus quotient and the cut quotient. Pointwise/rank-locus reasoning only gives containment in the radical of the kernel. Upgrading radical containment to kernel containment is the reducedness theorem.

So: **not packaged**; tensor/polynomial/localization plumbing is partly packaged, quotient/radical descent is hand-built and hard. Strict `Sred ≃ SchurLoc ⊗ FibreAlg` is months-scale/fresh AG, not a bounded multi-tide plumbing job. Reduced-version tensor packaging is tractable.

**B. Cheaper Radical Route**
`e_β` does **not** prove `fibreGenIdeal` radical. It is built over:
```lean
sweepFibreRing = k[Rep] ⧸ vanishingIdeal(F)
```
so it has already passed to the reduced fibre variety. It can prove dimension/component statements insensitive to nilpotents, but it cannot show:
```lean
fibreGenIdeal = vanishingIdeal(F)
```
because that is exactly the nilpotent-killing map being injective.

Jacobian/generic smoothness is also not a cheap radical proof. Dense smoothness only controls generic points. Nilpotents can be supported on the singular/deeper closed locus, and the fibre is reducible/non-equidimensional, so generic reducedness is not enough without a serious associated-prime/unmixedness argument.

**C. Smoothness**
Yes: the existing **generic-smoothness route** needs reducedness first:
```lean
Scheme.Hom.dense_smoothLocus_of_perfectField
```
requires `[IsReduced X]`. Applying it to the reduction proves smoothness of the reduced fibre, not of `FibreAlg`.

But a **direct local Jacobian/submersive route** can avoid global reducedness. Mathlib’s usable API is lower-level:
```lean
Algebra.PreSubmersivePresentation.naive
Algebra.SubmersivePresentation
SubmersivePresentation.isStandardSmooth
SubmersivePresentation.isStandardSmoothOfRelativeDimension
```
This means: choose equations, choose a square Jacobian minor, localize where its determinant is a unit, package a `SubmersivePresentation`. That proves smoothness on that open chart without first proving the whole fibre reduced. It does not prove global radicality.

**D. Sequencing**
Do not make strict reducedness the first gate unless the target is specifically:
```lean
(fibreGenIdeal d B).IsRadical
```
or a scheme-theoretic product with `FibreAlg`.

Minimal honest bundle statement, with no Mathlib `FiberBundle` API:

```lean
-- per pivot chart
Localization.Away chartDsig
  ≃ₐ[k]
Localization.Away chartGfib
```

and optionally tensor-package the RHS as:
```lean
SchurLoc ⊗[k] sweepFibreRing
```

That is an affine local-triviality statement for the reduced chart. For a full bundle, state a finite family of such chart `AlgEquiv`s, plus cover/no-drop/transition facts as needed. Do not call it a product with `FibreAlg` until radicality is proved.

Recommended decomposition:

1. **Reduced tensor packaging:** 1-2 modules.
2. **Chart-family / pivot cover packaging:** 2-4 modules.
3. **Direct smooth opens via `SubmersivePresentation`:** 3-6 modules, depending on how hard the Jacobian minor cover is.
4. **Strict `FibreAlg` radical/product iso:** 8-12+ modules, genuinely AG-heavy. Hardest rung is the kernel/radical containment collapse.