**Q1.** Yes: field (a) is exactly the right certificate if the headline says “over the rank-= r open.” It does not strengthen the local-product atlas itself; it identifies the base open geometrically. What it buys is that `rankROpen d r` is not merely “the union of pivot-minor basic opens,” but precisely the residue-field rank locus of the universal matrix. That is the missing honesty condition for the name. It is orthogonal to the product isomorphisms, so I would present it as a semantic/rank-locus field, not as part of the abstract notion of “local product atlas.” Folding it in is not overclaiming as long as the field is exactly the iff you stated. Field (b) is useful operationally but near-definitional; field (a) is the nontrivial name/content bridge.

**Q2.** The clean algebraic compatibility is not “projection” as a map out of the tensor product, but equality of `SchurLoc`-algebra structures. If `Total` has a specified base map `SchurLoc →ₐ[k] Total`, then the honest condition is:
```lean
∀ x : SchurLoc,
  triv (baseMap x) = Algebra.TensorProduct.includeLeft x
```
or equivalently `triv` is an `AlgEquiv` over `SchurLoc`, not merely over `k`. This is meaningful only if you have already identified the base-direction algebra map into `Total`. If that map is only implicit through `(awayCongr gauge).symm ≪≫ e_β ≪≫ tensor-package`, then the field is checkable only after you package that map explicitly. It is not automatic from a `k`-algebra equivalence. Do not include a projection-compatibility field unless you can name both maps being compared. If you cannot expose `baseMap : SchurLoc →ₐ[k] Total`, drop (d).

**Q3.** Yes, “local product over an open cover” is a coherent notion distinct from a fibre bundle, provided the name avoids “trivial,” “bundle,” or “gluing.” The object says: each member of a specified cover has a product presentation with a fixed fibre ring. It does not say these presentations agree on overlaps, nor that they define a global fibre-bundle object. The sharpest reviewer objection to `reducedFibre_isLocallyProductOverRankOpen` is that “locally product” often suggests compatible local product charts, i.e. bundle-like transition functions. That objection is not fatal if the theorem/structure name and docstring explicitly say “uncocycled” or “per-chart.” I would make the missing coherence impossible to miss in the declaration name or first sentence. The dangerous name is not `localProduct`; it is anything that reads like `locallyTrivial`.

**Q4.** The better public headline is a pointwise theorem, backed by a small record if reuse requires it. A theorem of the form “for every `P` with universal residue rank `r`, there exists a pivot basic open containing `P` and a product presentation on that open” reads honestly and uses S1, the cover, and the per-pivot trivializations directly. It avoids suggesting glued transition data. The structure is useful internally if later results need to reuse the cover, rank certificate, and chart data uniformly. But as the S4 deliverable, the pointwise theorem is harder to misread. I would still build a record named for what it literally contains, then expose the pointwise theorem as the reader-facing statement.

**RECOMMENDED SHAPE**

Use an explicitly uncocycled record:

```lean
structure RankROpenPerPivotLocalProductAtlas where
  isRankLocus :
    ∀ P : PrimeSpectrum (sweepSigmaRing k d r),
      P ∈ rankROpen d r ↔
        (universalMatrixResidue d r P).rank = r

  cover_rankROpen :
    (⋃ st,
      (PrimeSpectrum.basicOpen
        (chartDsigAt d r st.1 st.2) :
          Set (PrimeSpectrum (sweepSigmaRing k d r)))) =
      rankROpen d r

  chart :
    ∀ I : PivotDatum d r hp hq,
      LocalTrivializationDatum k Base Total BaseLoc Fibre

  chartElt_eq :
    ∀ I : PivotDatum d r hp hq,
      (chart I).chartElt = chartDsigAt d r I.s I.t

  productIso :
    ∀ I : PivotDatum d r hp hq,
      Localization.Away (chartDsigAt d r I.s I.t) ≃ₐ[k]
        (SchurLoc k d r I) ⊗[k] sweepFibreRing k d r
```

Then expose:

```lean
theorem reducedFibre_existsProductChartAt_rankEq
  (P : PrimeSpectrum (sweepSigmaRing k d r))
  (hP : (universalMatrixResidue d r P).rank = r) :
  ∃ I : PivotDatum d r hp hq,
    P ∈ PrimeSpectrum.basicOpen (chartDsigAt d r I.s I.t) ∧
    Nonempty
      (Localization.Away (chartDsigAt d r I.s I.t) ≃ₐ[k]
        (SchurLoc k d r I) ⊗[k] sweepFibreRing k d r)
```

Only add projection compatibility if you can state it over a named base map:

```lean
baseMap :
  ∀ I, SchurLoc k d r I →ₐ[k]
    Localization.Away (chartDsigAt d r I.s I.t)

base_compatible :
  ∀ I x,
    productIso I ((baseMap I) x) =
      Algebra.TensorProduct.includeLeft x
```

**DO NOT:** call the result `locallyTrivial`, `FiberBundle`, or imply glued transition compatibility before the fixed-target overlap cocycle is assembled.