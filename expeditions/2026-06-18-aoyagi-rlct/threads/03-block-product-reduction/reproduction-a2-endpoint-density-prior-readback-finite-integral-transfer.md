# A2 Endpoint Density Prior Readback Finite-Integral Transfer

Date: 2026-07-03.

## Local Calculation

Work in the enlarged with-following Case 2 source coordinates.  The prior
readback wrapper returns a local shrink `V subset G` and, for every p.13 chart
piece

```text
chartPiece subset sourceChart '' V,
```

sets

```text
P = rawSourceSet inter rawChart^{-1}(chartPiece),
Q = rawDetChart inter rawOrderOnEndpoint^{-1}(P).
```

Under the endpoint reference image identity and endpoint-density lower bound

```text
endpointReferenceImage = (rawHaar.restrict Q).withDensity Jprod,
Cdet < infinity,
1 <= Cdet * Jprod(y) for a.e. y with respect to rawHaar.restrict Q,
```

together with the source-density lower bound, the finite nonzero `epsilon`
side conditions, and a local prior-density upper bound, it gives

```text
Measure.map readback (originalPrior.restrict chartPiece)
  <= Cprior * coordinateSourceMeasure.restrict G
```

with `Cprior < infinity`, and also gives a.e.-measurability of `readback` for
the restricted original prior.

Now let `F : EdgeFamily x beta -> ENNReal` be any product integrand whose
source-chart pullback is measurable and finite over the coordinate-source
measure:

```text
Measurable (fun z : Theta x beta => F (sourceChart z.1, z.2)),

integral F(sourceChart z, u)
  over (coordinateSourceMeasure.restrict G).prod nu
  < infinity.
```

Because `chartPiece subset sourceChart '' V` and `readback (sourceChart z) = z`
on `V`, we have pointwise on `chartPiece`

```text
sourceChart (readback E) = E.
```

The generic readback-transfer lemma

```text
lintegral_prod_lt_top_of_aemeasurable_readback_map_le_smul
```

then pushes the finite source integral through the readback domination and
concludes

```text
integral F(E, u)
  over (originalPrior.restrict chartPiece).prod nu
  < infinity.
```

## Boundary

This is finite-integral transfer only.  It does not prove the endpoint
reference image identity, endpoint Jacobian lower bound, source-density lower
bound, prior-density upper bound, or the source-side finite integral.  It does
not identify the with-following source integral with Aoyagi's p.13 residual
product theorem, does not normalize Haar scalars to `1`, and proves no
source-image coverage, original-prior transport, normal crossings, pole order,
or RLCT extraction.
