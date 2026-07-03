# A2 coordinate-source finite integral from cylinder domination

Date: 2026-07-03.

## Calculation

The existing finite-source theorem constructs a finite following patch and a
local source measure

```text
localSourceMeasure =
  ((((passiveMeasure.prod weightedBox).prod followingMeasure).restrict
    {z | z.2 in followingPatch}).restrict V).
```

It also gives the dominated-target socket

```text
targetMeasure <= C • localSourceMeasure
C < infinity
```

implying p.13 product-residual a.e. positivity and finite negative-power
integral for `targetMeasure`.

For the concrete coordinate source, the density stack is

```text
referenceSource
  -> baseJ = referenceSource.withDensity jacobianDensity
  -> coordinateSourceMeasure = baseJ.withDensity sourceDensity.
```

The previous base-domination handoff gives, after the following patch is in
scope, the conditional domination

```text
referenceSource.restrict V <= Cpassive • localSourceMeasure
```

provided

```text
passiveRef.restrict passiveLocalSet <= Cpassive • passiveMeasure,
V subset {z | z.1.1 in passiveLocalSet},
V subset {z | z.2 in followingPatch}.
```

The concrete two-density handoff then gives

```text
coordinateSourceMeasure.restrict V
  <= (CS * (CJ * Cpassive)) • localSourceMeasure
```

from the two upper-density assumptions

```text
jacobianDensity <= CJ    a.e. on referenceSource.restrict V,
sourceDensity <= CS      a.e. on baseJ.restrict V,
```

and the scalar finite assumptions

```text
Cpassive < infinity, CJ < infinity, CS < infinity.
```

Finally, instantiate the dominated-target socket with

```text
targetMeasure = coordinateSourceMeasure.restrict V,
C = CS * (CJ * Cpassive).
```

## Quantifier order

The following patch is existentially constructed by the finite-source theorem.
The containment

```text
V subset {z | z.2 in followingPatch}
```

therefore cannot be an input before the existential patch is in scope unless
the caller has already chosen the patch.  The honest wrapper should return the
same patch witnesses and a continuation:

```text
V subset {z | z.2 in followingPatch} ->
  finite product-residual result for coordinateSourceMeasure.restrict V.
```

A later source-chart theorem may discharge this continuation by shrinking `V`
inside the open following-patch cylinder.  This wrapper should not claim that
the containment is automatic.

## Boundary

This composition still proves no passive local comparison measure
construction, no passive support theorem, no Jacobian-density upper bound, no
source-density upper bound, no determinant-Haar/raw-Haar transport, no
original-prior transport, no normal crossings, pole order, or RLCT extraction.
