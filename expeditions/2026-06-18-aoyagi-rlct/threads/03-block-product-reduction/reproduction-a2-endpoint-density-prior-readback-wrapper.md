# A2 Endpoint Density Prior Readback Wrapper

Date: 2026-07-03.

## Local Calculation

Start with the endpoint-density original-volume readback wrapper on the same
local shrink `V`.  For a p.13 chart piece `chartPiece subset sourceChart '' V`,
set

```text
P = rawSourceSet inter rawChart^{-1}(chartPiece)
Q = rawDetChart inter rawOrderOnEndpoint^{-1}(P).
```

Assume the endpoint reference image identity and endpoint-density lower bound

```text
endpointReferenceImage = (rawHaar.restrict Q).withDensity Jprod,
Cdet < infinity,
1 <= Cdet * Jprod(y) for a.e. y with respect to rawHaar.restrict Q.
```

Also assume the source-density lower bound and nonzero finite `epsilon`
conditions.  The endpoint-density volume wrapper gives

```text
Measure.map readback (originalVolume.restrict chartPiece)
  <= Dvol * coordinateSourceMeasure.restrict G,

Dvol = cHaar^{-1} * (Cdet * epsilon^{-1}).
```

Now let `density : EdgeFamily -> R` be an original-prior density with local
upper bound

```text
density(E) <= Kprior
```

for a.e. `E` with respect to `originalVolume.restrict chartPiece`.  The generic
prior restriction lemma gives

```text
originalPrior.restrict chartPiece
  <= ofReal(Kprior) * originalVolume.restrict chartPiece.
```

Pushing forward through `readback` and composing scalar dominations gives

```text
Measure.map readback (originalPrior.restrict chartPiece)
  <= (ofReal(Kprior) * Dvol) * coordinateSourceMeasure.restrict G.
```

## Boundary

This wrapper does not prove the endpoint reference image identity, endpoint
Jacobian lower bound, source-density lower bound, `epsilon` side conditions, or
prior-density upper bound; all remain explicit hypotheses.  It does not
normalize Haar scalars to `1`, prove raw-Haar transport, original-prior
transport, source-image coverage, normal crossings, pole order, finite-integral
transfer, or RLCT extraction.
