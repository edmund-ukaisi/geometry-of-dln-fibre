# A2 With-Following Localized Source-Density Raw Domination

## Purpose

The localized reverse-domination base theorem gives, for a raw-order patch
`P subset rawSourceSet`,

```text
rawHaar.restrict P
  <= Cdet • Measure.map rawMap (baseJ.restrict V),
```

provided the endpoint determinant patch

```text
rawDetChart ∩ rawOrderOnEndpoint preimage P
```

is dominated by the endpoint image of the reference source on `V`.

The existing source-density wrapper then turns domination by the Jacobian
weighted base measure into domination by the concrete coordinate source
measure.  That density calculation is local in the target measure, so it
should work with `rawHaar.restrict P` in place of
`rawHaar.restrict rawSourceSet`.

## Calculation

Let

```text
mu = referenceSource.restrict V
baseJ = referenceSource.withDensity jacobianDensity
coordinateSourceMeasure = baseJ.withDensity sourceDensity
```

and let

```text
target = rawHaar.restrict P.
```

Assume:

```text
P subset rawSourceSet,
rawHaar.restrict (rawDetChart ∩ rawOrderOnEndpoint preimage P)
  <= Cdet • Measure.map Y mu,
Cdet < infinity,
epsilon <= sourceDensity z for baseJ.restrict V-a.e. z,
epsilon != 0,
epsilon != infinity.
```

The localized base theorem gives

```text
target <= Cdet • Measure.map rawMap (baseJ.restrict V).
```

The lower-density adapter is purely measure-theoretic.  Since

```text
coordinateSourceMeasure.restrict V
  = (baseJ.withDensity sourceDensity).restrict V,
```

and `sourceDensity >= epsilon` a.e. on `baseJ.restrict V`, the adapter gives

```text
target
  <= (Cdet * epsilon^{-1}) •
     Measure.map rawMap (coordinateSourceMeasure.restrict V).
```

The scalar is finite by `Cdet < infinity`, `epsilon != 0`, and
`epsilon != infinity`.

## Boundary

The endpoint-patch domination and the lower-density hypothesis remain
explicit.  This still does not prove endpoint-Haar transport, exact raw-Haar
pushforward, raw-Haar normalization, source-image/source-rank coverage,
original source-prior transport, normal crossings, pole order, or RLCT.

## Verification

Focused and full local Lean builds passed:

```text
env LEAN_NUM_THREADS=3 lake build DLNFibre.DLN.Aoyagi.RetainedPassiveCase2PassiveThetaRawImageHandoff
env LEAN_NUM_THREADS=3 lake build DLNFibre
```

`scripts/sorries` reported `0 sorry, 0 #exit, 0 native_decide, 0 axiom`.
The touched Lean-file forbidden-marker scan and `git diff --check` passed.
Direct axiom probes for both new declarations reported:

```text
[propext, Classical.choice, Quot.sound]
```
