# Review - A2 With-Following Original-Volume Source-Cylinder Handoff

Date: 2026-07-07.

## Source-Fidelity Check

Reviewer: xhigh read-only sidecar `Kepler the 2nd`.

Verdict: the theorem is justified as scalar bookkeeping over the formal-product
source-cylinder handoff.

The checked calculation starts from

```text
formalProductMeasure.restrict chartPiece
  <= Ddet * sourceRef,

Ddet = Cdet * eps^-1,
sourceRef = Measure.map sourceChart (coordinateSourceMeasure.restrict V).
```

The p.13 inverse-Haar bridge converts this to

```text
originalVolume.restrict chartPiece
  <= (((cHaar^-1 : NNReal) : ENNReal) * Ddet) * sourceRef.
```

The reviewer confirmed that this uses only the Aoyagi p.10-13 block/product
chart structure already formalized and the p.13 formal-product/original-volume
scalar bridge.  It does not use the quiver paper or quiver Lean evidence.

## Lean-Route Check

Reviewer: xhigh read-only sidecar `Feynman the 2nd`.

Verdict: the theorem placement, statement shape, and proof route are the right
ones, and no helper lemma is structurally needed.

The review highlighted the key proof route:

1. Choose a local p.13 source-image shrink.
2. Run the formal-product source-cylinder theorem inside that shrink.
3. Derive `chartPiece subset p13SourceSet` internally from
   `chartPiece subset sourceChart '' (V inter sourceCylinder)`.
4. Feed the resulting formal-product domination to the existing p.13
   original-volume bridge.

## Boundary

The theorem must keep the following hypotheses explicit:

- `MeasurableSet chartPiece`;
- `chartPiece subset sourceChart '' (V inter sourceCylinder)`;
- `eps <= sourceDensity` a.e. on `baseJ.restrict V`;
- `eps != 0` and `eps != infinity`;
- an additive raw Haar measure, hence the corresponding inverse Haar scalar.

It does not prove determinant-chart Haar transport, exact raw-Haar
pushforward, Haar normalization or `cHaar = 1`, source-density positivity,
original-prior transport, source-image/source-rank coverage, normal crossings,
pole order, RLCT extraction, or finite-integral transfer.
