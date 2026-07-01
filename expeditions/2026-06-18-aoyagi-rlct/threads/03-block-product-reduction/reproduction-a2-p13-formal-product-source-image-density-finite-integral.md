# Reproduction - A2 p.13 formal-product source-image density finite integral

## Boundary

This note records the finite-integral consumer to be formalised as the
source-image bounded-density front end for the p.13 formal-product chart
measure.  The result is independent of the quiver paper and uses only Aoyagi's
p.13 retained-passive chart as the source of the geometric expression.

The theorem does not prove that the p.13 formal-product measure is a
bounded-density perturbation of the passive-theta source-image reference.  That
identity and the density bound remain explicit final-handler hypotheses.

## Objects

Let `W` be the passive-theta neighbourhood returned by the existing
formal-product readback finite-integral socket.  The local source-image theorem
then returns an open set

```text
V subset W
```

with:

```text
readback (sourceChart theta) = theta       for theta in V,
sourceChart injective on V,
sourceChart continuous on V,
sourceChart '' V measurable,
sourceChart z in p13SourceSet              for z in V.
```

For a measurable chart piece contained in `sourceChart '' V`, define the
formal p.13 chart-piece measure

```text
muP13 :=
  (Measure.map
    (fun z => p13SourceChart (topologyTupleEdgeRawOrder z))
    ((m.restrict rawDetChart).withDensity
      (fun z => ENNReal.ofReal
        (retainedPassiveFormalRawOrderJacobianProductAbsDetAt z))))
    .restrict chartPiece.
```

The final handler assumes

```text
muP13 =
  ((Measure.map sourceChart (coordinateSourceMeasure.restrict V)).withDensity
    formalDensity).restrict chartPiece
```

and

```text
formalDensity(E) <= D
```

for `Measure.map sourceChart (coordinateSourceMeasure.restrict V)` restricted
to `chartPiece`, with `D < infinity`.

## Calculation

1. The local source-image support theorem turns
`chartPiece subset sourceChart '' V` into both downstream geometric hypotheses:

```text
chartPiece subset p13SourceSet,
readback E in W and sourceChart (readback E) = E  for E in chartPiece.
```

The first follows from pointwise image support.  The second follows from the
right inverse on `sourceChart '' V` and `V subset W`.

2. The bounded-density readback socket for the p.13 formal-product measure
applies to the supplied equality and density bound:

```text
AEMeasurable readback muP13
Measure.map readback muP13 <= D * coordinateSourceMeasure.restrict W.
```

The scalar is exactly `D`; no Haar scalar appears in this readback-domination
step.

3. The existing formal-product readback finite-integral socket is then applied
with

```text
Cformal := D.
```

Its hypotheses are precisely the chart-piece measurability, local-source
containment, p.13 support, readback/right-inverse on the chart piece, prior
density bound, readback measurability of `muP13`, readback domination of
`muP13`, and `D < infinity`.

4. The conclusion is the same original edge-family prior finite integral over
the chart piece and regular variable ball:

```text
lintegral ... d(((originalEdgeFamilyPrior density).restrict chartPiece).prod nu)
  < infinity.
```

## Checks

The source-image theorem supplies `V` after `W` is known, so the final theorem
exposes both `W` and `V`.  The chart piece is asked only to lie in
`sourceChart '' V`; p.13 support and the readback/right-inverse condition are
derived internally.

The scalar passed to the formal-product socket is `D`, not `D * cHaar^-1`.  The
inverse Haar scalar belongs to the separate bridge from the formal-product
measure to original volume, and to the original-prior bridge already inside the
formal-product readback finite-integral socket.

## Nonclaims

No formal-product/source-image density identity is proved.  No density bound is
proved.  No source-image coverage, source-rank coverage, Haar transport,
normalization of Haar scalars, normal crossings, pole order, or RLCT extraction
is proved.
