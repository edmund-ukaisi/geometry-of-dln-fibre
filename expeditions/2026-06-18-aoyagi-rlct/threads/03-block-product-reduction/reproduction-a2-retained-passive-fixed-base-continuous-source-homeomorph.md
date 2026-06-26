# Reproduction - A2 Retained-Passive Fixed-Base Continuous Source Homeomorph

Date: 2026-06-26.

Status: pen-and-paper prerequisite for a fixed-base local inverse package.
This is still finite fixed-base source-chart topology.  It does not prove
source-rank coverage or measure transport.

## Question

The matrix-level retained-passive coordinate theory already has a homeomorphism
between determinant-chart coordinate data and source-recursive determinant
edge-matrix families:

```text
data |-> data.edgeMatrix,
E    |-> sourceReadback(E).
```

The fixed-base endpoint API also realises any prescribed edge-matrix family
as continuous reverse-edge maps.  We want the corresponding statement at the
continuous edge-family level:

```text
data |-> continuous edge family realising data.edgeMatrix,
E    |-> sourceReadback(edgeMatrix(E)).
```

where the target source set consists of continuous edge families whose
fixed-base edge matrices lie in the source-recursive determinant chart.

## Fixed-Base Matrix Extraction And Realisation

For a continuous reverse-edge family `E`, define its fixed-base matrix family

```text
EMat(p) =
  paperEndpointFixedBaseEdgeMatrixOfReverseEdges W B U0 hU0 E p.
```

The existing prescribed-matrix realisation theorem gives

```text
edgeMatrix(realise(M)) = M.
```

The reverse identity is equally elementary.  By definition,

```text
realise(edgeMatrix(E))(p)
  = toContinuousLinearMap
      (Matrix.toLin b_p b_{p+1}
        (LinearMap.toMatrix b_p b_{p+1} (E p))).
```

The basis cancellation theorem `Matrix.toLin_toMatrix` gives the underlying
linear map `E p`.  Extensionality of continuous linear maps then gives

```text
realise(edgeMatrix(E)) = E.
```

This is the only extra fixed-base lemma needed beyond the existing extraction
direction.

## Source Set

Define the fixed-base retained-passive continuous source set by

```text
E in SourceSet  iff
  edgeMatrix(E) in sourceRecursiveDetChartSet.
```

Equivalently, source readback can be applied to `edgeMatrix(E)` and lands in
the retained-passive determinant chart.

## Homeomorphism

The forward map is the named source-chart leg:

```text
Phi(data) = paperEndpointFixedBaseRetainedPassiveP13SourceChart W B U0 hU0 data.
```

The inverse map on the source set is

```text
Psi(E) =
  sourceReadback(edgeMatrix(E)).
```

with the determinant-chart proof supplied by
`sourceReadback_detChart_of_sourceRecursiveDetChart`.

The left inverse is the already-proved readback identity:

```text
sourceReadback(edgeMatrix(Phi(data))) = data.
```

The right inverse is the composition of two identities:

1. source-recursive readback recovers the edge matrices,

   ```text
   edgeMatrix(sourceReadback(edgeMatrix(E))) = edgeMatrix(E);
   ```

2. fixed-base realisation-after-extraction recovers the continuous edge
   family,

   ```text
   realise(edgeMatrix(E)) = E.
   ```

Continuity of the forward map is already proved for the named source-chart
leg.  Continuity of the inverse is the composition of fixed-base edge-matrix
extraction with the existing matrix-level source-readback continuity on the
source-recursive determinant-chart subtype.

## Boundary

This proves a local inverse/homeomorphism between retained-passive
determinant-chart coordinates and the fixed-base continuous edge-family source
set defined by the recursive determinant-chart condition.

It does not prove that an arbitrary exact-rank source point lies in this set,
does not identify a source-rank neighborhood, does not prove source-image
coverage for the original DLN source, does not push forward Lebesgue or source
measure, does not compute a Jacobian or density, does not establish selected
entry residual-factor compatibility, and does not prove normal crossings,
pole order, or RLCT extraction.
