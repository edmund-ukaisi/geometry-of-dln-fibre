# Statement Card - A2 Original Edge-Family Raw-Order Edge-Volume Bridge

## Claim

The raw-order restricted measure bridge can be lifted from tuple coordinates
to fixed-basis continuous edge-family coordinates by applying
`tupleToEdgeFamily`.

For

```text
L := rawOrderMatrixTupleContinuousLinearEquiv e
T := tupleToEdgeFamily b
c := (Measure.map L m).addHaarScalarFactor (originalTupleVolume d)
```

Lean proves:

```text
Measure.map (fun y => T (rawOrderMatrixTuple e y)) (m.restrict S)
= c • (originalEdgeFamilyVolume b).restrict
    ((fun y => T (rawOrderMatrixTuple e y)) '' S).
```

The formal-product retained-passive raw-order COV version gives the same
right-hand side with `S` equal to
`topologyTupleRawOrderSourceRecursiveDetChartSet` and left-hand side mapped
from the determinant-chart density.

## Public Lean Names

```text
map_tupleToEdgeFamily_originalTupleVolume_restrict_eq_originalEdgeFamilyVolume_restrict_image
map_rawOrderMatrixTuple_tupleToEdgeFamily_restrict_eq_smul_originalEdgeFamilyVolume_restrict_image
map_formalProduct_rawOrderMatrixTuple_tupleToEdgeFamily_eq_smul_originalEdgeFamilyVolume_restrict_image
```

## Inputs Used

- `edgeFamilyMatrixTupleContinuousLinearEquiv b` and its inverse
  `tupleToEdgeFamily b`;
- `originalEdgeFamilyVolume b`, defined as the pushforward of
  `originalTupleVolume d` by `tupleToEdgeFamily b`;
- the tuple-side raw-order restricted measure bridge;
- the existing retained-passive formal-product raw-order COV theorem composed
  with an a.e.-measurable target map.

## Proof Shape

1. Use the measurable equivalence `tupleToEdgeFamily b` to prove restricted
   pushforward compatibility from tuple volume to edge-family volume.
2. Map the tuple-side raw-order bridge through `tupleToEdgeFamily b`.
3. Rewrite `T '' (L '' S)` as `(T ∘ L) '' S`.
4. For the formal-product theorem, use the existing composed COV with
   `ψ y := T (rawOrderMatrixTuple e y)`, then apply the restricted theorem.

## Nonclaims

This is not a chart coverage theorem, not source-image equality with the
whole original edge-family space, not a restricted-Haar theorem, not a scalar
normalization theorem, and not a normal-crossing/RLCT theorem.
