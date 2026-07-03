# A2 with-following readback-local pivot condition

## Claim

The lower-level enlarged with-following source-chart readback construction can
export the selected-entry pivot condition on its returned local set.

The existing construction takes

```text
V = Udet ∩ pivotSet,
```

where `Udet` is the retained-passive determinant-chart neighborhood and

```text
pivotSet = {z | case2PassiveThetaPivotNonzero z.1}.
```

Thus every `z in V` satisfies the pivot-nonzero condition, and the already
proved readback left inverse still holds on the same `V`.

## Pen-and-paper check

The base point satisfies both hypotheses:

```text
z0 ∈ Udet
z0 ∈ pivotSet
```

so `z0 ∈ V`.  Openness follows because `Udet` is open and the pivot coordinate
map `z ↦ z.1.yNext pivotNext` is continuous, so the nonzero locus is open.

For `z ∈ V`, the second component of membership gives

```text
case2PassiveThetaPivotNonzero z.1.
```

The determinant component supplies the determinant-chart data used in the
existing proof of

```text
readback(sourceChart z) = z.
```

Therefore the same local set supports both the pivot condition and the
readback left inverse.

## Boundary

This is not a source-image reverse-inclusion theorem.  It only exposes a local
condition already present in the construction.  The future reverse inclusion
still needs a pointwise theorem saying that an arbitrary `E` in the p.13 source
set is recovered by `sourceChart(readback E)` under this pivot condition.
