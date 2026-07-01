# Statement Card - A2 Case 2 passive-reference determinant-chart transfer

## Claim

For the concrete Case 2 passive-theta endpoint topology-tuple map `Y`, if

```text
passiveMeasure <= d • passiveReferenceMeasure
```

on passive fields, and if the passive reference product source satisfies

```text
Measure.map Y (passiveReferenceSource.restrict V)
  <= c • rawReference.restrict rawDetChart,
```

then the actual passive product source satisfies

```text
Measure.map Y (passiveSource.restrict V)
  <= (d * c) • rawReference.restrict rawDetChart.
```

Here both product sources use the same selected-entry `weightedBox` on the
right:

```text
passiveSource = passiveMeasure.prod weightedBox
passiveReferenceSource = passiveReferenceMeasure.prod weightedBox.
```

Public Lean names:

```text
map_prod_restrict_le_smul_of_left_le_smul_of_map_prod_restrict_le_smul

measure_map_case2PassiveThetaEndpointTopologyTuple_passiveSource_restrict_le_smul_detChart_of_passiveMeasure_le_smul_reference
```

## Inputs Used

- scalar domination of the passive-field measure by a passive reference
  measure;
- fixed selected-entry `weightedBox`, shared by source and reference;
- product-measure domination in the left factor;
- restriction and map monotonicity under scalar domination;
- a supplied determinant-chart comparison for the reference product source.

## Output

This turns the future concrete passive-reference COV theorem into a reusable
adapter: after the reference theorem is proved, dominated passive-field
measures can use the current raw-Haar `baseJ` sockets without reproving the
endpoint determinant-chart comparison from scratch.

## Nonclaims

The theorem does not define or construct the concrete passive reference
measure.  It does not prove determinant-chart Haar transport, exact raw-Haar
pushforward, Haar normalization, original source-prior transport,
source-image coverage, source-rank coverage, normal crossings, pole order, or
RLCT extraction.
