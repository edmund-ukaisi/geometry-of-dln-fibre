# Statement Card - A2 suffix-step raw-order inverse density handoff

## Lean Files

- `lean/DLNFibre/DLN/Aoyagi/ProductReductionStepMeasure.lean`
- `lean/DLNFibre/DLN/Aoyagi/ProductReductionStepSuffixDensity.lean`

## Claim

Lean defines the raw-shaped target tuple obtained from an arbitrary
deterministic suffix-state one-step coordinate tuple:

```text
chartLocalSuffixStateStepRawOrderTargetTuple E p S F3prev.
```

If `S.Ctop` and the transformed edge top-left block are determinant units,
this target tuple lies in the raw-shaped target determinant chart.  If the
raw step tuple varies continuously, or if the relevant fields vary
continuously, then the target tuple varies continuously.  The chart-side
inverse product-step Jacobian density is therefore continuous along the target
tuple and positive at the basepoint.

## Lean Names

```text
continuousAt_productReductionStepTopologyTupleToChartRawOrder_of_mem_rawDetChartSet
chartLocalSuffixStateStepRawOrderTargetTuple
chartLocalSuffixStateStepRawOrderTargetTuple_mem_rawDetChartSet
continuousAt_chartLocalSuffixState_stepRawCoordinates_topologyTuple
continuousAt_chartLocalSuffixStateStepRawOrderTargetTuple_of_raw
continuousAt_chartLocalSuffixStateStepRawOrderTargetTuple
continuousAt_chartLocalSuffixStateStepRawOrderTargetTuple_inverseJacobianDensity
continuousAt_chartLocalSuffixStateStepRawOrderTargetTuple_inverseJacobianDensity_of_fields
chartLocalSuffixStateStepRawOrderTargetTuple_inverseJacobianDensity_pos
```

## Inputs

- A finite product-reduction edge family `E`.
- A suffix state `S : ChartLocalSuffixState ρ κ R j p.succ`.
- A previous lower-left field `F3prev`.
- Determinant-chart hypotheses:
  `IsUnit det(S.Ctop)` and
  `identityCornerDetChart (ChartLocalSuffixState.transformedEdge E p S)`.
- For continuity: continuity of `E p`, `S.B`, `S.Ctop`, `S.D`, and `F3prev`,
  or a direct continuity hypothesis for the raw step tuple.

## Method

The raw one-step tuple is

```text
(S.Ctop, S.D, F3prev, A1, A2, A3, A4),
```

where `A1,A2,A3,A4` are the four blocks of the transformed edge.  The existing
raw-order product-step map sends this tuple to the raw-shaped chart target
tuple.  Determinant-chart membership follows by composing
`stepRawCoordinates_detChart` with
`mapsTo_productReductionStepTopologyTupleToChartRawOrder_detChart`.

Continuity is split into two reusable parts: first the raw step tuple is
fieldwise continuous, then the ambient raw-order chart map is continuous at
determinant-chart points by the already proved Frechet derivative theorem.
The inverse-density continuity and positivity are direct applications of the
existing abstract inverse-density composition lemmas.

## Not Proved

This checkpoint does not prove source coverage, p.13 product-chart
construction for the original DLN source, original source/prior transport,
signed-box density identification, normal crossings, pole order, or RLCT.

## Verification

Focused check:

```text
cd lean
env LAKE_SHARED=/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/aoyagi-rlct/lean/.lake-local-shared scripts/lb DLNFibre.DLN.Aoyagi.ProductReductionStepSuffixDensity
```

Full aggregate check:

```text
cd lean
env LAKE_SHARED=/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/aoyagi-rlct/lean/.lake-local-shared scripts/lb DLNFibre
```

Both passed on 2026-06-26.  The aggregate build reported pre-existing warnings
from unrelated files and long import comments.
