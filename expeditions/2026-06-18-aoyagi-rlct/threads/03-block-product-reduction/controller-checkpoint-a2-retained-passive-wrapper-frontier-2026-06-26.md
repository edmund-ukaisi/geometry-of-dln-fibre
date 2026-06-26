# Controller Checkpoint - A2 Retained-Passive Wrapper Frontier

Date: 2026-06-26.

Status: post-VM-recovery controller checkpoint after read-only xhigh scout
reports.  No Lean theorem is claimed here.

## Source Recheck

The controller re-extracted Aoyagi PDF pp. 10-13 with Ghostscript
`txtwrite`.  The relevant formulas remain the expected elementary block
algebra:

```text
F2 = -A1^{-1} A2
F3 = -A3 A1^{-1}
C4 = -A3 A1^{-1} A2 + A4
```

In the inductive Theorem 3 step, the accumulated left factor updates by

```text
F3new = F3old - D * A3 * (C1 * A1)^{-1},
```

where `D` is the previous residual product and `C1 * A1` is the new top block.
The displayed p.13 product-difference readout is

```text
[ C1 - E_r        -F2
  -F3        prod C^(s) - F3 F2 ].
```

This supports the signs and factor order used in the retained-passive
coordinate reproduction and Lean API.  It does not state source-rank coverage,
measure pushforward, density/Jacobian transport, normal crossings, pole order,
or RLCT extraction.

## Scout Reports

Singer the 4th checked the remaining `hchart_mem` assumptions in the
chart-produced selected-entry retained-passive local-measure theorems.  The
assumption is necessary for arbitrary chart codomain `alpha`: it supplies the
support fact that the pushed-forward measure lands in the retained-passive
local source.

Two source-faithful specializations can remove it:

- make the codomain the source-edge-family-set subtype;
- make the codomain the retained-passive determinant-chart subtype and use the
  named retained-passive p.13 source chart.

Both are wrappers unless a downstream theorem consumes that codomain shape.
They do not construct the signed-box-to-coordinate chart, prove residual
factor identities, or prove source-measure/Jacobian transport.

Darwin the 4th checked the remaining `hfactor` assumption.  Existing Lean
reduces it to supplied retained-passive data or closes synthetic two-edge
Case 2 data, but there is no real source-chart theorem constructing the
needed `retainedData y`, proving fixed-base edge realization for that data,
or identifying the full retained-passive suffix product with the two-edge
Case 2 window.

Gibbs the 4th independently audited the retained-passive coordinate-domain
and inverse reproduction against Aoyagi pp. 10-13.  No blocking sign, order,
or dimension mismatch was found.  In particular:

- the one-step formulas `F2 = -A1^{-1} A2`,
  `C = A4 - A3 A1^{-1} A2`, and
  `F3new = F3old - D * A3 * (C1 * A1)^{-1}` match Lemma 2 and
  Theorem 3;
- the endpoint solve `A1_0 = Tail^{-1} * Ctop` has the correct product
  orientation;
- the endpoint solve `A3_last = -(F3 - earlyTail) * CtopLast` has the
  correct sign because each lower-left step contributes
  `-(D * A3 * Ctop_current^{-1})`;
- `RetainedPassiveNonredundantCoordinateData` stores exactly the intended
  nonredundant fields, and the determinant chart inverts only `Ctop` and the
  passive `A1` blocks.

Pauli the 4th inspected the measure/Jacobian frontier.  The existing one-step
raw-order derivative and measure stack is strong, but it does not compose into
a retained-passive chart theorem at this head.  The blocker is structural:
the retained-passive source chart is an `OpenPartialHomeomorph` with
topological inverse/readback algebra, not a differentiable finite tuple map
with a determinant formula.

The real downstream field remains an external/source restricted pushforward
such as `hmap`; the chart-produced variants remove it only by defining the
measure to be the pushforward.  A source-faithful retained-passive
measure/Jacobian theorem needs a common tuple coordinate model,
`HasFDerivWithinAt` for the retained-passive source tuple map, a determinant
formula, Haar/null-measurability setup, and a bridge back to the fixed-base
continuous edge-family form.

## Current Lean Layer

The retained-passive coordinate-domain and inverse layer is already present
for the source-recursive determinant chart:

```text
RetainedPassiveNonredundantCoordinateData
RetainedPassiveNonredundantCoordinateData.detChart
RetainedPassiveNonredundantCoordinateData.edgeMatrix
RetainedPassiveNonredundantCoordinateData.sourceReadback
sourceRecursiveDetChart_edgeMatrix_of_detChart
sourceReadback_detChart_of_sourceRecursiveDetChart
edgeMatrix_sourceReadback_eq_of_sourceRecursiveDetChart
paperEndpointFixedBaseRetainedPassiveP13SourceEdgeFamily_homeomorph
paperEndpointFixedBaseRetainedPassiveP13SourceEdgeFamily_openPartialHomeomorph
```

This covers the coordinate domain, source map, and local inverse for the
explicit fixed-base source-recursive determinant-chart model.  It does not
identify that model with the original source-rank stratum or with an original
source measure.

The self-base local-source coverage theorem is also correctly scoped:
`exists_open_paperEndpointFixedBaseRetainedPassiveP13LocalSource_coverage_of_selfBase`
chooses an open neighborhood contained in the determinant-chart preimage, so
the final source-rank inclusion is rank-insensitive.  It is useful as a
handoff-shaped local-source inclusion, not as exact-rank/source-rank openness
or global chart coverage.

## Controller Decision

The A2 wrapper search is closed at this frontier.

Do not add the `hchart_mem` subtype specializations unless a named downstream
consumer needs exactly one of those codomain shapes.  Do not try to discharge
`hfactor` from the existing Case 2/sourceChart API; the required real source
datum and fixed-base realization theorem are not present.

The next source-moving work must remove a real field by construction.  The
live options are:

- construct source-specific retained-passive data for an actual selected-entry
  chart point and prove fixed-base edge realization plus the data-level
  residual-factor product identity;
- prove endpoint/factor alignment or full-to-window transport for a real
  retained-passive suffix, including the pivot-nonzero provenance needed by
  the current Case 2 bridge;
- begin the retained-passive measure/Jacobian package: compose one-step
  Jacobian factors, isolate passive unit factors, and state exactly whether
  the result is raw Haar, product-coordinate measure, or a weaker chart
  measure.

The precise first theorem shape for that last option should be a tuple-level
retained-passive pushforward theorem, for example:

```text
Measure.map retainedPassiveP13SourceRawOrderTuple
  ((m.restrict retainedPassiveP13DetChartTupleSet).withDensity
    (ofReal retainedPassiveP13SourceJacobianAbsDet))
=
  m.restrict retainedPassiveP13SourceRecursiveDetChartRawOrderSet.
```

This theorem is not available yet; it names the construction package rather
than a current Lean target that can be discharged from existing wrappers.

The general normal-crossing-to-RLCT extraction remains the only cited
boundary.  The items above are Aoyagi-specific construction frontiers unless a
further probe shows a genuine analytic theorem is being invoked.
