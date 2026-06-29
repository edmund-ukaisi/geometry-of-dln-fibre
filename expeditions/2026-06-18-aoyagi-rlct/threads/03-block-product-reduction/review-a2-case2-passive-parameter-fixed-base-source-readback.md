# Review - A2 Case 2 Passive-Parameter Fixed-Base Source Readback

Date: 2026-06-29.

Status: PASS.  Controller review plus xhigh read-only reviewer `Ampere the
3rd`; no findings.

## Scope Reviewed

Lean theorem:

```text
retainedPassiveP13LocalSource_mem_and_sourceReadback_residualFactorProduct_eq_matrix_of_case2EndpointTransport_sourceEdgeFamilyOfData_withPassive
```

Location:

```text
lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCase2LocalJacobianMeasure.lean
```

Reproduction and statement card:

```text
reproduction-a2-case2-passive-parameter-fixed-base-source-readback.md
statement-card-a2-case2-passive-parameter-fixed-base-source-readback.md
```

## Findings

No issues found.

The Lean statement is narrow.  It proves pointwise local-source landing for the
fixed-base p.13 source edge family and equality of the source-readback residual
factor product with the selected-entry center-coordinate matrix.  It does not
state source-image equality, arbitrary-source local coverage, measure
pushforward, source-prior or Jacobian transport, normal crossings, pole order,
or RLCT.

The determinant assumptions are exactly the supplied passive-unit assumptions:

```text
forall theta, IsUnit ((Ctop theta).det)
forall theta p, IsUnit ((A1passive theta p).det)
```

The review checked the underlying `detChart` definition and found no hidden
unit condition on `F2`, `A3passive`, or `F3`.

The passive fields are stored in the retained-passive datum and transported
through the fixed-base source realization, but the selected-entry residual
readout is still the center-coordinate matrix supplied by the `center -> R`
coordinate.  The readout theorem has no extra determinant assumptions and
simplifies back to the non-passive selected-entry readout.

The reproduction and statement card keep the citation boundary at Aoyagi
pp. 10-13: the source evidence is the elementary block/product bookkeeping and
the p.13 residual product display.  The card's deferred/nonclaim lists exclude
coverage, measure pushforward, source-prior or Jacobian transport, normal
crossings, pole order, and RLCT.

Placement in `RetainedPassiveCase2LocalJacobianMeasure.lean` is acceptable for
this banked step.  The theorem sits next to the existing zero-passive Case 2
fixed-base local-source/readback bridge, and the file already hosts the
Case 2 endpoint-transported fixed-base inputs consumed by the local-measure
layer.

## Gates

Controller gates:

```text
git diff --check
scripts/sorries
scripts/lb DLNFibre.DLN.Aoyagi.RetainedPassiveCase2LocalJacobianMeasure
lake env lean /tmp/aoyagi_case2_source_readback_axioms.lean
```

Results: whitespace clean; `0 sorry, 0 #exit, 0 native_decide, 0 axiom`;
focused build passed; direct axiom probe reports only
`[propext, Classical.choice, Quot.sound]`.

## Decision

Accept and bank.  Next boundary remains source-measure construction: image or
local coverage for the passive-selected-entry source sector, passive Jacobian
and bounded-unit density accounting, and any external source-prior transport.
