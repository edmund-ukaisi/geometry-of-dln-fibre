# Reproduction - A2 Case 2 Selected-Entry Passive-Parameter Datum

Date: 2026-06-29.

Status: controller pen-and-paper reproduction for the finite Lean bridge
landed in `RetainedPassiveCase2SelectedEntryChartBridge.lean`.  This is a
coordinate-algebra step only.

## Question

Can the current Case 2 selected-entry retained-passive datum be enlarged so
that it carries the passive retained variables suppressed by the reduced
p.13 section, while preserving the selected-entry residual readout?

Answer: yes, for the finite retained-passive datum.  The residual readout
depends only on the stored residual `C` factors.  The passive fields
`A1passive`, `F2`, `A3passive`, `Ctop`, and `F3` can therefore be supplied
independently, with determinant-chart membership controlled by `Ctop` and
`A1passive`.

This does not yet build a passive-coordinate source measure, local inverse,
image theorem, source-prior comparison, normal-crossing chart, pole order, or
RLCT theorem.

## Source Calculation

Aoyagi pp. 10-13 give the elementary block substitutions that motivate the
retained-passive fields.  For one block matrix

```text
A = [A1 A2
     A3 A4]
```

with `A1` invertible, Lemma 2 uses

```text
F2 = -A1^{-1} A2,
F3 = -A3 A1^{-1},
C4 = -A3 A1^{-1} A2 + A4.
```

In the product reduction, the retained-passive one-step chart can be written
with raw variables

```text
(C1, D, F3old, A1, A2, A3, A4)
```

and chart variables

```text
(Ctop, D, A1, A3, F2, F3, C),
```

where

```text
Ctop = C1 A1,
F2   = -A1^{-1} A2,
F3   = F3old - D A3 Ctop^{-1},
C    = A4 - A3 A1^{-1} A2.
```

The p.13 product-difference display has the form

```text
[ C1 - I        -F2
  -F3    prod C^(s) - F3 F2 ].
```

Thus the singular residual product is the product of the `C` factors.  The
passive coordinates affect the surrounding regular/off-diagonal terms and the
Jacobian accounting, but they do not change the finite readout of the
selected-entry residual product from the stored `C` family.

## Existing Reduced Datum

The existing Case 2 selected-entry datum builds a retained-passive
nonredundant coordinate object from the successor selected-entry coordinates
`yNext` and the residual-column equivalence `eNext`.

Its reduced base fixes the passive fields:

```text
A1passive = 1,
F2        = 0,
A3passive = 0,
Ctop      = 1,
F3        = 0.
```

Only the residual `C` field is selected-entry-dependent, via the two-edge
post-pivot free factor family.  This is enough for the existing
chart-produced selected-entry finite-integral wrappers, but it is not a full
passive coordinate chart.

## Passive-Parameter Enlargement

The new finite datum keeps exactly the same residual `C` field and supplies
the passive fields as independent parameters:

```text
case2PostPivotSelectedEntryRetainedPassiveDataWithPassive
  A1passive F2 A3passive Ctop F3 yNext eNext
```

Its fields are:

```text
A1passive := A1passive
F2        := F2
A3passive := A3passive
C         := selected-entry successor residual C family
Ctop      := Ctop
F3        := F3
```

The retained-passive determinant chart is the conjunction

```text
IsUnit Ctop.det
and
forall p, IsUnit (A1passive p).det.
```

Therefore the determinant-chart theorem needs exactly those supplied unit
hypotheses:

```text
hCtop : IsUnit Ctop.det
hA1passive : forall p, IsUnit (A1passive p).det
```

Endpoint transport only reindexes the endpoint domains.  Since it does not
alter the determinant fields, the same determinant-chart proof transports.

## Residual Readout Check

The residual-factor product theorem for the reduced datum says that after
endpoint transport, the residual factor product of the stored `C` family is
the selected-entry center-coordinate chart matrix:

```text
residualFactorProduct C (Fin.last 2) 0
  =
matrix (fun c =>
  SelectedEntrySignedBox.CenterCoord.chartMap pivot yNext
    (case2 residual-coordinate equivalence c)).
```

The passive-parameter datum has the same `C` field as the reduced datum.  Hence
the same equality follows by unfolding the passive-parameter datum and using
the existing reduced theorem.

This proves the important finite check:

- the selected-entry residual readout is independent of the supplied passive
  fields;
- passive determinant hypotheses are only `Ctop` and `A1passive`;
- no passive field is smuggled into the selected-entry residual exponent.

## Lean Verification

New Lean declarations:

```text
case2PostPivotSelectedEntryRetainedPassiveDataWithPassive
case2PostPivotSelectedEntryRetainedPassiveDataWithPassive_detChart
case2PostPivotSelectedEntryRetainedPassiveDataWithPassive_endpointTransport_detChart
case2PostPivotSelectedEntryRetainedPassiveDataWithPassive_endpointTransport_residualFactorProduct_eq_successorSelectedEntryCenterCoordChartMapMatrix
```

Focused build passed from `lean/`:

```text
scripts/lb DLNFibre.DLN.Aoyagi.RetainedPassiveCase2SelectedEntryChartBridge
```

The replayed warnings are in imported
`ProductReductionStepRegularDensity.lean`, not in the new declarations.

## Kill Conditions

- Reject any use of this datum as a source-image or source-coverage theorem.
- Reject any use of this datum to replace
  `m.restrict Sdet = Measure.map chart weightedBox`.
- Reject any source-prior or raw-Haar claim that does not add a source map,
  local inverse or image theorem, and Jacobian density accounting.
- Reject any statement in which the selected-entry residual readout depends on
  the passive fields.
- Reject any determinant-chart proof that omits the supplied `Ctop` and
  `A1passive` unit hypotheses.
- Keep normal-crossing-to-RLCT extraction as the cited analytic boundary.

## Next Boundary

This bridge supplies a finite passive-parameter coordinate object.  The next
source-measure payoff still needs a genuine passive-coordinate domain and one
of the following, stated explicitly:

- a source map with local inverse and image or coverage theorem;
- a measure pushforward with passive Jacobian density;
- an external source-prior comparison or density theorem.

Until that is proved, the selected-entry signed-box source measure remains
chart-produced rather than an original/full determinant-chart source prior.
