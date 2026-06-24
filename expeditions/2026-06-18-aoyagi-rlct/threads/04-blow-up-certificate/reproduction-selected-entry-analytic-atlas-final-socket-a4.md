# Reproduction - Selected-entry analytic atlas final socket

Date: 2026-06-24.

Status: pen-and-paper projection check and Lean target record.  This note
contains no new analytic atlas construction and no new finite exponent
calculation.

## Question

The previous boundary introduced

```text
SelectedEntryAnalyticAtlasBoundary
```

as a supplied analytic-atlas contract carrying a
`AoyagiNormalCrossingChartCertificate` plus fields for coverage, chart
regularity, transition regularity, unit regularity, analytic Jacobian
compatibility, source production, and branch termination.

The next formalisation question is downstream and much smaller:

```text
If such a supplied boundary is available, can its carried chart certificate be
fed into the existing A0/A6 Theorem 2 chart-final socket?
```

The intended answer is yes, but only as a projection/adapter.  The theorem must
not use the existence of the supplied boundary to infer the extraction
hypothesis, finite Theorem 2 exponent formulas, active-ratio lower bounds,
chart counts, source production, or any analytic regularity theorem.

## Existing Lean Sockets

The supplied analytic-atlas boundary has the shape

```text
SelectedEntryAnalyticAtlasBoundary
  Param R Coverage ChartRegular TransitionRegular UnitRegular
    AnalyticJacobianCompatible SourceProduction BranchTermination
```

with a field

```text
B.chartCertificate :
  AoyagiNormalCrossingChartCertificate Param R
```

and the definitional projection

```text
B.exponentData = B.chartCertificate.exponentData.
```

The chart-final Theorem 2 socket is

```text
AoyagiTheorem2SuppliedChartFinalBoundary
  Cnc L ell H r cuts m data lambda poleOrder.
```

It is already intentionally conditional.  Its fields are exactly:

- selected-width provenance
  `m = aoyagiSelectedReducedWidths H r cuts`;
- the cited normal-crossing extraction input
  `Cnc.ExtractionHypothesis lambda poleOrder`;
- the finite Theorem 2 exponent formula boundary
  `AoyagiTheorem2FiniteExponentFormulaHypothesis
    Cnc.exponentData L ell H r m data`.

The existing active-ratio/chart-count constructors are useful downstream
ways to build the finite formula boundary.  They should not be confused with
data supplied by `SelectedEntryAnalyticAtlasBoundary` itself.

## Pen-and-paper Projection

Let

```text
B : SelectedEntryAnalyticAtlasBoundary ...
```

and write

```text
Cnc = B.chartCertificate,
D = B.exponentData.
```

By definition,

```text
D = Cnc.exponentData.
```

Suppose the following are supplied:

```text
hselected :
  m = aoyagiSelectedReducedWidths H r cuts

hNC :
  Cnc.ExtractionHypothesis lambda poleOrder

hFormula :
  AoyagiTheorem2FiniteExponentFormulaHypothesis
    D L ell H r m data.
```

Because `D` is definitionally `Cnc.exponentData`, `hFormula` is exactly the
finite formula field expected by

```text
AoyagiTheorem2SuppliedChartFinalBoundary
  Cnc L ell H r cuts m data lambda poleOrder.
```

No mathematical calculation happens here.  The proof is:

1. unfold the projection from `B` to `B.chartCertificate.exponentData`;
2. fill the three fields of `AoyagiTheorem2SuppliedChartFinalBoundary`;
3. return the supplied final boundary for `B.chartCertificate`.

If desired, a later wrapper may replace `hFormula` by the existing active-ratio
and chart-count hypotheses.  That wrapper is still only finite arithmetic
plumbing: it does not become atlas production or extraction.

## What This Does Not Prove

This bridge does not prove that the analytic-atlas boundary exists.

It also does not prove:

- chart coverage;
- chart or transition regularity;
- unit nonvanishing on analytic domains;
- analytic Jacobian or volume-form compatibility;
- source production of `Csucc`, `Cterm`, `C'^(S+1)`, or suffix products;
- branch termination;
- the extraction hypothesis `B.chartCertificate.ExtractionHypothesis`;
- finite Theorem 2 exponent formulas;
- active-ratio lower bounds or chart-count/order facts;
- pole order or RLCT without the explicit final-socket hypotheses.

The generic boundary predicates can technically be instantiated by
`fun _ => True`.  Their nontriviality is therefore a project discipline and
future instantiation requirement, not a Lean theorem enforced by this adapter.

The theorem is safe only if named as a final-socket adapter or projection from
a supplied boundary.  It should not be named as atlas production, source
production, normal crossings, or RLCT.

## Lean Target

Add a separate downstream module rather than importing the selected-entry file
into the older final assembly module:

```text
DLNFibre.DLN.Aoyagi.SelectedEntryAnalyticAtlasFinalBridge
```

with the first theorem inside namespace
`SelectedEntryAnalyticAtlasBoundary`:

```text
theorem theorem2SuppliedChartFinalBoundary_of_selectedWidths_eq_reduced_of_extractionHypothesis_of_finiteExponentFormula
```

It should take

```text
B : SelectedEntryAnalyticAtlasBoundary ...
```

and return

```text
AoyagiTheorem2SuppliedChartFinalBoundary
  B.chartCertificate L ell H r cuts m data lambda poleOrder.
```

The finite formula hypothesis should be stated over `B.exponentData`, so the
theorem reads as consuming the supplied analytic-atlas boundary while Lean
reduces that data to `B.chartCertificate.exponentData`.

The module may later add active-ratio and ratio-count convenience wrappers,
but only after this boring projection has landed and been checked.

## Check

The only definitional equality required is

```text
B.exponentData = B.chartCertificate.exponentData.
```

This was already supplied by
`SelectedEntryAnalyticAtlasBoundary.exponentData_eq`, and it is `rfl`.

Thus this slice is formalisation-ready once the independent checker confirms
that the file is in the Aoyagi worktree and the theorem wording remains
conditional.
