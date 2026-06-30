# Reproduction - A2 selected-entry all-pivot transition regular data

Date: 2026-06-29.

Status: controller pen-and-paper reproduction before review.

## Question

The all-pivot selected-entry finite chart family now has a shared
universal-domain context, source coverage, chart/unit regularity, and
Jacobian/volume data.  Can the already formalized finite selected-entry overlap
formula be packaged as `SelectedEntryAnalyticTransitionRegularData` over the
same shared context?

Answer: yes, at exactly the transition-regularity scope required by the
interface.  The transition from source pivot `p` to target pivot `q` is defined
on the open algebraic overlap where the target normalized coordinate in the
source chart is nonzero.  The transition map is the usual selected-entry
coordinate change:

```text
u' = u * denom
r'_i = normalized_i / denom
```

where

```text
denom = selectedEntryNormalizedMap p residual q.
```

## Calculation

Fix a finite center, a nonempty witness `hcenter`, an enumeration

```text
chartEquiv : Fin center.card ≃ center,
```

and source/target chart indices `source target : Fin center.card`.  Write

```text
p = chartEquiv source,
q = chartEquiv target.
```

For a source chart point

```text
x : FormalChartPoint p,
```

the visible residual extension is

```text
residual = chartPointResidual p x.
```

The transition denominator is

```text
denom(x) = selectedEntryNormalizedMap p.1 residual q.1.
```

The transition domain is

```text
{x | denom(x) != 0}.
```

The target chart point is

```text
allPivotTransitionPoint source target x
  = (x.1 * denom(x),
      fun i_in_center_erase_q =>
        selectedEntryNormalizedMap p.1 residual i / denom(x)).
```

This is definitionally the existing finite transition point

```text
selectedEntryCenterSqFormalJacobianChartFamilyCertificate
  .sourceChartTransitionPoint hcenter chartEquiv source target
    x.1 residual.
```

The existing finite theorem then gives chart-map preservation on the overlap:

```text
chartMap target (transition source target x) =
chartMap source x.
```

The final rewrite uses the visible-residual identity

```text
sourceChartPoint p x.1 (chartPointResidual p x) = x.
```

## Continuity Check

The denominator is continuous in the source chart point.  If `q = p`, it is
the constant function `1`; otherwise it is the source residual coordinate for
`q`.

Each numerator

```text
selectedEntryNormalizedMap p.1 residual i
```

is likewise either the constant `1`, when `i = p`, or a visible residual
coordinate.  Therefore each quotient numerator/denominator is continuous on
the nonzero-denominator transition domain.  Product and pi-continuity then give
continuity of the whole target chart point on that domain.

The chart domains in the shared all-pivot context are `Set.univ`, so landing
and domain-subset fields are immediate.

## Lean Target

Add:

```text
lean/DLNFibre/DLN/Aoyagi/SelectedEntryAllPivotTransitionRegularData.lean
```

with:

```text
allPivotTransitionDenom
allPivotTransitionDomain
allPivotTransitionPoint
continuous_allPivotTransitionDenom
continuous_allPivotTransitionNumerator
continuousOn_allPivotTransitionPoint
selectedEntryAllPivotAnalyticTransitionRegularData
selectedEntryAllPivotAnalyticTransitionRegular
```

## Source Fidelity

Aoyagi PDF pp. 15-22 support the chosen-pivot selected-entry coordinate
substitution.  The all-pivot transition and renormalization record is
expedition-built finite overlap bookkeeping over the already formalized
selected-entry microcertificate transition lemmas.  It does not assert a
produced recursive source branch or a full analytic atlas producer.

## Kill Conditions

- The transition domain required by the analytic interface cannot be the
  normalized-target-coordinate nonzero overlap.
- `sourceChartTransitionPoint` is not definitionally the proposed target chart
  point after extending the visible residual coordinates.
- The finite chart-map preservation theorem cannot rewrite the source chart
  point back to the original chart point.
- Continuity of the quotient coordinates cannot be proved from the nonzero
  denominator condition.

## Nonclaims

This does not prove source production, branch termination, source-prior
transport, determinant-chart Haar transport, a full supplied analytic atlas
producer, normal-crossing extraction, pole order, or RLCT.
