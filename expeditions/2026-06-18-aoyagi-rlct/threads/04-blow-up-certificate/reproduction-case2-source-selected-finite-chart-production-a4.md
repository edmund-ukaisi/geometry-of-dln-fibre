# Reproduction - A4 Case 2 source-selected finite chart production

Date: 2026-06-24.

Status: Lean formalised; focused/full build, sorry audit, and xhigh review
passed.

## Source Anchor

Aoyagi PDF pp. 19-21 uses the Case 2 residual-block center

```text
d_ij = 0,    J+1 <= i <= M(S),    J+1 <= j <= M^(S+1),
```

and displays the selected-entry chart at the top-left residual pivot.  The
Lean all-pivot finite selected-entry certificate ranges over every residual
entry in this finite center, while the source-selected chart map is the same
selected-entry formula for a supplied pivot in that center.

This slice is only finite source-coordinate production for the residual-block
center values.  It is not analytic atlas coverage and does not assert that
Aoyagi prints non-top-left source charts.

## Reproduction

Let

```text
E = case2ResidualBlockPivotEntries n S J
```

and let

```text
value : E -> K
```

be a finite residual-block center value.

The selected-entry chart with pivot `p in E` has source-selected formula

```text
x_p = u,
x_q = u * residual_q    for q != p.
```

There are two cases.

### Zero value

If `value q = 0` for every `q in E`, choose any pivot `p in E`, take

```text
u = 0,
residual_q = 0.
```

Then

```text
x_p = 0 = value p,
x_q = 0 * 0 = 0 = value q.
```

The continuation hypotheses supply `E.Nonempty`, so an arbitrary pivot exists.

### Nonzero value

If some `p in E` has `value p != 0`, choose that `p` as pivot and set

```text
u = value p,
residual_q = value q / value p.
```

Then at the pivot,

```text
x_p = u = value p.
```

For `q != p`,

```text
x_q = u * residual_q
    = value p * (value q / value p)
    = value q,
```

using `value p != 0`.

Thus every finite residual-block center value has a source-selected
selected-entry chart representative.  In Lean, the all-pivot chart index is
the inverse image of the selected pivot under

```text
finsetSubtypeChartEquiv E : Fin E.card ~= E,
```

and the ambient residual function extends the erased-center residuals by an
irrelevant value away from `E`.

## Lean Targets

```text
selectedEntryCenterSqFormalJacobianChartFamilyCertificate.exists_sourceChartPoint_chartMap_eq_value
case2ResidualBlockCenterSqFormalJacobianChartFamilyCertificate.exists_sourceSelectedChartMap_eq_value
```

## Boundary

- This is finite selected-entry source-coordinate production for the residual
  center values only.
- It proves no analytic atlas coverage, no open-domain statement, no
  transition regularity, no source production of successor matrices or
  suffixes, no analytic Jacobian/volume theorem, no global normal crossings,
  no pole order, and no RLCT extraction.
- It does not claim that Aoyagi displays non-top-left selected-entry source
  charts.

## Kill Conditions

- Do not use this as analytic chart coverage.
- Do not use this as source production of the next recurrence state.
- Do not conflate finite center-value coverage with a global DLN loss
  normal-crossing certificate.
