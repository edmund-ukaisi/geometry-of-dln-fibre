# Pen-and-paper reproduction - Case 2 constructed source following factor

Status: checked finite source-coordinate bookkeeping.

This note records the source-coordinate representative for the already-proved
displayed Case 2 reverse following-factor direction.

## Source

Aoyagi PDF pp. 19-22 uses the displayed Case 2 coordinate operations

```text
C' = Q^-1 C,
D'' = D_chart Q,
P * weighted(D_chart) * C = weighted(D''') * C'.
```

The previous checkpoint constructed the old following factor only in
pivot-first coordinates:

```text
Csrc = Q*Cprime.
```

Here `Csrc` is indexed by the finite displayed residual-column domain after
putting the pivot column first.  To use the source-coordinate following-factor
API, we need a total function on source columns.

## Construction

Let `Rcols` be the old Case 2 residual-column set and let

```text
e : Unit + pivotComplement col ~= Rcols
```

be the pivot-first index equivalence used by the existing displayed API.
Given a pivot-first matrix

```text
Csrc : (Unit + pivotComplement col) -> tau -> R,
```

define the total source-coordinate representative

```text
C(j,a) =
  Csrc(e^-1(j),a)  if j in Rcols,
  0                otherwise.
```

The source following-factor restriction looks only at columns in `Rcols` and
then reindexes them through `e`.  Therefore, for every pivot-first residual
column `i` and following index `a`,

```text
sourceFollowingFactor(C)(i,a)
  = C(e(i),a)
  = Csrc(e^-1(e(i)),a)
  = Csrc(i,a).
```

So restriction recovers the supplied pivot-first matrix exactly:

```text
case2DisplayedSourceFollowingFactor(C) = Csrc.
```

Taking the special supplied matrix `Csrc = Q*Cprime` gives

```text
case2DisplayedPaperCprime(C)
  = Q^-1 * case2DisplayedSourceFollowingFactor(C)
  = Q^-1 * (Q*Cprime)
  = Cprime.
```

The supplied-boundary `Q/P` identity can then be written with the old following
factor represented by the total source-coordinate function `C`:

```text
(P * weighted source-substituted block) * sourceFollowingFactor(C)
  = (weighted D''') * Cprime.
```

## Lean Targets

```text
case2DisplayedConstructedSourceFollowingFactor
case2DisplayedSourceFollowingFactor_constructed
case2DisplayedPaperCprime_of_constructedSourceFollowingFactor
Case2DisplayedSuppliedChartFamilyBoundary.sourceDisplayedQP_constructedSourceFollowingFactor_paperQP
```

## Kill Conditions

- If `case2DisplayedSourceFollowingFactor` reads columns outside the residual
  column set, the zero-extension proof would be insufficient.
- If the pivot-first equivalence is not inverse to the residual-column
  reindexing used by `case2DisplayedSourceFollowingFactor`, the recovery
  equation would fail.
- If `Q^-1*Q=I` were not available over the displayed pivot-first domain, the
  constructed-source `Cprime` recovery would not follow.

## Nonclaims

- No successor chart family is constructed.
- No full next `C'^(S+1)` is source-produced.
- No recurrence or exponent post-data is produced from coordinates.
- No chart coverage, coordinate regularity, transition invariant, Jacobian
  arithmetic, normal crossings, RLCT extraction, arbitrary-pivot coverage,
  terminal relabeling, or printed-vector repair is proved.
