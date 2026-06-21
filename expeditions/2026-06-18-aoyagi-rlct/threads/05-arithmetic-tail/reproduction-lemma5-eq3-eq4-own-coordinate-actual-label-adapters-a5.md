# Pen-and-paper reproduction - Lemma 5 equations (3)/(4) own-coordinate actual-label adapters

Status: checked adapter slice.

This note records a small source-label packaging step.  Equation `(5)` already
had wrappers proving both the own-coordinate value `T(S)=k-1` and
`actualWidthLabel`.  Equations `(3)` and `(4)` had the two halves separately.
This slice combines the existing halves without changing the mathematical
boundary.

## Equation (4)

The supplied equation `(4)` piecewise certificate and repaired guards already
prove

```text
T(C.point p - 1) = Htilde_p.
```

The label relation is

```text
k = Htilde_p + 1.
```

Therefore

```text
T(C.point p - 1) = k - 1.
```

The existing actual-label bridge proves

```text
actualWidthLabel L n (C.point p - 1) k
```

from the same selected-width hypotheses, source range, and actual-width
compatibility at that source layer.  Combining these two conclusions gives
the adapter theorem.

## Equation (3)

The supplied equation `(3)` piecewise certificate, the interior guard
`a < ell`, and the explicit slack hypothesis already prove

```text
T(C.point 1 - 1) = Htilde'_1.
```

The label relation is

```text
k = Htilde'_1 + 1.
```

Therefore

```text
T(C.point 1 - 1) = k - 1.
```

The existing source-selected actual-label bridge, still requiring the explicit
one-unit slack and actual-width compatibility, proves

```text
actualWidthLabel L n (C.point 1 - 1) k.
```

## Lean Targets

```text
aoyagiLemma5Eq4_piecewise_ownCoordinate_actualWidthLabel_of_widthCompatibility
aoyagiLemma5Eq3_piecewise_ownCoordinate_actualWidthLabel_of_sourceSelected_slack
```

## Nonclaims

- No construction or existence proof for the displayed vectors in equations
  `(3)` or `(4)`.
- No proof of actual-width compatibility from Definition 3.
- No removal of equation `(3)`'s explicit slack hypothesis.
- No terminal `tilde t=0`, vector admissibility, chart sequence, Lemma 5
  order count, pole order, normal crossings, or RLCT extraction.
