# Pen-and-paper reproduction - Case 2 constructed Cprime Q/P

Status: checked finite pivot-first matrix algebra.

This note records the displayed Case 2 `Q/P` product identity after taking
`Cprime` itself as a free chart-coordinate following factor.

## Source

Aoyagi PDF pp. 19-22 displays the local Case 2 operations

```text
C' = Q^-1 C,
D'' = D_chart Q,
P * weighted(D_chart) * C = weighted(D''') * C'.
```

The previous checkpoint formalised the reverse coordinate direction

```text
C := Q * Cprime,
Q^-1 * C = Cprime.
```

## Calculation

Let `Csrc := Q*Cprime` be the old pivot-first following factor constructed
from the free chart coordinate `Cprime`.  The already-proved displayed
`Q/P` identity gives, for a quotient row operation `P`,

```text
(P * weighted source-substituted block) * Csrc
  = (weighted D''') * (Q^-1 * Csrc).
```

Substituting `Q^-1*Csrc=Cprime` gives

```text
(P * weighted source-substituted block) * (Q*Cprime)
  = (weighted D''') * Cprime.
```

In Lean this is expressed over the displayed top-left pivot, source-chart
substitution block, supplied successor recurrence weights, and paper-named
`D'''`.

## Lean Targets

```text
exists_case2DisplayedQP_mul_arbitraryPivotFirstFollowingFactor_of_flat_weights
CorrectedCase2NewLabelCertificate.exists_case2DisplayedQP_mul_freeFollowingFactor_of_postData
Case2DisplayedSuppliedChartFamilyBoundary.sourceDisplayedQP_constructedCprime_paperQP
```

## Nonclaims

- No total source-coordinate following function `ℕ -> τ -> R` is constructed
  from `Cprime`.
- No source-produced next `C'^(S+1)` is constructed.
- No recurrence or exponent post-data is produced from coordinates.
- No successor chart family, chart coverage, coordinate regularity,
  transition invariant, Jacobian arithmetic, normal crossings, RLCT
  extraction, arbitrary-pivot coverage, terminal relabeling, or printed-vector
  repair is proved.
