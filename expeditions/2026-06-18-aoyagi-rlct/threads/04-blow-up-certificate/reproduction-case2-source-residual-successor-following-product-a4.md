# Pen-and-paper reproduction - A4 Case 2 source residual successor following product

Status: reproduced, xhigh-checked, and formalised.

## Source Anchor

Aoyagi PDF pp. 19-22, Case 2.  This is still the displayed local product
`D''' * C'` after forming `C' = Q^-1 C`.

## Reproduction

Existing Lean already proves the lower-row product in source-residual/source
following notation:

```text
lowerRows(D''' * C')
  =
case2SourceResidualBlock(postPivotSourceResidual)
  *
case2SourceFollowingFactor(S,J+1,C).
```

The formula-level successor following factor is

```text
Csucc(j,a) =
  if j = J+1 then top row of (Q^-1 C) at a
  else C(j,a).
```

The following-factor restriction at `(S,J+1)` uses only post-pivot rows
`j >= J+2`, so it ignores the replaced row `J+1`:

```text
case2SourceFollowingFactor(S,J+1,Csucc)
  =
case2SourceFollowingFactor(S,J+1,C).
```

Substituting this equality gives the source-pair notation:

```text
lowerRows(D''' * C')
  =
case2SourceResidualBlock(postPivotSourceResidual)
  *
case2SourceFollowingFactor(S,J+1,Csucc).
```

## Lean Name

```text
case2DisplayedPaperDppp_mul_Cprime_postPivot_eq_sourceResidualBlock_successorFollowingFactor
```

## Boundary Checks

- This is a bare lower-row formula adapter.
- No `hnext` or next-center nonemptiness is included.
- The residual representative and `Csucc` remain formula-level data, not
  chart-produced successor coordinates.
- No lower-row diagonal or weighted source-chart handoff is added in this
  slice.

## Kill Conditions

- Do not call this chart production, successor chart-family construction, or a
  full successor `C'^(S+1)`.
- Do not infer pivot-row product, old-top rows, suffix product, arbitrary-pivot
  coverage, transition invariance, Jacobian arithmetic, normal crossings, pole
  order, termination, RLCT, or repair of the printed Case 2 vector mismatch.
- Do not use the Lehalleur-Rimanyi/quiver paper or quiver Lean as evidence.
