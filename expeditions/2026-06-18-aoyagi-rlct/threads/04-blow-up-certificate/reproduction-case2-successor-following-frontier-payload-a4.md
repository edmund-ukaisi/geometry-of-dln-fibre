# Pen-and-paper reproduction - A4 Case 2 successor following frontier payload

Status: reproduced, xhigh-checked, and formalised.

## Source Anchor

Aoyagi PDF pp. 19-22, Case 2.  This checkpoint stays inside the displayed
top-left chart and the already supplied chart-family boundary.  It only adds
the explicit next-center guard to the successor-following lower-row handoff.

## Reproduction

The previous successor-following handoff proves, under `hcont`,

```text
source lower rows =
  successor lower diagonal *
  (post-pivot residual block *
   case2SourceFollowingFactor(S,J+1,Csucc)).
```

For a genuine continuing residual block at the next same stage, add the
separate guard

```text
hnext : J+2 <= prefixMinNat n (S+1).
```

The existing finite arithmetic theorem gives

```text
case2ResidualBlockPivotEntries(n,S,J+1).Nonempty.
```

The finite principalization facts for the displayed current chart center are
unchanged:

```text
u is a transformed center value,
all transformed center values are divisible by u,
span(transformed current center values) = span({u}).
```

Pairing these four items gives the successor-following frontier payload:
next-center nonemptiness, the weighted lower-row handoff in `Csucc` notation,
and current-center principalization.

## Lean Names

```text
ContinuingWeightedSuccFollowingFrontierPayload
sourceChartMap_continuingWeightedSuccFollowingPayload_withFiniteCenterIdeal
```

## Boundary Checks

- This is theorem-only; it does not add another field to
  `SourceChartFrontierBoundaryPackages`.
- The `hnext` guard supplies only next-center nonemptiness.
- The finite ideal facts are still for the current displayed chart center at
  `(S,J)`.
- The lower-row handoff is still formula-level algebra through `Csucc`.
- The LHS is still the old displayed source-following factor `C`, not a chart
  produced successor matrix.

## Kill Conditions

- Do not call this chart production or successor chart-family construction.
- Do not claim a pivot-row product, old-top rows, suffix product, full
  successor `C'^(S+1)`, arbitrary-pivot coverage, transition invariance,
  Jacobian arithmetic, normal crossings, pole order, termination, RLCT, or
  repair of Aoyagi's printed Case 2 vector mismatch.
- Do not use the Lehalleur-Rimanyi/quiver paper or quiver Lean as evidence.
