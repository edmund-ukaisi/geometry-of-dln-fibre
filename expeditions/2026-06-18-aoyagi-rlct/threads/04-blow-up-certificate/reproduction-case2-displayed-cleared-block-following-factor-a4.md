# A4 Case 2 Displayed Cleared-Block Following-Factor Absorption

Status: reproduced the block multiplication consequence of a pivot-only
cleared block.  This is not the construction of Aoyagi's `C'^(S+1)`.

## Source Anchor

On PDF pp. 21-22 Aoyagi reaches a cleared displayed Case 2 pivot block and,
in the terminal case, rewrites the product into the inductive form with `S`
increased by one.  The previous Lean checkpoint proved only that the
lower-right part of the already-cleared displayed pivot block is zero when
the next continuation bound fails.

This checkpoint records the next elementary matrix multiplication fact: once
the cleared pivot block is pivot-only, multiplying it by a following factor
keeps the top row and kills the lower block.

## Pen-And-Paper Reproduction

The pivot-only cleared block has the block form

```text
[ 1  0 ]
[ 0  0 ].
```

Write a following factor in the same pivot-first row split as

```text
[ C_top  ]
[ C_tail ].
```

Then multiplication gives

```text
[ 1  0 ] [ C_top  ]   [ C_top ]
[ 0  0 ] [ C_tail ] = [ 0     ].
```

The displayed Case 2 specialization combines this generic identity with the
lower-right vacuity theorem:

```text
weightedPivotClearedBlock (D - x*y) = weightedPivotClearedBlock 0.
```

Hence, under displayed pivot validity and failed next continuation,

```text
weightedPivotClearedBlock (D - x*y) * [C_top; C_tail]
  = [C_top; 0].
```

## Boundaries

- The result is in pivot-first coordinates.
- The following factor is already supplied in the pivot-first vertical split.
- The failed-continuation hypothesis is the old-coordinate post-pivot bound
  `not (J+2 <= M(S+1))`; this is the shifted form after the displayed pivot at
  `(J+1,J+1)`.
- This does not identify `[C_top;0]` with Aoyagi's next `C'^(S+1)` data.
- It does not construct the full `D'''_J` terminal branch, choose row-vs-column
  presentation, build an `S+1` recurrence/exponent state, prove chart
  production or coverage, compute Jacobians, prove normal crossings, extract
  RLCT, prove termination, prove transition invariance, or repair the printed
  Case 2 vector mismatch.
