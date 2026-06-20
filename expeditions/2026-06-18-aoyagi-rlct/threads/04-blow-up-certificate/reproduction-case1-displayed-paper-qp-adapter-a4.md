# A4 Case 1(2) Displayed Paper `Q/P` Adapter

Status: reproduced a paper-named adapter for Aoyagi's displayed top-left
Case 1(2) `Q/P` calculation.

## Source Situation

In Aoyagi Case 1(2), the selected chart denominator is the displayed top-left
row-strip entry

```text
u = u_(S,J+1).
```

The displayed chart normalizes the Case 1 row strip by

```text
d_ij = u d'_ij,       J+1 <= i <= J+J1,
                      J+1 <= j <= M^(S+1),
d'_(J+1,J+1) = 1,
u_(s,k) = u u'_(s,k).
```

Only the row strip is divided by `u`; lower residual rows are not divided. The
hidden old-variable substitution contributes the same selected factor to the
lower row weights instead.

Aoyagi then writes a regular column operation `Q`, transforms the following
factor by

```text
C' = Q^-1 C,
```

and applies a regular row operation `P` with quotient entries

```text
-(b'_i / b'_(J+1)) d''_(i,J+1).
```

In Lean this division is represented by quotient witnesses
`b'_i = q_i b'_(J+1)`, not by inverting or cancelling `b'_(J+1)`.

## Paper-Named Blocks

Let `A` be the already normalized source-coordinate residual block.  In the
displayed chart:

```text
A_(J+1,J+1) = 1.
```

After putting the displayed pivot row and column first, write

```text
A^pivot = [ 1  y
            x  D ].
```

The paper operations are:

```text
Q      = [ 1  -y
           0   I ],

Q^-1   = [ 1   y
           0   I ],

D''    = A^pivot Q,

C'     = Q^-1 C,

D'''   = [ 1        0
           0  D - x y ].
```

The block `D'''` is the finite matrix called `blockdiag(1,D_(J+1))` in the
source display. Lean represents it as `weightedPivotClearedBlock (D - x*y)`.

## Weighted Source Identity

The weighted source block uses the old source weights on the left:

```text
diag(sourceWeight) * rowStripSource.
```

The already reproduced Case 1 row-strip identity rewrites this, in pivot-first
coordinates, as

```text
diag(postWeight) * A^pivot.
```

The selected variable is counted exactly once: on strip rows it comes from
`d_ij = u d'_ij`, and below the strip it comes from
`u_(s,k)=u u'_(s,k)`.

## Product Identity

With quotient witnesses for `P`, the local displayed calculation is:

```text
P * diag(sourceWeight) * rowStripSource * C
  =
diag(postWeight) * D''' * C'.
```

This is exactly the existing finite pivot-first source-order identity, but now
with the paper names `Q`, `Q^-1`, `D''`, `C'`, and `D'''` exposed at the
source-coordinate interface.

## Caveats

- The normalized chart block `A` and pivot condition are supplied as
  source-coordinate data.
- The selected-old pullback and recurrence/exponent post-data remain supplied.
- The hidden old label `(s0,k0)` is not derived from the `Unit` center token.
- No affine chart construction, atlas coverage, regularity proof, Jacobian,
  normal crossings, RLCT extraction, or transition invariant is proved.
- No non-displayed pivot chart or arbitrary-pivot coverage is asserted.
