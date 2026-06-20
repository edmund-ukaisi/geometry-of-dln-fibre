# A4 Case 2 Displayed Cleared-Block Vacuity

Status: reproduced the finite lower-right vacuity of the already-cleared
displayed Case 2 pivot block.  This is not the full terminal branch
construction.

## Source Anchor

On PDF pp. 21-22, after the displayed Case 2 `Q/P` calculation, Aoyagi writes
the cleared block `D'''_J` and then states that when the next continuation
condition fails, `D'''_J` is a one-row block `(1,0,...,0)` or its transpose.

The previous checkpoints proved the finite index content:

```text
not (J+2 <= M(S+1))
  => one displayed pivot-complement side is empty.
```

Therefore any lower-right matrix indexed by the displayed pivot-complement
row and column types is vacuous, hence equal to zero over a type with zero.

## Pen-And-Paper Reproduction

After the displayed pivot-first `Q/P` calculation, the cleared pivot block has
the generic form

```text
[ 1  0 ]
[ 0  D ]
```

where

```text
D = D_lower_right - x*y
```

is indexed by the displayed pivot-complement row and column types.  If the
next continuation bound fails, one of these complement types is empty.  Hence
there is no lower-right entry to determine, and the matrix `D` is equal to the
zero matrix in its index type.

Thus the already-cleared block is equal to the pivot-only cleared block

```text
[ 1  0 ]
[ 0  0 ].
```

This is exactly the lower-right vacuity part of Aoyagi's terminal prose.  It
does not decide the row-vs-column presentation or construct the next
following factor.

## Boundaries

- This is stated in pivot-first coordinates for the displayed top-left Case 2
  chart.
- It uses the already-cleared block expression
  `weightedPivotClearedBlock (D - x*y)`; it does not construct the `Q/P`
  calculation itself.
- It does not prove the full source statement
  `D'''_J = (1,0,...,0)` or `D'''_J = (1,0,...,0)^t`.
- It does not construct `C'^(S+1)`, build the `S+1` recurrence/exponent state,
  prove chart coverage, coordinate regularity, Jacobian/volume arithmetic,
  normal crossings, RLCT extraction, termination, transition invariance, or
  repair of the printed Case 2 vector mismatch.
