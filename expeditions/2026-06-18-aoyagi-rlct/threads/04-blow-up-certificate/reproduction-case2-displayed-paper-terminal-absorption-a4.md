# A4 Case 2 Displayed Paper Terminal Absorption

Status: reproduced the source-order notation layer and the zero-row
matrix-entry ideal consequence for displayed Case 2 after failed next
continuation.  This is not a construction of the next-stage object
`C'^(S+1)`.

## Source Anchor

On Aoyagi PDF pp. 21-22, after the displayed Case 2 `Q/P` calculation, the
paper considers the terminal situation where the next continuation condition
fails.  In that case the cleared block is described as `(1,0,...)` or its
transpose, and the product is rewritten toward the next `S+1` form.

The earlier Lean checkpoints already proved the finite domain statement:
after the displayed pivot at `(J+1,J+1)`, failure of

```text
J+2 <= M(S+1)
```

empties one lower-right pivot-complement side.

## Pen-And-Paper Reproduction

Write the displayed normalized source block in pivot-first coordinates.  The
column operation is

```text
Q = [1 -y; 0 I],
```

and the transported following factor is

```text
C' = Q^-1 C = [C0; Ctail].
```

After the `P` row operation, the cleared block has the pivot-first form

```text
D''' = [1 0; 0 E].
```

When the next continuation condition fails, one pivot-complement side is
empty.  Hence `E` is the zero lower-right block in Lean's matrix type, and

```text
D''' * C'
  = [1 0; 0 0] [C0; Ctail]
  = [C0; 0].
```

At the level of matrix entries, the zero lower rows contribute no generators.
Thus

```text
< entries([C0;0]) > = < entries(C0) >.
```

The Lean result records exactly this ideal equality for the paper-named
displayed Case 2 objects.  It does not identify `C0` with a complete
source-order `C'^(S+1)` matrix including old top rows, and it does not choose
the row-exhausted versus column-exhausted presentation in Aoyagi's prose.

## Boundaries

- The result is in the displayed top-left Case 2 chart.
- `D_chart`, `Q`, `Q^-1`, `D''`, `C'`, and `D'''` are paper-facing names for
  already formalized finite matrix expressions.
- The stopped-continuation hypothesis is the old-coordinate post-pivot bound
  `not (J+2 <= prefixMinNat n (S+1))`.
- The ideal equality drops zero rows only after multiplying by the transformed
  following factor `C' = Q^-1 C`.
- This does not construct `C'^(S+1)`, source chart coverage, arbitrary-pivot
  charts, transition regularity, recurrence or exponent post-data from
  coordinates, Jacobian/volume arithmetic, normal crossings, RLCT extraction,
  termination, transition invariance, or repair the printed Case 2 vector
  mismatch.
