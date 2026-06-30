# Reproduction - A2 Case 2 selected-entry Schur cleanup

Date: 2026-06-29.

Status: pen-and-paper reproduction before banking Lean.

## Question

Aoyagi's Case 2 selected-entry chart rewrites the residual block by selecting
the displayed top-left entry and then applying one right column operation and
one weighted left row operation.  What is the exact finite matrix algebra, and
which parts can be recorded as Lean wrappers without claiming analytic atlas
or RLCT content?

## Source anchor

Aoyagi PDF pp. 19-22:

- p. 19 sets the Case 2 center and the displayed top-left selected-entry
  substitution.
- p. 20 defines the column operation `Q` and the block `D'' = E Q`.
- p. 21 defines `C' = Q^-1 C`, the weighted row operation `P`, and the
  cleared block `D'''`.
- p. 22 continues or stops according to the residual block size.

This reproduction uses only Aoyagi's paper.  It is independent of the quiver
paper and of quiver-based Lean material.

## Calculation

Put the selected residual block in pivot-first notation.  Aoyagi's displayed
selected-entry chart has

```text
D = u E,
E = [[1, a],
     [c, Z]].
```

Here `a` is the pivot row away from the pivot, `c` is the pivot column below
the pivot, and `Z` is the lower-right residual subblock.  The equality
`D = u E` is exactly the selected-entry substitution:

```text
x_p = u,
x_q = u r_q   for q != p.
```

The right column operation is

```text
Q = [[1, -a],
     [0,  I]].
```

Multiplying out gives

```text
E Q
  = [[1, a],     [[1, -a],
     [c, Z]]  *   [0,  I]]

  = [[1, 0],
     [c, Z - c a]].
```

Thus the lower-right block after `Q` is the Schur expression `Z - c a`.
In Lean this is the pivot-first identity

```text
pivotFirstMatrix row col E * pivotQ (pivotFirstY row col E)
  = pivotPostQBlock (pivotFirstX row col E)
      (pivotFirstY row col E) (pivotFirstD row col E).
```

Now let the row weights after absorbing the selected variable be

```text
B = diag(b0, b_i),
b_i = q_i b0.
```

For

```text
P = [[1,        0],
     [-q_i c_i, I]],
```

we get

```text
P B (E Q)
  = B [[1, 0],
       [0, Z - c a]].
```

The lower-left entry is

```text
-(q_i c_i) b0 + b_i c_i = 0
```

using `b_i = q_i b0`, and the lower-right entries stay
`b_i (Z - c a)_ij`.

## Corrected `u` convention

The clean source-side formula is obtained by absorbing the selected variable
into the row weights:

```text
D = u E,
B' = u B_old,
P B_old D Q = B' [[1, 0],
                  [0, Z - c a]].
```

Equivalently, if `B` already denotes the post-substitution diagonal weights,
then

```text
P B E Q = B [[1, 0],
             [0, Z - c a]].
```

There is no additional global `u` after this absorption.  Read with p. 20's
`b'_i = u b_i`, any p. 21 display that appears to keep another outside `u`
must be interpreted through this absorption convention.

## Lean target

Record thin source-facing wrappers around existing finite matrix identities:

```text
case2SourceSelectedSubstitutionBlockOfMem_eq_mul_normalized
pivotFirstMatrix_mul_pivotQ_eq_pivotPostQBlock
case2SourceSelectedNormalizedBlockOfMem_mul_pivotQ
case2DisplayedPaperDchart_mul_Q_eq_pivotPostQBlock
```

The weighted left cleanup is already present as finite algebra:

```text
weightedPivotBlockRowOp_mul_diagonal_mul_pivotPostQBlock
weightedPivotBlockRowOp_mul_diagonal_mul_pivotPreQBlock_mul_pivotQ
weightedPivotBlockRowOp_mul_diagonal_mul_pivotFirstMatrix_mul_pivotQ
weightedPivotBlockRowOp_mul_oldDiagonal_mul_smul_pivotPreQBlock_mul_pivotQ
```

The last theorem is the corrected old-diagonal source-side statement: it
absorbs `u` into the row weights rather than adding a second global `u`.

## Kill conditions

- A theorem claims analytic atlas coverage, chart-domain regularity, transition
  regularity, Jacobian compatibility, source-prior transport, normal crossings,
  pole order, or RLCT.
- A theorem treats the one displayed pivot chart as all-pivot source coverage.
- A theorem adds an extra global `u` after replacing old weights by
  post-substitution weights.
- A theorem identifies the lower-right Schur block with the next residual
  block without the separate continuing-branch index and size hypotheses.
