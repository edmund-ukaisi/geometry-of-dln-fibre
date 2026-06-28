# A2 retained-passive to selected-entry fixed-pivot boundary

Status: controller reproduced after interruption; no Lean target selected.

## Purpose

This note records the current source boundary for trying to remove the
retained-passive selected-entry residual-factor hypothesis.  It checks
Aoyagi's elementary formulas independently of the quiver paper and separates
what the paper supplies from what Lean must still construct.

## Block reduction signs

For

```text
A = [ A1  A2
      A3  A4 ],
```

with `A1` invertible, Aoyagi's Lemma 2 uses left and right triangular
matrices

```text
Q1 = [ E        0
      -A3 A1^-1 E ],

Q2 = [ E -A1^-1 A2
       0 E ].
```

Thus

```text
Q1 A Q2 =
  [ A1 0
    0  A4 - A3 A1^-1 A2 ].
```

The retained-passive signs are therefore

```text
F2 = -A1^-1 A2,
F3 = -A3 A1^-1,
C4 = A4 - A3 A1^-1 A2.
```

In Theorem 3, after the first `S` factors have been reduced and
`A'^(S+1) = (Q2')^-1 A^(S+1)`, the next residual block is again

```text
C^(S+1) = A4' - A3' (A1')^-1 A2',
```

and the accumulated lower-left shear updates in the order

```text
F3'' = F3' - (product_{s=1}^S C^(s)) A3' (C1' A1')^-1.
```

This matches the retained-passive `D * A3 * (C1 * A1)^-1` convention already
used in Lean.

## Product-difference display

Aoyagi's p. 13 display is the literal block identity

```text
P1 (product_s A^(s) - [E_r 0; 0 0]) P2 =
  [ C1 - E_r        -F2
       -F3   product_s C^(s) - F3 F2 ].
```

The displayed lower-right block is not literally `product_s C^(s)`.  Passing
from this literal block to the cleaned generator family

```text
C1 - E_r, F2, F3, product_s C^(s)
```

is an algebraic generator or comparison step, not equality of square sums.

Kill-test: in the scalar case `F2 = F3 = 1` and `product C = 0`, the literal
lower-right block is `-1`, while the cleaned residual block is `0`.  A theorem
that identifies the literal p. 13 square sum with the cleaned square sum is
overclaiming unless it includes the missing comparison/generator argument.

## Case 2 fixed-pivot chart

On Aoyagi pp. 19-22, Case 2 blows up the center

```text
d_ij = 0
```

over the active row and column window and then chooses the displayed chart

```text
d_(J+1,J+1) = u_(S,J+1),
d_ij = u_(S,J+1) d'_ij       for the other entries.
```

Equivalently, the post-pivot residual block is

```text
D_J = u_(S,J+1) * Dhat,
```

where the selected pivot of `Dhat` is `1`.  The regular matrix `Q` clears the
first selected row except the pivot, replaces the following factor by
`C'_J = Q^-1 C_J`, and the regular matrix `P` clears the first selected
column, producing the block

```text
D'''_J = [1 0; 0 D_(J+1)].
```

Thus the source-backed two-edge product order is:

```text
post-pivot residual block * following free factor.
```

This is the order used by the retained-passive two-edge Case 2 Lean bridges.

## What is source-backed

- The signs for `F2`, `F3`, and `C4`.
- The p. 13 literal product-difference block and the `-F3 F2` correction.
- The Case 2 selected-pivot chart algebra.
- The two-edge order: post-pivot residual block followed by the next free
  factor.

## What remains constructed, not cited

- A cleaned-generator comparison from the literal product-difference display to
  the cleaned residual variables, whenever a theorem needs that exact passage.
- Factor alignment for an actual retained-passive source/readback point:
  `(sourceReadback E).C 1` must be proved to be the displayed post-pivot
  residual block and `(sourceReadback E).C 0` the following free factor.
- Pivot provenance: a fixed selected pivot must be nonzero, or the statement
  must be phrased as an all-pivot finite chart cover.
- Any selected-entry chart coverage or retained-passive-to-selected-entry
  pushforward theorem.

## Kill-test for the next theorem

Reject a fixed-pivot selected-entry readout theorem unless it carries either:

- a nonzero hypothesis for the chosen pivot entry; or
- a finite chart-cover conclusion selecting a pivot with nonzero entry.

Counterexample shape: a center matrix with the chosen pivot entry equal to zero
and another entry nonzero cannot be represented in that fixed selected-entry
chart, although another pivot chart may apply.

## Controller decision

Do not add a `sourceReadback` wrapper that merely repackages the existing
`hD`, `hF`, and `hpivot` hypotheses.  The source-moving target is to prove
factor alignment and pivot provenance for an actual retained-passive source
chart or to build an all-pivot finite selected-entry coverage statement.  The
general normal-crossing-to-RLCT extraction remains the only cited boundary.
