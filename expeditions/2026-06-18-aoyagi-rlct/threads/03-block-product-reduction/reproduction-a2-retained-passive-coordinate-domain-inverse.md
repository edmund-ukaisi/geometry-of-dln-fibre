# Reproduction - A2 Retained-Passive Coordinate Domain And Inverse

Date: 2026-06-26.

Status: pen-and-paper construction prerequisite.  No Lean theorem is claimed
from this note alone.

## Question

The reduced p.13 product-coordinate section fixes raw one-step variables
`C1 = I` and `A3 = 0`, so it cannot supply full raw-Haar pushforward.  The
retained-passive repair should instead keep the one-step chart variables that
the p.13 section fixed or suppressed.

This note writes the candidate retained-passive coordinate domain and the
recursive inverse back to fixed-base edge matrices.  It is only finite
coordinate algebra.  Source-rank coverage, source measure, density/Jacobian
transport, normal crossings, pole order, and RLCT remain separate fields.

## One-Step Input

For one product-reduction step the existing Lean API uses raw variables

```text
(C1, D, F3old, A1, A2, A3, A4)
```

and chart variables

```text
(Ctop, D, A1, A3, F2, F3, C)
```

with

```text
Ctop = C1 * A1
F2   = -A1^{-1} * A2
F3   = F3old - D * A3 * (C1 * A1)^{-1}
C    = A4 - A3 * A1^{-1} * A2.
```

The inverse is

```text
C1    = Ctop * A1^{-1}
D     = D
F3old = F3 + D * A3 * Ctop^{-1}
A1    = A1
A2    = -A1 * F2
A3    = A3
A4    = C - A3 * F2.
```

In suffix-state form, before processing edge `p`, the retained raw variables
are

```text
C1    = S_{p+1}.Ctop
D     = S_{p+1}.D
F3old = F3_{p+1}
A1    = topLeft(transformedEdge_p)
A2    = upperRight(transformedEdge_p)
A3    = lowerLeft(transformedEdge_p)
A4    = lowerRight(transformedEdge_p).
```

The one-step chart output updates the suffix state by

```text
Ctop_p = Ctop_{p+1} * A1_p
D_p    = D_{p+1} * C_p
B_p    = -F2_p
F3_p   = F3_{p+1} - D_{p+1} * A3_p * Ctop_p^{-1}.
```

Here `B_p` is the suffix-state upper-right field and `F3_p` denotes the
lower-left block of the accumulated lower unitriangular multiplier.

## Coordinate Choice

Let the edge count be `N`, with edges indexed by `p = 0,...,N-1`, and write
`last = N-1`.  In the p.13 application `N = M + 2`.

The full one-step chart variables for all edges are

```text
A1_p, F2_p, A3_p, C_p     for p = 0,...,N-1.
```

Their dimensions match the original fixed-base edge blocks.  To expose
Aoyagi's p.13 active variables without adding fake singular variables, replace
two endpoint variables by final accumulated fields:

```text
active:
  X          = Ctop_0 - I
  F2         = F2_0
  F3         = F3_0
  C_p        for all p

passive:
  A1_p       for p = 1,...,N-1
  F2_p       for p = 1,...,N-1
  A3_p       for p = 0,...,N-2
```

The missing endpoint variables `A1_0` and `A3_last` are recovered from the
active accumulated variables.  Set `Ctop_0 = I + X`, require `det(Ctop_0)`
and the passive `det(A1_p)` for `p>0` to be units, and use the convention

```text
F2_N = 0.
```

Thus the total coordinate count is unchanged:

```text
{X}    + {A1_p : p>0}       replaces {A1_p : all p},
{F3}   + {A3_p : p<last}    replaces {A3_p : all p},
{F2}   + {F2_p : p>0}       replaces {F2_p : all p},
{C_p : all p}               is unchanged.
```

The p.13 reduced section is the special point of the passive directions where

```text
A1_p = I       for p > 0,
F2_p = 0       for p > 0,
A3_p = 0       for p < last.
```

The active coordinates then give `Ctop_0 = I + X`, `F2_0 = F2`, and, for
`N > 1`, `A3_last = -F3` when the rightmost passive `A1_last` is `I`.  The
single-edge endpoint is the separate formula below: `A3_0 = -F3 * Ctop`.

## Recursive Reconstruction

Assume the retained invertible variables are in determinant-unit neighborhoods:
the passive `A1_p` for `p>0` are units and the active `Ctop_0 = I + X` is a
unit.  Define states from right to left.

Terminal state:

```text
Ctop_N = I
D_N    = I
B_N    = 0
F2_N   = 0
F3_N   = 0.
```

Residual products are determined by

```text
D_p = D_{p+1} * C_p.
```

For the top-left factors, first set

```text
P_1 = A1_last * A1_{last-1} * ... * A1_1
```

with `P_1 = I` if `N=1`, and solve

```text
A1_0 = P_1^{-1} * Ctop.
```

Then the recursion gives `Ctop_0 = Ctop`.  For all `p`, set

```text
Ctop_p = A1_last * A1_{last-1} * ... * A1_p.
```

For the upper-right fields, set

```text
F2_0 = F2,
F2_p = passive F2_p       for p > 0,
B_p  = -F2_p.
```

For the lower-left fields, the final accumulated field satisfies

```text
F3 =
  - sum_{p=0}^{last} D_{p+1} * A3_p * Ctop_p^{-1}.
```

The variables `A3_p` for `p < last` are passive, so solve the rightmost block:

```text
A3_last =
  -(F3 + sum_{p=0}^{last-1} D_{p+1} * A3_p * Ctop_p^{-1}) * Ctop_last.
```

For `N=1`, this reduces to

```text
A3_0 = -F3 * Ctop,
```

which matches the single-edge product-coordinate pattern
`[Ctop, -Ctop*F2; -F3*Ctop, C0 + F3*Ctop*F2]`.

Now define the transformed edge block

```text
M_p =
  [ A1_p       -A1_p * F2_p
    A3_p        C_p - A3_p * F2_p ].
```

Since

```text
transformedEdge_p = [I, B_{p+1}; 0, I] * E_p,
```

the original fixed-base edge matrix is recovered by

```text
E_p = [I, -B_{p+1}; 0, I] * M_p.
```

Equivalently, using `B_{p+1} = -F2_{p+1}` for `p+1<N`,

```text
E_p = [I, F2_{p+1}; 0, I] * M_p       for p < last,
E_last = M_last.
```

This is the candidate retained-passive source map at the fixed-base matrix
level.  The continuous edge-family version must still be obtained by applying
the existing fixed-base matrix-to-edge-family realization.

## Readback From A Source Point

Conversely, suppose a fixed-base source edge family lies in a neighborhood
where all recursive determinant-chart hypotheses hold.  Let `S_{p+1}` be the
deterministic suffix state of the source family before edge `p`, and let

```text
M_p = transformedEdge E p S_{p+1}.
```

Read

```text
A1_p = topLeft(M_p)
A2_p = upperRight(M_p)
A3_p = lowerLeft(M_p)
A4_p = lowerRight(M_p)
C_p  = A4_p - A3_p * A1_p^{-1} * A2_p
F2_p = -A1_p^{-1} * A2_p.
```

The active readback is

```text
Ctop = S_0.Ctop
F2   = F2_0 = -S_0.B
F3   = lowerLeftBlock(S_0.L).
```

The passive readback keeps `A1_p` and `F2_p` for `p>0`, and `A3_p` for
`p<last`.  The omitted variables `A1_0` and `A3_last` are then recovered by
the formulas above.  The one-step inverse theorem
`productReductionStepCoordinate_left_inverse_of_isUnit_A1` is the local
algebraic reason this readback followed by reconstruction returns the original
transformed edge blocks.

## What This Moves

This coordinate domain is the first construction that is large enough to have
a chance at the existing frontier fields:

```text
hcoverage
hraw_map
```

It gives a candidate local source map and local inverse at the fixed-base
matrix level.  It does not yet prove either field:

- coverage still requires an open neighborhood on which every source-rank
  point lies in the recursive determinant chart and is recovered by the
  readback;
- a pushforward theorem still requires a product measure on these coordinates
  and a calculation of the triangular one-step Jacobian factors;
- the reduced p.13 section remains lower-dimensional and is not being used as
  full raw Haar.

## First Lean Statement Shape

The first useful Lean statement should not be a measure theorem.  It should be
a finite algebraic reconstruction theorem for the retained-passive source map,
for example:

```text
retainedPassiveSourceMap_readback_reconstructs_transformedEdges
```

with content:

```text
readback (sourceMap retainedCoords) = retainedCoords
```

or the opposite direction on a recursive determinant-chart neighborhood:

```text
sourceMap (readback E) = E.
```

This theorem should name all determinant-unit hypotheses and should conclude
only reconstruction of fixed-base edge matrices or transformed edge blocks.
It should not mention raw-Haar pushforward, local source coverage, density,
normal crossings, pole order, or RLCT.

## Review

Xhigh read-only reviewer `Ramanujan the 3rd` checked the note against the Lean
suffix-state conventions and passed the order/sign choices.  In particular,
the reviewer confirmed the `Ctop_p` and `D_p` recursion orientations, the
`B_p = -F2_p` sign, the right multiplication in the `A3_last` formula, the
single-edge endpoint formula, and the fixed-base reconstruction
`E_p = [I,F2_{p+1};0,I] * M_p`.

## Nonclaims

No source-rank coverage, no source/image equality, no product-measure
pushforward, no Jacobian/prior density theorem, no proof that passive
coordinates are units on a source-rank neighborhood, no normal crossings, no
pole order, and no RLCT extraction are proved here.
