# A2 Case 2 product source-chart source-readback fields reproduction

Date: 2026-06-30.

## Scope

This note checks the pointwise fixed-base Case 2 instantiation of the raw
p.13 product-coordinate source-readback formula.  It is independent of the
quiver paper.  It does not prove original source-prior transport, Haar
transport, source-image coverage, normal crossings, pole order, or RLCT
extraction.

## Setup

Fix the Case 2 endpoint fixed-base source chart

```text
sourceChart theta
```

and form the p.13 product-coordinate chart

```text
productSourceChart (theta, u)
```

from the Euclidean regular variables `u`.  In fixed-base matrices, write

```text
Ebase_p = fixedBase(sourceChart theta)_p,
Eprod_p = fixedBase(productSourceChart(theta,u))_p.
```

Let the regular fields decoded from `u` be

```text
F2, F3, Ctop
```

and let the residual factors be the source-readback residual blocks of the
base family:

```text
C_p = residualBlock(Ebase)_p.
```

Assume `det(Ctop)` is a unit.

## Fixed-base p.13 edge shapes

The fixed-base Euclidean product-coordinate constructor prescribes the product
edge matrices by cases:

```text
Eprod_last = [ I    0      ; -F3  C_last ],
Eprod_p    = [ I    0      ; 0    C_p    ]   for 0 < p < last,
Eprod_0    = [ Ctop -Ctop F2 ; 0 C_0 ].
```

For the concrete Case 2 chain there are two edges.  Hence there is no middle
index: the condition `0 < p.val < 1` is impossible for `p : Fin 2`.  The
right endpoint and left endpoint are the only non-vacuous cases.

## Source-readback calculation

The raw product-coordinate source-readback theorem applies to these shapes.
The endpoint calculations are the same finite block algebra as in the raw
note:

```text
- Ctop^{-1} (-Ctop F2) = F2,
Schur([ Ctop -Ctop F2 ; 0 C_0 ]) = C_0,
Schur([ I 0 ; -F3 C_last ]) = C_last.
```

The right endpoint stores `-F3` in the transformed lower-left block, while the
source-readback field `F3` is read from the accumulated lower-unitriangular
suffix matrix, where the sign is converted to `+F3`.

Therefore

```text
sourceReadback(Eprod).A1passive = 1,
sourceReadback(Eprod).F2 = first F2, then zeros,
sourceReadback(Eprod).A3passive = 0,
sourceReadback(Eprod).C = C,
sourceReadback(Eprod).Ctop = Ctop,
sourceReadback(Eprod).F3 = F3.
```

Here `C` is the residual-block family extracted from `sourceChart theta`.

## Boundary

This theorem is not a full inverse theorem for `(theta,u)`.  The product chart
recovers the regular fields supplied by `u` and the residual factors of the
base source family, but the retained passive source-readback fields are reset
to the canonical values `A1passive = 1` and `A3passive = 0`.  A source-prior
or original-prior statement still needs separate local coverage and density
transport theorems.
