# Reproduction - A2 Retained-Passive Raw-Order Inverse Differentiability

Date: 2026-06-26.

Status: pen-and-paper reproduction for differentiability of the raw-order
readback inverse on the raw-order source-recursive determinant chart.  This is
local real-coordinate calculus only.  It does not identify the derivative,
prove a tangent equivalence, determinant unit/formula, density, measure
transport, normal-crossing statement, pole order, or RLCT consequence.

Source anchor: Aoyagi 2023 pp. 10-13, the block-elimination/product-reduction
calculation behind Lemma 2 and Theorem 3.  No quiver-paper input is used.

## Setup

For a raw-order tuple `y`, set

```text
E(y) = edgeFamilyOfRawOrderTuple y
H(y) = topologyTupleEdgeRawOrderInverse y
     = topologyTuple (sourceReadback (E(y))).
```

The raw edge-family reconstruction is blockwise linear:

```text
E(y)_p = fromBlocks Araw_p F2_p Lraw_p C_p,
```

with endpoint conventions

```text
Araw_0 = Ctop,                 Araw_(q.succ) = A1passive_q,
Lraw_(q.castSucc) = A3passive_q,    Lraw_last = F3.
```

Thus `y |-> E(y)` is differentiable by coordinate projections and `fromBlocks`.

## Source Readback Recursion

Let

```text
S_i(y) = sourceReadbackSuffixState (E(y)) i,
T_p(y) = sourceReadbackTransformedEdge (E(y)) p
       = [I  S_(p+1)(y).B; 0 I] * E(y)_p.
```

The source-recursive determinant chart at `y0` says each visited transformed
edge has invertible selected top-left block:

```text
IsUnit det(topLeftCorner T_p(y0)).
```

The suffix recursion also carries

```text
IsUnit det(S_i(y0).Ctop)
```

for every suffix state.  Hence the extra inverse in the `L` update,

```text
(S.Ctop * topLeftCorner T_p)^-1,
```

is differentiable at `y0`, because its determinant is a product of two units.

The deterministic step has fields

```text
B_new    = (topLeftCorner T_p)^-1 * upperRightBlock T_p
Ctop_new = S.Ctop * topLeftCorner T_p
D_new    = S.D * schurResidualBlock T_p
L_new    = [I 0; -(S.D * lowerLeftBlock T_p * (S.Ctop * topLeftCorner T_p)^-1) I] * S.L.
```

If the old fields `S.L`, `S.B`, `S.Ctop`, and `S.D` are differentiable, then
`T_p` is differentiable by block formation and matrix multiplication.  The
displayed formulas then show all four new fields are differentiable.  Starting
from the terminal constant suffix state, descending induction gives
differentiability of all suffix-state fields and all transformed edges.

## Readback Fields

The readback tuple fields are

```text
A1passive p = topLeftCorner T_(p.succ)
F2 p        = -((topLeftCorner T_p)^-1 * upperRightBlock T_p)
A3passive p = lowerLeftBlock T_(p.castSucc)
C p         = schurResidualBlock T_p
Ctop        = S_0.Ctop
F3          = lowerLeftBlock S_0.L.
```

Each expression is differentiable at `y0` by block projection, matrix
multiplication, subtraction/negation, and determinant-chart differentiability
of matrix inversion.  Assembling the finite product coordinates gives
`DifferentiableAt H y0`.

## Nonclaims

No derivative formula, tangent equivalence, determinant unit theorem,
determinant formula, Jacobian density, measure pushforward, source-rank
coverage, normal-crossing theorem, pole order, or RLCT statement is proved by
this slice.
