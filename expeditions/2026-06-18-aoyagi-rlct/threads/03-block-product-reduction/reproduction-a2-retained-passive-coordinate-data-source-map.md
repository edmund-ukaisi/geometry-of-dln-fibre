# Reproduction - A2 Retained-Passive Coordinate Data Source Map

Date: 2026-06-26.

Status: pen-and-paper prerequisite for bundling the finite retained-passive
constructor data.  This is still fixed-base algebra only.

## Question

The solved-family constructor rung defines the omitted endpoint blocks

```text
A1_0 = Tail^{-1} * Ctop,
A3_last = -(F3 - EarlyTail) * CtopLast.
```

The next step is to package the inputs into a single retained-passive
coordinate-data object and define the associated fixed-base edge family.

## Coordinate Data

For `M+1` nonempty edges, the finite coordinate data consists of:

```text
A1seed_p    passive top-left blocks, with p=0 a placeholder,
F2_i        right-field blocks, with F2_last required to be zero later,
A3seed_p    passive lower-left blocks, with p=last a placeholder,
C_p         residual blocks,
Ctop        active source-left top block,
F3          active source-left lower-left block.
```

This data is not yet a topological domain.  The determinant-unit requirements
are separate hypotheses:

```text
det(Ctop) is a unit,
det(A1seed_p) is a unit for p != 0,
F2_last = 0.
```

## Source Map

From the data, define:

```text
A1 = solved A1 family from A1seed and Ctop,
A3 = solved A3 family from A1, A3seed, C, and F3,
E_p = retainedPassiveFixedBaseEdgeMatrix(A1,F2,A3,C)_p.
```

The previously proved solved-family theorem then gives the fixed-base readback
package:

```text
-S_0.B = F2_0,
S_0.Ctop = Ctop,
lowerLeft(S_0.L) = F3,
```

and for every edge `p`, the deterministic transformed edge reads back

```text
topLeft(T_p) = A1_p,
upperRight(T_p) = -A1_p * F2_p,
-(A1_p^{-1} * upperRight(T_p)) = F2_p,
lowerLeft(T_p) = A3_p,
schurResidualBlock(T_p) = C_p.
```

This is a source-map theorem in the finite algebraic sense: it names the input
coordinate object and the edge family it constructs.

## Nonclaims

This does not define an open coordinate domain, a topology, a measure, or a
Jacobian.  It does not prove a two-sided local inverse, source-rank coverage,
source/image equality, source-measure pushforward, density/Jacobian accounting,
normal crossings, pole order, or RLCT extraction.
