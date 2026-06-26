# Reproduction - A2 Retained-Passive Recoverable Readbacks

Date: 2026-06-26.

Status: pen-and-paper prerequisite for the bundled finite local-inverse
readback layer.  This remains fixed-base algebra only.

## Question

The coordinate-data source-map package builds an edge family

```text
E = data.edgeMatrix
```

from retained-passive data

```text
A1seed, F2, A3seed, C, Ctop, F3.
```

The previous readback theorem recovers the solved full families
`data.solvedA1` and `data.solvedA3` from the deterministic transformed edges.
The local-inverse question is which fields of the original coordinate data are
actually recovered by `E`.

## Dummy Endpoint Fields

The definitions intentionally ignore two seed entries:

```text
data.solvedA1 0 = Tail(data.A1seed)^{-1} * data.Ctop,
data.solvedA1 p = data.A1seed p       for p != 0,
```

and

```text
data.solvedA3 (last edge) = -(F3 - EarlyTail) * CtopLast,
data.solvedA3 p           = data.A3seed p       for p != last edge.
```

Thus `A1seed 0` and `A3seed (last edge)` are placeholders.  The edge family
cannot recover them, and no injectivity statement may include them.

## Recoverable Readbacks

Under the same finite side conditions as the source-map theorem,

```text
F2_last = 0,
det(A1seed_p) is a unit for p != 0,
det(Ctop) is a unit,
```

the constructed edge family has source-left readbacks

```text
-S_0.B = F2_0,
S_0.Ctop = Ctop,
lowerLeft(S_0.L) = F3.
```

For each edge `p`, with

```text
T_p = transformedEdge E p S_{p+1},
```

the previous solved-family readback theorem gives

```text
topLeft(T_p) = data.solvedA1 p,
-((data.solvedA1 p)^{-1} * upperRight(T_p)) = F2_{p.castSucc},
lowerLeft(T_p) = data.solvedA3 p,
schurResidualBlock(T_p) = C_p.
```

Replacing solved fields by seed fields away from dummy endpoints yields the
recoverable-coordinate readbacks:

```text
topLeft(T_p) = A1seed_p       for p != 0,
-((topLeft(T_p))^{-1} * upperRight(T_p)) = F2_{p.castSucc},
lowerLeft(T_p) = A3seed_p     for p != last edge,
schurResidualBlock(T_p) = C_p.
```

The `F2` readback over `p.castSucc` covers every non-final `F2` coordinate.
The final `F2_last` coordinate is not read from a transformed edge in this
statement; it is fixed by the side condition `F2_last = 0`.

## Recoverable Extensionality

If two coordinate-data objects satisfy the finite side conditions and have the
same constructed edge family, then the displayed readbacks imply equality of
the recoverable fields:

```text
A1seed_p = A1seed'_p       for p != 0,
F2 = F2',
A3seed_p = A3seed'_p       for p != last edge,
C = C',
Ctop = Ctop',
F3 = F3'.
```

The proof compares both data objects against the same readback expression for
the common edge family.  For `F2`, `Fin.forall_iff_castSucc` splits the index
set into non-final coordinates `p.castSucc` and the final coordinate; the
final coordinate equality follows from the two `F2_last = 0` hypotheses.

## Corner Cases

When `M=0`, there is one edge.  The predicates `p != 0` and
`p != last edge` are both vacuous, so no seed entry of `A1seed` or `A3seed` is
recoverable.  The theorem still recovers `F2_0`, `F2_last=0`, `C_0`, `Ctop`,
and `F3`.

## Nonclaims

This is not an open coordinate domain, topology, source-stratum coverage
theorem, source/image equality, measure pushforward, density/Jacobian theorem,
normal-crossing production, pole-order statement, or RLCT extraction.  It is
also not full injectivity of `RetainedPassiveCoordinateData`, because the two
dummy endpoint seed fields are deliberately outside the recovered coordinate
set.
