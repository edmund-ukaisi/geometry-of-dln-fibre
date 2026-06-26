# Reproduction - A2 Retained-Passive Projection Continuity

Date: 2026-06-26.

Status: elementary projection-continuity layer for the nonredundant
retained-passive coordinate object.  This follows the determinant-domain
topology rung and prepares the later inverse-dependent endpoint formulas.

## Question

The nonredundant retained-passive coordinate record has finite matrix fields

```text
A1passive, F2, A3passive, C, Ctop, F3.
```

The previous topology rung gave this record the product topology through the
tuple

```text
(A1passive, (F2, (A3passive, (C, (Ctop, F3))))).
```

Before proving continuity of solved endpoint formulas or of the source map,
record the elementary continuity consequences of this topology: every stored
coordinate projection is continuous, and the dummy-slot embeddings into the
older bundled coordinate object are continuous componentwise.

## Stored Fields

For each finite index, the projection maps

```text
data ↦ data.A1passive p
data ↦ data.F2 p
data ↦ data.A3passive p
data ↦ data.C p
data ↦ data.Ctop
data ↦ data.F3
```

are continuous.  This is just the definition of the induced product topology:
compose `topologyTuple` with the corresponding product projection and, for
families, with the finite-function evaluation map.

No determinant hypothesis is needed for these statements.  They are pure
product-topology facts under `[TopologicalSpace K]`.

## Dummy-Slot Embeddings

The nonredundant object embeds into the older coordinate data by filling three
dummy slots:

```text
A1seed 0 = 0,
A1seed (p.succ) = A1passive p,

F2full (p.castSucc) = F2 p,
F2full (last) = 0,

A3seed (p.castSucc) = A3passive p,
A3seed (last) = 0.
```

Each component of these embeddings is continuous because it is either a stored
field projection or a constant zero map.  These componentwise facts require
the algebraic structure needed to mention the zero-filled definitions, but
they still do not require determinant-unit hypotheses or inverse continuity.

## Boundary To The Next Step

The next endpoint/source-map continuity layer is stronger.  The solved first
top-left block has the form

```text
A1_0 = Tail(A1passive)^-1 * Ctop,
```

so it needs continuity of finite tail products plus matrix inverse continuity
on the passive determinant chart.  The solved final lower-left block has the
form

```text
A3_last = -(F3 - EarlyTail(A1, A3passive, C)) * CtopLast,
```

so it additionally needs continuity of the finite lower-left tail sum.  Those
are still elementary finite algebra, but they are not part of this projection
continuity rung.

## Nonclaims

This rung does not prove continuity of `solvedA1`, `solvedA3`,
`toCoordinateData`, or `edgeMatrix`.  It does not prove image openness,
source-rank coverage, source/image equality, measure transport,
density/Jacobian accounting, normal crossings, pole order, or RLCT
extraction.
