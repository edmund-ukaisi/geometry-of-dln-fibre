# Reproduction - A2 Retained-Passive Edge-Matrix Continuity

Date: 2026-06-26.

Status: source-map continuity layer for the nonredundant retained-passive
determinant chart.

## Question

The previous topology rungs proved continuity of the stored nonredundant
coordinates, the zero-filled seed embeddings, and the two solved endpoint
families `solvedA1` and `solvedA3` on the determinant-chart subtype
`{data // data.detChart}`.

The next source-map statement is continuity of

```text
data -> data.1.edgeMatrix p
```

for each edge `p : Fin (M+1)`, and then of the whole finite family
`data -> data.1.edgeMatrix`.

## Formula

For a determinant-chart point `data`, write

```text
A1 p = (data.1.toCoordinateData).solvedA1 p
F2 i = data.1.F2full i
A3 p = (data.1.toCoordinateData).solvedA3 p
C  p = data.1.C p
```

The transformed retained-passive edge at `p` is

```text
T_p =
  fromBlocks
    (A1 p)
    (-(A1 p * F2 p.castSucc))
    (A3 p)
    (C p - A3 p * F2 p.castSucc).
```

The fixed-base source edge is obtained by left multiplying by the
upper-unitriangular factor attached to the next `F2` coordinate:

```text
E_p =
  fromBlocks
    1
    (F2 p.succ)
    0
    1
  * T_p.
```

Thus the two `F2` indices have different roles:

- `F2 p.castSucc` is the current transformed-edge block;
- `F2 p.succ` is the next suffix/base-change block in the left multiplier.

For the terminal edge, `F2 p.succ` is the zero-filled terminal value, so the
same formula still applies.

## Continuity Derivation

On `{data // data.detChart}`, the available ingredients are:

```text
continuous_solvedA1_detChart_subtype p
continuous_solvedA3_detChart_subtype p
(continuous_F2full p.castSucc).comp continuous_subtype_val
(continuous_F2full p.succ).comp continuous_subtype_val
(continuous_C p).comp continuous_subtype_val
```

The transformed edge is continuous because each of its four blocks is
continuous:

```text
A1 p
-(A1 p * F2 p.castSucc)
A3 p
C p - A3 p * F2 p.castSucc
```

using matrix multiplication, negation, subtraction, and `fromBlocks`
continuity.

The left upper-unitriangular factor is continuous because its four blocks are

```text
1, F2 p.succ, 0, 1.
```

The fixed-base edge `E_p` is then continuous by matrix multiplication.

Finally, the family-valued source map is continuous by componentwise continuity
in the Pi topology.

## Lean Boundary

Lean should prove:

```text
continuous_edgeMatrix_detChart_subtype_apply
continuous_edgeMatrix_detChart_subtype
```

The first theorem is the per-edge continuity statement.  The second is only
the Pi-family wrapper.

## Nonclaims

This rung proves continuity of the coordinate-domain source map on the
determinant-chart subtype only.  It does not prove image openness,
source-rank coverage, source/image equality, local homeomorphism, measure
pushforward, density/Jacobian accounting, normal crossings, pole order, or
RLCT extraction.
