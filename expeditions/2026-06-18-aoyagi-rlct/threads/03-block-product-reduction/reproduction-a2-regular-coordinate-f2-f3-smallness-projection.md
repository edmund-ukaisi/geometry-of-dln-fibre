# Reproduction - A2 regular-coordinate F2/F3 smallness projection

Date: 2026-06-24.

Status: pen-and-paper reproduced; finite real topology formalised in Lean.

## Target

The finite literal-vs-cleaned loss comparison requires a neighborhood where

```text
squareSum(F2_x) + squareSum(F3_x) <= 1.
```

The preceding generic topology slice proves this for any two centered
continuous finite real coordinate families.  This note records the exact
projection from the tagged p. 13 regular-coordinate family to those two
families.

## Tagged Regular Coordinates

The regular-coordinate index is

```text
(iota x iota) ⊕ ((iota x nu) ⊕ (mu x iota)).
```

The three summands represent

```text
Ctop - 1,   F2,   F3.
```

Let

```text
coord : alpha -> AoyagiRegularBlockCoordinateIndex iota mu nu -> real
```

be any finite tagged regular-coordinate family.  Assume that every tagged
coordinate is centered and continuous at `x0`:

```text
for every c,
  coord(x0,c) = 0
  and x |-> coord(x,c) is continuous at x0.
```

Define the two projected coordinate families

```text
f2_x(i,j) = coord(x, inr (inl (i,j))),
f3_x(a,i) = coord(x, inr (inr (a,i))).
```

For every `(i,j)`, the centered-continuity hypothesis for the tagged coordinate
`inr (inl (i,j))` gives centered continuity of `f2_x(i,j)`.  For every
`(a,i)`, the same hypothesis at `inr (inr (a,i))` gives centered continuity of
`f3_x(a,i)`.

Applying the two-family generic theorem gives

```text
eventually x in nhds x0,
  squareSum(f2_x) + squareSum(f3_x) <= 1.
```

## Boundary

This is still ambient finite real topology.  It identifies the correct tagged
subfamilies inside the p. 13 regular coordinates, but it does not assert that
the tagged coordinates are analytic chart coordinates, does not weaken the
ambient neighborhood to a source-rank stratum, and does not prove source-rank
openness, analytic ideal transport, Fubini/polar regular-variable shift,
normal crossings, pole order, or RLCT.
