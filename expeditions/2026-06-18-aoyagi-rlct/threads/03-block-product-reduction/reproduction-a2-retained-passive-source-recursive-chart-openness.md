# Reproduction - A2 Retained-Passive Source-Recursive Chart Openness

Date: 2026-06-26.

Status: reproduced and formalised ambient openness of the explicit
source-recursive determinant chart.

## Question

The previous rung packaged the finite two-sided source readback as a
homeomorphism

```text
{data // data.detChart} equiv_homeomorph {E // sourceRecursiveDetChart E}.
```

The remaining topological question for this chart is whether the source-side
domain

```text
sourceRecursiveDetChart E
```

is open in the ambient edge-family space.

## Proof-Irrelevance Cleanup

The definition of `sourceRecursiveDetChart` is written with an explicit proof
argument

```text
hp : p.succ <= Fin.last (M + 1).
```

For each edge `p` this proof is unique, so the predicate is equivalent to the
canonical proof-free form

```text
forall p,
  identityCornerDetChart (sourceReadbackTransformedEdge E p).
```

Lean records this as

```text
sourceRecursiveDetChart_iff.
```

The set form is also named:

```text
sourceRecursiveDetChartSet.
```

## Local Neighborhood Argument

Fix an edge family `E0` satisfying `sourceRecursiveDetChart`.  For each edge
`p`, the already proved continuity theorem gives

```text
E |-> sourceReadbackTransformedEdge E p
```

continuous at `E0`.  At `E0`, the transformed edge lies in the selected
determinant chart by `sourceRecursiveDetChart_iff`.

The selected determinant chart is open in matrix space, so its preimage under
the transformed-edge map is a neighborhood of `E0`.  This gives, for every
edge `p`, a neighborhood where the `p`-th transformed-edge determinant
condition holds.

There are finitely many edges, so the intersection of these neighborhoods is a
neighborhood of `E0`.  By `sourceRecursiveDetChart_iff`, this intersection is
exactly the source-recursive determinant chart set.  Lean records this as

```text
sourceRecursiveDetChartSet_mem_nhds.
```

## Openness

Since every point of the set has the set as a neighborhood, the source-recursive
determinant chart set is open:

```text
isOpen_sourceRecursiveDetChartSet.
```

## Nonclaims

This proves ambient openness of the named source-recursive determinant chart.
It does not prove that this chart equals the whole source image, source-rank
coverage, measure pushforward, density/Jacobian transport, normal crossings,
pole order, or RLCT extraction.

