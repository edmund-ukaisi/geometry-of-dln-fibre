# Statement Card - A2 continuity to small loss neighborhood

Date: 2026-06-24.

Lean file:

- `lean/DLNFibre/DLN/Aoyagi/RegularSuspensionCoordinates.lean`

## Lean Names

```text
aoyagiCoordinateSquareSum_continuousAt
aoyagiCoordinateSquareSum_eventually_le_one_of_continuousAt_zero
aoyagiCoordinateSquareSum_add_eventually_le_one_of_continuousAt_zero
aoyagiCoordinateSquareSum_eventually_le_one_of_forall_centered_continuousAt
aoyagiCoordinateSquareSum_add_eventually_le_one_of_forall_centered_continuousAt
```

## Statement Shape

For a finite real coordinate family `f : alpha -> eta -> real`, if `f` is
continuous at `x0` and `f x0 = 0`, then eventually in the ambient neighborhood
filter `nhds x0`,

```text
aoyagiCoordinateSquareSum (f x) <= 1.
```

For two centered continuous finite real coordinate families `f` and `g`, Lean
also proves eventually in `nhds x0`,

```text
aoyagiCoordinateSquareSum (f x) +
  aoyagiCoordinateSquareSum (g x) <= 1.
```

The two-family theorem is proved by applying the one-family theorem to the
disjoint-sum coordinate family and using `aoyagiCoordinateSquareSum_sumElim`.
The `forall_centered_continuousAt` variants first assemble coordinatewise
centered-continuity data into Pi-valued centered continuity.

## Scope

Real finite topology only.  The theorem is ambient `nhds`, not primarily
`nhdsWithin`.  A source-stratum version should be a later weakening or
intersection with the source-rank-stratum neighborhood.

## Nonclaims

No analytic chart, local inverse, source-rank openness, analytic
regular-coordinate theorem, Fubini/polar regular-variable shift, normal
crossings, pole order, or RLCT extraction is proved.
