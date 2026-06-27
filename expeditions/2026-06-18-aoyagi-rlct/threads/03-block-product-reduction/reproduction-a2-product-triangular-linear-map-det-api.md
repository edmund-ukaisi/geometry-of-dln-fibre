# A2 product triangular linear-map determinant API

Status: controller reproduced; Lean-proved; xhigh-reviewed.

## Scope

This note records a small finite-linear-algebra API needed for the retained
passive derivative comparison.  It is not an analytic derivative theorem and
does not mention normal crossings or RLCT extraction.

## Upper triangular block map

For finite free modules `M` and `N`, let

```text
f : M -> M
g : N -> N
h : N -> M.
```

The upper block-triangular map is

```text
(x,y) |-> (f x + h y, g y).
```

In matrix form with product bases it is

```text
[ f  h ]
[ 0  g ].
```

Therefore its determinant is

```text
det f * det g.
```

Lean definitions and theorem:

```text
linearMapUpperTriangular
linearMapUpperTriangular_apply
linearMapUpperTriangular_det_eq_mul
```

## Lower triangular block map

For

```text
f : M -> M
g : N -> N
h : M -> N,
```

the lower block-triangular map is

```text
(x,y) |-> (f x, h x + g y).
```

In product bases it is

```text
[ f  0 ]
[ h  g ].
```

Its determinant is again

```text
det f * det g.
```

Lean definitions and theorem:

```text
linearMapLowerTriangular
linearMapLowerTriangular_apply
linearMapLowerTriangular_det_eq_mul
```

## Why this matters for retained-passive raw order

The compact formal retained-passive raw-order map captures the diagonal
determinant-bearing blocks.  The actual raw coordinate derivative is expected
to add cross terms from already exposed coordinates into later raw components.
Those cross terms should be packaged as upper or lower block-triangular
off-diagonal entries.  The two determinant lemmas above make that comparison
independent of whether the diagonal blocks themselves are equivalences.
