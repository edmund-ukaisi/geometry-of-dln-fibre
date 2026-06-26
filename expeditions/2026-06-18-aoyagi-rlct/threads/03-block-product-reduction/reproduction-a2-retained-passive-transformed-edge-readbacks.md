# Reproduction - A2 Retained-Passive Transformed-Edge Readbacks

Date: 2026-06-26.

Status: pen-and-paper prerequisite for the fixed-base retained-passive
two-sided coordinate inverse.  This is finite matrix algebra only.

## Question

The retained-passive fixed-base edge-family theorem already proves that the
deterministic suffix-state transformed edge is the prescribed block

```text
M_p =
  [ A1_p       -A1_p * F2_p
    A3_p        C_p - A3_p * F2_p ].
```

The next readback step is to check that the usual one-step chart readout
recovers the supplied coordinate blocks from `M_p`.

## Direct Block Readbacks

The block projections give immediately:

```text
topLeft(M_p)    = A1_p,
upperRight(M_p) = -A1_p * F2_p,
lowerLeft(M_p)  = A3_p.
```

The one-step chart readout for the upper-right coordinate is

```text
F2read_p = -A1_p^{-1} * upperRight(M_p).
```

Under the determinant-unit hypothesis for `A1_p`,

```text
F2read_p
  = -A1_p^{-1} * (-(A1_p * F2_p))
  = A1_p^{-1} * (A1_p * F2_p)
  = F2_p.
```

The Schur residual readout is

```text
Cread_p =
  lowerRight(M_p) - lowerLeft(M_p) * A1_p^{-1} * upperRight(M_p).
```

Substituting the displayed blocks,

```text
Cread_p
  = (C_p - A3_p * F2_p)
      - A3_p * A1_p^{-1} * (-(A1_p * F2_p))
  = C_p - A3_p * F2_p + A3_p * F2_p
  = C_p.
```

This is exactly the existing retained-passive Schur-residual lemma.

## Fixed-Base Corollary

For the fixed-base edge family

```text
E_p = [I,F2_{p+1};0,I] * M_p,
```

the previously proved transformed-edge theorem says

```text
transformedEdge(E,p,S_{p+1}) = M_p.
```

Therefore the same readbacks hold for the actual deterministic transformed
edge at every suffix-state step.

## Nonclaims

This does not define a bundled coordinate domain and does not prove a two-sided
local inverse.  It does not prove source-rank coverage, source/image equality,
measure pushforward, density/Jacobian accounting, normal crossings, pole
order, or RLCT extraction.
