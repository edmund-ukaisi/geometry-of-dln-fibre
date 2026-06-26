# Reproduction - A2 Retained-Passive `A1_0` Endpoint Target

Date: 2026-06-26.

Status: pen-and-paper prerequisite for the retained-passive coordinate-domain
inverse.  This note is finite matrix algebra only.

## Question

In the retained-passive coordinate choice, the active top-left coordinate is
the accumulated endpoint

```text
Ctop_0 = Ctop = I + X.
```

The passive top-left variables are the one-edge blocks `A1_p` for `p > 0`.
The missing first block `A1_0` should be solved so that the recursive top-left
product really has endpoint value `Ctop`.

## Product Orientation

For `N = M + 1` nonempty edges, the suffix-state recursion gives

```text
Ctop_p = Ctop_{p+1} * A1_p
```

with terminal value `Ctop_N = I`.  Therefore the left endpoint is the ordered
product

```text
Ctop_0 = A1_last * A1_{last-1} * ... * A1_1 * A1_0.
```

In Lean this product is

```text
residualFactorProduct A1 (Fin.last (M+1)) 0.
```

The passive tail after the first edge is

```text
Tail = residualFactorProduct A1 (Fin.last (M+1)) 1
     = A1_last * A1_{last-1} * ... * A1_1.
```

For `M = 0`, the tail is the empty product `I`.

The one-step unfold at the first edge is exactly

```text
residualFactorProduct A1 (Fin.last (M+1)) 0 = Tail * A1_0.
```

## Endpoint Solve

Assume `det(Tail)` is a unit.  To force the active endpoint `Ctop`, set

```text
A1_0 = Tail^{-1} * Ctop.
```

Then

```text
Tail * A1_0
  = Tail * Tail^{-1} * Ctop
  = Ctop.
```

Thus the full top-left product is the target active coordinate:

```text
residualFactorProduct A1 (Fin.last (M+1)) 0 = Ctop.
```

The tail determinant is a unit whenever each passive `det(A1_p)` for `p>0` is
a unit, because the tail is an ordered product of exactly those passive
blocks.  This is proved by the same right-to-left product induction as the
endpoint product split.

If also `det(Ctop)` is a unit, then the solved first block is in the
determinant chart:

```text
det(A1_0) = det(Tail^{-1}) * det(Ctop)
```

is a unit.  Combined with the passive hypotheses `det(A1_p)` unit for `p>0`,
this gives the full determinant-unit family needed by the deterministic
suffix-state API.

## What This Moves

This supplies the top-left half of the retained-passive inverse:

- active `Ctop` is realized as the endpoint recursive top product;
- the passive tail is determinant-unit from the passive determinant-unit
  hypotheses;
- the solved `A1_0` is determinant-unit if `Ctop` is determinant-unit;
- the existing suffix-state theorem then turns this product statement into
  `(suffixState E last 0).Ctop = Ctop` for retained-passive fixed-base edges.

## Nonclaims

No retained-passive coordinate-domain theorem is proved here.  No `F2`
readback, no `A3_last`/`F3` packaging, no transformed-edge readback inverse, no
source-rank coverage, no source/image equality, no measure pushforward, no
density/Jacobian theorem, no normal crossings, no pole order, and no RLCT
extraction is claimed.
