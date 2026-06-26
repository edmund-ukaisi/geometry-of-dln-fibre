# Reproduction - A2 Retained-Passive Active Endpoint Package

Date: 2026-06-26.

Status: pen-and-paper package for the finite Lean endpoint theorem.  This is
still fixed-base coordinate algebra only.

## Question

The retained-passive source map has already been built in pieces:

- fixed-base edge matrices with prescribed transformed edge blocks;
- suffix-state `B`, `Ctop`, `D`, and lower-left `L` recurrences;
- the `A3_last` solve that forces the active accumulated `F3`;
- the `A1_0` solve that forces the active accumulated `Ctop`.

The next package should combine these pieces at the source-left endpoint.  It
should not claim local coverage, source/image equality, density, Jacobian,
normal crossings, pole order, or RLCT.

## Input

For `N = M + 1` nonempty edges, suppose the retained-passive fixed-base edge
family is built from full block families

```text
A1_p, F2_p, A3_p, C_p.
```

The active top-left target is `Ctop`, and the active lower-left target is
`F3`.  The active upper-right coordinate is `F2_0`, read from the suffix state
with the existing sign convention

```text
B_0 = -F2_0.
```

Assume:

```text
F2_last = 0,
det(Ctop) is a unit,
det(A1_p) is a unit for p != 0,
A1_0 = Tail^{-1} * Ctop,
```

where

```text
Tail = A1_last * ... * A1_1.
```

The previous top-left endpoint theorem proves the full `A1` family is
determinant-unit and gives

```text
Ctop_0 = Ctop.
```

For the lower-left endpoint, let `A3early` be the family with the final
`A3_last` replaced by zero and let

```text
EarlyTail = Tail_0(A3early).
```

Let

```text
Ctop_last = A1_last
```

in product notation, more generally the residual top-left product at the final
edge.  The previous lower-left endpoint theorem proves that if

```text
A3_last = -(F3 - EarlyTail) * Ctop_last,
```

then

```text
lowerLeft(S_0.L) = F3.
```

The required determinant-unit hypothesis for `Ctop_last` follows from the full
`A1` determinant-unit family.  In the single-edge case this is the solved
`A1_0`, whose determinant unit follows from `det(Ctop)` and the empty passive
tail.

## Endpoint Package

For the fixed-base edge family `E` and source-left suffix state `S_0`, the
finite package should prove:

```text
-S_0.B = F2_0,
S_0.Ctop = Ctop,
lowerLeft(S_0.L) = F3,
transformedEdge(E,p,S_{p+1}) = retainedPassiveTransformedEdge_p for every p.
```

These are exactly the readbacks of the retained active fields and the
constructor-side transformed-edge reconstruction.

## Nonclaims

This package still does not define a bundled coordinate domain or prove a
two-sided local inverse.  It does not prove source-rank coverage, source/image
equality, source-measure pushforward, density/Jacobian transport, normal
crossings, pole order, or RLCT extraction.
