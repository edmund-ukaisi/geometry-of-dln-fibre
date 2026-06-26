# Reproduction - A2 Retained-Passive Fixed-Base Readback Package

Date: 2026-06-26.

Status: pen-and-paper prerequisite for a finite Lean package theorem.  This is
fixed-base matrix algebra only.

## Question

The active endpoint package already proves, for the retained-passive fixed-base
edge family `E`,

```text
-S_0.B = F2_0,
S_0.Ctop = Ctop,
lowerLeft(S_0.L) = F3,
transformedEdge(E,p,S_{p+1}) = M_p.
```

The transformed-edge readback lemma now proves that, from each

```text
M_p =
  [ A1_p       -A1_p * F2_p
    A3_p        C_p - A3_p * F2_p ],
```

the one-step chart reads back `A1_p`, `F2_p`, `A3_p`, and `C_p`.

The next finite package should combine these two facts.

## Hypotheses

Use the same hypotheses as the active endpoint package:

```text
F2_last = 0,
det(Ctop) is a unit,
det(A1_p) is a unit for p != 0,
A1_0 = Tail^{-1} * Ctop,
A3_last = -(F3 - EarlyTail) * Ctop_last.
```

The solved `A1_0` theorem already derives the full determinant-unit family

```text
det(A1_p) is a unit for every p.
```

This supplies the only extra side condition needed by the transformed-edge
readback theorem.

## Combined Readback

For every edge `p`, define the deterministic transformed edge

```text
T_p = transformedEdge(E,p,S_{p+1}).
```

Then the combined fixed-base package proves the source-left active readbacks

```text
-S_0.B = F2_0,
S_0.Ctop = Ctop,
lowerLeft(S_0.L) = F3,
```

and the per-edge readbacks

```text
topLeft(T_p) = A1_p,
upperRight(T_p) = -A1_p * F2_p,
-(A1_p^{-1} * upperRight(T_p)) = F2_p,
lowerLeft(T_p) = A3_p,
schurResidualBlock(T_p) = C_p.
```

The proof route is:

1. apply the existing active endpoint package for the three source-left fields;
2. derive full `A1` determinant-unit hypotheses from the passive units and
   solved `A1_0`;
3. apply the fixed-base transformed-edge readback theorem at each edge.

## Nonclaims

This does not define a bundled coordinate domain and does not prove a
two-sided local inverse.  It does not prove source-rank coverage, source/image
equality, source-measure pushforward, density/Jacobian accounting, normal
crossings, pole order, or RLCT extraction.
