# Reproduction - A2 Retained-Passive Source-Readback Object

Date: 2026-06-26.

Status: finite source-side coordinate readback package for the retained-passive
edge family.

## Question

The nonredundant retained-passive source map

```text
data -> data.edgeMatrix
```

is injective on `data.detChart`, and the previous rung proved it is continuous
on the determinant-chart subtype.  The next finite inverse-side object is an
explicit coordinate readback map from an arbitrary edge family `E` to a
nonredundant retained-passive coordinate record.

This should package the already-proved component readbacks into a named
object.  It should not assert that an arbitrary edge family lies in the image
of the source map.

## Source-Side Suffix State

For an edge family

```text
E p : Matrix (rho ⊕ kappa p.succ) (rho ⊕ kappa p.castSucc) K,
```

let

```text
S_i(E) = suffixState E (Fin.last (M+1)) i
```

for `i <= Fin.last (M+1)`.  For an edge `p : Fin (M+1)`, let

```text
T_p(E) = transformedEdge E p S_{p.succ}(E).
```

These are the same deterministic suffix-state and transformed-edge objects
used throughout the product-reduction recursion.

## Readback Formulas

The nonredundant readback record has fields:

```text
A1passive p = topLeftCorner T_{p.succ}(E),        p : Fin M
F2 p        = -(topLeftCorner T_p(E))^-1
                * upperRightBlock T_p(E),         p : Fin (M+1)
A3passive p = lowerLeftBlock T_{p.castSucc}(E),   p : Fin M
C p         = schurResidualBlock T_p(E),          p : Fin (M+1)
Ctop        = S_0(E).Ctop
F3          = lowerLeftBlock S_0(E).L.
```

The index choices match the nonredundant fields:

- `A1passive p` is the old full `A1seed` component at edge `p.succ`, because
  the dummy `A1seed 0` is not a coordinate.
- `A3passive p` is the old full `A3seed` component at edge `p.castSucc`,
  because the final `A3seed` slot is dummy.
- `F2 p` is recovered from the transformed edge at `p`; it is equivalent to
  the negative suffix-state `B` readback after processing edge `p`.

## Inverse Check On The Retained-Passive Image

For `E = data.edgeMatrix` with `data.detChart`, the existing theorem

```text
data.edgeMatrix_readbacks_eq_targets_of_detChart
```

gives:

```text
S_0(E).Ctop = data.Ctop
lowerLeftBlock S_0(E).L = data.F3
topLeftCorner T_{p.succ}(E) = data.A1passive p
-((topLeftCorner T_p(E))^-1 * upperRightBlock T_p(E)) = data.F2 p
lowerLeftBlock T_{p.castSucc}(E) = data.A3passive p
schurResidualBlock T_p(E) = data.C p.
```

These are exactly the six fields of the readback record.  Extensionality of
the structure then gives

```text
sourceReadback data.edgeMatrix = data.
```

## Lean Boundary

Lean should define:

```text
sourceReadbackSuffixState
sourceReadbackTransformedEdge
sourceReadback
```

and prove:

```text
sourceReadback_edgeMatrix_eq
```

under the determinant-chart hypothesis.

## Nonclaims

This rung defines a total finite readback map and proves it is a left inverse
on the retained-passive determinant-chart image.  It does not prove that an
arbitrary edge family lies in the image, does not prove image openness or a
local homeomorphism, and does not prove source-rank coverage, source/image
equality, measure pushforward, density/Jacobian accounting, normal crossings,
pole order, or RLCT extraction.
