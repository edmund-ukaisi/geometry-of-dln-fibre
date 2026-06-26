# Reproduction - A2 Retained-Passive Source-Readback Continuity

Date: 2026-06-26.

Status: reproduced and formalised finite inverse-side topology of the
retained-passive source chart.

## Question

The previous rung defined the total readback map

```text
sourceReadback E
```

from an arbitrary retained-passive-shaped edge family to nonredundant
retained-passive coordinates.  The next finite topology statement is that this
readback is continuous at any edge family for which the deterministic suffix
recursion stays in the selected determinant chart.

This is inverse-side finite topology only.  It should not assert that arbitrary
edge families lie in the retained-passive source-map image.

## Source-Side Determinant Predicate

For an edge family

```text
E p : Matrix (rho + kappa p.succ) (rho + kappa p.castSucc) K,
```

write

```text
S_i(E) = suffixState E (last) i,
T_p(E) = transformedEdge E p S_{p.succ}(E).
```

The source-side recursive determinant predicate is

```text
sourceRecursiveDetChart E :=
  forall p hp,
    identityCornerDetChart
      (transformedEdge E p (suffixState E last p.succ hp)).
```

The proof argument `hp : p.succ <= last` is kept in the predicate so that it
matches the existing suffix-state continuity API exactly.  This predicate is
not an image-membership condition.  It only says that every transformed edge
visited by the deterministic readback recursion has an invertible selected
top-left corner.

## Continuity Of Suffix States

Let `E_x` be a continuous edge-family at a base point `x0`, and assume
`sourceRecursiveDetChart E_x0`.  The already-proved chart-local topology API
applies with `j = last`:

```text
continuousAt_chartLocalSuffixState_suffixState_fields
```

It gives, for every `i <= last`, continuity at `x0` of

```text
S_i(E_x).L, S_i(E_x).B, S_i(E_x).Ctop, S_i(E_x).D,
```

and it records that `S_i(E_x0).Ctop.det` is a unit.  The same hypotheses give
continuity of the visited Schur residual block through

```text
continuousAt_chartLocalSuffixState_residualBlock.
```

## Continuity Of Transformed Edges

For a fixed edge `p`, the transformed edge is

```text
T_p(E_x) =
  [I, S_{p.succ}(E_x).B; 0, I] * E_x p.
```

The suffix-state field theorem supplies continuity of `S_{p.succ}.B`, and
the ambient edge-family continuity supplies continuity of `E_x p`.  Matrix
block formation and multiplication therefore give continuity of `T_p(E_x)`.

The selected determinant hypothesis at `x0` then gives continuity of

```text
(topLeftCorner T_p(E_x))^-1
```

at `x0`.

## Readback Components

The readback fields are continuous componentwise:

```text
A1passive p = topLeftCorner T_{p.succ}(E)
F2 p        = -((topLeftCorner T_p(E))^-1 * upperRightBlock T_p(E))
A3passive p = lowerLeftBlock T_{p.castSucc}(E)
C p         = schurResidualBlock T_p(E)
Ctop        = S_0(E).Ctop
F3          = lowerLeftBlock S_0(E).L.
```

The only inverse in these formulas is the selected top-left inverse in `F2`;
the basepoint determinant predicate is exactly the needed hypothesis.  The
`C` component can be proved either directly from transformed-edge continuity
and inverse continuity or by the existing residual-block continuity theorem.

The index shifts are:

- `A1passive p` reads edge `p.succ`, since the omitted first top-left block is
  not a passive coordinate.
- `A3passive p` reads edge `p.castSucc`, since the omitted final lower-left
  block is not a passive coordinate.
- `Ctop` and `F3` read from the source-left suffix state `S_0`.

## Bundled Continuity

The topology on `RetainedPassiveNonredundantCoordinateData` is induced from the
six-field product tuple.  Once the six component families are continuous at
`x0`, product continuity gives continuity of

```text
topologyTuple (sourceReadback (E_x)).
```

Unfolding the induced topology gives

```text
ContinuousAt (fun x => sourceReadback (E_x)) x0.
```

As a global corollary, the readback map is continuous on the subtype of edge
families satisfying `sourceRecursiveDetChart`.

## Nonclaims

This rung proves finite continuity of the explicit readback formulas on a
recursive determinant domain.  It does not prove arbitrary edge-family image
membership, image openness, source-rank coverage, source/image equality, a
local homeomorphism, measure pushforward, density/Jacobian transport, normal
crossings, pole order, or RLCT extraction.
