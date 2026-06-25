# Reproduction - A2 residual-coordinate map measurability

Date: 2026-06-25.

Status: pen-and-paper reproduction for the deterministic suffix-recursion
measurability slice.

## Source Anchor

Aoyagi p.13 rewrites the product-difference block by repeatedly applying
elementary block transformations.  In the fixed-base Lean model, the bases are
the endpoint bases attached to the base chain `B` and complement `U0`; the
variable input is the reversed edge family, expressed in those fixed bases.

This slice proves that once those fixed-basis edge matrices are measurable,
the final residual `D`-block coordinate map is measurable.

## Calculation

For each edge `p`, set

```text
E_p(x) =
  paperEndpointFixedBaseEdgeMatrixOfReverseEdges W B U0 hU0
    (fun q => Cedge x q) p.
```

These matrices have rows indexed by

```text
Fin (finrank U0) + endpointComplementIndex(p.succ)
```

and columns indexed by

```text
Fin (finrank U0) + endpointComplementIndex(p.castSucc).
```

The residual-coordinate theorem assumes the Pi-valued family

```text
x |-> (p |-> E_p(x))
```

is measurable.

The suffix state consists of four finite matrices

```text
(L, B, Ctop, D).
```

At one step, the previous upper block forms

```text
M = [[I, B],
     [0, I]] * E_p
```

and, writing block entries of `M` as

```text
M = [[A, U],
     [V, W]],
```

the update is built from

```text
B'    = A^{-1} U,
Ctop' = Ctop A,
D'    = D (W - V A^{-1} U),
L'    = [[I, 0],
         [-D V (Ctop A)^{-1}, I]] L.
```

Every operation here is a finite real matrix operation: block projection,
block assembly, matrix multiplication, subtraction, negation, and matrix
inverse.  Mathlib's `Matrix.inv` over a commutative ring is the adjugate
multiplied by the totalized scalar inverse of the determinant, so over `R` it
is a globally Borel measurable map on square matrices.  Therefore no
determinant-chart or invertibility hypothesis is needed for measurability.

The recursion starts from constant terminal matrices, hence measurable fields.
Inducting backward through the suffix recursion shows all four fields of

```text
ChartLocalSuffixState.suffixState (E x) (Fin.last N) 0
```

are measurable.  Projecting the final `D` entries gives measurability of

```text
paperEndpointFixedBaseResidualBlockCoordinateMap W B U0 hU0 Cedge.
```

The local-measure corollary then feeds this residual-coordinate measurability
into the existing positive-set handoff, removing the explicit `hres_meas`
argument from the weighted signed-box residual source constructor when the
fixed-basis edge matrices are measurable.

## Formalization Notes

The Lean theorem is stated using fixed-basis edge-matrix measurability, not
raw `Measurable Cedge`.  This is deliberate: the surrounding Aoyagi
development works with finite-dimensional topological real modules, not a
normed-space API with a canonical Borel instance on arbitrary continuous
linear maps.  The theorem consumes the finite matrix family actually used by
the suffix recursion.

## Boundaries

This proves source-side finite Borel bookkeeping only.  It does not prove
source-rank openness, construct the p.13 analytic chart, prove any source
measure pushforward identity, transport Jacobian or prior density factors,
compare with the original DLN/statistical loss, prove residual positivity or
negative-power integrability by itself, produce normal crossings, compute pole
order, or extract an RLCT.

## Kill Conditions

- Do not use this theorem from only a centered `ContinuousAt Cedge x0`
  hypothesis.  It needs global measurability of the fixed-basis edge-matrix
  family.
- Do not silently replace the fixed-basis edge-matrix hypothesis by raw
  `Measurable Cedge` unless the measurable structure on the continuous-linear
  map spaces has been explicitly supplied and checked.
- Do not add a determinant-chart assumption for this measurability result:
  total matrix inverse over `R` is already Borel measurable.
