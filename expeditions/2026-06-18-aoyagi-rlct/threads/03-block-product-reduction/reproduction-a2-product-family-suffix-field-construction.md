# Reproduction - A2 product-family suffix-field construction

Date: 2026-06-25.

Status: pen-and-paper reproduction for the finite matrix algebra behind a
concrete p.13 product family.

## Source Boundary

Aoyagi p.13 uses the cleaned variables

```text
X = Ctop - I,    F2,    F3,    D = product of residual factors.
```

The product-family goal is to vary the regular variables independently while
keeping the residual coordinate equal to the base residual coordinate:

```text
regularBlock(CedgeProd(x,u)) = u,
residualBlock(CedgeProd(x,u)) = residualBlock(CedgeBase x).
```

This note is only finite suffix-state algebra.  It does not yet construct
continuous edge maps in the original vector spaces, prove source coverage, or
transport measure/density/Jacobian data.

## Residual Factor Input

The construction cannot start from an arbitrary final residual matrix `D`
alone.  It needs residual factors through the intermediate residual-index
types:

```text
C_p(x) : kappa(p+1) -> kappa(p),    p = 0, ..., N-1.
```

In the intended use these are the base transformed Schur residual factors
visited by the existing suffix recursion:

```text
C_p(x) = residualBlock(Ebase x, last, p).
```

Their ordered product is the base final residual field:

```text
Sbase.D = C_{N-1}(x) C_{N-2}(x) ... C_0(x).
```

This is already the content of the existing residual-product API, not a new
factorisation theorem.

## Desired Regular Variables

Decode the regular parameter `u` into the three p.13 regular fields:

```text
X  : rho -> rho,
F2 : rho -> kappa(0),
F3 : kappa(last) -> rho.
```

Set

```text
Ctop = I + X.
```

The endpoint `Ctop` must lie in the determinant chart.  Over `R`, a later
small ball condition can provide this; the finite algebra below only needs
`IsUnit det(Ctop)`.

## Edge Shapes For `N >= 2`

Write the raw edge matrices in the fixed suffix-state coordinates.  Since the
intermediate suffix `B` remains zero until the left endpoint, these are also
the transformed edges visited by the suffix recursion.

For the rightmost edge:

```text
E_{N-1} = [ I      0
           -F3    C_{N-1}(x) ].
```

For middle edges:

```text
E_p = [ I     0
        0     C_p(x) ],        1 <= p <= N-2.
```

For the left endpoint:

```text
E_0 = [ Ctop     -Ctop F2
        0         C_0(x) ].
```

The suffix-state step formulas give:

```text
after E_{N-1}:  B = 0,   Ctop = I,   lowerLeftBlock(L) = F3,
                D = C_{N-1}(x);

after middle:   B = 0,   Ctop = I,   lowerLeftBlock(L) = F3,
                D multiplies by C_p(x);

after E_0:      B = -F2, Ctop = Ctop, lowerLeftBlock(L) = F3,
                D multiplies by C_0(x).
```

Thus the final fixed-base coordinate maps read

```text
Ctop - I = X,     -B = F2,     lowerLeftBlock(L) = F3,
D = product_p C_p(x).
```

## Single-Edge Case `N = 1`

When `N = 1`, the same edge must create both endpoint fields.  Use

```text
E_0 = [ Ctop        -Ctop F2
       -F3 Ctop     C_0(x) + F3 Ctop F2 ].
```

The Schur residual is

```text
C_0(x) + F3 Ctop F2 - (-F3 Ctop) Ctop^{-1} (-Ctop F2) = C_0(x),
```

under `IsUnit det(Ctop)`.  The other suffix fields are again

```text
B = -F2,    Ctop = Ctop,    lowerLeftBlock(L) = F3.
```

## Lean Targets

The first Lean layer is now proved by one-step suffix-field lemmas for these
edge shapes:

```text
ChartLocalSuffixState.step_finalF3_fromBlocks
ChartLocalSuffixState.step_middleResidualFactor_fromBlocks
ChartLocalSuffixState.step_leftEndpointF2Ctop_fromBlocks
ChartLocalSuffixState.step_singleEdgeF2F3Ctop_fromBlocks
```

The iteration layer is now also proved:

```text
ChartLocalSuffixState.suffixState_tail_fields_of_productFamily_transformedEdges
ChartLocalSuffixState.suffixState_productFamily_fields_fromBlocks_one
ChartLocalSuffixState.suffixState_productFamily_fields_fromBlocks_succSucc
```

For chains with at least two edges, the theorem assembles the transformed-edge
shape hypotheses into final fields `B = -F2`, `Ctop = Ctop`,
`D = residualProduct E last 0`, and `L = [I, 0; F3, I]`.  Only after this
matrix-level theorem is stable should we wrap matrices back into fixed-base
continuous linear maps.

## Boundaries

No arbitrary-final-`D` realisation is claimed.  If no residual factors through
the intermediate residual dimensions are supplied, an additional finite
factorisation theorem would be needed.  The Aoyagi application avoids that by
using the base suffix recursion's residual factors.
