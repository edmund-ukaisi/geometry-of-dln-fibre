# Statement Card - A2 p.13 product-coordinate left-step raw preimage

## Lean Files

- `lean/DLNFibre/DLN/Aoyagi/ProductReductionStepRegularDensity.lean`

## Claim

Lean defines the source-dependent multi-edge p. 13 product-coordinate edge
matrix family obtained by applying the p. 13 product-coordinate constructor to the
fixed-base edge matrices determined by `CedgeBase`.

For its left endpoint step, the raw suffix-step coordinate tuple is exactly
the explicit p. 13 raw source tuple:

```text
(I, Dtail(x), F3(u), Ctop(u), -Ctop(u) * F2(u), 0, C0(x)).
```

Consequently, under `IsUnit det(Ctop(u))`, the corresponding suffix-step
raw-order target tuple is the explicit p. 13 raw-shaped target tuple:

```text
(Ctop(u), Dtail(x), F3(u), Ctop(u), F2(u), 0, C0(x)).
```

## Lean Names

```text
paperEndpointFixedBaseP13ProductCoordinateMatrixFamily
p13ProductCoordinateLeftStepRawTopologyTuple_eq_rawPreimageTuple
p13ProductCoordinateLeftStepRawOrderTargetTuple_eq_rawOrderTuple
```

## Inputs

- A finite paper chain `V`, fixed paper edge family `Bv`, and through subspace
  `U0` complementary to the total kernel.
- A base reversed-edge family `CedgeBase`.
- A regular-coordinate point `xu`.
- For the raw-order target theorem, the determinant-unit hypothesis
  `IsUnit det(Ctop(u))`.

## Method

The proof identifies the tail state before the left endpoint using the
existing product-coordinate suffix-state lemmas:

```text
S.B = 0,
S.Ctop = I,
S.L = [I, 0; F3(u), I].
```

It then transfers the tail residual product from the product-coordinate
family back to the fixed-base family, so `S.D = Dtail(x)`.

At the left endpoint, the constructed product-coordinate edge is

```text
[Ctop(u), -Ctop(u) * F2(u); 0, C0(x)].
```

Since `S.B = 0`, the transformed edge has the same four blocks.  Substituting
these fields into `ChartLocalSuffixState.stepRawCoordinates` gives the raw
preimage tuple.  The raw-order target theorem then applies the already-proved
raw product-step preimage theorem.

## Not Proved

This checkpoint does not prove original DLN source/prior transport, source
coverage, p. 13 source-chart construction from original coordinates,
signed-box density identification, product-measure pushforward,
regular-suspension certification, normal crossings, pole order, or RLCT.

## Verification

Focused check:

```text
cd lean
env LAKE_SHARED=/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/aoyagi-rlct/lean/.lake-local-shared scripts/lb DLNFibre.DLN.Aoyagi.ProductReductionStepRegularDensity
```

passed on 2026-06-26.

Review:

```text
expeditions/2026-06-18-aoyagi-rlct/threads/03-block-product-reduction/review-a2-p13-product-coordinate-left-step-raw-preimage.md
```

passed on 2026-06-26 after low-severity naming and stale-note repairs.
