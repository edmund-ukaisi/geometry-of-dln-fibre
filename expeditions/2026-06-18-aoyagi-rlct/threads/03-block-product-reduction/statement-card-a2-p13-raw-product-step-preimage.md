# Statement Card - A2 p.13 raw product-step preimage

## Lean Files

- `lean/DLNFibre/DLN/Aoyagi/ProductReductionStepRegularDensity.lean`

## Claim

Lean defines the raw source tuple for the left-endpoint p. 13
regular-coordinate product step:

```text
X(x,u) = (I, Dtail(x), F3(u), Ctop(u), -Ctop(u) * F2(u), 0, C0(x)).
```

If `det Ctop(u)` is a unit, then `X(x,u)` lies in the source determinant
chart for the raw product-step coordinate map.  At a centered coordinate
point `(x0,0)`, this determinant-chart condition holds automatically.

Under the same determinant hypothesis, the raw-order product-step map sends
this source tuple to the already-defined p. 13 raw-shaped target tuple:

```text
Y(x,u) = (Ctop(u), Dtail(x), F3(u), Ctop(u), F2(u), 0, C0(x)).
```

## Lean Names

```text
paperEndpointFixedBaseP13RawPreimageTuple
paperEndpointFixedBaseP13RawPreimageTuple_mem_rawDetChartSet
paperEndpointFixedBaseP13RawPreimageTuple_mem_rawDetChartSet_center
productReductionStepTopologyTupleToChartRawOrder_paperEndpointFixedBaseP13RawPreimageTuple
```

## Inputs

- A finite paper chain `V`, fixed paper edge family `Bv`, and through subspace
  `U0` complementary to the total kernel.
- A base reversed-edge family `CedgeBase`.
- A regular-coordinate point `xu`.
- For non-centered points, the determinant-unit hypothesis
  `IsUnit det(Ctop(u))`.

## Method

The proof is the direct raw product-step substitution.  The raw-order
product-step map is

```text
(C1,D,F3old,A1,A2,A3,A4)
  ↦ (C1*A1,
     D,
     F3old - D*A3*(C1*A1)^(-1),
     A1,
     -A1^(-1)*A2,
     A3,
     A4 - A3*A1^(-1)*A2).
```

Substituting

```text
(I, Dtail, F3, Ctop, -Ctop*F2, 0, C0)
```

gives

```text
(Ctop, Dtail, F3, Ctop, F2, 0, C0).
```

The only inverse used is `Ctop⁻¹`; no inverse of `Dtail` or of the passive
suffix block is introduced.

## Not Proved

This checkpoint does not prove original DLN source/prior transport, source
coverage, p. 13 source-chart construction from original coordinates, signed-box
density identification, product-measure pushforward, regular-suspension
certification, normal crossings, pole order, or RLCT.

## Verification

Focused check:

```text
cd lean
env LAKE_SHARED=/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/aoyagi-rlct/lean/.lake-local-shared scripts/lb DLNFibre.DLN.Aoyagi.ProductReductionStepRegularDensity
```

passed on 2026-06-26.

Review:

```text
expeditions/2026-06-18-aoyagi-rlct/threads/03-block-product-reduction/review-a2-p13-raw-product-step-preimage.md
```

passed on 2026-06-26 with no correctness or scope issues found.  The reviewer
noted only a proof-maintenance warning from Lean's flexible-tactic linter.
