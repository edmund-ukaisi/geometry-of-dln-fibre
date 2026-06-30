# Review: A2 Case 2 product source-chart source-readback fields

Date: 2026-06-30.

Reviewer: xhigh scout `Anscombe the 2nd`.

## Verdict

PASS.

## Scope check

The Lean theorem

```text
case2PassiveThetaEndpointProductSourceChart_sourceReadback_fields
```

defines fixed-base `Ebase` and `Eprod` matrices, then sets
`data := sourceReadback Eprod` and concludes only the six field equalities for
`A1passive`, `F2`, `A3passive`, `C`, `Ctop`, and `F3`.  It does not assert a
full inverse/readback theorem for `(theta,u)`.

The theorem docstring and reproduction note explicitly exclude full theta
recovery, source-prior transport, source-image coverage, normal crossings,
pole order, and RLCT extraction.

## Source fidelity

The reproduction note's two-edge p.13 shapes match the raw
product-coordinate constructors.  In the concrete Case 2 `Fin 2` edge family,
there is no middle edge, so the middle-shape condition is vacuous.

The Lean proof applies the raw theorem
`sourceReadback_productCoordinate_fields_succSucc`, whose conclusion is the
same field package.

## Concern

The proof uses definitional unfolding plus `simp ...; rfl` for the product
matrix constructor endpoint cases.  This is Lean/API fragility rather than
mathematical overreach: if the constructor implementation changes, the theorem
may need a small proof repair even if the statement remains true.

## Verification

The reviewer independently checked:

```text
lake env lean DLNFibre/DLN/Aoyagi/RetainedPassiveCase2PassiveThetaSourceImage.lean
```
