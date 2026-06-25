# Review - A2 fixed-base single-edge product-family coordinate readout

Date: 2026-06-25.

## Verdict

Passed at the finite one-edge coordinate-readout scope.

## Checks

The Lean theorem delegates to
`ChartLocalSuffixState.suffixState_productFamily_fields_fromBlocks_one`, so
the only new layer is fixed-base specialization and coordinate readout.

Signs match the p.13 cleaned coordinates:

```text
S.B = -F2             so -S.B = F2,
S.L = [I,0;F3,I]     so lowerLeftBlock S.L = F3,
S.D = C0             so residual coordinate is C0.
```

The prescribed-matrix wrapper uses the fixed-base matrix-realisation API and
then delegates to the fixed-base one-edge theorem.

## Residual Risk

The one-edge theorem is still conditional on the displayed transformed-edge
shape.  A later constructor must produce the matrix family and prove the shape
before this can feed the product-coordinate lower-bound socket.
