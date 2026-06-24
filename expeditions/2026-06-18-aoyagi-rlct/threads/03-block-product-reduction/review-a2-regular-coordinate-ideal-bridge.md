# Review - A2 regular-coordinate ideal bridge

Date: 2026-06-24.

Reviewers: controller self-check and xhigh `Bohr the 3rd`.

## Verdict

Passed.

The theorem is exactly finite ideal algebra: the scalar-coordinate range over
`AoyagiRegularBlockCoordinateIndex ι μ ν` generates the same ideal as the join
of matrix-entry ideals for `X`, `F2`, and `F3`.  The proof is by two
`Ideal.span_le` inclusions and uses no analytic data.

The residual block `D` is not included.  The composed fixed-base theorem
rewrites the product-difference entry ideal as the scalar regular-coordinate
ideal joined with `matrixEntryIdeal S.D`; this is still only algebraic ideal
bookkeeping.

Bohr's xhigh review found one low wording issue: the ideal bridge is stated
without `[Fintype ι] [Fintype μ] [Fintype ν]`, so it is valid for arbitrary
generator families.  This is algebraically correct and not an overclaim; the
file/doc prose now distinguishes this algebraic bridge from the finite count
theorems.

## Build Check

```text
cd lean
lake env lean DLNFibre/DLN/Aoyagi/RegularSuspensionCoordinates.lean
lake build DLNFibre.DLN.Aoyagi.RegularSuspensionCoordinates
```

Focused controller checks passed; Bohr also reported the focused Lean check
passed.
