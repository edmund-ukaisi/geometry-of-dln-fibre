# Review - A2 residual-coordinate source data

Date: 2026-06-24.

Reviewers: controller self-check and xhigh `Curie the 3rd`.

## Verdict

Passed after wording repair.

Curie found no mathematical issue with the residual scalar-coordinate API:

- `AoyagiResidualBlockCoordinateIndex` is exactly the scalar entry index
  `mu x nu` for the residual block.
- `AoyagiResidualBlockCoordinateIndex.entryIdeal_eq_matrixEntryIdeal` is the
  expected equality between the scalar-coordinate span and `matrixEntryIdeal D`.
- The endpoint residual count is mathematically correct:

```text
|mu x nu| = (H 1-r) * (H(N+1)-r).
```

- Adding residual fields to
  `PaperEndpointFixedBaseRegularCoordinateSourceData` does not overclaim
  regular-coordinate semantics because the fields are residual-prefixed and
  kept separate from the regular-coordinate index.

## Repair

Curie flagged the prose labels "source residual" and "target residual" as
misleading.  The fixed-base matrix convention puts `mu` on the row/left
endpoint with cardinality `H 1-r`, and `nu` on the column/right endpoint with
cardinality `H(N+1)-r`.  The Lean statements were already correct, but the
comments and reproduction text were changed to use row/column or left/right
endpoint language.

## Residual API Note

Curie also noted that
`PaperEndpointFixedBaseCanonicalProductDifferenceLocalCertificate.residualBlockCoordinateIndex_card_eq_endpointResidualEntryCount`
lives in the `LocalCertificate` namespace while taking a local source
certificate argument.  This mirrors the existing regular-coordinate theorem.
It is an API-discoverability issue, not a mathematical or scope issue, and was
left unchanged to avoid unrelated namespace churn in this slice.

## Checks

Curie independently ran:

```text
cd lean
lake env lean DLNFibre/DLN/Aoyagi/RegularSuspensionCoordinates.lean
lake env lean DLNFibre.lean
scripts/sorries
```

All passed, and `scripts/sorries` reported:

```text
0 sorry, 0 #exit, 0 native_decide, 0 axiom
```

The controller also ran focused downstream checks after the residual-field
change:

```text
cd lean
lake env lean DLNFibre/DLN/Aoyagi/RegularSuspensionCoordinates.lean
lake build DLNFibre.DLN.Aoyagi.RegularSuspensionCoordinates
lake env lean DLNFibre/DLN/Aoyagi/RegularSuspensionAlgebraicSource.lean
lake build DLNFibre.DLN.Aoyagi.RegularSuspensionAlgebraicSource
lake env lean DLNFibre.lean
lake build DLNFibre
scripts/sorries
git diff --check
```

These checks passed.  The full build emitted pre-existing linter warnings in
Core files, but no errors.

## Nonclaims Checked

No analytic residual chart, reduced normal-crossing certificate, germ-ideal
transport, chart coverage, Jacobian compatibility, exponent shift,
regular-coordinate additivity, pole order, or RLCT is proved.
