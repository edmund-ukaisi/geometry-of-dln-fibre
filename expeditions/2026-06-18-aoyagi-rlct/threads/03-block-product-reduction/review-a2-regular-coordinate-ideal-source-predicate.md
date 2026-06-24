# Review - A2 regular-coordinate ideal source predicate

Date: 2026-06-24.

Reviewers: controller self-check and xhigh `Carson the 3rd`.

## Verdict

Passed.

The source predicate is intentionally stronger than the earlier
`AoyagiCanonicalProductDifferenceRegularChartSource`: it carries both a
fixed-base canonical local source certificate and the named scalar
regular-coordinate/residual ideal neighborhood.  The existential fixed-base
shape matches the existing canonical local source certificate and avoids adding
an import from `RegularSuspensionInterface.lean` back into
`RegularSuspensionCoordinates.lean`.

The signs remain the canonical p. 13 signs used by the product-difference
algebra:

```text
S.Ctop - 1,  -S.B,  lowerLeftBlock S.L,
```

with `S.D` retained as the residual ideal.

The boundary constructor
`AoyagiSuppliedRegularSuspensionBoundary.of_canonicalProductDifferenceRegularCoordinateIdealSource`
fills only `regular_chart_source`.  It keeps `regular_ideal_transport`,
`regular_coverage`, `regular_jacobian_compatible`, and
`exponentData_eq_shift` as explicit supplied hypotheses.

Carson's xhigh review found no formal overclaim.  The review confirmed that
the fixed-base predicate records an ordinary source-stratum guarded
neighborhood, the bridge predicate only adds this derived neighborhood to the
existing existential local source certificate, and the supplied-boundary
constructor assigns the supplied analytic fields unchanged.  The reviewer also
checked the import shape and recommended keeping this bridge out of
`RegularSuspensionInterface.lean` to avoid an import cycle.

## Build Check

```text
cd lean
lake build DLNFibre.DLN.Aoyagi.RegularSuspensionCoordinates
lake env lean DLNFibre/DLN/Aoyagi/RegularSuspensionAlgebraicSource.lean
lake build DLNFibre.DLN.Aoyagi.RegularSuspensionAlgebraicSource
```

Focused checks passed.  The `scripts/lb` wrapper could not be used in this
sandbox because its shared semaphore write under `/home/ubuntu/.lake-shared`
was rejected, so the focused coordinate module was rebuilt with `lake build`.

## Nonclaims Checked

No analytic source-rank openness, analytic germ-ideal transport,
regular-suspension chart construction, chart coverage, Jacobian compatibility,
normal crossings, pole order, or RLCT is proved.
