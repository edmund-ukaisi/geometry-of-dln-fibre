# Review - A2 regular-coordinate ideal source existence

Date: 2026-06-24.

Reviewers: controller self-check and xhigh `Zeno the 3rd`.

## Verdict

Passed.

The theorem
`exists_aoyagiCanonicalProductDifferenceRegularCoordinateIdealSource` matches
its name and statement.  It produces only the named source predicate
`AoyagiCanonicalProductDifferenceRegularCoordinateIdealSource`, whose content
is an existential fixed-base local source certificate together with the named
regular-coordinate/residual ideal source-neighborhood predicate.

The proof is exactly the advertised composition:

```text
exists_paperEndpointCanonicalProductDifferenceLocalSourceCertificate
  --> aoyagiCanonicalProductDifferenceRegularCoordinateIdealSource_of_localSourceCertificate
```

The wrapper theorem does not construct a regular-suspension chart and does not
hide analytic transport, coverage, Jacobian compatibility, exponent shift,
normal crossings, pole order, or RLCT extraction.  The existing supplied
regular-suspension boundary constructor continues to keep `regular_ideal_transport`,
`regular_coverage`, `regular_jacobian_compatible`, and `exponentData_eq_shift`
as explicit hypotheses.

Zeno noted one minor prose precision issue in the reproduction note: the
informal p. 13 block summary should make the signed Lean convention visible.
The note was tightened to list the regular coordinates as `Ctop - 1`, `-B`,
and `lowerLeftBlock L`.

## Build Check

```text
cd lean
lake env lean DLNFibre/DLN/Aoyagi/RegularSuspensionAlgebraicSource.lean
```

Focused elaboration passed.

## Nonclaims Checked

No source-rank openness, analytic germ-ideal transport, `Cfull` construction,
ideal transport, coverage, Jacobian compatibility, exponent shift, normal
crossings, pole order, or RLCT is proved.
