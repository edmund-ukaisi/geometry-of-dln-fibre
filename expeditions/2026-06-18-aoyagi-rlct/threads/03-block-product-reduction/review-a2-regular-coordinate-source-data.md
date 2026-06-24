# Review - A2 regular-coordinate source data

Date: 2026-06-24.

Reviewers: controller self-check and xhigh `McClintock the 3rd`.

## Verdict

Passed.

The new source-data package stays within the intended A2 boundary.  It packages
only:

- the dimension convention `H(k+1)=finrank(W k)`;
- the already proved local source certificate;
- the source-stratum guarded regular/residual ideal split;
- centered continuity for scalar entries of `S.Ctop - 1`, `-S.B`, and
  `lowerLeftBlock S.L`;
- the finite cardinality equality with
  `aoyagiTheorem2RegularVariableCount N H r`.

The rank-equality constructor uses
`exists_paperEndpointCanonicalProductDifferenceLocalSourceCertificate_of_rank_eq`
and the supplied dimension convention.  It does not infer exact-rank openness
and does not construct analytic regular-suspension data.

McClintock noted one residual API issue: an older theorem in the
`PaperEndpointFixedBaseCanonicalProductDifferenceLocalCertificate` namespace
takes a local source certificate.  This is slightly awkward organization but
not a mathematical or scope issue for the new package.

## Build Check

```text
cd lean
lake env lean DLNFibre/DLN/Aoyagi/RegularSuspensionCoordinates.lean
lake build DLNFibre.DLN.Aoyagi.RegularSuspensionCoordinates
lake env lean DLNFibre/DLN/Aoyagi/RegularSuspensionAlgebraicSource.lean
lake build DLNFibre.DLN.Aoyagi.RegularSuspensionAlgebraicSource
lake env lean DLNFibre.lean
scripts/sorries
git diff --check
```

All checks passed.  `scripts/sorries` reported:

```text
0 sorry, 0 #exit, 0 native_decide, 0 axiom
```

## Nonclaims Checked

No exact-rank or source-rank openness, analytic germ-ideal transport,
regular-suspension chart construction, chart coverage, Jacobian compatibility,
exponent shift, normal crossings, pole order, or RLCT is proved.
