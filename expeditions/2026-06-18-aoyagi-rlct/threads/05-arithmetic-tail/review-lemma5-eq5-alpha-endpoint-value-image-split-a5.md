# Review - Lemma 5 Eq5 alpha endpoint value-image split

Status: reviewed/formalised after one low finding was addressed.

Reviewer: Sagan, xhigh effort.

## Scope

This slice proves one-coordinate finite value-image coverage for supplied
alpha-indexed Eq5 strict-offset branches plus supplied endpoint branch values:

```text
aoyagiLemma5Eq5_alphaIndexedBranch_suppliedEndpointCoverage_value_image_split
```

It is a value-image adapter, not a branch-family construction or classifier.

## Checks

Focused Lean check passed from the Lake project root `lean/`:

```text
lake env lean DLNFibre/DLN/Aoyagi/Lemma5DisplayedVector.lean
```

The controller also ran:

```text
lake build DLNFibre.DLN.Aoyagi.Lemma5DisplayedVector
lake build DLNFibre
git diff --check
scripts/sorries
```

The serial module build and full build passed.  A concurrent module build
attempt raced the full build on the same `.olean` output path and failed with
an output-write error; the serial rerun passed and the full build passed.

## Findings

One low finding was raised and addressed.

The initial theorem required

```text
value lower = Tlower(C.point p - 1)
```

unconditionally, even though the lower endpoint is used only in the rising
case.  This was stronger than the intended boundary.  The theorem and
reproduction note were tightened so the lower branch-value bridge is required
only under `p <= a` and `p <= ell-a`.

No other issues were found.  The theorem proves only one-coordinate finite
value-image coverage.  It correctly uses the alpha-indexed value-image bridge
to rewrite the supplied branch image to the Eq5 offset set, then applies the
supplied endpoint-deficit split.  The `Finset.image_insert` rewrites are in
the correct order for both `insert upper branches` and
`insert upper (insert lower branches)`.

The reproduction note aligns with Aoyagi p. 27 equation `(5)`: strict offsets
`1 <= alpha < p`, value `Htilde'_p-alpha`, upper endpoint always missing from
Eq5 offsets, and lower endpoint missing only in the rising region.

## Residual Boundary

This review covers only the conditional one-coordinate value-image split.  It
does not validate Eq5 branch construction, endpoint source-label legality,
value injectivity, base-value membership, cross-coordinate disjointness,
classifier construction, no-extra terminal-minimum coverage, global Lemma 5
counting, normal crossings, or RLCT extraction.
