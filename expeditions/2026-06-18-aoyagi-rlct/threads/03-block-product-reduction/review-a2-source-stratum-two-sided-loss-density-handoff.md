# Review - A2 source-stratum two-sided loss-density handoff

Date: 2026-06-29.

Reviewers: xhigh read-only scouts `Darwin the 2nd` and `Peirce the 2nd`;
xhigh read-only final reviewer `Singer the 2nd`.

## Verdict

PASS as a modest API wrapper.

The theorem

```text
exists_open_ae_restrict_source_prod_p13RegularCoordinates_two_sided_loss_density_bounds
```

is mathematically honest: the hypotheses are four supplied source-stratum
filter bounds, uniform in the regular-coordinate ball, and the conclusion is
four a.e. bounds over

```text
(mu.restrict (U inter sourceStratum)).prod nu.
```

## Checks

Peirce confirmed the fully qualified namespace and proof skeleton.  The proof
calls the local-source theorem with `source := sourceStratum` and rewrites the
witness back; it does not duplicate the filter-to-measure proof.

Darwin confirmed that this is useful as a theorem surface for later
source-stratum consumers, provided the nonclaims are recorded.  In particular,
the theorem does not prove source-rank-stratum openness, local chart coverage,
or any comparison/transport statement.

Singer checked the final diff and found no naming, namespace, theorem-scope,
or documentation blockers.  The final review confirmed that the docs exclude
positivity, source-stratum openness/coverage/image, comparison proof,
transport, residual integrability, finite iff/integral claims, normal
crossings, pole order, and RLCT.

## Reviewer Verification

The controller ran the focused build:

```text
cd lean
env LAKE_SHARED="$PWD/.lake-local-shared" scripts/lb DLNFibre.DLN.Aoyagi.RegularSuspensionLocalMeasure
```

It passed.
