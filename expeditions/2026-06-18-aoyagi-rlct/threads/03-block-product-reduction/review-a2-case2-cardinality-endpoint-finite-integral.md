# Review - A2 Case 2 cardinality endpoint finite integral

Reviewer: xhigh read-only checker `Newton the 2nd`.

Verdict: PASS.

## Findings

None.

The new theorem is a faithful cardinality-entry wrapper around the existing
equivalence-based theorem.  It replaces the supplied endpoint equivalences
`eNext` and `e` with cardinality hypotheses `hNext` and `hEndpoints`,
constructs

```text
equivs = case2EndpointTransportEquivs_of_card_eq ... hNext hEndpoints,
```

and applies the prior radius finite-integral theorem by `simpa`.  The
hypotheses and conclusion match the endpoint-equivalence theorem, with only
the cardinality-to-equivalence construction added.

The theorem and notes do not overclaim relative to Aoyagi p.13 or the Case 2
selected-entry calculation.  They correctly state that the endpoint
equivalences are noncanonical finite reindexings, not label-preserving
constructors, source-prior/Jacobian transport, normal crossings, pole order, or
RLCT.

## Boundary

This is worth banking as an API improvement for downstream callers that have
endpoint cardinalities rather than explicit equivalences.  It is still a
wrapper in the narrow sense, so it should not be treated as a new mathematical
frontier.  The next real source-moving work remains a source-data package,
source-rank/image coverage, external measure pushforward, or the p.13
regular-suspension bridge.

The reviewer kept the pass read-only.  Controller verification separately ran
the focused build, full `DLNFibre` build, `scripts/sorries`,
`git diff --check`, and direct theorem axiom audit.
