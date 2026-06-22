# Review - Lemma 5 Eq5 two-value wrappers

Status: reviewed/formalised.

## Scope

This slice packages the already-proved supplied Eq5 terminal-room
binary-prefix deltas into existing Lemma 4 two-value, count, and Htilde-bound
APIs.

## Checks

Focused Lean check passed:

```text
lake env lean DLNFibre/DLN/Aoyagi/Lemma5Eq5EndpointProfile.lean
```

## Findings

No formal findings.  Independent xhigh API scout `Gibbs` confirmed that the
four local wrappers are the best immediate API package:

```text
aoyagiLemma5Eq5_endpointChain_F_twoValue_of_terminalRoom
aoyagiLemma5Eq5_endpointChain_twoValueCount_of_terminalRoom
aoyagiLemma5Eq5_endpointChain_binaryIncrementPrefix_count_eq_of_terminalRoom
aoyagiLemma5Eq5_endpointChain_HtildeChainBounds_of_terminalRoom
```

The scout also noted that the next counted-datum membership bridge should live
in the counted-datum bridge layer, not in the endpoint-profile file.

## Nonclaims

This slice does not prove Eq5 vector construction, endpoint realisation,
terminality, counted-datum membership, classifier data, order count, pole
order, normal crossings, or RLCT extraction.
