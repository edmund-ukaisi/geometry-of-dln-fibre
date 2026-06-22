# Statement card - A5 Lemma 5 Eq5 two-value wrappers

## Lean Names

- `DLNFibre.DLN.Aoyagi.aoyagiLemma5Eq5_endpointChain_F_twoValue_of_terminalRoom`
- `DLNFibre.DLN.Aoyagi.aoyagiLemma5Eq5_endpointChain_twoValueCount_of_terminalRoom`
- `DLNFibre.DLN.Aoyagi.aoyagiLemma5Eq5_endpointChain_binaryIncrementPrefix_count_eq_of_terminalRoom`
- `DLNFibre.DLN.Aoyagi.aoyagiLemma5Eq5_endpointChain_HtildeChainBounds_of_terminalRoom`

## Claim

The supplied Eq5 terminal-room endpoint-chain binary-delta theorem feeds the
existing Lemma 4 APIs for two-value increments, two-value counts,
binary-prefix counts, and Htilde chain bounds.

## Proved

Lean proves thin wrappers from
`aoyagiLemma5Eq5_endpointChain_binaryIncrementPrefixDelta_of_terminalRoom` to
the existing Lemma 4 bridge theorems.

## Assumed

The wrappers assume the same supplied Eq5 branch data, endpoint-chain
correspondence, source endpoint, terminal endpoint, selected-width sum, and
terminal-room inequality as the binary-delta theorem.

## Deferred

Eq5 vector construction, endpoint realisation, terminality, counted-datum
membership, classifier data, order count, pole order, normal crossings, and
RLCT extraction.

## Review

Focused Lean check passed.  Independent xhigh API scout `Gibbs` confirmed the
wrapper set and recommended moving the next counted-datum bridge to the
counted-datum layer.
