# Statement card - A5 Lemma 5 Eq5 endpoint counted-datum bridge

## Lean Names

- `DLNFibre.DLN.Aoyagi.aoyagiLemma5Eq5_endpointChain_countDatumSet_mem_of_terminalRoom`
- `DLNFibre.DLN.Aoyagi.aoyagiLemma5Eq5_endpointValue_countDatumSet_mem_of_terminalRoom`

## Claim

For a supplied Eq5 terminal-room endpoint chain, every supplied nonbase
interior endpoint value maps into `aoyagiLemma5CountDatumSet`.

## Proved

Lean proves the chain-value form for `H_j` using the existing
terminal-binary counted-datum maps-to theorem and the Eq5 binary-prefix
deltas.  It also proves the source-facing endpoint form for
`T(C.point j - 1)` by rewriting with the supplied endpoint-chain
correspondence.

## Assumed

The theorems assume supplied Eq5 branch data, terminal room, source endpoint,
terminal endpoint, selected-width sum, endpoint-chain correspondence, an
interior coordinate `j`, and the relevant nonbase inequality.

## Deferred

Eq5 vector construction, endpoint-chain realisation, proof of nonbase status,
classifier data, injection, back-to-label coverage, order count, pole order,
normal crossings, and RLCT extraction.

## Review

Focused Lean check and full `DLNFibre` build passed.  Independent xhigh
reviewer `Curie` found no formalisation or mathematical correctness issues.
