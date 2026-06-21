# Statement card - A5 Lemma 5 Eq5 binary prefix delta

## Lean Names

- `DLNFibre.DLN.Aoyagi.aoyagiLemma5Eq5_endpointChain_incrementPrefix_profile_of_terminalRoom`
- `DLNFibre.DLN.Aoyagi.aoyagiLemma5Eq5_endpointChain_binaryIncrementPrefixDelta_of_terminalRoom`

## Claim

For a supplied equation `(5)` piecewise vector, a supplied endpoint-chain
correspondence, supplied source and terminal endpoint values, the selected
sum, and terminal room, every successive Lemma 4 increment-prefix delta is
binary:

```text
aoyagiLemma4IncrementPrefixDelta ell M m H r = 0
or
aoyagiLemma4IncrementPrefixDelta ell M m H r = 1.
```

## Proved

Lean packages the full endpoint-prefix profile, including `D_0=0` and
`D_ell=a`, and then checks the adjacent differences through the four Eq5
regions: initial rise, alpha plateau, post-`p` rise, and final plateau.

## Assumed

The theorem assumes the supplied Eq5 branch data, endpoint-chain
correspondence, source convention `H_0=m_0`, terminal convention `H_ell=0`,
selected-width sum, and terminal-room inequality.  The strict alpha-domain
facts are carried by the supplied Eq5 certificate.

## Deferred

Eq5 vector construction, source-label endpoint realisation, terminality,
classifier data, order count, pole order, normal crossings, and RLCT
extraction.

## Review

Focused Lean checks and full `DLNFibre` build passed.  Independent xhigh
reviewer `Ohm` found one low stale-header documentation issue, fixed, and no
formal arithmetic findings.
