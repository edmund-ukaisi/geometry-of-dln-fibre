# Statement card - A5 Lemma 5 Eq5 endpoint prefix profile

## Lean Names

- `DLNFibre.DLN.Aoyagi.aoyagiLemma5Eq5_endpointChain_incrementPrefix_preAlpha`
- `DLNFibre.DLN.Aoyagi.aoyagiLemma5Eq5_endpointChain_incrementPrefix_alphaToP`
- `DLNFibre.DLN.Aoyagi.aoyagiLemma5Eq5_endpointChain_incrementPrefix_postP`
- `DLNFibre.DLN.Aoyagi.aoyagiLemma5Eq5_endpointChain_incrementPrefix_tail`

## Claim

For a supplied Eq5 piecewise vector and supplied endpoint-chain correspondence,
the Lemma 4 increment-prefix value at a left endpoint is the branchwise profile
advertised by Eq5:

```text
pre-alpha:  b
alpha-to-p: alpha - 1
post-p:     alpha + b - p
tail:       a
```

## Proved

Lean uses the supplied Eq5 branch equality at `C.point b - 1`, the generic
prefix-profile computations for upper/lower Htilde values, and the relevant
alpha-domain or terminal-room arithmetic to collapse the Htilde high-count.

## Assumed

The Eq5 piecewise certificate and endpoint-chain correspondence are supplied.
The alpha-to-`p` and post-`p` branch profiles also assume the terminal-room
inequality.  Each theorem assumes the branch guards for its own case.

## Deferred

Adjacent-branch case splitting, binary prefix deltas, Lemma 4 two-value
increments, Eq5 vector construction, endpoint realisation, terminality,
classifier data, order count, pole order, normal crossings, and RLCT
extraction.

## Review

Focused Lean check passed for `DLNFibre.DLN.Aoyagi.Lemma5Eq5EndpointProfile`.
Independent xhigh reviewer `James` found one low documentation issue, fixed in
the ledger-style summaries.
