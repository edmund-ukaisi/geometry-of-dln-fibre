# Review - Definition 3 Eq5 hlast bridge

Date: 2026-06-24.

Reviewer: Darwin the 2nd, xhigh read-only slice review.

Verdict: PASS.

## Findings

`AoyagiDefinition3SourceData.cut_le` stores

```text
forall j : Fin(ell+1), C.cut j <= L+1.
```

Since `C.point ell` unfolds to `C.cut (Fin.last ell)`, this directly gives the
Eq5 endpoint source-range hypothesis

```text
C.point ell <= L+1.
```

Removing explicit `hlast` from the Definition 3-specific Eq5 wrapper is safe
because that wrapper receives `Ssrc : AoyagiDefinition3SourceData ...`.  The
generic Eq5 APIs should keep `hlast` explicit because they do not receive
Definition 3 source data.

## Nonclaims

This does not construct selected cutpoints or Definition 3 source data.

It does not prove Eq5 endpoint-family construction, actual-width/block
dominance, injectivity, branch synchronisation, terminal exactness, chart
production, normal crossings, pole order, or RLCT.

## Lean Verification

Controller focused build passed:

```text
cd lean && scripts/lb DLNFibre.DLN.Aoyagi.Lemma5Eq5TerminalOrderDefinition3Bridge
```
