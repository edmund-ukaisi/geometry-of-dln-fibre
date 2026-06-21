# Statement card - A5 Lemma 5 Eq5 counted-datum bridge

## Lean Names

- `DLNFibre.DLN.Aoyagi.aoyagiLemma5Eq5_nonfirstBlock_countDatumSet_mem_of_alphaDomain_of_postPLowerGuard`
- `DLNFibre.DLN.Aoyagi.aoyagiLemma5Eq5_nonfirstBlock_countDatumSet_mem_of_alphaDomain_of_terminalRoom`

## Claim

For a supplied equation `(5)` piecewise vector, every nonfirst selected block
value that is already known to be nonbase gives a counted datum:

```text
some (Sigma.mk b (T S)) in
  aoyagiLemma5CountDatumSet ell a M m baseValue.
```

There are two variants: one uses the explicit post-`p` lower guard, and one
uses the terminal-room inequality.

## Proved

Lean combines the existing Eq5 nonfirst interval-admissibility theorem with
the counted-datum maps-to adapter.  The only extra arithmetic is deriving
`b in Finset.Icc 1 (ell-1)` from `1 <= b` and `C.block b S`.

## Assumed

The Eq5 piecewise certificate, strict alpha-domain membership, nonfirst block
condition, block membership, non-base-value inequality, and either the
post-`p` guard or terminal-room inequality are supplied.

## Deferred

Eq5 vector construction, non-base-value production, source-label legality,
alpha-domain coverage, source-backed guard production, classifier construction,
injection, back-to-label coverage, Lemma 5 order count, pole order, normal
crossings, and RLCT extraction.

## Review

Focused Lean check passed for `DLNFibre.DLN.Aoyagi.Lemma5Eq5CountDatumBridge`.
Independent xhigh reviewer `Euler` found no fidelity or claim-soundness break.
