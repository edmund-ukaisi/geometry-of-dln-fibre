# Statement card - A5 Lemma 5 first-nonbase order-formula bound

## Lean Names

- `DLNFibre.DLN.Aoyagi.aoyagiLemma5FirstInteriorNonbaseCountDatumOrBase_candidates_card_le_theorem2OrderFormula`

## Claim

Under Definition 3 ceiling data, the deterministic first-nonbase-or-base
selector cardinal bound is expressed directly as a bound by
`data.theorem2OrderFormula`.

## Proved

The previous first-nonbase cardinal theorem gives

```text
candidates.card <= data.aParam * (ell - data.aParam) + 1.
```

The new theorem rewrites the right-hand side to
`data.theorem2OrderFormula`.

## Assumed

All source-facing hypotheses from the previous first-nonbase theorem remain
explicit: terminal endpoint data for every candidate chain, binary prefix
deltas, base-value interval membership, and injectivity of the deterministic
selector on the candidate set.

## Cited

None. This is finite notation bookkeeping.

## Deferred

No source classifier, no selector injectivity proof, no back-to-label map, no
terminal exactness, no finite minimum-to-`lambda` equality, no pole order, no
normal crossings, and no RLCT extraction.

## Verification

Focused module build passed:

```text
cd lean && env LAKE_SHARED="$PWD/.lake-local-shared" scripts/lb DLNFibre.DLN.Aoyagi.Lemma5FirstNonbaseOrderBridge
```

Review passed after one low import-placement fix:
`review-lemma5-first-nonbase-order-formula-bound-a5.md`.
