# Review - Lemma 5 first-nonbase order-formula bound

Reviewer: `Averroes the 2nd` (xhigh).
Status: passed after one low process fix.

## Scope

Reviewed the uncommitted Lean theorem

```text
aoyagiLemma5FirstInteriorNonbaseCountDatumOrBase_candidates_card_le_theorem2OrderFormula
```

in `lean/DLNFibre/DLN/Aoyagi/Lemma5FirstNonbaseOrderBridge.lean`, the umbrella
import in `lean/DLNFibre.lean`, and the A5 reproduction and statement-card
notes for this slice.

## Findings

Low, fixed: the first review pass found the new `DLNFibre.lean` import inserted
before the end of the aggregator file, contrary to the file's local import
discipline.  The import has been moved to the end of `DLNFibre.lean`.

No mathematical or source-fidelity issue was found.  The Lean theorem is a
thin wrapper around the existing first-nonbase cardinal bound:

```text
candidates.card <= data.aParam * (ell - data.aParam) + 1.
```

It specializes the previous theorem to `a = data.aParam` and
`M = data.ceilWidth`, then rewrites the right-hand side using
`AoyagiDefinition3CeilData.theorem2OrderFormula`.

The source-facing hypotheses remain explicit: terminal chain endpoints,
binary prefix deltas, base-value interval membership, and selector injectivity
on the candidate set.  The docs correctly avoid claiming source classifier
construction, selector injectivity, terminal exactness, pole order, normal
crossings, or RLCT extraction.

## Residual Boundaries

- Construction of Aoyagi's source vectors.
- Proof that the deterministic selector is source-canonical.
- Selector injectivity.
- Counted-datum back-to-label coverage.
- Exact terminal-minimum label count.
- Finite minimum-to-`lambda` equality.
- Pole order, normal crossings, and RLCT extraction.
