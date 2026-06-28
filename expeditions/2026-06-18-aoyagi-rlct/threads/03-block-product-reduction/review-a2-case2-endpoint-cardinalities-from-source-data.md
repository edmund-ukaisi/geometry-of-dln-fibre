# Review - A2 Case 2 endpoint cardinalities from source data

Reviewer: Noether.  Effort: xhigh.  Mode: read-only.

## Verdict

PASS.

## Scope Checked

- `case2PostPivotTwoEdgeDomain_card_eq_endpointComplementIndex_of_sourceData`
  in `lean/DLNFibre/DLN/Aoyagi/Case2ResidualFactorProduct.lean`.
- `reproduction-a2-case2-endpoint-cardinalities-from-source-data.md`.
- `statement-card-a2-case2-endpoint-cardinalities-from-source-data.md`.
- Ledger updates in `priorities.md`, `synthesis.md`, `claims.md`,
  `theorem-ledger.md`, and thread `03-block-product-reduction/thread.md`.

## Findings

The Lean theorem proves only:

```text
sourceData + hTau + hCol + hRow
  -> forall q : Fin 3,
       card (case2PostPivotTwoEdgeDomain n S J tau q)
       =
       card (throughSubspaceEndpointComplementIndex ... q).
```

It does not construct `tau`, endpoint labels, endpoint equivalences, source
priors, Jacobians, normal crossings, pole order, or RLCT.  The proof is the
existing source-data cardinality theorem plus case analysis on `q : Fin 3`.

## Wording Fixes Applied

- The reproduction now records reuse of
  `endpointComplementIndex_card_eq_H_rev_sub_rank` rather than saying there is
  no reused theorem.
- The statement card now says no source-prior, measure, or Jacobian comparison.
- The theorem-ledger source reference now describes p.13 regular-coordinate
  block sizes formalized as endpoint-complement counts, avoiding any suggestion
  of canonical endpoint labels.
