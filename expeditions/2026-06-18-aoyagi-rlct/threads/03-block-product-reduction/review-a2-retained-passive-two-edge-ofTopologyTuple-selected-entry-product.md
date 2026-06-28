# Review: A2 retained-passive two-edge `ofTopologyTuple` selected-entry product adapter

Reviewer: xhigh `Noether the 3rd`.

Verdict: PASS.

## Checks

- The Lean theorem is fixed to `M = 1`, an endpoint family
  `kappa : Fin 3 -> Type*`, and the whole product
  `residualFactorProduct (ofTopologyTuple z).C (Fin.last 2) 0`.
- The displayed factor identities `hD` and `hF`, and the entrywise
  selected-entry readout `hentry`, remain explicit supplied hypotheses.
- The proof is exactly the data-level theorem specialized to
  `data := ofTopologyTuple z`.
- The patch does not use the adjacent-window/full-suffix split theorem and
  does not infer or remove outside factors.
- The reproduction, statement card, and thread note state the longer-suffix
  nonclaim and outside-factor nonremoval.

## Verification

The reviewer ran:

```text
lake env lean DLNFibre/DLN/Aoyagi/RetainedPassiveCase2SelectedEntryChartBridge.lean
scripts/sorries
git diff --check
#print axioms residualFactorProduct_ofTopologyTuple_eq_selectedEntryCenter_matrix_of_case2PostPivot_entrywise
```

The axiom set was the standard Lean/Mathlib foundation
`[propext, Classical.choice, Quot.sound]`.

## Residual risks

This is not a selected-entry identity for arbitrary longer suffixes, and it
does not prove outside factor absorption/removal, zero-locus/nullity,
positivity, integrability, density transport, normal crossings, pole order, or
RLCT extraction.
