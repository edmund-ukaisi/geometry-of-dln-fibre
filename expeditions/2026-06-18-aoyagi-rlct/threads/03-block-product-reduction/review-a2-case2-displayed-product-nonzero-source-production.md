# Review - A2 Case 2 displayed product nonzero source production

Date: 2026-06-28.

Reviewer: xhigh `Wegener`.

Verdict: PASS.  No blocking soundness issues found.

## Scope Checked

The review checked the new finite constructed-data Lean layer:

```text
lean/DLNFibre/DLN/Aoyagi/Case2ResidualFactorProduct.lean
lean/DLNFibre/DLN/Aoyagi/Case2ResidualSelectedEntryChartBridge.lean
```

The product-side construction is generic over `[CommRing R]`: zero-extension
realises a prescribed successor Schur block, the free `Cprime` constructor
realises a prescribed following factor, and the chosen pair
`D = M.submatrix id eNext.symm`, `F = 1.submatrix id eNext` multiplies back to
`M`.

The selected-entry production layer is currently specialised to `ℝ`, matching
the existing real-valued selected-entry coordinate APIs.  The reproduction note
was updated after review to make this coefficient-domain split explicit.

## Confirmed Nonclaims

The review found no theorem upgrading this construction to arbitrary
retained-passive `sourceReadback` data.  The Lean docstrings and reproduction
keep the boundary explicit: no arbitrary retained-passive factor alignment, no
nonzeroness for `ofTopologyTuple z`, no source/prior transport, no normal
crossings, no pole order, and no RLCT extraction.

The reviewer did not run Lean builds.  The controller subsequently ran the
focused build for
`DLNFibre.DLN.Aoyagi.Case2ResidualSelectedEntryChartBridge`, a full `DLNFibre`
build, `scripts/sorries`, `git diff --check`, changed-Lean-file
forbidden-marker search, and direct `#print axioms` audits for the new public
endpoints.  These passed; the axiom footprint is
`[propext, Classical.choice, Quot.sound]`.
