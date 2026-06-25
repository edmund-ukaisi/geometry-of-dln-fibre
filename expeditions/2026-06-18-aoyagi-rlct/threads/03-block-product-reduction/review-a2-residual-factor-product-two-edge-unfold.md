# Review - A2 residual-factor product two-edge unfold

Date: 2026-06-25.

Reviewer: controller, using xhigh source scout `Ohm` and xhigh Lean/API scout
`Goodall`.

## Verdict

Pass.  The theorem is a small generic unfold of the existing explicit
residual-factor product and does not overstate the Case 2 source boundary.

## Checks

- Source fit: Aoyagi pp. 19-22 support the local two-factor product
  `D_{J+1} * C'_+`, but only as finite Case 2 product algebra.
- API fit: the theorem stays in `ProductReduction.lean`, where
  `residualFactorProduct` is defined, and does not import product-reduction
  API into `BlowupArithmetic.lean`.
- Indexing: the statement exposes the necessary casts to the canonical middle
  endpoint `(1 : Fin 3)`.
- Deferred Case 2 package: no concrete dependent `Fin 3` Case 2 `Cfac` is
  introduced, because the residual-index equivalences and selected-entry
  matrix RHS are still supplied.
- Scope: no source/image equality, analytic coverage, Jacobian/density
  theorem, normal crossings, pole order, or RLCT is inferred.

## Lean Check

Focused check passed:

```text
lake env lean DLNFibre/DLN/Aoyagi/ProductReduction.lean
```

Full build passed:

```text
env LAKE_SHARED=/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/aoyagi-rlct/lean/.lake-local-shared scripts/lb
```

Sorry scan passed:

```text
scripts/sorries
```
