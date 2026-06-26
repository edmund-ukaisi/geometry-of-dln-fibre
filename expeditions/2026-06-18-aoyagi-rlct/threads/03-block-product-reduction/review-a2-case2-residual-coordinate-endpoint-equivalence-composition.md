# Review - A2 Case 2 residual-coordinate endpoint-equivalence composition

Date: 2026-06-25.

Reviewer: controller, with xhigh source scout `Mendel` for the larger
endpoint-equivalence production question.

## Verdict

Pass for the stated finite bookkeeping claim.  The theorem only composes two
supplied endpoint equivalences with the already-landed Case 2 product-center
equivalence.

Mendel's source verdict for the larger frontier is negative: Aoyagi supplies
the displayed Case 2 interval reindexing, but not a source-faithful canonical
identification of the p.13 fixed-base endpoint complement indices with those
interval row and column types.  The endpoint row and column equivalences should
therefore remain explicit hypotheses unless a later construction adds
source-backed basis data.

## Checks

- The forward map sends `(i,j)` to the candidate pivot entry with source labels
  `((rowEquiv i).val, (colEquiv j).val)`.
- The orientation wrapper sends `(i,j)` to the source labels
  `((rowEquiv.symm i).val, (colEquiv.symm j).val)`, matching the endpoint
  equivalence orientation used by the Case 2 residual-factor product bridge.
- The inverse uses the inverse of the product-center equivalence and then the
  inverse endpoint row/column equivalences.
- The statement does not assert that Aoyagi supplies canonical endpoint
  equivalences; that remains the source-moving question.
- A noncanonical `Fintype.equivOfCardEq` construction would not be
  source-faithful endpoint readout data.

## Lean Check

Focused module build passed:

```text
env LAKE_SHARED=/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/aoyagi-rlct/lean/.lake-local-shared scripts/lb DLNFibre.DLN.Aoyagi.Case2ResidualIndex
```
