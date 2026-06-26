# Review - A2 retained-passive Ctop determinant chart

Date: 2026-06-26.

Reviewer: xhigh read-only reviewer `Mill the 3rd`.

## Scope

Audit the uncommitted Ctop-tracking slice in
`lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCoordinates.lean`:

```text
ChartLocalSuffixState.step_retainedPassiveFixedBaseEdgeMatrix_Ctop
ChartLocalSuffixState.suffixState_Ctop_retainedPassiveFixedBaseEdgeMatrix_castSucc
ChartLocalSuffixState.suffixState_Ctop_det_isUnit_retainedPassiveFixedBaseEdgeMatrix
```

The review checked for formalisation or mathematical inaccuracies, index/sign
errors hidden by simplification, overclaiming relative to the retained-passive
coordinate inverse reproduction, and whether the determinant-unit theorem
states only the finite chart fact proved.

## Verdict

PASS.  No findings.

## Checks

- `step_retainedPassiveFixedBaseEdgeMatrix_Ctop` matches the existing
  suffix-state step definition: after the retained-passive transformed-edge
  cancellation, the step updates `Ctop` by multiplying with the transformed
  edge's top-left block, namely `A1 p`.
- `suffixState_Ctop_retainedPassiveFixedBaseEdgeMatrix_castSucc` has the right
  orientation:

  ```text
  Ctop_p = Ctop_{p+1} * A1_p.
  ```

  This matches the pen-and-paper retained-passive recursion.
- `suffixState_Ctop_det_isUnit_retainedPassiveFixedBaseEdgeMatrix` proves the
  finite constructor-side propagation from terminal `Ctop_N = I` under
  `∀ p, IsUnit det(A1_p)`.  No hidden index or sign issue was found.

## Caveat

The determinant-unit theorem is for the reconstructed fixed-base family after
all edge variables `A1_p` are assumed or proved determinant units.  It is not
yet the retained-passive coordinate-domain theorem where `Ctop_0` is active
and only the passive `A1_p` for `p > 0` are input variables.

## Nonclaims

No active endpoint recovery for `A1_0` or `A3_last`, no source coverage, no
source-measure pushforward, no Jacobian/prior density theorem, no normal
crossings, no pole order, and no RLCT are proved.

## Verification

The focused build passed:

```text
cd lean
env LAKE_SHARED="$PWD/.lake-local-shared" scripts/lb DLNFibre.DLN.Aoyagi.RetainedPassiveCoordinates
```
