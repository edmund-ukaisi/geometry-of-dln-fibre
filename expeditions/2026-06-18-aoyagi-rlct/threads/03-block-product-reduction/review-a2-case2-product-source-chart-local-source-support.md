# Review - A2 Case 2 product source-chart local-source support

Reviewer: xhigh `Avicenna the 2nd`

Status: PASS.

## Findings

- The generic local-source theorem uses the correct index shift: the
  product-coordinate family has `N := M + 2`, while the retained-passive local
  source is instantiated at `M := M + 1`.
- The proof soundly converts the product-coordinate certificate into
  local-source membership through
  `mem_paperEndpointFixedBaseRetainedPassiveP13LocalSource_iff_recursiveDetCharts`,
  using the certificate's `detCharts` field.
- The concrete Case 2 source-side wrapper correctly instantiates the generic
  theorem at `M := 0` for the product-coordinate construction and at `M := 1`
  for the two-edge retained-passive local source.
- The conversion from `(theta,u)` in the local source of `productSourceChart`
  to `productSourceChart (theta,u)` in the local source of `(fun E => E)` is
  definitional for the pullback edge-matrix predicate used by
  `paperEndpointFixedBaseRetainedPassiveP13LocalSource`.
- The small-ball wrapper uses only the determinant-unit radius for `ctopMatrix`
  and then applies the pointwise Case 2 theorem eventually.
- The reproduction and statement card keep the one-way support claim separate
  from source-rank coverage, source-image equality, source-prior transport,
  Haar/Jacobian transport, normal crossings, pole order, and RLCT extraction.

## Nonblocking Notes

No formal or mathematical issue was found.  The public theorem names are long,
but they state the exact chart and source-filter scope.

## Verification

Reviewer read-only checks reported `git diff --check` passing and no
`sorry`, `admit`, `axiom`, `#exit`, or `native_decide` markers in the touched
Lean file.  Controller verification also passed focused direct file checking
and the focused module build.  Controller final gates passed: full local
`lake build DLNFibre`, `scripts/sorries`, `git diff --check`, and a direct
axiom probe with footprint `[propext, Classical.choice, Quot.sound]`.
