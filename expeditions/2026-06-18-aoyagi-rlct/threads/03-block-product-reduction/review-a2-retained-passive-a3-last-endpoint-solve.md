# Review - A2 retained-passive `A3_last` endpoint solve

Date: 2026-06-26.

Reviewer: xhigh read-only reviewer `Einstein the 3rd`.

## Scope

Audit the uncommitted Lean additions in
`lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCoordinates.lean`:

```text
ChartLocalSuffixState.retainedPassiveLowerLeftProductTailSum_last
ChartLocalSuffixState.retainedPassiveLowerLeftProductTailSum_last_eq_of_A3_eq_neg_target_mul_Ctop
```

The review checked nonempty final-edge indexing, sign and multiplication order,
the determinant-unit hypothesis used for cancellation, total-inverse caveats,
and whether the documentation overclaims beyond local endpoint algebra.

## Verdict

PASS.  No blocking findings.

## Checks

- Edges are indexed by `Fin (M+1)`, vertices by `Fin (M+2)`, and the final edge
  is `Fin.last M`; `(Fin.last M).succ` is the terminal vertex
  `Fin.last (M+1)` in the theorem signatures.
- The final product tail has the displayed order
  `-(I * A3_last * CtopLast^-1)`.
- The hypothesis `A3_last = -G * CtopLast` has the correct sign and right
  multiplication order.
- The only cancellation step is
  `Matrix.mul_nonsing_inv CtopLast hCtop`, with `hCtop : IsUnit CtopLast.det`.
- No inverse or cancellation of a residual `C` factor is introduced.
- The reproduction and statement card remain local: no prefix `G`
  construction, coordinate-domain theorem, coverage, measure transport, normal
  crossings, pole order, or RLCT is claimed.

## Verification

The reviewer ran:

```text
cd lean
env LAKE_SHARED="$PWD/.lake-local-shared" scripts/lb DLNFibre.DLN.Aoyagi.RetainedPassiveCoordinates
```

The focused build passed.

## Follow-up

The next retained-passive coordinate-domain target is to build the prefix term
from earlier passive `A3_p` variables, instantiate
`G = F3_0 + prefix`, and connect the local endpoint solve to the active source
coordinate.
