# Review - A2 retained-passive recoverable readbacks

Date: 2026-06-26.

Reviewer: xhigh read-only reviewer `Hegel the 3rd`.

## Scope

Audit the retained-passive recoverable readback rung in
`lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCoordinates.lean`:

```text
ChartLocalSuffixState.RetainedPassiveCoordinateData.edgeMatrix_recoverableReadbacks_eq_targets
ChartLocalSuffixState.RetainedPassiveCoordinateData.edgeMatrix_recoverable_ext
```

The review also checked the reproduction and statement card for endpoint
scope, dummy-field exclusions, and nonclaims.

## Verdict

PASS.

## Checks

The recovered fields are exactly scoped as intended:

```text
source-left: F2_0, Ctop, F3;
per-edge: A1seed_p only for p != 0,
          F2_{p.castSucc},
          A3seed_p only for p != Fin.last M,
          C_p.
```

The extensionality theorem avoids the false full equality claim
`data = data'`.  It proves equality only of the recoverable fields.  Full
`F2 = F2'` is obtained by splitting with `Fin.forall_iff_castSucc`: non-final
coordinates come from transformed-edge readbacks, and the final coordinate is
determined by the two `F2_last=0` side conditions.

The `M=0` endpoint case is sound.  On `Fin 1`, the hypotheses `p != 0` and
`p != Fin.last M` are vacuous, while `p.castSucc` covers the non-final
`F2_0` coordinate and `Fin.last (M+1)` is fixed by the side condition.

The Lean proofs use only existing finite readback algebra:

```text
RetainedPassiveCoordinateData.edgeMatrix_readbacks_eq_targets
retainedPassiveSolvedA1_eq_of_ne_zero
retainedPassiveSolvedA3_eq_of_ne_last
Fin.forall_iff_castSucc
```

No topology, coverage, measure, RLCT, or quiver-paper dependence was found.

## Nonclaims

No full coordinate-data injectivity is proved.  The dummy seed fields
`A1seed 0` and `A3seed (Fin.last M)` are intentionally outside the recovered
coordinate set.  No open coordinate domain, source-rank coverage,
source/image theorem, measure pushforward, density/Jacobian theorem, normal
crossings, pole order, or RLCT extraction is claimed.
