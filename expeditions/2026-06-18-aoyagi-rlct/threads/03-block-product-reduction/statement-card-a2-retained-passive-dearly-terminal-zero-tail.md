# Statement Card - A2 retained-passive dEarly terminal zero tail

Status: reproduced by controller; Lean proved; focused build passed; xhigh
review passed; full verification passed.

## Claim

The retained-passive lower-left product tail with the final `A3` block zeroed
is constant zero at the terminal tail index:

```text
Tail_M(y) = 0.
```

Therefore

```text
d(Tail_M)_z(v) = 0.
```

## Lean Target

File:

```text
lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCoordinatesDerivative.lean
```

Lean name:

```text
fderiv_retainedPassiveLowerLeftProductTailSum_withoutLast_last_apply
```

## Dependencies

- `retainedPassiveLowerLeftProductTailSum_withoutLast_last`;
- `fderiv_const_apply`.

## Cited

None.

## Review

Xhigh reviewer `Aquinas` passed the theorem boundary, proof route, and
nonclaims.  Review record:
`review-a2-retained-passive-dearly-terminal-zero-tail.md`.

## Verification

Focused build of
`DLNFibre.DLN.Aoyagi.RetainedPassiveCoordinatesDerivative`, full `DLNFibre`
build, `scripts/sorries`, and `git diff --check` passed.  The theorem axiom
audit reports only `[propext, Classical.choice, Quot.sound]`.

## Deferred

Source staging for `dCprod`; source staging for `dPcast`; iteration of the
recurrence into a closed `dEarly` derivative expression; positive-tail `F3`
target staging; determinant theorem; measure theorem; normal crossings; pole
order; RLCT.

## Kill Conditions

- Do not read this as solved terminal `A3` or `F3` staging.
- Do not add determinant-chart or invertibility hypotheses to this boundary
  theorem.
- Do not claim `dCprod` or `dPcast` staging.
- Do not claim target staging, determinant equality, measure transport,
  normal crossings, pole order, or RLCT.
