# Review - A2 Case 2 explicit selected-entry source chart

Date: 2026-06-28.

Reviewer: xhigh `Hypatia`.

Verdict: PASS.  No blocking findings.

## Findings

The implementation exposes the constructed Case 2 source-production map as
explicit functions of successor selected-entry coordinates.

The endpoint orientation is correct:

```text
residual(yNext) zero-extends T(yNext).submatrix id eNext.symm,
Cprime(yNext) uses (1).submatrix id eNext as the following-factor tail.
```

The product order is correct.  The two-edge retained-passive residual-factor
product from `Fin.last 2` to `0` unfolds as `C 1 * C 0`, namely the post-pivot
residual block followed by the free following factor.

The main source-readback theorem goes through the actual source edge family
and `sourceReadback_edgeMatrix_eq`; it is not merely a theorem about the
constructed datum's `C` field.

The equality theorems do not require a nonzero pivot hypothesis.  Nonzeroness
is isolated in the `_ne_zero_of_yNext_pivot_ne_zero` corollaries.

The documentation and theorem names keep the scope narrow: this is a
parametric constructed source family.  It does not prove arbitrary retained-
passive coverage, continuity/measurability, Jacobian or source-prior
pushforward, normal crossings, pole order, or RLCT.

## Controller Verification

Focused build of
`DLNFibre.DLN.Aoyagi.RetainedPassiveCase2SelectedEntryChartBridge` passed.
Full `DLNFibre` build passed.  `scripts/sorries` reported zero forbidden
markers.  `git diff --check` and touched-Lean-file forbidden-marker search
were clean.  Direct axiom-footprint probes for the new endpoints reported
`[propext, Classical.choice, Quot.sound]`.
