# Review - A4/A0 Case 1 exponent-coordinate bridge

Date: 2026-06-23.

Status: xhigh source/math and Lean/API review passed.

## Reviewed Artifact

- `lean/DLNFibre/DLN/Aoyagi/Case1FiniteExponentBridge.lean`
- `reproduction-case1-a0-exponent-coordinate-bridge-a4.md`
- `statement-card-a4-a0-case1-exponent-coordinate-bridge.md`

Lean names reviewed:

```text
Case1SelectedEntryExponentCoordinateBridge
Case1SelectedEntryExponentCoordinateBridge.activePair_and_ratioAt_eq_nonpivotCount_add_one_div_two
Case1SelectedEntryExponentCoordinateBridge.exponentMinimum_eq_nonpivotCount_add_one_div_two_of_forall_le
Case1SelectedEntryA0ExponentCoordinateBridge
Case1SelectedOldUnitA0ExponentCoordinateBridge
Case1SelectedOldUnitA0ExponentCoordinateBridge.of_coord_exponents
Case1SelectedOldUnitA0ExponentCoordinateBridge.of_chartCertificate_coord_exponents
Case1SelectedOldUnitA0ExponentCoordinateBridge.activePair_and_ratioAt_eq_nonpivotCount_add_one_div_two
Case1SelectedOldUnitA0ExponentCoordinateBridge.exponentMinimum_eq_nonpivotCount_add_one_div_two_of_forall_le
case1SelectedOldCenterSqFormalJacobianChartCertificate.localExponentCoordinateBridge
case1DisplayedRowStripCenterSqFormalJacobianChartCertificate.localExponentCoordinateBridge
```

## Findings

Reviewer: `Kuhn`.

Verdict: pass; no blockers or correctness findings.

The reviewer confirmed that the generic bridge is narrow: it stores only the
two coordinate exponent equalities, derives active membership and the ratio

```text
((1 + J1 * (n (S + 1) - J)) : Q) / 2,
```

and requires an explicit all-active-coordinate lower bound before proving the
finite minimum.  This matches the finite `ratioAt = (h+1)/(2k)` interface in
`NormalCrossingInterface.lean`.

The selected-old source-moving wrapper was judged not to overclaim.  It
carries `Case1SelectedOldUnitSuppliedChartFamilyBoundary` as provenance, but
the constructors still require separately supplied exponent equalities.  The
carried boundary itself remains only a supplied chart-family/lowered-recurrence
package, not chart production.

The docs state the required caveats: no construction of `D` or `p`, no
selected-old boundary to A0 chart certificate, no global lower bound, no chart
count/order, no analytic Jacobian, no pole order, and no RLCT extraction.

## Verification

Focused reviewer check:

```text
cd lean && scripts/lb DLNFibre.DLN.Aoyagi.Case1FiniteExponentBridge
```

Controller checks:

```text
cd lean && scripts/lb DLNFibre.DLN.Aoyagi.Case1FiniteExponentBridge
cd lean && scripts/lb
cd lean && scripts/sorries
git diff --check
```

The focused build, full build, no-sorry audit, and diff hygiene gate passed.
The full build emitted only unrelated pre-existing Core linter warnings.

## Boundary

This review does not certify construction of finite exponent data, coordinate
production, global active-ratio lower bounds, chart counts, A0 chart
certificates, analytic Jacobian/volume-form control, pole order, or RLCT
extraction.
