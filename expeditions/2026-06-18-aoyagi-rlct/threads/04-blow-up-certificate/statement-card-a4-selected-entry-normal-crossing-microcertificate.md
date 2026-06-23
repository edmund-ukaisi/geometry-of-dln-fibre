# Statement card - A4 selected-entry finite normal-crossing microcertificate

## Lean Artifact

File:

- `lean/DLNFibre/DLN/Aoyagi/SelectedEntryNormalCrossing.lean`

Names:

- `selectedEntryCenterSqFormalJacobianChartCertificate`
- `selectedEntryCenterSqFormalJacobianChartCertificate.lossExp_zero_zero`
- `selectedEntryCenterSqFormalJacobianChartCertificate.jacobianPriorExp_zero_zero`
- `case2DisplayedCenterSqFormalJacobianChartCertificate`
- `case2DisplayedCenterSqFormalJacobianChartCertificate.lossExp_zero_zero`
- `case2DisplayedCenterSqFormalJacobianChartCertificate.jacobianPriorExp_zero_zero`
- `case2DisplayedCenterSqFormalJacobianChartCertificate.localExponentCoordinateBridge`

## Claim

The elementary selected-entry chart for a finite center gives a one-chart
`AoyagiNormalCrossingChartCertificate` for the finite center square-sum and
the formal pivot-first determinant.  The parameter type is the finite-center
value function, and the chart residual coordinates are indexed by
`center.erase pivot`.  In the Case 2 displayed residual-block center, the
unique coordinate has loss exponent `1` and formal Jacobian/prior exponent
equal to the number of non-pivot residual-block center entries.

## Inputs Kept Explicit

- a finite center `center : Finset iota`;
- a selected pivot `pivot : center`;
- an ordered field coefficient type;
- residual coordinates indexed only by the erased finite center
  `center.erase pivot`;
- for the Case 2 specialization, `1 <= S` and
  `J+1 <= prefixMinNat n (S+1)`, which put `(J+1,J+1)` in the residual-block
  center;
- for the bridge theorem, the existing displayed continuing Case 2 local
  finite certificate.

## Proved

The generic certificate has one chart and one coordinate `u`.  Its loss field
is

```text
selectedEntryCenterSq center value,
```

and its chart pullback is

```text
selectedEntryCenterSqUnitFactor (center.erase pivot) residual * u^(2 * 1),
```

where `residual` is the ambient extension of the erased-center residual
coordinates.  The loss unit is an algebraic unit over an ordered field.  The
Jacobian/prior field is the formal pivot-first determinant

```text
u ^ (center.erase pivot).card
```

with unit factor `1`.  The Case 2 specialization applies this to
`case2ResidualBlockPivotEntries n S J` at the displayed pivot `(J+1,J+1)`.
For this microcertificate's own exponent data, the Case 2/A0 exponent
coordinate bridge is constructed rather than supplied.

## Not Proved

No chart coverage, no source production of successor data, no analytic
regularity or transition regularity, no analytic Jacobian or volume-form
theorem, no total DLN loss monomial identity, no global A0 chart family, no
active-ratio lower bound, no pole-order count, no pole order, and no RLCT
extraction.

## Verification

Controller ran:

```text
cd lean && lake build DLNFibre.DLN.Aoyagi.SelectedEntryNormalCrossing
```

The focused build passed.  Full-library verification also passed.

## Review

Xhigh fidelity/bedrock review passed with no substantive issue; residual
polish was incorporated.  See
`review-selected-entry-normal-crossing-microcertificate-a4.md`.
