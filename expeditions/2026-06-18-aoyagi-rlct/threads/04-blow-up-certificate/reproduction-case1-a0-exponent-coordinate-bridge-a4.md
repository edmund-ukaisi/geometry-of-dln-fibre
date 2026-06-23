# Reproduction - A4/A0 Case 1 exponent-coordinate bridge

Date: 2026-06-23.

Status: reproduced, formalised, and reviewed.

Review:
`review-case1-a0-exponent-coordinate-bridge-a4.md`.

## Source Anchor

Aoyagi PDF pp. 5-6 gives the finite normal-crossing ratio for an active
coordinate with loss exponent `k_j > 0` and Jacobian/prior exponent `h_j`:

```text
(h_j + 1) / (2 k_j).
```

For Case 1(1), Aoyagi PDF pp. 15-16 uses the selected old exceptional
variable as the chart denominator.  In the finite Lean center this old
exceptional variable is represented by the left `Unit` token of
`Case1CenterGenerator`; the actual source label `(s0,k0)` remains supplied by
`Case1SelectedOldUnitSuppliedChartFamilyBoundary`.

The preceding selected-entry microcertificate slices proved the finite local
calculation for Case 1 centers: a selected-entry chart contributes one square
factor `u^2` and formal Jacobian/prior exponent equal to the number of
non-pivot center generators.  For the finite Case 1 center, erasing either the
selected-old token or Aoyagi's displayed row-strip pivot leaves

```text
J1 * (n (S + 1) - J)
```

non-pivot generators.

## Pen-and-Paper Calculation

Let `D` be supplied finite normal-crossing exponent data and let `p` be a
supplied coordinate of `D`.  Assume `p` matches the Case 1 selected-entry
local exponent calculation:

```text
D.lossExp p = 1,
D.jacobianPriorExp p = J1 * (n (S + 1) - J).
```

The first equality makes `p` active.  Its finite ratio is

```text
D.ratioAt p
  = (D.jacobianPriorExp p + 1) / (2 * D.lossExp p)
  = (J1 * (n (S + 1) - J) + 1) / 2
  = (1 + J1 * (n (S + 1) - J)) / 2.
```

If this candidate ratio lower-bounds every active coordinate in `D`, then the
finite minimum certificate from A0 proves

```text
D.exponentMinimum = (1 + J1 * (n (S + 1) - J)) / 2.
```

No chart count or order statement follows from this bridge.

## Source-Moving Wrapper

The useful source-facing wrapper is the selected-old one:

```text
Case1SelectedOldUnitA0ExponentCoordinateBridge
```

Its type carries a

```text
Case1SelectedOldUnitSuppliedChartFamilyBoundary
```

so downstream statements remember that the `Unit` token is tied to the
source-supplied selected old label.  The ratio proof still uses only the
explicit exponent equalities on the supplied coordinate.  This is deliberate:
the wrapper does not construct the A0 exponent datum, the coordinate `p`, or a
normal-crossing chart certificate.

## Lean Names

```text
Case1SelectedEntryExponentCoordinateBridge
Case1SelectedEntryExponentCoordinateBridge.of_chartCertificate_coord_exponents
Case1SelectedEntryExponentCoordinateBridge.activePair_and_ratioAt_eq_nonpivotCount_add_one_div_two
Case1SelectedEntryExponentCoordinateBridge.activePair
Case1SelectedEntryExponentCoordinateBridge.ratioAt_eq_nonpivotCount_add_one_div_two
Case1SelectedEntryExponentCoordinateBridge.exponentMinimum_eq_nonpivotCount_add_one_div_two_of_forall_le
Case1SelectedEntryA0ExponentCoordinateBridge
Case1SelectedEntryA0ExponentCoordinateBridge.of_chartCertificate_coord_exponents
Case1SelectedEntryA0ExponentCoordinateBridge.activePair_and_ratioAt_eq_nonpivotCount_add_one_div_two
Case1SelectedEntryA0ExponentCoordinateBridge.exponentMinimum_eq_nonpivotCount_add_one_div_two_of_forall_le
Case1SelectedOldUnitA0ExponentCoordinateBridge
Case1SelectedOldUnitA0ExponentCoordinateBridge.of_coord_exponents
Case1SelectedOldUnitA0ExponentCoordinateBridge.of_chartCertificate_coord_exponents
Case1SelectedOldUnitA0ExponentCoordinateBridge.activePair_and_ratioAt_eq_nonpivotCount_add_one_div_two
Case1SelectedOldUnitA0ExponentCoordinateBridge.exponentMinimum_eq_nonpivotCount_add_one_div_two_of_forall_le
case1SelectedOldCenterSqFormalJacobianChartCertificate.localExponentCoordinateBridge
case1DisplayedRowStripCenterSqFormalJacobianChartCertificate.localExponentCoordinateBridge
```

## Proved

- A supplied Case 1 selected-entry coordinate with loss exponent `1` and
  Jacobian/prior exponent `J1 * (n(S+1)-J)` is active.
- Its finite ratio is `(1 + J1 * (n(S+1)-J)) / 2`.
- Under an explicit all-active-coordinate lower bound by that ratio, the
  supplied finite exponent datum has that ratio as its finite minimum.
- The selected-old source-moving wrapper carries the existing Case 1(1)
  selected-old boundary as a type parameter.
- The selected-old and displayed-row-strip one-coordinate microcertificates
  supply the generic bridge for their own local exponent data.

## Not Proved

- No construction of `D` or `p`.
- No proof that the selected-old boundary produces an A0 chart certificate.
- No global active-ratio lower bound.
- No chart-count or exponent-order statement.
- No chart production, chart coverage, transition regularity, analytic unit
  neighbourhood, analytic Jacobian/volume-form theorem, pole order, or RLCT
  extraction.

## Kill Conditions

- Do not infer the hidden old source label `(s0,k0)` from the `Unit` token
  without the carried selected-old boundary.
- Do not use the local Case 1 ratio as the global exponent minimum unless the
  explicit lower-bound hypothesis has been proved for the supplied full A0
  exponent data.
- Do not use the formal selected-entry determinant exponent as an analytic
  Jacobian theorem.
