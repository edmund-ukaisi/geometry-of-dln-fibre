# Review - A2 Case 2 Passive Product-Measure Support

Date: 2026-06-29.

Reviewers: Lorentz the 3rd and Averroes the 3rd, xhigh, read-only scouts.

Verdict: PASS.

## Scope Checked

Lean theorem targets:

```text
case2PassiveDomainProductMeasure_eq_prod_withDensity_sourceDensity
measure_map_case2EndpointTransport_sourceEdgeFamilyOfData_withPassive_passiveProductMeasure_restrict_retainedPassiveP13LocalSource_eq_self
measure_map_case2EndpointTransport_sourceEdgeFamilyOfData_withPassive_passiveProductMeasure_restrict_sourceRankStratum_eq_self
```

## Findings

No API blocker was found for the theorem shape.

The local-source theorem is the preferred first target: it closes the exact
gap between arbitrary chart-produced support and passive chart continuity by
naming the concrete product measure and deriving `AEMeasurable sourceChart
sourceMeasure` from continuity.

The source-rank sibling is acceptable only with the successor-rank equation
left explicit as an a.e. hypothesis on the concrete `sourceMeasure`.  The
controller adjusted the statement to keep that a.e. hypothesis visible.

The product-density identity is harmless chart-domain bookkeeping using
Mathlib `prod_withDensity_right_0`; it should not be described as a source
Jacobian or prior transport theorem.

## Boundary

The package proves support of a chart-produced pushforward measure.  It does
not prove source-prior transport, determinant-chart pushforward, Jacobian
density, source-image equality, local coverage, source-rank coverage, normal
crossings, pole order, or RLCT.  It also does not prove determinant units,
rank equations, or positivity of signed-box radii.

## Gates

Focused build passed:

```text
scripts/lb DLNFibre.DLN.Aoyagi.RetainedPassiveCase2LocalJacobianMeasure
```

`git diff --check` passed.  `scripts/sorries` reports
`0 sorry, 0 #exit, 0 native_decide, 0 axiom`.

Direct axiom probes for all three theorem names report only
`[propext, Classical.choice, Quot.sound]`.
