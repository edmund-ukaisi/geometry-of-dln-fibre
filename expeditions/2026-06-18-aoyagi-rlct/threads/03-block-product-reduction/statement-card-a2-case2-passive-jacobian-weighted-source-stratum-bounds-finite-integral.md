# Statement Card - A2 Case 2 Passive Jacobian-Weighted Source-Stratum Bounds Finite Integral

Status: focused build, full aggregator build, hygiene checks, direct axiom
probe, and xhigh reviews passed.

Reproduction:

```text
reproduction-a2-case2-passive-jacobian-weighted-source-stratum-bounds-finite-integral.md
```

Review:

```text
review-a2-case2-passive-jacobian-weighted-source-stratum-bounds-finite-integral.md
```

Lean files:

```text
lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCase2LocalJacobianMeasure.lean
```

## Claim

For the chart-produced passive product-domain measure restricted to the
constructed open determinant neighborhood, weighted by the retained-passive
formal raw-order Jacobian factor, and pushed forward by the p.13 source chart,
the regular-coordinate finite-integral handoff holds with the loss and density
bounds stated on the source-rank stratum.

The residual positivity and residual negative-power integrability hypotheses
still come from the retained-passive local source.  The theorem bridges from
that local-source residual package to source-stratum comparison hypotheses by
using the retained-passive local-source coverage neighborhood at the fixed base
edge family.

## Lean

```text
exists_open_lintegral_ofReal_loss_rpow_neg_mul_density_p13RegularCoordinates_lt_top_of_case2EndpointTransport_sourceEdgeFamilyOfData_withPassive_passiveProductMeasure_withDensity_jacobian_finiteMass_sourceStratum_bounds
```

## Proved

The theorem constructs a source-domain open set `Udom` with `z0 in Udom`.  For

```text
jacobianWeightedMeasure =
  (sourceMeasure.restrict Udom).withDensity (fun z => ofReal (J z))

muJ = Measure.map sourceChart jacobianWeightedMeasure
```

it proves that there exists an open edge-family neighborhood `U` of the fixed
base edge family such that

```text
int^- (E,u),
  ofReal (1_{ball(0,R)}(u) *
    loss(E,u)^(-(t + regularVariableCount/2)) * density(E,u))
  d ((muJ.restrict (U inter sourceStratum)).prod nu)
  < infinity.
```

The proof invokes the passive Jacobian-weighted residual-source theorem,
installs `IsFiniteMeasure passiveMeasure` to obtain `SFinite muJ`, obtains the
retained-passive local-source coverage open set for `Cedge E = E`, and applies
the generic source-stratum-bounds/local-source finite-integral consumer.

## Assumed

- Case 2 dimension hypotheses `hS`, `hcont`, and `hnext`.
- Endpoint equivalences `e` and `eNext`.
- Continuity of `A1passive`, `F2`, `A3passive`, `Ctop`, and `F3`.
- Pointwise determinant units for `Ctop` and `A1passive`.
- A regular-coordinate source-data package at the fixed base edge family.
- Finite total passive mass: `passiveMeasure Set.univ < infinity`.
- Selected-entry signed-box radius positivity: `forall i, 0 < Rres i`.
- Exponent hypotheses `0 < t` and the selected-entry critical inequality.
- Loss lower bound on `nhdsWithin base sourceStratum`.
- Density nonnegativity and upper bound on `nhdsWithin base sourceStratum`.
- An additive Haar regular-coordinate measure `nu`.
- Borel/measurable-space structure on the source edge-family type when
  stating the pushforward conclusion.

## Cited

Aoyagi pp. 12-13 support the p.13 block/product-reduction display and the
separation of regular variables from the reduced product variables.  This Lean
theorem is a chart-produced finite-integral handoff; it does not cite an
analytic theorem.

## Deferred

- External or original DLN source-prior transport.
- Exact localized residual marginal.
- Determinant-chart Haar pushforward.
- Raw/source Haar theorem.
- Source-prior Jacobian formula.
- Source-image equality or source-rank coverage.
- Normal crossings, pole order, and RLCT extraction.

## Build

Focused build passed from `lean/`:

```text
scripts/lb DLNFibre.DLN.Aoyagi.RetainedPassiveCase2LocalJacobianMeasure
```

Full aggregator build passed:

```text
scripts/lb DLNFibre
```

`git diff --check` passed.  `scripts/sorries` reports
`0 sorry, 0 #exit, 0 native_decide, 0 axiom`.

Direct axiom probe for the new theorem reports
`[propext, Classical.choice, Quot.sound]`.

Independent xhigh reviews by `Bernoulli the 3rd` and `Kant the 3rd` passed
after one docstring-boundary repair; see
`review-a2-case2-passive-jacobian-weighted-source-stratum-bounds-finite-integral.md`.

## Nonclaims

This card does not prove an exact localized residual marginal, determinant-
chart Haar pushforward, raw/source Haar theorem, original source-prior
transport, source-prior Jacobian formula, source-image equality, source-rank
coverage, normal crossings, pole order, or RLCT.
