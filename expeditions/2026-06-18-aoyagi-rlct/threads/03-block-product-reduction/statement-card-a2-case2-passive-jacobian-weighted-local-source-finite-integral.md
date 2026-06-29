# Statement Card - A2 Case 2 Passive Jacobian-Weighted Local-Source Finite Integral

Status: sorry-free focused build and full aggregator build passed; direct
axiom probe passed; xhigh reviews PASS.

Reproduction:

```text
reproduction-a2-case2-passive-jacobian-weighted-local-source-finite-integral.md
```

Review:

```text
review-a2-case2-passive-jacobian-weighted-local-source-finite-integral.md
```

Lean files:

```text
lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCase2LocalJacobianMeasure.lean
```

## Claim

For the chart-produced passive product-domain measure restricted to the
constructed open determinant neighborhood, weighted by the retained-passive
formal raw-order Jacobian factor, and pushed forward by the p.13 source chart,
the regular-coordinate finite-integral handoff holds over the retained-passive
local source, assuming the local loss lower bound and density bounds.

## Lean

```text
exists_open_lintegral_ofReal_loss_rpow_neg_mul_density_p13RegularCoordinates_lt_top_of_case2EndpointTransport_sourceEdgeFamilyOfData_withPassive_passiveProductMeasure_withDensity_jacobian_finiteMass
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

The proof invokes the banked passive Jacobian-weighted residual-source theorem,
then applies the generic retained-passive p.13 local-source finite-integral
handoff with `Cedge E = E`, `continuous_id`, and `rfl` for the fixed base.

## Assumed

- Case 2 dimension hypotheses `hS`, `hcont`, and `hnext`.
- Endpoint equivalences `e` and `eNext`.
- Continuity of `A1passive`, `F2`, `A3passive`, `Ctop`, and `F3`.
- Pointwise determinant units for `Ctop` and `A1passive`.
- A regular-coordinate source-data package at the fixed base edge family.
- Finite total passive mass: `passiveMeasure Set.univ < infinity`.
- Selected-entry signed-box radius positivity: `forall i, 0 < Rres i`.
- Exponent hypotheses `0 < t` and the selected-entry critical inequality.
- Local loss lower bound on `nhdsWithin base localSource`.
- Local density nonnegativity and upper bound on `nhdsWithin base localSource`.
- An additive Haar regular-coordinate measure `nu`.
- Borel/measurable-space structure on the source edge-family type when
  stating the pushforward conclusion.

## Cited

Aoyagi pp. 10-13 motivate the retained-passive p.13 block coordinates,
regular-coordinate decomposition, and Jacobian factor.  Aoyagi pp. 19-22
motivate the selected-entry residual chart.  The Lean proof is a
measure-theoretic local-source finite-integral handoff and does not cite an
analytic theorem.

## Deferred

- Exact localized residual marginal.
- Determinant-chart Haar pushforward.
- Raw/source Haar theorem.
- Original or external DLN source-prior transport.
- Source-prior Jacobian formula.
- Source-image equality or local coverage.
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

Independent xhigh reviews by `Erdos the 3rd` and `Lovelace the 3rd` passed;
see
`review-a2-case2-passive-jacobian-weighted-local-source-finite-integral.md`.

## Nonclaims

This card does not prove an exact localized residual marginal, determinant-
chart Haar pushforward, raw/source Haar theorem, original source-prior
transport, source-prior Jacobian formula, source-image equality, local
coverage, normal crossings, pole order, or RLCT.
