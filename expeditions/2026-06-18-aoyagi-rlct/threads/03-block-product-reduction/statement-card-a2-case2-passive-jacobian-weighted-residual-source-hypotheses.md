# Statement Card - A2 Case 2 Passive Jacobian-Weighted Residual Source Hypotheses

Status: sorry-free focused build and full aggregator build passed; direct
axiom probe passed; xhigh reviews PASS.

Reproduction:

```text
reproduction-a2-case2-passive-jacobian-weighted-residual-source-hypotheses.md
```

Review:

```text
review-a2-case2-passive-jacobian-weighted-residual-source-hypotheses.md
```

Lean files:

```text
lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCase2LocalJacobianMeasure.lean
```

## Claim

For the local passive product-domain measure restricted to the constructed open
determinant neighborhood and weighted by the retained-passive formal raw-order
Jacobian factor, the source-chart pushforward satisfies the residual-source
positivity and finite negative-power integrability hypotheses over the
retained-passive p.13 local source.

## Lean

```text
exists_open_residualSourceHypotheses_of_case2EndpointTransport_sourceEdgeFamilyOfData_withPassive_passiveProductMeasure_withDensity_jacobian_finiteMass
```

## Proved

The theorem constructs an open set `U` with `z0 in U`.  For

```text
weighted =
  (sourceMeasure.restrict U).withDensity (fun z => ofReal (J z))

muJ = Measure.map sourceChart weighted

localSource =
  paperEndpointFixedBaseRetainedPassiveP13LocalSource ...
```

it proves

```text
for muJ.restrict localSource-a.e. E,
  0 < aoyagiCoordinateSquareSum
        (paperEndpointFixedBaseResidualBlockCoordinateMap ... E)

residualNegPowerIntegrableOn ... localSource muJ t.
```

The proof reuses the banked whole-measure Jacobian-weighted residual theorem,
rewrites the selected-entry `center` residual coordinate square-sum through
`aoyagiCoordinateSquareSum_comp_equiv`, and uses chart-produced support on the
retained-passive local source to rewrite `muJ.restrict localSource = muJ`.

## Assumed

- Case 2 dimension hypotheses `hS`, `hcont`, and `hnext`.
- Endpoint equivalences `e` and `eNext`.
- Continuity of `A1passive`, `F2`, `A3passive`, `Ctop`, and `F3`.
- Pointwise determinant units for `Ctop` and `A1passive`.
- Finite total passive mass: `passiveMeasure Set.univ < infinity`.
- Selected-entry signed-box radius positivity: `forall i, 0 < Rres i`.
- Exponent hypotheses `0 <= t` and the selected-entry critical inequality.
- Borel/measurable-space structure on the source edge-family type when
  stating the support conclusion.

## Cited

Aoyagi pp. 10-13 motivate the retained-passive p.13 block coordinates and
Jacobian factor.  Aoyagi pp. 19-22 motivate the selected-entry residual chart.
The Lean proof is measure-support packaging and finite-coordinate reindexing;
it does not cite an analytic theorem.

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

Independent xhigh reviews by `Dirac the 3rd` and `Hegel the 3rd` passed; see
`review-a2-case2-passive-jacobian-weighted-residual-source-hypotheses.md`.

## Nonclaims

This card does not prove an exact localized residual marginal, determinant-
chart Haar pushforward, raw/source Haar theorem, original source-prior
transport, source-prior Jacobian formula, source-image equality, local
coverage, normal crossings, pole order, or RLCT.
