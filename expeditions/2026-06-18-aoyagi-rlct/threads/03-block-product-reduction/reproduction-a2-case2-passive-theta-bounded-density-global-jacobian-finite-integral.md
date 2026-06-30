# Reproduction - A2 Case 2 passive theta bounded-density global-Jacobian finite integral

Date: 2026-06-30.

Status: pen-and-paper reproduction for a landed Lean slice.

## Question

The current concrete `Case2PassiveTheta` residual-source frontier has a
theorem for an arbitrary `candidateMeasure`, but it still asks the caller to
supply the local domination

```text
candidateMeasure.restrict W <= c •
  (passiveSource.withDensity jacobianDensity).restrict W.
```

Can this field be removed when the candidate measure has the prior-shaped form

```text
sourceMeasure =
  (passiveSource.withDensity jacobianDensity).withDensity sourceDensity
```

and the extra density is locally bounded above?

Answer: yes.  On the returned open set `W`, the a.e. bound

```text
forall^ae z with respect to
  (passiveSource.withDensity jacobianDensity).restrict W,
sourceDensity z <= Csrc
```

implies the required local domination by the elementary `withDensity`
monotonicity calculation.  The existing residual-source theorem then supplies
local-source support, residual positivity, and residual negative-power
integrability.  The standard source-stratum finite-integral handoff converts
these residual hypotheses plus the source-stratum loss/density bounds into
the p.13 finite-integral conclusion.

## Measure Calculation

Let

```text
baseJ := passiveSource.withDensity jacobianDensity,
sourceMeasure := baseJ.withDensity sourceDensity.
```

On a measurable open set `W`,

```text
sourceMeasure.restrict W
  = (baseJ.withDensity sourceDensity).restrict W
  = (baseJ.restrict W).withDensity sourceDensity.
```

If

```text
sourceDensity <= Csrc     baseJ.restrict W-a.e.,
```

then

```text
(baseJ.restrict W).withDensity sourceDensity
  <= (baseJ.restrict W).withDensity (fun _ => Csrc)
  = Csrc • baseJ.restrict W.
```

This is exactly the domination hypothesis required by

```text
exists_open_residualSourceHypotheses_of_case2PassiveThetaEndpointSourceChart_puncturedSector_yNext_of_restrict_le_smul_globalWithDensity_jacobian_passiveProductMeasure_finiteMass.
```

The scalar must be finite (`Csrc < top`) because the residual-source theorem
uses finite scalar domination to preserve integrability.

## Finite-Integral Handoff

The residual-source theorem returns, for

```text
mu := map sourceChart (sourceMeasure.restrict W),
localSource := retained-passive p.13 local source,
```

the facts

```text
mu.restrict localSource = mu,
residualSquareSum > 0       mu.restrict localSource-a.e.,
residualNegPowerIntegrableOn localSource mu t.
```

As in the existing passive selected-entry finite-integral theorem, the
self-base retained-passive coverage lemma supplies an open neighborhood
`Ulocal` of the base source point such that

```text
Ulocal ∩ sourceStratum ⊆ Ulocal ∩ localSource.
```

The source-stratum finite-integral consumer then applies with loss and density
bounds stated on `nhdsWithin base sourceStratum`, yielding an open `U` in the
source edge-family space with

```text
lintegral over (mu.restrict (U ∩ sourceStratum)).prod nu < top.
```

## Source Boundary

Aoyagi's block calculations support the retained-passive p.13 coordinates,
the residual readout, and the selected-entry pivot chart used here.  This
slice adds only measure-theoretic bounded-density bookkeeping around those
already formalised coordinates.

It does not identify determinant-chart Haar measure, raw-order Haar measure,
or an original DLN source prior.  The source density is supplied as an
arbitrary nonnegative `ENNReal` density with an a.e. upper bound.  The theorem
therefore removes a local domination field but does not remove the external
source-prior construction gap.

## Lean Targets

Add in `RetainedPassiveCase2PassiveThetaJacobianMeasure.lean`:

```text
exists_open_residualSourceHypotheses_of_case2PassiveThetaEndpointSourceChart_puncturedSector_yNext_of_withDensity_ae_le_const_globalWithDensity_jacobian_passiveProductMeasure_finiteMass
```

and

```text
exists_open_lintegral_ofReal_loss_rpow_neg_mul_density_p13RegularCoordinates_lt_top_of_case2PassiveThetaEndpointSourceChart_puncturedSector_yNext_of_withDensity_ae_le_const_globalWithDensity_jacobian_passiveProductMeasure_finiteMass_sourceStratum_bounds
```

The helper should call the existing arbitrary-candidate residual-source
theorem with

```text
candidateMeasure := (passiveSource.withDensity jacobianDensity).withDensity sourceDensity
```

and discharge its domination field by `restrict_withDensity` and
`withDensity_mono`.

## Kill Conditions

- Do not name or state the theorem as source-prior transport.
- Do not claim exact passive-sector Haar transport.
- Do not replace `prod C - F3 F2` by `prod C` in any source-facing statement.
- Do not remove source-stratum loss/density hypotheses.
- Keep the normal-crossing-to-RLCT extraction outside this slice.
