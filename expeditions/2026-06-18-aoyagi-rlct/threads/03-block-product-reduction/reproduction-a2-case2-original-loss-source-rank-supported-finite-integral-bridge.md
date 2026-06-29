# A2 Case 2 original-loss source-rank-supported finite-integral bridge

## Claim

For the endpoint-transported explicit continuing Case 2 selected-entry source
chart, the newly proved endpoint-basis original-loss finite-integral theorem
can be restated over the open-neighborhood restriction `mu.restrict U` when the
chart-produced measure is supported on the source-rank stratum.

The theorem is a support restatement.  It does not prove source-rank coverage
or selected-entry source/image equality.

## Source Calculation

Aoyagi Theorem 3, PDF pp. 11-13, gives the p.13 product-coordinate chart used
through the Case 2 endpoint-transport construction.  In the continuing Case 2
selected-entry chart, the source-rank equations are:

```text
rank(total base product) = r,
r + card(tau) = rEdge 0,
forall yNext, r + rank(successor selected-entry matrix yNext) = rEdge 1.
```

These are not proved by the support wrapper.  They are explicit hypotheses.
Under these hypotheses, the already formalised pointwise source-rank readout
shows that every chart-produced edge family lies in

```text
sourceStratum =
  paperEndpointFixedBaseSourceRankStratum W2 B2 (fun E => E) r rEdge.
```

Therefore the chart-produced selected-entry source measure

```text
mu = Measure.map sourceChart sourceMeasure
```

is supported on `sourceStratum`:

```text
mu.restrict sourceStratum = mu.
```

## Measure Rewrite

The source-stratum original-loss finite-integral theorem returns an open
neighborhood `U` of `base` and a finite integral over

```text
(mu.restrict (U inter sourceStratum)).prod nu.
```

Since `U` is open, it is measurable, and the standard restriction identity
gives

```text
mu.restrict (U inter sourceStratum)
  = (mu.restrict sourceStratum).restrict U.
```

Using `mu.restrict sourceStratum = mu`, this becomes

```text
mu.restrict (U inter sourceStratum) = mu.restrict U.
```

Replacing the measure in the product integral gives the desired conclusion
over

```text
(mu.restrict U).prod nu.
```

The loss, target matrix, endpoint bases, density, radius, and exponent are
unchanged from the source-stratum theorem.

## Lean Route

1. Call

   ```text
   exists_radius_open_lintegral_ofReal_lossDLN_chainMapMatrixTuple_rpow_neg_mul_density_p13RegularCoordinates_lt_top_of_case2EndpointTransport_sourceEdgeFamilyOfData_selectedEntryCenter_signedBox_withDensity_sourceStratum_bounds_chartProducedMeasure_continuousAt_pos_density
   ```

   to get `R`, `C`, `U`, and finiteness over `U inter sourceStratum`.
2. Use

   ```text
   measure_map_case2EndpointTransport_sourceEdgeFamilyOfData_selectedEntryCenter_signedBox_withDensity_restrict_sourceRankStratum_eq_self
   ```

   with the explicit rank equations `hprod`, `hr0`, and `hr1`.
3. Prove

   ```text
   mu.restrict (U inter sourceStratum) = mu.restrict U
   ```

   by the same restriction calculation used in the existing generic-loss
   source-rank-supported wrapper.
4. Rewrite the final lower integral by that measure equality.

## Boundary

This proves only that an already chart-produced endpoint-basis original-loss
finite-integral result can be stated over `mu.restrict U` when support on the
source-rank stratum is supplied by explicit rank equations.  It does not prove
source-rank coverage, selected-entry source/image equality, external
source-prior transport, Jacobian comparison for such a prior, normal crossings,
pole order, or RLCT.

## Kill Conditions

- The rank equations do not match the hypotheses of the existing support
  theorem.
- The final measure is changed without proving
  `mu.restrict (U inter sourceStratum) = mu.restrict U`.
- The theorem is described as source-rank coverage rather than as a support
  restatement.
- The theorem claims any external prior or Jacobian transport.
