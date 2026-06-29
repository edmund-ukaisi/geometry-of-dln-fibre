# Reproduction - A2 Retained-Passive Source-Prior Passive-Variable Frontier

Date: 2026-06-29.

Status: controller pen-and-paper reproduction and frontier sharpening after
post-interruption xhigh scout round.  No Lean theorem is claimed here.

## Question

Can the current Case 2 selected-entry signed-box source measure be used to
remove the determinant-chart pushforward hypothesis

```text
m.restrict Sdet = Measure.map chart weightedBox
```

or to identify the raw-order inverse-Jacobian retained-passive chart measure
with an original DLN source prior?

Answer: not by itself.  The selected-entry signed-box chart is a reduced
section.  It is sufficient for the chart-produced finite-integral theorems
already proved, but it is not full determinant-chart Haar measure and not an
original source prior.  To remove the map/source-prior field, the construction
must add the passive variables that Aoyagi's p.13 algebra suppresses after the
block reductions.

## Source Calculation

Aoyagi pp. 10-13 give the following finite matrix substitutions.

For one block matrix

```text
A = [A1 A2
     A3 A4]
```

with `A1` invertible, Lemma 2 sets

```text
F2 = -A1^{-1} A2,
F3 = -A3 A1^{-1},
C4 = -A3 A1^{-1} A2 + A4.
```

Then

```text
[I 0; F3 I] A [I F2; 0 I] = [A1 0; 0 C4].
```

In Theorem 3, suppose the first `S` factors have already been reduced to a
top block `C1'` and a residual product `D = prod_{s=1}^S C^(s)`.  Write the
next transformed factor as

```text
A' = [A1' A2'
      A3' A4'].
```

The source text uses

```text
C^(S+1) = -A3' A1'^{-1} A2' + A4',
F2'' = -A1'^{-1} A2',
F3'' = F3' - D A3' (C1' A1')^{-1}.
```

The p.13 product-difference display is

```text
P1 (prod_s A^(s) - [I 0; 0 0]) P2
  =
[ C1 - I        -F2
  -F3    prod_s C^(s) - F3 F2 ].
```

The order of the last product is `F3 F2`, with signs as displayed.

## One-Step Full Coordinate Change

The one-step product-reduction coordinate change already present in Lean is
the correct local model for the passive variables.

Raw variables:

```text
(C1, D, F3old, A1, A2, A3, A4)
```

Chart variables:

```text
(Ctop, D, A1, A3, F2, F3, C)
```

On the determinant chart, with `A1` and `Ctop = C1 A1` invertible, the forward
change is

```text
Ctop = C1 A1,
D    = D,
A1   = A1,
A3   = A3,
F2   = -A1^{-1} A2,
F3   = F3old - D A3 Ctop^{-1},
C    = A4 - A3 A1^{-1} A2.
```

The inverse is

```text
C1    = Ctop A1^{-1},
D     = D,
F3old = F3 + D A3 Ctop^{-1},
A1    = A1,
A2    = -A1 F2,
A3    = A3,
A4    = C - A3 F2.
```

Substituting the inverse into the forward equations recovers each chart
variable:

- `Ctop`: `(Ctop A1^{-1}) A1 = Ctop`.
- `F2`: `-A1^{-1} (-A1 F2) = F2`.
- `F3`: `(F3 + D A3 Ctop^{-1}) - D A3 Ctop^{-1} = F3`.
- `C`: `(C - A3 F2) - A3 A1^{-1} (-A1 F2) = C`.

Substituting the forward equations into the inverse recovers each raw variable:

- `C1`: `(C1 A1) A1^{-1} = C1`.
- `A2`: `-A1 (-A1^{-1} A2) = A2`.
- `F3old`:
  `(F3old - D A3 (C1 A1)^{-1}) + D A3 (C1 A1)^{-1} = F3old`.
- `A4`:
  `(A4 - A3 A1^{-1} A2) - A3 (-A1^{-1} A2) = A4`.

This is a full-dimensional coordinate change.  The variables `A1` and `A3`
are passive for the p.13 singular residual but essential for the source-prior
or raw-Haar measure.

## Why The Reduced Section Cannot Remove The Map Hypothesis

The reduced p.13 section used by the current selected-entry lane does not
range over the full raw determinant chart.  In the one-step language, it fixes
passive raw coordinates such as

```text
C1 = I,
A3 = 0.
```

This is a positive-codimension condition whenever the retained block and
lower-left block have positive dimension.  Therefore a pushforward from this
reduced section cannot equal Haar measure restricted to the full raw
determinant chart.  At most it can produce a chart-image measure supported on
that section or on a selected-entry residual image.

The current Case 2 source measure

```text
sourceMeasure =
  (signed selected-entry box).withDensity sourceDensity
mu = Measure.map sourceChart sourceMeasure
```

is exactly such a chart-produced measure.  Its role is legitimate in the
proved finite-integral theorems, but it does not identify the original source
prior.

## Measure Accounting

For the full one-step coordinate change, the determinant of the derivative is
already represented in Lean by the product-reduction raw-order Jacobian
package:

```text
productReductionStepRawOrderJacobianAbsDet
productReductionStepRawOrderInverseJacobianDensity
map_productReductionStepRawOrder_restrict_detChart_eq_withDensity_inverseJacobian
```

For the multi-step retained-passive chart, the analogous retained-passive
package is:

```text
topologyTupleEdgeRawOrderFDerivAbsDet
topologyTupleEdgeRawOrderInverseJacobianDensity
map_topologyTupleEdgeRawOrder_restrict_detChart_eq_withDensity_inverseJacobian
measure_map_paperEndpointFixedBaseRetainedPassiveP13SourceEdgeFamilyOfData_restrict_detChart_eq_map_rawOrderSourceChart_withDensity_inverseJacobian
```

These theorems identify determinant-chart coordinate Haar measure with the
raw-order retained-passive source chart measure after applying the appropriate
inverse-Jacobian density.  They do not include the selected-entry
residual-coordinate substitution and they do not identify an external prior.

The selected-entry density

```text
SelectedEntrySignedBox.CenterCoord.sourceDensity pivot y = |y_pivot|^(# center.erase pivot)
```

accounts only for the finite selected-entry residual chart.  A full
source-prior construction must multiply this selected-entry factor by the
passive-coordinate Jacobian unit factors from the retained-passive chart, or
must prove that those factors are bounded above and below by positive constants
on the chosen passive neighborhood.

Near the self-base, the passive determinant factors are units because the
determinant-chart conditions place the invertible blocks near identity.  Thus
they should not alter the singular exponent, but they must still appear in the
measure theorem or in a bounded-unit comparison theorem.

## Multi-Step Construction Target

The needed construction is a product coordinate domain of the following form:

```text
passive retained coordinates
  x
selected-entry residual coordinates
  y
regular p.13 coordinates
  u
```

The source map should first build retained-passive determinant-chart data from
`(x,y)`, then realise those data as fixed-base source edge families by

```text
paperEndpointFixedBaseRetainedPassiveP13SourceEdgeFamilyOfData.
```

The local inverse should recover:

- the passive retained coordinates from source readback;
- the selected-entry residual coordinates from the chosen pivot chart;
- the p.13 regular variables from the existing regular-coordinate readout.

The measure theorem should state one of the following, without conflating
them.

Full retained-passive chart measure:

```text
Measure.map sourceChart
  ((fullCoordinateHaar.restrict fullChartDomain).withDensity fullJacobian)
= rawOrderRetainedPassiveSourceMeasure
```

Selected-entry sector measure with passive variables:

```text
Measure.map sourceChart
  ((passiveHaar.prod selectedEntryWeightedBox).withDensity passiveUnitDensity)
= selectedEntrySectorMeasure
```

External source-prior comparison:

```text
externalSourcePrior.restrict U
  is mutually absolutely continuous with
rawOrderRetainedPassiveSourceMeasure.restrict U
```

or, if the prior is exactly Lebesgue in these coordinates, an equality with an
explicit density.  The theorem must state which of these it proves.

## Formalisation Consequence

The next Lean theorem should remove an actual supplied field.  The following
names are schematic placeholders only:

```text
-- full/passive chart source-prior transport
map_retainedPassiveFullCoordinateSourceChart_eq_rawOrderMeasure_withDensity

-- selected-entry sector with passive variables included
map_retainedPassivePassiveSelectedEntryChart_eq_sectorMeasure

-- image/coverage theorem for source-rank points
exists_open_case2EndpointTransport_sourceRankStratum_subset_selectedEntryPassiveImage
```

Before implementation, one target must be sharpened into a concrete statement
with explicit coordinate domain, source map, inverse or image theorem, source
and target measures, local neighborhood, pivot-sector, and rank hypotheses.

A theorem that still assumes the determinant-chart pushforward
`m.restrict Sdet = Measure.map chart weightedBox`, assumes an external
source-prior equality, or defines the source measure to be the desired target
is not a payoff at this frontier.

## Kill Conditions

- Reject any proof that uses the current reduced selected-entry section to
  conclude full determinant-chart Haar or raw-Haar pushforward.
- Reject any source-prior theorem without a named coordinate domain, source
  map, local inverse, image or coverage theorem, measure theorem, and
  Jacobian density.
- Do not treat the selected-entry density as accounting for passive
  determinant variables.
- Do not add passive variables to the singular exponent shift; prove they are
  bounded units or keep their density factors explicit.
- Do not drop source-rank equations, image coverage, or exact-rank openness
  unless they are proved.
- Keep normal-crossing-to-RLCT extraction as the cited analytic boundary.

## Current Status

This reproduction confirms that the next A2 work is a construction package,
not another finite-integral wrapper.  The source-backed elementary part is the
retained-passive full-coordinate algebra above.  The measure/source-prior
payoff is not formalisation-ready until the passive coordinate domain and its
source map, inverse, coverage/image theorem, and Jacobian accounting are
written as explicit Lean objects.
