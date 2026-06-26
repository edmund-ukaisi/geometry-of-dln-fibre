# Construction Plan - A2 Retained-Passive p.13 Source Chart

Date: 2026-06-26.

Status: controller construction plan after VM reorientation and xhigh scout
check-in.  No Lean theorem is claimed here.

## Trigger

The current p.13 raw-density frontier has one named supplied field that would
be meaningful to remove:

```text
hraw_map :
  Measure.map
    (p13ProductCoordinateLeftStepRawTopologyTuple V Bv U0 hU0 CedgeBase) eta =
  m.restrict (productReductionStepRawDetChartSet ...)
```

It appears in the concrete p.13 consumers

```text
map_p13RawOrderTuple_eq_withDensity_inverseJacobian_of_leftStepRaw_map
map_p13RawOrderTuple_eq_withDensity_inverseJacobian_of_leftStepRaw_map_of_measurable_edgeMatrix
```

and is the p.13 specialization of the generic `hpre_map` consumed by

```text
map_productReductionStepRawOrder_comp_eq_withDensity_inverseJacobian.
```

The second meaningful supplied field is the local source-rank coverage
hypothesis

```text
hcoverage :
  Ulocal inter sourceStratum subset Ulocal inter localSource
```

in

```text
exists_open_lintegral_ofReal_loss_rpow_neg_mul_density_p13RegularCoordinates_lt_top_of_sourceStratum_locally_subset_localSource.
```

The existing p.13 section cannot remove either field by itself.

## Negative Check

The tempting theorem

```text
Measure.map
  (p13ProductCoordinateLeftStepRawTopologyTuple V Bv U0 hU0 CedgeBase) eta =
  m.restrict (productReductionStepRawDetChartSet ...)
```

is false as a consequence of the current reduced p.13 section in positive
rank.  Lean proves the two fixed-section facts:

```text
p13ProductCoordinateLeftStepRawTopologyTuple_C1_eq_one
p13ProductCoordinateLeftStepRawTopologyTuple_A3_eq_zero
```

so the map lands in the locus `C1 = I`, `A3 = 0`, while the raw determinant
chart only requires determinant-unit conditions on `C1` and `A1`.  This is a
positive-codimension section whenever the retained rank block is nonzero.

The honest section-level measure theorem is already present:

```text
map_p13RawOrderTuple_eq_map_leftStepRawOrder_image_of_measurable_edgeMatrix
exists_pos_radius_le_map_p13RawOrderTuple_eq_map_leftStepRawOrder_image_of_ae_regular_mem_ball
```

These give functorial section-image identities, not raw-Haar transport.

## Retained-Passive Target

The next real A2 construction must replace the reduced section by a new chart
which keeps the passive variables that the p.13 section fixes or suppresses.

At one product-reduction step the already-formalised coordinate change is

```text
Raw:
  (C1, D, F3old, A1, A2, A3, A4)

Chart:
  (Ctop, D, A1, A3, F2, F3, C)

Ctop = C1 * A1
F2   = -A1^{-1} * A2
F3   = F3old - D * A3 * (C1 * A1)^{-1}
C    = A4 - A3 * A1^{-1} * A2
```

with inverse

```text
C1    = Ctop * A1^{-1}
D     = D
F3old = F3 + D * A3 * Ctop^{-1}
A1    = A1
A2    = -A1 * F2
A3    = A3
A4    = C - A3 * F2.
```

Lean already proves the one-step formal inverse and determinant-chart
infrastructure:

```text
productReductionStepCoordinate_left_inverse_of_isUnit_A1
productReductionStepCoordinate_right_inverse_of_isUnit_A1
map_productReductionStepRawOrder_restrict_detChart_eq_withDensity_inverseJacobian
map_productReductionStepRawOrder_comp_eq_withDensity_inverseJacobian
```

The retained-passive p.13 chart is not another proof of these one-step facts.
It is a multi-step source chart whose coordinate domain must include enough
passive data to reconstruct a local original edge family and enough active
data to expose the p.13 regular coordinates.

## Required Fields

A construction package is non-wrapper only if it produces all of the following
objects or makes the missing ones explicit in its theorem statement.

1. **Coordinate domain.**
   A finite-dimensional coordinate type with active p.13 coordinates
   `Ctop - I`, `F2`, `F3`, residual coordinates, and retained passive
   variables such as the invertible `A1` blocks and lower-left `A3` blocks.
   The domain must include determinant-unit neighborhoods for the retained
   invertible blocks.

2. **Source map.**
   A map from retained-passive coordinates to the original fixed-base edge
   family, or to a local source model that is explicitly related to the
   original fixed-base edge family.

3. **Local inverse.**
   A theorem that recovers the retained-passive coordinates from the source
   map on a specified local domain.  The one-step `toRaw`/`toChart` inverse is
   a component, not the whole theorem.

4. **Source-rank coverage.**
   A local theorem of the shape

   ```text
   Ulocal inter paperEndpointFixedBaseSourceRankStratum ... subset
     Ulocal inter retainedPassiveLocalSource
   ```

   or a stronger local image equality.  This is the field that can feed the
   existing `hcoverage` consumer.

5. **Measure pushforward.**
   A source-measure theorem for the retained-passive chart.  If it is meant to
   feed the raw-density p.13 consumer, it must produce a pushforward statement
   strong enough to replace `hraw_map`; otherwise it must state the exact
   weaker measure model it supplies.

6. **Density/Jacobian/prior accounting.**
   A proof that the transported source density is a bounded unit times the
   intended monomial factor, or a named theorem giving the exact inverse
   Jacobian/prior density required by the downstream finite-integral sockets.

7. **Residual and loss compatibility.**
   A proof that the residual block and p.13 active coordinates in the retained
   chart are the ones consumed by the already-landed square-sum and
   finite-integral theorems.

## First Lean Payoff

The first Lean theorem that would count as real progress is one of:

```text
-- Coverage payoff:
exists_retainedPassiveP13LocalSource_coverage :
  exists Ulocal localSource, ... /\
    Ulocal inter sourceStratum subset Ulocal inter localSource

-- Raw-density payoff:
map_retainedPassiveP13RawTuple_eq_restrict_rawDetChart :
  Measure.map retainedPassiveRawTuple eta =
    m.restrict (productReductionStepRawDetChartSet ...)

-- Consumer payoff:
map_p13RawOrderTuple_eq_withDensity_inverseJacobian_of_retainedPassiveChart :
  ... -- no hraw_map hypothesis for the reduced section;
      -- instead consumes the retained-passive chart construction.
```

A theorem that still assumes `hraw_map`, assumes `hcoverage`, or only combines
the existing section-image theorem with existing consumers is not progress at
this frontier.

## Pen-And-Paper Obligations

Before Lean implementation, reproduce the following on paper.

1. Write the retained-passive coordinate list for depth `M+2`, including the
   basepoint values and determinant-unit variables.
2. Derive the recursive inverse from retained coordinates back to edge blocks.
3. Check that the p.13 active square-sum still reads only `Ctop - I`, `F2`,
   `F3`, and the residual block, and that passive variables do not alter the
   singular exponent shift.
4. Prove or isolate the exact-rank/source-rank local coverage step.
5. Compute the product of one-step Jacobian factors and identify which factors
   are passive units near the basepoint.
6. Decide whether the resulting measure theorem feeds full raw Haar, a
   product measure on retained coordinates, or only a weaker source chart
   measure.  Do not collapse these three possibilities.

## Kill Conditions

- Reject any theorem using the current reduced
  `p13ProductCoordinateLeftStepRawTopologyTuple` to conclude full raw-Haar
  pushforward.
- Reject any retained-passive theorem that does not name its coordinate
  domain, source map, local inverse, coverage/image theorem, and density or
  Jacobian factor.
- Reject any coverage theorem that only sets
  `localSource = U inter sourceStratum` but does not provide the chart/source
  fields required downstream.
- Keep exact-rank openness, finite cover of determinant charts, and
  source-rank coverage explicit unless proved.
- Do not count passive variables as additional singular variables in the p.13
  regular-variable shift; they must be accounted for as units or harmless
  product factors.

## Controller Decision

The A2 wrapper search is closed.  The next A2 work is a construction package,
starting with a pen-and-paper retained-passive coordinate domain and inverse.
If that construction is too large for the next Lean tide, the correct
intermediate artifact is a statement card for one of the payoff theorem shapes
above, not another conditional consumer.
