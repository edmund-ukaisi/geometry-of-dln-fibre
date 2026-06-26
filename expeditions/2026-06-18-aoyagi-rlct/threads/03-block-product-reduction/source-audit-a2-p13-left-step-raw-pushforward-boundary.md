# Source Audit - A2 p.13 left-step raw pushforward boundary

Date: 2026-06-26.

Status: source boundary audited; no Lean theorem added.

## Question

Can Aoyagi pp. 5-14, and in particular Theorem 3 on pp. 11-13, be read as
supplying the raw source pushforward used by the p.13 left-step inverse-density
consumer?

In Lean shape, the candidate unsupported theorem would prove

```text
Measure.map p13ProductCoordinateLeftStepRawTopologyTuple eta =
  m.restrict rawDetChart
```

from the p.13 product-coordinate algebra alone.

## Source Readout

The page-pinned source audit used local Ghostscript text extraction and a
rendered check of the relevant pages.

- PDF p. 5 defines LCT and ideal LCT, and states Lemma 1 as ideal-generator
  monotonicity/invariance.  It does not state a product-coordinate
  pushforward.
- PDF p. 6 gives the generic Hironaka pullback form: a proper analytic map,
  monomialized loss, Jacobian/prior factor, and an integral substitution
  formula.  This is generic resolution machinery, not the p.13 product chart.
- PDF pp. 7-9 state the DLN model, Definition 3, and Theorem 2.  There is no
  source/product-coordinate measure theorem.
- PDF p. 10 starts Lemma 2.  The proof changes block variables such as
  `A4` to a Schur-complement variable and `A2,A3` to triangular coordinates.
  This is algebraic coordinate rewriting.
- PDF pp. 11-13 prove Theorem 3 by induction with explicit block
  substitutions and regular block triangular matrices.
- PDF p. 13 then writes the block product-difference and the displayed LCT
  equality with the regular-variable contribution.  It does not state a
  Jacobian determinant, density transport, image/coverage theorem, or measure
  equality for the raw determinant chart.
- PDF p. 14 starts Theorem 4 and the recursive blow-up setup.  It does not
  repair the p.13 raw-chart measure gap.

Verdict: pp. 5-14 do not supply a source/product-coordinate pushforward,
density/Jacobian transport theorem, or change-of-variables statement strong
enough to derive the raw pushforward above.  The generic Hironaka substitution
on p. 6 is the extraction background, not a concrete p.13 chart construction.

## Lean Boundary

The current Lean API correctly keeps the raw pushforward supplied.

In `ProductReductionStepMeasure.lean`:

```text
map_productReductionStepRawOrder_comp_eq_withDensity_inverseJacobian
```

takes

```text
hpre     : AEMeasurable pre eta
hpre_map : Measure.map pre eta =
             m.restrict (productReductionStepRawDetChartSet rho pi mu nu)
```

and produces the inverse-Jacobian weighted raw target measure.  The support
lemma

```text
ae_mem_productReductionStepRawDetChartSet_of_map_eq_restrict
```

also consumes the same supplied raw pushforward.

In `ProductReductionStepRegularDensity.lean`, the p.13 specializations

```text
ae_isUnit_ctopMatrix_det_of_p13RawPreimage_map_eq_restrict_rawDetChart
ae_isUnit_ctopMatrix_det_of_p13LeftStepRaw_map_eq_restrict_rawDetChart
map_p13RawOrderTuple_eq_withDensity_inverseJacobian_of_rawPreimage_map
map_p13RawOrderTuple_eq_withDensity_inverseJacobian_of_leftStepRaw_map
map_p13RawOrderTuple_eq_withDensity_inverseJacobian_of_leftStepRaw_map_of_measurable_edgeMatrix
```

all keep the corresponding raw pushforward as an explicit hypothesis.  The
last theorem derives a.e. measurability from fixed-base edge-matrix
measurability, but it does not derive the pushforward.

## Pen-and-Paper Obstruction

The p.13 raw preimage tuple is a section of the full raw tuple space

```text
(C1, D, F3, A1, A2, A3, A4).
```

It fixes

```text
C1 = I
A3 = 0.
```

Lean records these guardrails as

```text
paperEndpointFixedBaseP13RawPreimageTuple_C1_eq_one
paperEndpointFixedBaseP13RawPreimageTuple_A3_eq_zero
p13ProductCoordinateLeftStepRawTopologyTuple_C1_eq_one
p13ProductCoordinateLeftStepRawTopologyTuple_A3_eq_zero
```

The raw determinant chart only asks that `det C1` and `det A1` are units.  If
the rank block `rho` is nonzero, the chart contains open sets with `C1 != I`,
for example near `2 * I`.  Additive Haar measure restricted to the raw chart
has positive mass on such open sets, while the p.13 section image has zero
mass there.  Hence the p.13 section cannot push any source measure to full
raw Haar restricted to the raw determinant chart.

The section codimension is

```text
(card rho)^2 + (card mu) * (card rho).
```

The `A3 = 0` part is vacuous if `mu = 0` or `rho = 0`, but `C1 = I` still
obstructs full raw-Haar pushforward whenever `rho > 0`.  When `rho = 0`, this
specific obstruction disappears; that exceptional case still does not prove
the remaining source-map pushforward.

## Decision

Do not add a theorem proving full raw-Haar pushforward from p.13 raw algebra.
The already-proved section-image theorem is the honest replacement:

```text
map_p13RawOrderTuple_eq_map_leftStepRawOrder_image_of_measurable_edgeMatrix
```

and its small-ball support wrapper:

```text
exists_pos_radius_le_map_p13RawOrderTuple_eq_map_leftStepRawOrder_image_of_ae_regular_mem_ball
```

Any future theorem with an inverse-Jacobian density conclusion must either keep
the raw pushforward supplied or construct a genuine p.13 source chart,
coverage theorem, and density/prior transport theorem for the correct source
measure.

## Nonclaims

No p.13 source coverage, no original DLN source/prior transport, no signed-box
density identification, no product-measure pushforward, no
regular-suspension certificate, no normal crossings, no pole order, and no
RLCT.
