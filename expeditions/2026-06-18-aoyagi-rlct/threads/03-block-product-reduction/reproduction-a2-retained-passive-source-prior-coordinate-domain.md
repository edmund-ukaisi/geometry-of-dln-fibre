# Reproduction - A2 Retained-Passive Source-Prior Coordinate Domain

Date: 2026-06-29.

Status: controller pen-and-paper reproduction after post-interruption scout
round; xhigh read-only review PASS.  No new Lean theorem is claimed here.

## Question

The current Case 2 selected-entry lane uses a chart-produced source measure.
Can it be promoted to a source-prior theorem for the p.13 retained-passive
coordinates?

Answer: only after keeping the passive variables and stating the measure
domain precisely.  Aoyagi pp. 10-13 support the elementary Schur algebra and
the p.13 product-difference variables.  They do not by themselves identify the
selected-entry signed-box measure with full determinant-chart Haar measure or
with an external DLN source prior.

## Source Equations

For one block matrix

```text
A = [ A1  A2
      A3  A4 ],
```

with `A1` invertible, Aoyagi Lemma 2 sets

```text
F2 = -A1^{-1} A2,
F3 = -A3 A1^{-1},
C4 = -A3 A1^{-1} A2 + A4,
```

and obtains

```text
[I 0; F3 I] A [I F2; 0 I] = [A1 0; 0 C4].
```

In the induction step of Theorem 3, after the first `S` factors have been
reduced to top block `C1'` and residual product `D = prod_{s=1}^S C^(s)`,
the next transformed factor

```text
A' = [ A1'  A2'
      A3'  A4' ]
```

gives

```text
C^(S+1) = -A3' (A1')^{-1} A2' + A4',
F2''    = -(A1')^{-1} A2',
F3''    = F3' - D A3' (C1' A1')^{-1}.
```

The p.13 product-difference display is

```text
[ C1 - I             -F2
  -F3     prod_s C^(s) - F3 F2 ].
```

The lower-right entry is the corrected residual block `D - F3 F2`, not just
`D`.

## One-Step Full Coordinates

The one-step full coordinate change has raw variables

```text
(C1, D, F3old, A1, A2, A3, A4)
```

and chart variables

```text
(Ctop, D, A1, A3, F2, F3, C),
```

with

```text
Ctop = C1 A1,
F2   = -A1^{-1} A2,
F3   = F3old - D A3 Ctop^{-1},
C    = A4 - A3 A1^{-1} A2.
```

On the determinant chart, the inverse is

```text
C1    = Ctop A1^{-1},
D     = D,
F3old = F3 + D A3 Ctop^{-1},
A1    = A1,
A2    = -A1 F2,
A3    = A3,
A4    = C - A3 F2.
```

This is the elementary calculation that keeps the variables suppressed by the
reduced p.13 selected-entry section.  The variables `A1` and `A3` are passive
for the singular residual but are necessary for a full source-measure theorem.

## Recursive Coordinate Domain

For the retained-passive p.13 chart with `M + 1` edges, the Lean coordinate
object is

```text
RetainedPassiveNonredundantCoordinateData
```

with stored fields

```text
A1passive : Fin M -> Matrix rho rho
F2        : forall p : Fin (M + 1), Matrix rho (kappa' p.castSucc)
A3passive : forall p : Fin M, Matrix (kappa' p.castSucc.succ) rho
C         : forall p : Fin (M + 1), Matrix (kappa' p.succ) (kappa' p.castSucc)
Ctop      : Matrix rho rho
F3        : Matrix (kappa' (Fin.last (M + 1))) rho.
```

The stored variables have the following interpretation.

```text
A1passive_q  = non-first invertible A1 blocks
F2_p         = all nonterminal right regular blocks
A3passive_q  = non-final lower-left blocks
C_p          = residual Schur factors
Ctop         = accumulated top block, with active variable Ctop - I
F3           = accumulated lower-left regular block
```

The full embedded coordinate record fills dummy slots

```text
A1seed_0 = 0,
A3seed_last = 0,
F2full_last = 0,
```

then solves the real endpoint variables:

```text
A1_0 = (A1_tail_after_first)^{-1} Ctop,
A3_last = -(F3 - earlyTail) CtopLast.
```

Here `A1_tail_after_first` is the product of the passive `A1` blocks to the
right of the first edge, `earlyTail` is the lower-left contribution from the
non-final passive `A3` blocks, and `CtopLast` is the corresponding rightmost
tail product of solved `A1` blocks.  These formulas are the recursive form of
the one-step inverse above.

The determinant chart is

```text
IsUnit Ctop.det
and
forall q : Fin M, IsUnit (A1passive q).det.
```

No determinant condition is imposed on the selected-entry residual coordinate
`y`.

## Source Map And Readback

From a retained-passive datum, define the solved full families `A1`, `A3`,
`F2full`, and `C`.  For each edge `p`, set the transformed block

```text
T_p =
  [ A1_p       -A1_p F2full_p
    A3_p        C_p - A3_p F2full_p ].
```

The fixed-base edge matrix is reconstructed by undoing the next upper
unitriangular suffix factor:

```text
E_p = [I, F2full_{p+1}; 0, I] T_p,
```

with `F2full_last = 0`, so the last multiplier is the identity.  In Lean this
is `RetainedPassiveNonredundantCoordinateData.edgeMatrix`.

Conversely, for a source edge family `E`, the deterministic source readback
uses the suffix state `S_{p+1}(E)` and transformed edge

```text
T_p(E) = [I, S_{p+1}.B; 0, I] E_p.
```

It reads

```text
A1_p = topLeft(T_p(E)),
F2_p = -A1_p^{-1} upperRight(T_p(E)),
A3_p = lowerLeft(T_p(E)),
C_p  = SchurResidual(T_p(E)),
Ctop = S_0.Ctop,
F3   = lowerLeft(S_0.L).
```

On the source-recursive determinant chart, the readback lies in the
retained-passive determinant chart and gives the coordinate inverse on the
determinant/source-recursive charts.  This is already represented by the
`sourceRecursiveDetChart`, `sourceReadback`,
`sourceReadback_edgeMatrix_eq`,
`edgeMatrix_sourceReadback_eq_of_sourceRecursiveDetChart`, and
`topologyTupleEdgeRawOrderInverse` families.

## Existing Measure Layer

There is already a full retained-passive determinant-chart change of
variables:

```text
Measure.map directChart (m.restrict S)
  =
Measure.map rawChart
  ((m.restrict T).withDensity inverseJacobianDensity).
```

Here `S` is the retained-passive topology-tuple determinant chart and `T` is
the raw-order source-recursive determinant chart.  This is a chart-layer
Haar/change-of-variables theorem for the retained-passive coordinates.  It
does not identify an external DLN source prior.

For Case 2 selected-entry coordinates, there are two current chart-produced
front ends.  The reduced selected-entry front end uses only residual
coordinates:

```text
sourceMeasure = weightedBox,
weightedBox = signedBox.withDensity selectedEntrySourceDensity,
mu = Measure.map sourceChart sourceMeasure.
```

The passive-sector helper layer adds a passive parameter measure:

```text
sourceMeasure = passiveMeasure.prod weightedBox,
weightedBox = signedBox.withDensity selectedEntrySourceDensity,
mu = Measure.map sourceChart sourceMeasure.
```

The selected-entry density accounts for the residual pivot chart only.  It
does not account for the passive determinant-chart variables unless those
variables are included in `passiveMeasure` and their Jacobian factor is kept
explicit or proved to be a bounded positive unit on a chosen neighborhood.

The passive-Jacobian unit facts already show that the solved-`A1` product
raw-order Jacobian is locally bounded above and below by positive constants
along the passive selected-entry parametrization, under continuity and
determinant-unit hypotheses.  That is bounded-unit accounting; it is not a
determinant-chart Haar pushforward.

## What Remains Open

The following statements are still distinct and must not be conflated.

Full retained-passive determinant-chart transport:

```text
full coordinate Haar on S
  --retained-passive COV-->
raw-order retained-passive source chart with inverse-Jacobian density.
```

Selected-entry passive sector measure:

```text
passiveMeasure.prod selectedEntryWeightedBox
  --sourceChart-->
chart-produced Case 2 source measure.
```

External source-prior comparison:

```text
external DLN source prior restricted to U
  is equal or mutually absolutely continuous to one of the chart measures.
```

The first is already present as retained-passive chart COV.  The second is the
measure used in the current Case 2 finite-integral theorems.  The third is not
proved.

The raw-order inverse-Jacobian Case 2 lane still contains the hypothesis

```text
m.restrict Sdet = Measure.map chart weightedBox.
```

This is not removable by the reduced selected-entry section: that section is
lower-dimensional inside the full determinant chart.  Removing it requires a
sector-level theorem with passive variables included, or a reparameterized
consumer whose measure is explicitly the chart-produced passive sector
measure.

## Next Lean Target Constraints

The next Lean statement should remove one named field, not repackage a
finite-integral theorem.  The acceptable shapes are:

```text
-- Sector transport, local and passive-variable explicit.
Measure.map sectorChart sectorMeasure =
  m.restrict sectorSet
```

with `sectorSet` not the full determinant chart unless the dimensions match;

```text
-- Source-prior comparison, explicit about density.
externalPrior.restrict U
  is mutually absolutely continuous with
Measure.map sourceChart sectorMeasure
```

or

```text
-- A consumer rewritten over the chart-produced passive sector measure,
-- with no hidden determinant-chart Haar hypothesis.
finiteIntegral_for_passiveSectorMeasure_without_hmap
```

The last option is useful only if it eliminates an existing downstream
`hmap`-style field and states that the measure is the passive sector measure,
not determinant-chart Haar.

## Kill Conditions

- Do not use the reduced selected-entry section to claim full
  determinant-chart Haar or raw-Haar pushforward.
- Do not call the selected-entry signed-box density a passive-variable
  Jacobian.
- Do not call chart-produced passive sector measure the original source prior.
- Do not drop passive `A1`, tail `F2`, or non-final `A3` variables from any
  source-prior theorem.
- Do not read the p.13 lower-right block as `prod C^(s)` instead of
  `prod C^(s) - F3 F2`.
- Do not treat local determinant-chart support as source-rank coverage.
- Keep normal-crossing-to-RLCT extraction as the only cited analytic boundary.

## Current Verdict

The retained-passive coordinate-domain and inverse layer is strong enough for
local source-map and chart-COV work.  The source-prior frontier is not solved
until the selected-entry passive sector is related to a precise measure on a
precise local sector, or until the downstream consumers are explicitly
rewritten to use the chart-produced passive sector measure without asserting
full determinant-chart Haar transport.
