# Reproduction - A2 p.13 passive-variable local source chart boundary

Date: 2026-06-26.

Status: source-boundary audit after the p.13 raw-section obstruction.  No Lean
theorem is proposed from this note alone.

## Question

The current p.13 left-step raw tuple is a section of the full raw
product-step determinant chart.  In one-step notation it has shape

```text
X(x,u) = (I, Dtail(x), F3(u), Ctop(u), -Ctop(u) F2(u), 0, C0(x)),
```

so the raw `C1` variable is fixed to `I` and the raw `A3` variable is fixed to
`0`.  This killed the proposed full raw-Haar pushforward.

The natural repair question is:

> If we retain the passive product-step variables instead of taking the p.13
> section, can Lemma 2 and Theorem 3 supply a genuine local source chart,
> local inverse, source-rank coverage, and source-measure/density transport
> near the p.13 base chain?

## Source Readout

Aoyagi Lemma 2, PDF p. 10, performs a block Schur-complement substitution on
a matrix whose top-left block is regular.  Theorem 3, PDF pp. 11-13, uses
that substitution inside an accumulated product-reduction induction.  In
source-normalised one-step notation, the resulting induction step is the
determinant-chart transformation between raw variables

```text
(C1, D, F3old, A1, A2, A3, A4)
```

and chart variables, in the raw-shaped target order used by the
determinant-facing measure API,

```text
(Ctop, D, F3, A1, F2, A3, C).
```

The Lean convention uses

```text
Ctop = C1 A1,
F2   = -A1^{-1} A2,
F3   = F3old - D A3 Ctop^{-1},
C    = A4 - A3 A1^{-1} A2.
```

The inverse formulas are

```text
C1    = Ctop A1^{-1},
D     = D,
F3old = F3 + D A3 Ctop^{-1},
A1    = A1,
A2    = -A1 F2,
A3    = A3,
A4    = C - A3 F2.
```

These are the formulas already represented by the raw product-step coordinate
API.  They do give a one-step determinant-chart inverse when `det C1` and
`det A1` are units, equivalently when `det Ctop` and `det A1` are units on
the target side.

Aoyagi Theorem 3, PDF pp. 11-13, iterates these block substitutions and then
displays the p.13 product-difference block.  In Lean one-step notation its
top-left product block is `Ctop`; the paper's local display writes this block
with a `C1`-style subscript, which should not be confused with the raw
product-step `C1` slot above.

```text
[ Ctop - Er      -F2 ]
[ -F3       prod C - F3 F2 ].
```

The p.13 reduction then reads the regular-variable contribution from the
entries of `Ctop-Er`, `F2`, and `F3`, and the residual contribution from the
lower-right product.  The printed text does not state a local inverse for the
full multi-step source map with every passive `A1`/`A3`-type variable retained.
It also does not state source-rank coverage, an image theorem, a source
pushforward, or a Jacobian/prior density theorem for that retained-passive
chart.

## Pen-And-Paper Separation

There are three different charts or parametrisations.

1. **Full one-step raw determinant chart.**  This is the elementary
   determinant chart for a single product-reduction step.  It keeps all raw
   variables and has the inverse formulas above.  In Lean this is already
   proved at the finite topological, derivative, determinant-unit, and
   additive-Haar change-of-variables levels.

2. **p.13 reduced section.**  The actual fixed-base p.13 regular-coordinate
   tuple used in the current A2 development sets

   ```text
   C1 = I,    A3 = 0,    A1 = Ctop.
   ```

   This section is source-faithful for the displayed p.13 reduced variables,
   but it is lower-dimensional inside the full raw determinant chart in
   positive rank.  It cannot push any measure to full raw Haar on that chart.
   The proved section-image theorem is therefore the honest measure statement:

   ```text
   Measure.map Y eta = Measure.map Phi (Measure.map X eta).
   ```

3. **Hypothetical retained-passive multi-step source chart.**  This would
   iterate the full one-step determinant charts while keeping the passive
   variables that the p.13 section fixes.  At one step, the extra `A1`
   direction is passive relative to the product-difference expression once
   `Ctop = C1 A1` is used, and the extra `A3` direction is also passive in
   the lower-right residual coordinate after the Schur substitution.  Thus an
   expanded chart is plausible as a way to repair the section obstruction.
   But it is a different object from the p.13 reduced section and would need
   its own source map, coverage theorem, product-measure decomposition, and
   density/Jacobian accounting.

The key calculation is that retaining `A1` changes the section equation
`C1=I, A1=Ctop` into the invertible change

```text
(C1,A1) <-> (Ctop,A1),    Ctop = C1 A1.
```

The product-difference only sees `Ctop-Er` in the regular top-left block, so
the additional `A1` variable is not a new singular coordinate.  Similarly,
retaining `A3` in the one-step inverse changes the section equation `A3=0`
into a passive chart variable, while the Schur coordinate `C` remains the
lower-right residual variable.

This explains why the full one-step raw product chart has a unit Jacobian
up to the already-proved determinant density, and why the p.13 section cannot
be used as full raw Haar.  It does not prove that the full retained-passive
multi-step chart covers the original source-rank stratum near the base chain.

## Current Lean Boundary

Already proved:

```text
productReductionStepCoordinate_detChart_homeomorph
hasFDerivAt_productReductionStepTopologyTupleToChart_rawOrder
fderivWithin_productReductionStepTopologyTupleToChart_rawOrder_det_isUnit
map_productReductionStepRawOrder_restrict_detChart_eq_withDensity_inverseJacobian
```

These prove the full one-step determinant-chart infrastructure.

Already proved for the p.13 section:

```text
p13ProductCoordinateLeftStepRawTopologyTuple_C1_eq_one
p13ProductCoordinateLeftStepRawTopologyTuple_A3_eq_zero
map_p13RawOrderTuple_eq_map_leftStepRawOrder_image_of_measurable_edgeMatrix
exists_pos_radius_le_map_p13RawOrderTuple_eq_map_leftStepRawOrder_image_of_ae_regular_mem_ball
```

These prove section support and section-image functoriality, not full raw
Haar transport.

Still supplied or deferred:

```text
Ulocal inter sourceStratum subset Ulocal inter localSource
Measure.map sourceChart weightedBox = sourceMeasure.restrict localSource
source-density/Jacobian monomial-unit identities
residual-product monomial lower bound
local original-loss comparison
```

The retained-passive chart would need to produce or replace these fields.  It
is not enough to compose the existing one-step raw COV theorem with the p.13
section, because the section is not the full raw source measure.

## Decision

Do not add a Lean theorem claiming a p.13 local source chart, local inverse,
or source-measure transport from Lemma 2/Theorem 3 alone.

The strongest source-faithful statement currently justified is:

- the full one-step raw determinant chart is valid and already formalised;
- the p.13 reduced section is a section, with section-image measure identity
  already formalised;
- a retained-passive multi-step source chart is a plausible future route, but
  it is not present as a theorem in Aoyagi pp. 10-13 and must be built as an
  explicit new construction with coverage and density fields.

## Kill Conditions For Future Work

- If a proposed theorem derives full raw-Haar pushforward from the p.13
  section `C1=I, A3=0`, reject it.
- If a proposed retained-passive theorem does not name the passive variables,
  its source map, its image/source-rank coverage, and its density/Jacobian
  factor, treat it as a wrapper.
- If exact-rank or source-rank openness is used, prove it or keep it as an
  explicit hypothesis; do not read it off from the displayed p.13 algebra.
- If passive variables are integrated out, provide the product-measure or
  finite-measure argument explicitly.  Do not count them as additional
  singular variables in the p.13 regular-variable shift.
- If the theorem only restates the existing local inclusion into `localSource`,
  do not formalise it.

## Nonclaims

This note proves no local source chart, no source-rank coverage, no
source-measure pushforward, no density/Jacobian identity, no signed-box
residual chart, no normal crossings, no pole order, and no RLCT extraction.
