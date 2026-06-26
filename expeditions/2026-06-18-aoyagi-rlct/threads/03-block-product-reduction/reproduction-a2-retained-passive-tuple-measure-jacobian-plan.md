# Reproduction - A2 Retained-Passive Tuple Measure/Jacobian Plan

Date: 2026-06-26.

Status: controller pen-and-paper construction plan.  No new Lean theorem is
claimed by this note.

## Question

The retained-passive coordinate chart has a record-level source map

```text
data |-> data.edgeMatrix
```

and a record-level inverse on the source-recursive determinant chart.  The
measure/Jacobian layer cannot be obtained from that topology alone.  It needs
an explicit finite tuple map between normed vector spaces, a Frechet derivative
on the determinant chart, a determinant formula, and only then a
change-of-variables theorem.

This note fixes the intended tuple objects and the exact missing ingredients.
It is independent of the quiver-based paper.  The only cited boundary remains
the later normal-crossing-to-RLCT extraction.

## Source Check

Aoyagi's p.13 construction is an iteration of the p.10 block calculation.  At
one step the raw blocks

```text
(C1, D, F3old, A1, A2, A3, A4)
```

are changed to

```text
(Ctop, D, F3, A1, F2, A3, C)
```

with

```text
Ctop = C1 * A1
F2   = -A1^{-1} * A2
F3   = F3old - D * A3 * (C1 * A1)^{-1}
C    = A4 - A3 * A1^{-1} * A2.
```

The retained-passive chart keeps the variables that the reduced p.13 section
had fixed or suppressed.  It replaces only the endpoint variables by the
accumulated endpoint fields:

```text
A1_0      is solved from Ctop and the passive A1_tail,
A3_last   is solved from F3 and the earlier passive A3 fields,
F2_last   is fixed to 0 by the source-recursive convention.
```

The sign/order audit remains:

```text
A1_0    = Tail^{-1} * Ctop
A3_last = -(F3 - earlyTail) * CtopLast
F3new   = F3old - D * A3 * (C1 * A1)^{-1}.
```

This is the elementary calculation that the future derivative package must
differentiate.

## Tuple Objects

The existing Lean source tuple is

```text
RetainedPassiveNonredundantCoordinateData.TopologyTuple rho kappa R
```

with order

```text
(A1passive, F2, A3passive, C, Ctop, F3).
```

The record map already exists:

```text
RetainedPassiveNonredundantCoordinateData.topologyTuple
RetainedPassiveNonredundantCoordinateData.edgeMatrix
RetainedPassiveNonredundantCoordinateData.detChartSet
sourceRecursiveDetChartSet
```

The first tuple-level Lean foothold should add the reverse constructor

```text
ofTopologyTuple :
  TopologyTuple rho kappa R ->
    RetainedPassiveNonredundantCoordinateData kappa
```

with the two inverse identities.  This is not a measure theorem; it is the
coordinate-space API needed before stating differentiability.

The target source-edge tuple is

```text
forall p : Fin (M + 1),
  Matrix (rho Sum kappa p.succ) (rho Sum kappa p.castSucc) R.
```

The current source map in tuple language is therefore

```text
topologyTupleEdgeMatrix z =
  (ofTopologyTuple z).edgeMatrix.
```

It maps the tuple determinant chart to `sourceRecursiveDetChartSet` and is
injective on the determinant chart, by the existing source-readback inverse.

## Endomap Issue

The raw one-step measure theorem works because the chart output is reordered
back into the same raw tuple type:

```text
ProductReductionStepRawTopologyTuple -> ProductReductionStepRawTopologyTuple.
```

At this Lean pin, the additive-Haar change-of-variables theorem used in
`ProductReductionStepMeasure.lean` is also in this endomap form.  The retained
source map above has different domain and codomain types.  A future retained
measure theorem should therefore either:

```text
1. build a raw-order linear equivalence from source-edge tuples to the
   retained-passive tuple shape and apply change-of-variables to the endomap

     z |-> edgeRawOrderEquiv ((ofTopologyTuple z).edgeMatrix),

or

2. prove or import a heteromorphic change-of-variables theorem for finite
   vector spaces with separate source and target Haar measures.
```

Route 1 matches the existing one-step pattern and is the smaller local
extension.  It also gives a named bridge back to fixed-base source-edge
families instead of defining the source measure tautologically by pushforward.

## Jacobian Shape

The retained-passive Jacobian is not the reduced p.13 section Jacobian.  The
reduced section fixes `C1 = I` and `A3 = 0` in one-step raw coordinates and is
lower-dimensional inside the full raw determinant chart.  The retained chart is
full-dimensional because it keeps the passive fields.

The derivative should factor into:

```text
endpoint solve for A1_0 from (Ctop, A1_tail),
successive one-step raw-order derivatives,
endpoint solve for A3_last from (F3, A3_early, C, A1),
block extraction/reordering equivalences.
```

The unchanged passive fields are identity directions.  The endpoint solves are
not to be ignored: they contribute invertible linear factors depending on the
determinant-chart units.  For the integrability applications, the immediate
goal is weaker than a closed monomial determinant formula: it is enough to
prove that the absolute determinant density is positive and continuous on the
determinant chart, and locally bounded above and below.

The exact density can be named abstractly once the derivative endomorphism is
defined:

```text
retainedPassiveTopologyTupleJacobianCLM z
retainedPassiveTopologyTupleJacobianAbsDet z
```

The expected proof of nonvanishing should compose:

```text
productReductionStepFormalJacobianRawOrder_det_isUnit
endpoint-solve linear equivalence determinant units
linear reordering equivalence determinant units.
```

The pen-and-paper determinant audit gives a more concrete future check for
each one-step raw-order factor.  If `|rho| = r` and the right residual width is
`|nu|`, the forward one-step absolute determinant should have the form

```text
|det A1|^(r - |nu|)
```

before endpoint-solve factors are included.  The reason is that
`C1 |-> C1 * A1` contributes right-multiplication by `A1` on an `r`-row
matrix space, while `A2 |-> -A1^{-1} * A2` contributes left-multiplication by
`A1^{-1}` on a `|nu|`-column matrix space; the copied and shear variables do
not change the determinant.  Current Lean proves only that the one-step
formal Jacobian determinant is a unit, not this monomial formula.

The nonredundant retained chart then adds endpoint factors from replacing
`A1_0` by `Ctop = Tail * A1_0` and replacing the terminal lower-left block by
`F3`.  Those factors must be included in any exact density formula.  No
inverse of `D` should appear.

## Initial Lean Foothold

Lean now has the tuple bridge needed before differentiability:

```text
ofTopologyTuple
topologyTuple_ofTopologyTuple
ofTopologyTuple_topologyTuple
topologyTuple_injective
topologyTupleDetChartSet
topologyTupleEdgeMatrix
mapsTo_topologyTupleEdgeMatrix_detChartSet_sourceRecursiveDetChartSet
injOn_topologyTupleEdgeMatrix_detChartSet
image_topologyTupleEdgeMatrix_detChartSet
continuous_ofTopologyTuple
isOpen_topologyTupleDetChartSet
```

These are coordinate-space facts only.  They do not define a derivative,
Jacobian density, inverse density, or measure pushforward.

## Future Theorem Shape

After the raw-order target equivalence and derivative package exist, the
measure theorem should have the same scope as the one-step theorem:

```text
Measure.map retainedPassiveTopologyTupleToSourceRawOrder
  ((m.restrict retainedPassiveTopologyTupleDetChartSet).withDensity
    (fun z => ENNReal.ofReal
      (retainedPassiveTopologyTupleJacobianAbsDet z)))
=
  m.restrict
    (retainedPassiveTopologyTupleToSourceRawOrder ''
      retainedPassiveTopologyTupleDetChartSet).
```

Then a separate image theorem can rewrite the image as the raw-order version of
`sourceRecursiveDetChartSet`.  A separate linear-equivalence transport theorem
can rewrite the target measure on raw-order edge coordinates as the desired
fixed-base edge-family Haar measure.

Do not state the stronger source-edge measure theorem before these bridges
exist.

## Missing Lean Ingredients

- raw-order linear equivalence between source-edge tuples and the retained
  tuple shape;
- ambient `HasFDerivWithinAt` for the retained tuple endomap;
- derivative determinant unit theorem;
- continuity and local bounds for the determinant density;
- null-measurability of the raw-order source image;
- bridge from raw-order edge tuples to fixed-base continuous edge families.

## Nonclaims

No source-rank coverage, no original DLN prior, no signed-box density
identification, no product-coordinate source pushforward, no normal crossings,
no pole order, and no RLCT extraction are proved here.
