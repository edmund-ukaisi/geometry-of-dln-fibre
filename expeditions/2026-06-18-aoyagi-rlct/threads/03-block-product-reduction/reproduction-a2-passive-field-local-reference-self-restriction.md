# A2 passive-field local reference self-restriction

Date: 2026-07-03.

## Calculation

The passive-field reference measure is the nested product

```text
passiveRef =
  A1Measure.prod
    (F2Measure.prod
      (A3Measure.prod
        (CtopMeasure.prod F3Measure))).
```

Here the factors are coordinate-product matrix-entry reference measures for
the passive `A1`, `F2`, `A3`, `Ctop`, and `F3` coordinates.

For a finite family of matrices `F0 i`, define the dependent Pi-box

```text
piMatrixEntryBox F0 R = {F | forall i, F i in matrixEntryBox (F0 i) R}.
```

For `R > 0`, the center belongs to this box because each matrix belongs to its
own entrywise box.  The set is open by rewriting it as a finite `Set.pi` of
open matrix-entry boxes.  It is measurable by the analogous finite `Set.pi`
measurability theorem.  Its coordinate-product reference measure is finite:

```text
Measure.pi (fun i => matrixEntryReferenceMeasure (r i) (c i))
  (piMatrixEntryBox F0 R)
= product_i matrixEntryReferenceMeasure (r i) (c i)
    (matrixEntryBox (F0 i) R)
< infinity.
```

The equality is `Measure.pi_pi`; each factor is finite by the existing
`matrixEntryReferenceMeasure_matrixEntryBox_lt_top`.

For a passive-field point `theta0`, define the passive box

```text
P(theta0, R) =
  piMatrixEntryBox theta0.1 R
    x (piMatrixEntryBox theta0.2.1 R
      x (piMatrixEntryBox theta0.2.2.1 R
        x (matrixEntryBox theta0.2.2.2.1 R
          x matrixEntryBox theta0.2.2.2.2 R))).
```

It contains `theta0`, is open, and is measurable by the five factorwise
statements.  Its passive reference mass is finite by repeated product
submultiplicativity:

```text
passiveRef P(theta0, R)
  <= mass(A1Box) *
      (mass(F2Box) *
        (mass(A3Box) *
          (mass(CtopBox) * mass(F3Box))))
  < infinity.
```

The proof uses `Measure.prod_prod_le` at each product layer.  Exact product
rectangle equalities are unnecessary for finiteness.

## Self-Restriction

Take `R = 1`, set

```text
passiveLocalSet = P(theta0, 1),
passiveMeasure = passiveRef.restrict passiveLocalSet,
Cpassive = 1.
```

Then

```text
passiveMeasure Set.univ = passiveRef passiveLocalSet < infinity,
passiveRef.restrict passiveLocalSet <= Cpassive • passiveMeasure.
```

The last comparison is the identity comparison with scalar `1`.

## Lean Targets

The reusable Pi-box layer is:

```text
piMatrixEntryBox
mem_piMatrixEntryBox_self
isOpen_piMatrixEntryBox
measurableSet_piMatrixEntryBox
piMatrixEntryReferenceMeasure_piMatrixEntryBox_lt_top
```

The passive-field box layer is:

```text
case2PassiveThetaPassiveFieldBox
mem_case2PassiveThetaPassiveFieldBox_self
isOpen_case2PassiveThetaPassiveFieldBox
measurableSet_case2PassiveThetaPassiveFieldBox
case2PassiveThetaPassiveFieldReferenceMeasure_box_lt_top
```

The final self-restriction theorem is:

```text
exists_open_passiveLocalSet_case2PassiveThetaPassiveFieldReferenceMeasure_restrict_self_le_smul
```

All are in:

```text
lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCase2PassiveThetaEndpointReference.lean
```

## Boundary

This constructs only a finite open coordinate-reference self-restriction for
the passive-field reference measure.  It proves no original-prior comparison,
no determinant-Haar/raw-Haar transport, no Jacobian-density upper bound, no
source-density upper bound, no normal crossings, pole order, or RLCT
extraction.
