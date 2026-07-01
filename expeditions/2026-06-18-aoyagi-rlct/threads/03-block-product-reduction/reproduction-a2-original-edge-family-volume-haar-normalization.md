# Reproduction - A2 Original Edge-Family Volume Haar Normalization

Date: 2026-07-01.

Status: pen-and-paper check before Lean. This is full-space
coordinate/Haar infrastructure for fixed-basis edge-family volume. It is not a
retained-passive chart-transport theorem.

## Question

For fixed bases

```text
b j : Basis (Fin (d j)) R (V j),
```

the existing original edge-family volume is

```text
originalEdgeFamilyVolume b
  := Measure.map (tupleToEdgeFamily b) (originalTupleVolume d).
```

Is this an additive Haar measure on the full continuous edge-family space

```text
EdgeFamily := forall p : Fin N, V p.castSucc ->L[R] V p.succ,
```

and how does it compare to any other additive Haar measure on the same full
space?

## Calculation

The fixed-basis matrix readout is

```text
edgeFamilyMatrixTuple b : EdgeFamily -> Tuple (k := R) d.
```

It reads each continuous edge map in the chosen source and target bases.  The
inverse map is

```text
tupleToEdgeFamily b : Tuple (k := R) d -> EdgeFamily,
```

which reconstructs a continuous edge family from the tuple of matrices.

The existing inverse identities say

```text
edgeFamilyMatrixTuple b (tupleToEdgeFamily b A) = A,
tupleToEdgeFamily b (edgeFamilyMatrixTuple b E) = E.
```

Both maps are linear. Addition and scalar multiplication are entrywise on
matrix tuples, and continuous-linear-map addition and scalar multiplication are
read entrywise by fixed-basis matrix coordinates. The existing continuity
theorems give

```text
Continuous (edgeFamilyMatrixTuple b),
Continuous (tupleToEdgeFamily b).
```

Therefore `edgeFamilyMatrixTuple b` and `tupleToEdgeFamily b` package as a
continuous linear equivalence

```text
EdgeFamily ~=L[R] Tuple (k := R) d.
```

The previous tuple-volume step proved that `originalTupleVolume d` is an
additive Haar measure. Haar measure is preserved by pushforward along a
continuous linear equivalence, so

```text
Measure.map (tupleToEdgeFamily b) (originalTupleVolume d)
```

is an additive Haar measure on the full edge-family space. This is precisely
`originalEdgeFamilyVolume b`.

Haar uniqueness then gives, for any additive Haar measure `nu` on the same
full edge-family space,

```text
originalEdgeFamilyVolume b
  = addHaarScalarFactor (originalEdgeFamilyVolume b) nu • nu.
```

The scalar is positive. Since the scalar is an element of `R>=0`, its coercion
to `R>=0∞` is finite. This is the right downstream form for finite-scalar
domination or equality statements.

## Source Fidelity

Aoyagi p.13 uses finite-dimensional fixed-basis edge-map coordinates. This
reproduction formalizes the elementary full-space coordinate/Haar fact for
those fixed-basis edge-family coordinates. It adds no new analytic citation
and makes no claim about the retained-passive determinant chart or any
restricted chart-domain measure.

## Lean Target

Add:

```text
lean/DLNFibre/DLN/Aoyagi/OriginalEdgeFamilyPriorHaar.lean

edgeFamilyMatrixTupleLinearEquiv
edgeFamilyMatrixTupleLinearEquiv_apply
edgeFamilyMatrixTupleLinearEquiv_symm_apply
edgeFamilyMatrixTupleContinuousLinearEquiv
isAddHaarMeasure_originalEdgeFamilyVolume
originalEdgeFamilyVolume_eq_addHaarScalarFactor_smul
originalEdgeFamilyVolume_addHaarScalarFactor_pos
originalEdgeFamilyVolume_addHaarScalarFactor_coe_lt_top
```

The scalar-comparison theorem should require explicit
`LocallyCompactSpace EdgeFamily` and `SecondCountableTopology EdgeFamily`
hypotheses. The vertex assumptions in this file are intentionally generic, so
the file should not install broad global topology instances for continuous
linear-map product spaces.

## Kill Conditions

- If the fixed-basis matrix readout and reconstruction are not inverse linear
  maps, the edge-family volume is not known to be Haar by this route.
- If the edge-family measurable space is not the Borel measurable space, the
  continuous-linear-equivalence Haar pushforward API does not apply.
- Haar uniqueness is a full-space theorem. It must not be applied directly to
  `m.restrict T`, `Measure.map sourceChart (m.restrict T)`, or any other
  restricted chart-domain measure.
- A scalar equal to `1` would require an additional normalization or
  volume-preservation theorem; Haar uniqueness alone gives only a positive
  finite scalar.

## Nonclaims

No theorem here identifies `originalEdgeFamilyVolume` with a retained-passive
or selected-entry chart-produced source-image measure. No theorem proves
chart-piece equality, readback domination, determinant-chart Haar transport,
Jacobian density equality for an Aoyagi chart, source-rank coverage, normal
crossings, pole order, or RLCT extraction.
