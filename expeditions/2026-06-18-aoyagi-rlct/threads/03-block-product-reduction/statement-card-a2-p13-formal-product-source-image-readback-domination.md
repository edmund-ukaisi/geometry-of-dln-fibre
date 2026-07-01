# Statement card - A2 p.13 formal-product source-image readback domination

## Lean theorem

```text
map_paperEndpointFixedBaseRetainedPassiveP13RawOrderSourceChart_withDensity_formalProductAbsDet_restrict_chartPiece_readback_le_smul_coordinateSourceMeasure_restrict_of_sourceImageReference_eq_withDensity_of_continuousOn_injOn
```

File:

```text
lean/DLNFibre/DLN/Aoyagi/OriginalEdgeFamilyP13ReadbackFiniteIntegral.lean
```

## Statement

For a measurable chart piece, assume the p.13 formal-product chart measure on
that piece is a bounded-density perturbation of the concrete passive-theta
source-image reference

```text
Measure.map sourceChart (coordinateSourceMeasure.restrict V).
```

If `sourceChart` is continuous and injective on `V`, `readback` is a left
inverse there, and `V subset W`, then `readback` is a.e.-measurable for the
restricted p.13 formal-product chart measure and

```text
Measure.map readback muP13 <= D * coordinateSourceMeasure.restrict W.
```

Here `D` is the supplied a.e. density bound.

## Inputs kept explicit

- the bounded-density identity between `muP13` and the source-image reference;
- the a.e. density bound by `D`;
- measurability of `V` and `chartPiece`;
- continuity and injectivity of `sourceChart` on `V`;
- the local left inverse `readback (sourceChart theta) = theta`;
- the containment `V subset W`.

## Dependencies

- `aemeasurable_readback_and_measure_map_readback_restrict_piece_le_smul_restrict_superset_of_restrict_eq_withDensity_of_continuousOn_injOn`;
- the p.13 formal-product measure expression already used by the finite-integral socket;
- local source-image inverse hypotheses.

## Nonclaims

No formal-product/source-image comparison is proved.  No Haar transport,
source-image coverage, source-rank coverage, scalar normalization, normal
crossings, pole order, or RLCT extraction is proved.
