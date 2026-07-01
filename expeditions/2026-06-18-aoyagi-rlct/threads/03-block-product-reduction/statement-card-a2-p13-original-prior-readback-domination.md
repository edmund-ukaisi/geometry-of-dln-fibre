# Statement Card - A2 p.13 Original-prior Readback Domination

## Claim

A locally bounded original edge-family prior on a supplied p.13 chart piece
inherits any supplied readback-side domination of the formal-product p.13 chart
measure.

Let

```text
alpha := ENNReal.ofReal K * ((c^-1 : NNReal) : ENNReal),
```

where `c` is the tuple-side full-space Haar scalar from the p.13 chart-piece
measure comparison.  If

```text
originalPriorPiece <= alpha • muP13
```

is the already-proved bounded-prior p.13 domination, and if the caller supplies

```text
AEMeasurable readback muP13
Measure.map readback muP13 <= Cformal • thetaRef,
```

then

```text
AEMeasurable readback originalPriorPiece
Measure.map readback originalPriorPiece <= (alpha * Cformal) • thetaRef.
```

The companion scalar lemma records that `(alpha * Cformal) < infinity` whenever
`Cformal < infinity`.

## Public Lean Names

```text
measure_le_smul_of_le_smul_of_le_smul
originalEdgeFamilyPrior_map_readback_restrict_chartPiece_le_smul_of_formalProductAbsDet_map_readback_le_smul
originalEdgeFamilyPrior_p13ReadbackDominationScalar_lt_top
```

## Inputs Used

- the existing p.13 bounded-prior domination theorem;
- `Measure.absolutelyContinuous_of_le_smul`;
- `map_le_smul_map_of_le_smul_aemeasurable`;
- elementary composition of two scalar measure dominations;
- finiteness of `ENNReal.ofReal K` and of coerced `NNReal` scalars.

## Proof Shape

1. Use the existing source-side theorem to obtain
   `originalPriorPiece <= alpha • muP13`.
2. Derive `originalPriorPiece << muP13`, hence a.e. measurability of `readback`
   for `originalPriorPiece` from a.e. measurability for `muP13`.
3. Map the source-side domination through `readback`.
4. Compose the result with the supplied formal-product readback domination.
5. Prove finite scalar transfer by two applications of `ENNReal.mul_lt_top`.

## Nonclaims

This does not prove the formal-product readback domination, identify `muP13`
with a passive-theta source-image measure, prove passive-theta image
containment in the p.13 source set, transport the original prior through a
full p.13 parameter chart, normalize the Haar scalar to `1`, prove restricted
Haar structure, construct normal crossings, prove pole order, or extract an
RLCT.
