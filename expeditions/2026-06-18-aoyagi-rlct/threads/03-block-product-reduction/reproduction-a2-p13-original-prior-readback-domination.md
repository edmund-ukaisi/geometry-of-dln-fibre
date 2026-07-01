# Reproduction - A2 p.13 Original-prior Readback Domination

Date: 2026-07-01.

Status: pen-and-paper check before Lean.  This is a conditional bridge from
the p.13 formal-product chart measure to a downstream readback domination
socket.

## Question

The chart-piece inverse-scalar theorem gives, under a measurable
`chartPiece` contained in the named p.13 source edge-family set and a local
upper bound on the original edge-family prior density,

```text
originalPriorPiece <= alpha • muP13,
```

where

```text
alpha := ENNReal.ofReal K * ((c^-1 : NNReal) : ENNReal).
```

Here `c` is the full-space Haar scalar comparing the raw-order tuple Haar
pushforward with `originalTupleVolume`, and `muP13` is the formal-product
p.13 chart measure restricted to `chartPiece`.

Suppose a later geometric/chart calculation supplies a readback domination

```text
Measure.map readback muP13 <= Cformal • thetaRef.
```

Can the same readback domination be transferred to `originalPriorPiece`?

## Calculation

The original prior bound implies absolute continuity:

```text
originalPriorPiece << muP13.
```

Therefore any function `readback` that is a.e. measurable for `muP13` is also
a.e. measurable for `originalPriorPiece`.

Mapping preserves scalar domination for an a.e. measurable map checked against
the reference measure:

```text
Measure.map readback originalPriorPiece
  <= alpha • Measure.map readback muP13.
```

Composing with the supplied formal-product readback domination gives

```text
Measure.map readback originalPriorPiece
  <= alpha • (Cformal • thetaRef)
   = (alpha * Cformal) • thetaRef.
```

The finite-scalar side condition needed by finite-integral transfer is also
elementary:

```text
Cformal < infinity
-----------------------------------------------
(ENNReal.ofReal K * ((c^-1 : NNReal) : ENNReal) * Cformal) < infinity.
```

`ENNReal.ofReal K` is finite for every real `K`, the coercion of an `NNReal`
is finite, and finite elements are closed under multiplication.

## Lean Target

Add a generic scalar-domination composition lemma to:

```text
lean/DLNFibre/DLN/Aoyagi/LocalMeasureHandoff.lean
```

Then add the p.13 consumer theorem to:

```text
lean/DLNFibre/DLN/Aoyagi/OriginalEdgeFamilyP13SourceMeasureBridge.lean
```

with content:

```text
originalEdgeFamilyPrior_map_readback_restrict_chartPiece_le_smul_of_formalProductAbsDet_map_readback_le_smul
originalEdgeFamilyPrior_p13ReadbackDominationScalar_lt_top
```

## Kill Conditions

- If the theorem proves or suggests the formal-product readback domination,
  it overclaims.  That domination remains a hypothesis.
- If it identifies `muP13` with the passive-theta source-image measure, it
  overclaims.
- If it proves passive-theta image containment in the p.13 source set, source
  coverage, scalar normalization, restricted Haar structure, normal
  crossings, pole order, or RLCT extraction, it overclaims.
