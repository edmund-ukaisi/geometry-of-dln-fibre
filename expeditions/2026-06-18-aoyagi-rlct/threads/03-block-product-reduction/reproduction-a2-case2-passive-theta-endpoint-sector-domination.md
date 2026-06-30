# Reproduction - A2 Case 2 passive theta endpoint-sector domination

Date: 2026-06-30.

Status: pen-and-paper check before Lean.  This is conditional measure
domination on the named endpoint sector, not Haar transport or source-prior
construction.

## Question

After naming the endpoint sector image

```text
S_Omega = case2PassiveThetaEndpointSectorSet Omega = Y '' Omega,
```

can finite-scalar domination on the theta domain be pushed forward to
finite-scalar domination on `S_Omega`?

Answer: yes.  This is elementary measure functoriality plus the already
proved support theorem.

## Setup

Let

```text
Y theta =
  case2PassiveThetaEndpointTopologyTuple n hS hcont hnext theta eNext e
```

and let `Omega` be a measurable theta-domain sector.  Suppose

```text
sourceMeasure.restrict Omega
  <= c * referenceMeasure.restrict Omega.
```

The endpoint-sector measures are

```text
nu_source = Measure.map Y (sourceMeasure.restrict Omega)
nu_ref    = Measure.map Y (referenceMeasure.restrict Omega).
```

Both are supported on `S_Omega`, assuming the same explicit measurability
hypotheses used in the sector-support theorem.

## Calculation

Measurable maps preserve scalar domination:

```text
Measure.map Y (sourceMeasure.restrict Omega)
  <= c * Measure.map Y (referenceMeasure.restrict Omega).
```

Since both sides are supported on `S_Omega`, restricting both endpoint
pushforwards to `S_Omega` does not change them.  Therefore

```text
(Measure.map Y (sourceMeasure.restrict Omega)).restrict S_Omega
  <= c * (Measure.map Y (referenceMeasure.restrict Omega)).restrict S_Omega.
```

For a weighted theta measure, if

```text
density theta <= c
```

for `baseMeasure.restrict Omega`-almost every theta, then

```text
(baseMeasure.withDensity density).restrict Omega
  <= c * baseMeasure.restrict Omega.
```

This follows by rewriting the left side as a restricted `withDensity` and
comparing it to the constant-density measure.  The first domination theorem
then gives the endpoint-sector domination.

## Lean Target

Add the theorem pair to

```text
lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCase2PassiveThetaSourceMeasure.lean
```

Public names:

```text
measure_map_case2PassiveThetaEndpointTopologyTuple_restrict_endpointSectorSet_le_smul
measure_map_case2PassiveThetaEndpointTopologyTuple_withDensity_restrict_endpointSectorSet_le_smul_of_ae_le
```

## Nonclaims

This slice assumes theta-domain domination or a theta-domain density bound.
It does not prove local injectivity of `Y`, image measurability without
hypothesis, an exact passive-sector Haar pushforward, determinant-chart Haar
transport, raw-order Haar transport, source-prior comparison, source-image
equality, source-rank coverage, normal crossings, pole order, or RLCT
extraction.
