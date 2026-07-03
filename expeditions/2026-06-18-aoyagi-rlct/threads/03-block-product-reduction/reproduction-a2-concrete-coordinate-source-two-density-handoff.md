# A2 concrete coordinate-source two-density handoff

Date: 2026-07-03.

## Calculation

Work on the enlarged Case 2 passive-theta source with an independent following
factor.  The named coordinate source measure is a two-stage density
perturbation of the with-following reference source:

```text
referenceSource =
  case2PassiveThetaWithFollowingFactorReferenceSourceMeasure ...

jacobianDensity z =
  ofReal (retainedPassiveFormalRawOrderJacobianProductAbsDetAt (Y z))

baseJ = referenceSource.withDensity jacobianDensity

sourceDensity z = sourceImageDensity (sourceChart z)

coordinateSourceMeasure = baseJ.withDensity sourceDensity.
```

Let `V` be measurable and let `nu` be any comparison measure on the same
source.  Suppose the base reference source is already dominated on `V`:

```text
referenceSource.restrict V <= Cbase • nu.
```

Assume the raw-order Jacobian density is locally bounded against the base
restricted source,

```text
jacobianDensity z <= CJ
  for referenceSource.restrict V-a.e. z,
```

and the endpoint source-image density is locally bounded against the
once-weighted restricted source,

```text
sourceDensity z <= CS
  for baseJ.restrict V-a.e. z.
```

Then the generic two-density handoff applies with

```text
mu = referenceSource,
J = jacobianDensity,
S = sourceDensity.
```

It gives the concrete domination

```text
coordinateSourceMeasure.restrict V
  <= (CS * (CJ * Cbase)) • nu.
```

If the three input scalars are finite, then the final scalar is finite:

```text
Cbase < infinity, CJ < infinity, CS < infinity
  implies CS * (CJ * Cbase) < infinity.
```

## Intended downstream instantiation

For the finite following-patch cylinder application, `nu` should later be
instantiated as the local finite cylinder source measure, typically of the
shape

```text
((((passiveMeasure.prod weightedBox).prod followingMeasure).restrict
  {z | z.2 in followingPatch}).restrict V).
```

This wrapper deliberately does not prove that base domination.  That remaining
input is product-cylinder/passive-local bookkeeping and should be proved as a
separate layer.

## Lean targets

The concrete theorem is:

```text
case2PassiveThetaWithFollowingFactor_coordinateSourceMeasure_restrict_le_smul_of_referenceSource_restrict_le_smul
```

The finite-scalar wrapper is:

```text
case2PassiveThetaWithFollowingFactor_coordinateSourceMeasure_restrict_le_smul_of_referenceSource_restrict_le_smul_of_lt_top
```

Both are in:

```text
lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCase2PassiveThetaRawImageHandoff.lean
```

## Boundary

This is a conditional concrete source-measure adapter.  It proves no passive
local domination, no domination of `referenceSource.restrict V` by a finite
following-patch cylinder, no Jacobian-density upper bound, no source-density
upper bound, no determinant-Haar/raw-Haar transport, no original-prior
transport, no normal crossings, no pole order, and no RLCT extraction.

Verification passed: focused local build of
`DLNFibre.DLN.Aoyagi.RetainedPassiveCase2PassiveThetaRawImageHandoff`, full
local `lake build DLNFibre`, `scripts/sorries`, `git diff --check`, touched
Lean-file marker scan, and direct axiom probes.  The new declarations report
`[propext, Classical.choice, Quot.sound]`.
