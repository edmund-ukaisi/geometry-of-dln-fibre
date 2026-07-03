# A2 reference-source finite-cylinder base domination

Date: 2026-07-03.

## Calculation

The with-following reference source has product shape

```text
referenceSource = (passiveRef.prod weightedBox).prod followingMeasure.
```

The finite following-patch cylinder built from a passive comparison measure is

```text
localFiniteCylinder =
  (((passiveMeasure.prod weightedBox).prod followingMeasure).restrict
    {z | z.2 in followingPatch}).restrict V.
```

Let `P` be a passive-local set.  Suppose the passive reference is locally
dominated by `passiveMeasure`:

```text
passiveRef.restrict P <= Cpassive • passiveMeasure.
```

Product domination lifts first through the selected-entry center factor and
then through the following-factor measure:

```text
((passiveRef.restrict P).prod weightedBox).prod followingMeasure
  <= Cpassive • ((passiveMeasure.prod weightedBox).prod followingMeasure).
```

The set

```text
{z | z.1.1 in P}
```

is `(P × univ) × univ` under the product convention

```text
Case2PassiveThetaWithFollowingFactor
  = (PassiveFields × Center) × FollowingMatrix.
```

Therefore product-restriction bookkeeping identifies

```text
((passiveRef.prod weightedBox).prod followingMeasure).restrict {z | z.1.1 in P}
  =
((passiveRef.restrict P).prod weightedBox).prod followingMeasure.
```

If the local set `V` is supported in this passive-local cylinder,

```text
V subset {z | z.1.1 in P},
```

then restricting the preceding domination to `V` gives

```text
referenceSource.restrict V
  <= Cpassive • (((passiveMeasure.prod weightedBox).prod followingMeasure).restrict V).
```

If `V` is also supported in the following patch,

```text
V subset {z | z.2 in followingPatch},
```

then

```text
(((passiveMeasure.prod weightedBox).prod followingMeasure).restrict
  {z | z.2 in followingPatch}).restrict V
=
((passiveMeasure.prod weightedBox).prod followingMeasure).restrict V.
```

Combining these identities gives the target base domination:

```text
referenceSource.restrict V <= Cpassive • localFiniteCylinder.
```

## Lean targets

The reusable product-measure lemma should be:

```text
prod_prod_restrict_le_smul_restrict_cylinder_of_left_restrict_le_smul_of_subset
```

in:

```text
lean/DLNFibre/DLN/Aoyagi/LocalMeasureHandoff.lean
```

The concrete Aoyagi wrapper should be:

```text
case2PassiveThetaWithFollowingFactor_referenceSource_restrict_le_smul_sourceCylinder_restrict_of_passive_restrict_le_smul
```

in:

```text
lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCase2PassiveThetaWithFollowingFactorEndpointReference.lean
```

## Boundary

This is still a conditional base-domination theorem.  It proves no passive
local finite measure construction, no Jacobian-density upper bound, no
source-density upper bound, no coordinate-source finite-integral theorem by
itself, no determinant-Haar/raw-Haar transport, no original-prior transport,
no normal crossings, no pole order, and no RLCT extraction.
