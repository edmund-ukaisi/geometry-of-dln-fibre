# Statement Card - A6 Theorem 2 Supplied Regular-Suspension Final Bridge

## Lean File

- `lean/DLNFibre/DLN/Aoyagi/Theorem2RegularSuspensionFinalBridge.lean`

## Claim

Definition 3 source data plus source-range rank-width can be composed with a
supplied regular-suspension full chart certificate to produce the existing
Theorem 2 chart-final boundary for `Cfull`.

The extraction hypothesis is for `Cfull`.  The reduced certificate `Cred` is
used only through the supplied finite exponent equality

```text
Cfull.exponentData =
  Cred.exponentData.jacobianPriorLossShift regularCount
```

and the reduced finite min/order obligations.

## Lean Names

```text
AoyagiDefinition3SourceData
  .exists_theorem2SuppliedChartFinalBoundary_of_rankWidth_suppliedRegularSuspension
AoyagiDefinition3SourceData
  .exists_theorem2SuppliedChartFinalBoundary_of_sourceRankStratum_suppliedRegularSuspension
```

## Inputs Kept Explicit

- Definition 3 source data `S`;
- source-range rank-width `hr`, or source-rank-stratum data plus the
  dimension convention;
- supplied regular-suspension certificate `Sreg`;
- regular count equality
  `regularCount = aoyagiTheorem2RegularVariableCount L H r`;
- reduced minimum-plus-regular-term equality for every produced `m,data`;
- reduced finite order equality for every produced `m,data`.

## Not Proved

No source-data construction, no `Cfull` construction, no proof of the abstract
regular-suspension predicates, no analytic ideal transport, no Aoyagi Lemma 1,
no regular-coordinate additivity, no normal-crossing production, no active
ratio or chart-count theorem, and no pole-order/RLCT theorem beyond extraction
for `Cfull`.

## Verification

Run:

```text
cd lean && scripts/lb DLNFibre.DLN.Aoyagi.Theorem2RegularSuspensionFinalBridge
cd lean && scripts/lb
cd lean && scripts/sorries
git diff --check
```

Verified on 2026-06-24 with:

```text
LEAN_NUM_THREADS=1 lake env lean DLNFibre/DLN/Aoyagi/Theorem2RegularSuspensionFinalBridge.lean
LEAN_NUM_THREADS=1 lake build DLNFibre.DLN.Aoyagi.Theorem2RegularSuspensionFinalBridge
LEAN_NUM_THREADS=1 lake build DLNFibre
lean/scripts/sorries
git diff --check
```
