# Statement Card - A2 Supplied Regular-Suspension Interface

## Lean File

- `lean/DLNFibre/DLN/Aoyagi/RegularSuspensionInterface.lean`

## Claim

A supplied full regular-suspension chart certificate can be connected to a
reduced chart certificate through an explicit finite exponent equality

```text
Cfull.exponentData = Cred.exponentData.jacobianPriorLossShift regularCount.
```

From this equality, Lean may project the finite minimum and order shifts, and
when `regularCount` is Aoyagi's p. 13 regular block-entry count, build the
existing Theorem 2 chart final boundary for `Cfull`.

## Planned Lean Names

```text
AoyagiSuppliedRegularSuspensionBoundary
AoyagiSuppliedRegularSuspensionCertificate
AoyagiSuppliedRegularSuspensionBoundary
  .full_exponentMinimum_eq_reduced_add_half_regularCount
AoyagiSuppliedRegularSuspensionBoundary
  .full_exponentOrder_eq_reduced
AoyagiSuppliedRegularSuspensionBoundary
  .full_exponentMinimum_eq_reduced_add_regularTerm
AoyagiSuppliedRegularSuspensionCertificate
  .theorem2SuppliedChartFinalBoundary_of_regularVariableCount
```

## Inputs Kept Explicit

- reduced chart certificate `Cred`;
- full chart certificate `Cfull`;
- independent reduced and full chart parameter/coefficient types;
- regular variable count `regularCount`;
- abstract supplied predicates for chart source, ideal transport, coverage,
  and Jacobian compatibility;
- finite equality
  `Cfull.exponentData = Cred.exponentData.jacobianPriorLossShift regularCount`;
- chart extraction hypothesis for `Cfull`;
- selected-width provenance;
- endpoint rank-width bounds for identifying the regular count shift with
  Aoyagi's regular term;
- reduced minimum-plus-regular-term equality;
- reduced finite order equality.

## Not Proved

No regular-suspension chart construction, no proof of the abstract predicates,
no analytic ideal transport, no Aoyagi Lemma 1, no analytic additivity theorem,
no normal-crossing production, no pole-order theorem, and no RLCT theorem
beyond the supplied extraction hypothesis for the full certificate.

## Verification

Run:

```text
cd lean && scripts/lb DLNFibre.DLN.Aoyagi.RegularSuspensionInterface
cd lean && scripts/lb
cd lean && scripts/sorries
git diff --check
```

Verified on 2026-06-24 with:

```text
LEAN_NUM_THREADS=1 lake env lean DLNFibre/DLN/Aoyagi/RegularSuspensionInterface.lean
LEAN_NUM_THREADS=1 lake build DLNFibre.DLN.Aoyagi.RegularSuspensionInterface
LEAN_NUM_THREADS=1 lake build DLNFibre
lean/scripts/sorries
git diff --check
```
