# Statement Card - A2 supplied regular-suspension extraction projection

## Claim

For a supplied full regular-suspension certificate, extraction on `Cfull`
projects to the reduced finite minimum plus the supplied regular count shift,
and projects the pole order to the reduced finite order.

## Source

Aoyagi PDF p. 13 motivates the regular-variable count and shift.  The analytic
construction of the full regular-suspension certificate is not supplied by this
slice; it remains an explicit hypothesis.

## Lean Names

```text
AoyagiSuppliedRegularSuspensionCertificate.
  lambda_eq_reduced_add_half_regularCount
AoyagiSuppliedRegularSuspensionCertificate.
  poleOrder_eq_reduced_exponentOrder
AoyagiSuppliedRegularSuspensionCertificate.
  lambda_eq_reduced_add_regularTerm
AoyagiSuppliedRegularSuspensionCertificate.
  lambda_and_poleOrder_eq_reduced_add_regularTerm
```

## Statement Shape

Given

```text
S : AoyagiSuppliedRegularSuspensionCertificate
      Cred Cfull regularCount ... lambda poleOrder,
```

Lean proves

```text
lambda =
  Cred.exponentData.exponentMinimum + regularCount / 2
```

and

```text
poleOrder = Cred.exponentData.exponentOrder.
```

Under the p. 13 count identification and endpoint bounds, Lean rewrites the
lambda statement as

```text
lambda =
  Cred.exponentData.exponentMinimum + aoyagiTheorem2RegularTerm L H r.
```

## Boundary

The extraction hypothesis remains on `Cfull`.  This is not a theorem about
extracting from `Cred`, not a proof of regular-coordinate additivity, and not
a construction of the analytic regular-suspension chart.

## Reproduction

`reproduction-a2-supplied-regular-suspension-extraction-projection.md`
