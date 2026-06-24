# Reproduction - A2 supplied regular-suspension extraction projection

Date: 2026-06-24.

Status: reproduced and formalised as a boundary-hardening Lean slice.

## Source Anchor

Aoyagi PDF p. 13 displays the regular-variable shift after the Theorem 3
block reduction.  The expedition has already separated two facts:

- the elementary block/count data on p. 13;
- the analytic regular-suspension construction still required to pass from a
  reduced normal-crossing certificate to a full certificate for the p. 13
  full loss.

The current Lean interface therefore uses a supplied full certificate

```text
Cfull
```

and a reduced certificate

```text
Cred
```

with the finite exponent equality

```text
Cfull.exponentData = Cred.exponentData.jacobianPriorLossShift regularCount.
```

The single allowed analytic citation is still the normal-crossing extraction
theorem, represented in Lean as an extraction hypothesis on `Cfull`.

## Projection Calculation

Suppose

```text
S : AoyagiSuppliedRegularSuspensionCertificate
      Cred Cfull regularCount ... lambda poleOrder.
```

The extraction field of `S` is

```text
Cfull.ExtractionHypothesis lambda poleOrder.
```

Hence the cited extraction boundary gives only

```text
lambda    = Cfull.exponentData.exponentMinimum,
poleOrder = Cfull.exponentData.exponentOrder.
```

The supplied regular-suspension boundary then gives the finite equalities

```text
Cfull.exponentData.exponentMinimum
  = Cred.exponentData.exponentMinimum + regularCount / 2,

Cfull.exponentData.exponentOrder
  = Cred.exponentData.exponentOrder.
```

Combining these proves

```text
lambda
  = Cred.exponentData.exponentMinimum + regularCount / 2,

poleOrder
  = Cred.exponentData.exponentOrder.
```

If additionally

```text
regularCount = aoyagiTheorem2RegularVariableCount L H r,
r <= H 1,
r <= H (L+1),
```

then the previously formalised count arithmetic rewrites `regularCount / 2`
as Aoyagi's displayed p. 13 regular term:

```text
lambda
  = Cred.exponentData.exponentMinimum + aoyagiTheorem2RegularTerm L H r.
```

## Lean Target

The formalised theorems are in
`lean/DLNFibre/DLN/Aoyagi/RegularSuspensionInterface.lean`:

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

These are projection theorems.  They do not create a new analytic citation:
the only extraction input remains `Cfull.ExtractionHypothesis`.

## Nonclaims

- No construction of `Cfull` from `Cred`.
- No extraction hypothesis for `Cred`.
- No proof that `Cred.jacobianPriorLossShift regularCount` is an analytic
  full regular-suspension certificate.
- No Fubini/polar theorem.
- No Aoyagi Lemma 1, Theorem 4, or regular-coordinate additivity theorem.
- No normal-crossing production, pole-order theorem, or RLCT theorem beyond
  the supplied full-certificate extraction boundary.
