# Review - A0 normal-crossing chart-certificate spine

Reviewer: xhigh Lean/API scout `Meitner the 2nd`.

Status: passed.

## Verdict

The current chart-certificate spine is the smallest non-vacuous A0 improvement:
it carries chart-local monomial identities and unit factors, then forgets to
the existing finite `AoyagiNormalCrossingExponentData`.  It does not prove the
cited analytic normal-crossing extraction theorem.

## Accepted Lean Shape

Accepted declarations:

```text
AoyagiNormalCrossingChartCertificate
AoyagiNormalCrossingChartCertificate.exponentData
AoyagiNormalCrossingChartCertificate.exponentData_numCharts
AoyagiNormalCrossingChartCertificate.exponentData_numCoords
AoyagiNormalCrossingChartCertificate.exponentData_lossExp
AoyagiNormalCrossingChartCertificate.exponentData_jacobianPriorExp
AoyagiNormalCrossingChartCertificate.mem_exponentData_activePairs
AoyagiNormalCrossingChartCertificate.ExtractionHypothesis
AoyagiTheorem2SuppliedChartFinalBoundary
AoyagiTheorem2SuppliedChartFinalBoundary.toSuppliedFinalBoundary
```

The final-boundary wrapper belongs in `Theorem2FinalAssembly.lean`, since it
projects to the already established finite final socket.

## Boundary Checks

- Do not add a theorem turning `AoyagiNormalCrossingChartCertificate` alone
  into `ExtractionHypothesis`.
- Zero `lossExp` coordinates remain ignored.
- Pole order is the maximum over chartwise counts at the global minimum, not
  an arbitrary chart count.
- No Aoyagi Lemma 1, Theorem 4, regular-coordinate additivity, or
  generator-RLCT invariance enters A0.
- `CommMonoid R` is enough for monomial/unit bookkeeping, but it says nothing
  analytic.

## Verification

Reviewer ran:

```text
lake env lean DLNFibre/DLN/Aoyagi/NormalCrossingInterface.lean
lake build DLNFibre.DLN.Aoyagi.NormalCrossingInterface
lake env lean DLNFibre/DLN/Aoyagi/Theorem2FinalAssembly.lean
```

All passed after rebuilding the modified dependency.
