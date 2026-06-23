# Thread 02 - analytic interface

Type: explore/formalisation. Status: closed.

## Task

Specify the cited normal-crossing-to-RLCT extraction interface and decide what
parts of Aoyagi's use of RLCT background are genuinely analytic.

## Output contract

- A precise interface with inputs, outputs, and naming that cannot be confused
  with a proved analytic theorem.
- A verdict on Aoyagi Theorem 4: prove by elementary reduction if possible;
  cite only after a real probe.
- Candidate Lean statement shape, including all assumptions.

## Controller notes

The operator has allowed the normal-crossing extraction theorem to remain Cited.
Do not expand the cited boundary without evidence.

## 2026-06-18 controller draft

Scout `Boole` returned and the controller extracted a draft cited-interface
shape at `interface-draft.md`. This remains a draft until A4 supplies the exact
normal-crossing certificate data. It explicitly excludes Aoyagi Lemma 1 and
Theorem 4 from the allowed citation boundary.

## 2026-06-18 A2 interface repair

Reopened the analytic boundary after the A2 chart-local induction step landed.
Xhigh scouts `Hypatia` and `Kepler` independently checked the post-Theorem-3
passage on PDF p. 13. Controller decision: keep A0 as a concrete
normal-crossing extraction boundary, not as a broad analytic-ideal invariance
package.

Repair note: `interface-repair-a2.md`.

Consequences:

- Aoyagi Lemma 1 remains outside A0 as a general RLCT generator-comparison
  theorem.
- Regular-coordinate additivity after Theorem 3 is not cited separately.
- The preferred route is to prove elementary matrix-entry ideal algebra and to
  build the regular variables into a full normal-crossing certificate, so the
  `c/2` shift is finite certificate arithmetic before the single extraction
  citation.

## 2026-06-22 finite exponent interface

Lean now contains the exponent-only interface
`lean/DLNFibre/DLN/Aoyagi/NormalCrossingInterface.lean`, imported by
`lean/DLNFibre.lean`.

This module records only the finite formula after a normal-crossing chart
certificate has been supplied:

- active coordinates have `k > 0`;
- `exponentMinimum` is the minimum of `(h+1)/(2*k)` over active chart
  coordinates;
- `exponentOrder` is the maximum, over charts, of the number of active
  coordinates attaining the global minimum;
- `AoyagiNormalCrossingExtractionHypothesis` is the explicit cited-boundary
  hypothesis equating external `lambda, theta` with those finite values.

Artifacts:

- `reproduction-normal-crossing-exponent-interface-a0.md`;
- `statement-card-a0-normal-crossing-exponent-interface.md`;
- `review-normal-crossing-exponent-interface-a0.md`.

Nonclaims remain unchanged: no analytic theorem, chart production,
nonvanishing units, Aoyagi Lemma 1, regular-coordinate additivity, Theorem 4,
pole-order theorem, or RLCT theorem is proved by this module.

## 2026-06-22 finite min/order certificates

Lean now also exposes finite certificate lemmas in
`lean/DLNFibre/DLN/Aoyagi/NormalCrossingInterface.lean`.

For the finite minimum, a candidate `q` is certified by either:

```text
q in D.activeRatios
forall r in D.activeRatios, q <= r
```

or by an active coordinate whose ratio is `q`, plus the corresponding
lower-bound inequality against every active coordinate.

For the finite order, a candidate `q` is certified by either:

```text
q in D.chartMinCounts
forall r in D.chartMinCounts, r <= q
```

or by a chart whose minimum-coordinate count is `q`, plus a uniform upper
bound for all chart counts.

Artifacts:

- `reproduction-normal-crossing-finite-certificates-a0.md`;
- `statement-card-a0-normal-crossing-finite-certificates.md`;
- `review-normal-crossing-finite-certificates-a0.md`.

Nonclaims remain unchanged: these are finite `min'`/`max'` lemmas only.  They
do not produce charts, prove normal crossings, identify chartwise counts with
Lemma 5 terminal labels, prove pole order without A0, or extract RLCT.

## 2026-06-22 ratio chart counts

Lean now also exposes source-facing chart counts at a specified ratio:

```text
coordsInChartAtRatio
countInChartAtRatio
minCoordsInChart_eq_coordsInChartAtRatio_of_exponentMinimum_eq
minCountInChart_eq_countInChartAtRatio_of_exponentMinimum_eq
exponentOrder_eq_of_countInChartAtRatio_eq_of_forall_le
```

These lemmas rewrite ratio-specific chart counts to the existing
global-minimum chart counts once the candidate ratio is proved equal to
`D.exponentMinimum`.  This is finite definitional bookkeeping only; it does
not construct charts, prove source chart counts, prove pole order, or extract
RLCT.

Artifacts:

- `reproduction-normal-crossing-ratio-chart-counts-a0.md`;
- `statement-card-a0-normal-crossing-ratio-chart-counts.md`;
- `review-normal-crossing-ratio-chart-counts-a0.md`.

## 2026-06-23 chart-certificate spine

Lean now adds a source-facing chart-certificate spine in
`lean/DLNFibre/DLN/Aoyagi/NormalCrossingInterface.lean`:

```text
AoyagiNormalCrossingChartCertificate
AoyagiNormalCrossingChartCertificate.exponentData
AoyagiNormalCrossingChartCertificate.ExtractionHypothesis
```

The certificate records finite chart domains, chart maps, coordinates,
loss/Jacobian-prior functions, monomial identities with unit factors, unit
witnesses, and exponent arrays.  Forgetting this data gives the existing
`AoyagiNormalCrossingExponentData`.  The chart-level extraction hypothesis is
only a wrapper around the existing cited
`AoyagiNormalCrossingExtractionHypothesis`.

`lean/DLNFibre/DLN/Aoyagi/Theorem2FinalAssembly.lean` now also contains
`AoyagiTheorem2SuppliedChartFinalBoundary`, which projects a supplied chart
certificate into the existing final boundary.

Artifacts:

- `reproduction-normal-crossing-chart-certificate-spine-a0.md`;
- `statement-card-a0-normal-crossing-chart-certificate-spine.md`.

This is a non-vacuous certificate target for future A4 chart production, not
an analytic theorem.  It does not prove chart construction, coverage, analytic
nonvanishing, change of variables, Aoyagi Lemma 1, finite formula equalities,
pole order without A0, or RLCT extraction.

## 2026-06-23 Jacobian-prior loss shift

Lean now adds a finite exponent-array shift operation in
`lean/DLNFibre/DLN/Aoyagi/NormalCrossingInterface.lean`:

```text
jacobianPriorLossShift
ratioAt_jacobianPriorLossShift_of_mem_activePairs
exponentMinimum_jacobianPriorLossShift
coordsInChartAtRatio_jacobianPriorLossShift
countInChartAtRatio_jacobianPriorLossShift
minCoordsInChart_jacobianPriorLossShift
minCountInChart_jacobianPriorLossShift
exponentOrder_jacobianPriorLossShift
```

The operation keeps the loss exponents `k` fixed and replaces each
Jacobian/prior exponent `h` by `h + m*k`.  On active coordinates this shifts
`(h+1)/(2*k)` by `m/2`, shifts the finite minimum by `m/2`, and preserves the
minimum-coordinate chart counts and finite order.

Artifacts:

- `reproduction-normal-crossing-jacobian-prior-loss-shift-a0.md`;
- `statement-card-a0-normal-crossing-jacobian-prior-loss-shift.md`.

This is certificate arithmetic motivated by Aoyagi PDF p. 13's regular-variable
count.  It is not chart production, analytic regular-coordinate additivity,
Jacobian/volume-form construction, normal crossings, pole order, or RLCT
extraction.

## 2026-06-23 chart-certificate Jacobian-prior loss shift

Lean now lifts the finite exponent-array shift to the chart-certificate spine:

```text
AoyagiNormalCrossingChartCertificate.jacobianPriorLossShift
AoyagiNormalCrossingChartCertificate.exponentData_jacobianPriorLossShift
AoyagiNormalCrossingChartCertificate.exponentData_exponentMinimum_jacobianPriorLossShift
AoyagiNormalCrossingChartCertificate.exponentData_exponentOrder_jacobianPriorLossShift
```

The operation leaves the chart maps, coordinates, loss, loss unit, and
Jacobian/prior unit unchanged, and replaces the chart certificate's
Jacobian/prior value by the old value times
`prod_j coord_j^(m * lossExp_j)`.  The projected finite exponent data is
definitionally the existing `jacobianPriorLossShift` on
`AoyagiNormalCrossingExponentData`.

Artifacts:

- `reproduction-normal-crossing-chart-certificate-jacobian-prior-loss-shift-a0.md`;
- `statement-card-a0-normal-crossing-chart-certificate-jacobian-prior-loss-shift.md`;
- `review-normal-crossing-chart-certificate-jacobian-prior-loss-shift-a0.md`.

This is certificate algebra on supplied chart data.  It defines a certificate
for a modified `jacobianPrior`; it does not prove an analytic
Jacobian/volume-form theorem, regular-suspension chart construction, chart
coverage, transition regularity, pole order, RLCT additivity, or extraction
transfer from a reduced certificate.

## 2026-06-23 chart-certificate unit multiplication

Lean now adds a unit-only chart-certificate transformer:

```text
AoyagiNormalCrossingChartCertificate.unitMultiply
AoyagiNormalCrossingChartCertificate.exponentData_unitMultiply
AoyagiNormalCrossingChartCertificate.exponentData_exponentMinimum_unitMultiply
AoyagiNormalCrossingChartCertificate.exponentData_exponentOrder_unitMultiply
```

The operation takes replacement loss and Jacobian/prior functions, supplied
chartwise multiplicative identities against the old certificate, and supplied
unit witnesses for those multipliers.  It absorbs the multipliers into the
recorded unit fields and leaves the chart maps, coordinates, loss exponents,
and Jacobian/prior exponents unchanged.  Therefore the projected finite
exponent data, minimum, and order are unchanged.

Artifacts:

- `reproduction-normal-crossing-chart-certificate-unit-multiply-a0.md`;
- `statement-card-a0-normal-crossing-chart-certificate-unit-multiply.md`;
- `review-normal-crossing-chart-certificate-unit-multiply-a0.md`.

This is certificate algebra only.  It does not prove analytic unit
neighbourhoods, chart construction, chart coverage, a Jacobian/volume-form
theorem, global normal crossings, pole order, RLCT extraction, or permission
to treat coordinate monomial factors as units.
