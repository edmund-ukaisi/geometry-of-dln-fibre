# Boundary Map - Remaining Source Obligations for Aoyagi Theorem 2

Date: 2026-06-22.

Status: roadmap boundary.  This is not a theorem and not a source citation.

## Current Final Socket

Lean already has a supplied final socket:

```text
AoyagiTheorem2SuppliedFinalBoundary
```

It packages:

```text
m = aoyagiSelectedReducedWidths H r C
AoyagiNormalCrossingExtractionHypothesis D lambda poleOrder
AoyagiTheorem2FiniteExponentFormulaHypothesis D L ell H r m data
```

The strongest current A6 route can replace the finite exponent formula fields
by active-ratio and displayed-ratio chart-count certificates, and can route
the terminal-order upper bound through a supplied
`TC.TerminalMinimumCountDatumClassifier`.

## Obligations Still Needed Before a Source-Backed Theorem 2

1. Selected cutpoint and Definition 3 provenance.

   Produce the selected cutpoints `C`, the integer widths
   `m = aoyagiSelectedReducedWidths H r C`, the ceiling data
   `AoyagiDefinition3CeilData`, rank-width hypotheses, and the strict
   source-selected inequality from Aoyagi's DLN dimension/rank assumptions.

2. Normal-crossing certificate production.

   Produce concrete normal-crossing exponent data `D`, including charts,
   active coordinates, loss exponents, Jacobian/prior exponents, unit
   nonvanishing, and the finite chart/order count data used by the A0
   interface.  The analytic extraction from such data is the only planned
   citation.

3. Active-ratio lower bound.

   Prove that some active coordinate realizes
   `aoyagiTheorem2Lambda_fromCeilData ...`, and that this displayed ratio is
   less than or equal to every active ratio.

4. Displayed-ratio chart counts.

   Prove a chart whose coordinate count at the displayed ratio is
   `TC.terminalMinimumLabels.card`, plus an all-chart upper bound by that
   same count.

5. A4 blow-up source/chart production.

   Produce the branchwise source data behind the blow-up recursion: successor
   chart/source data, suffix production, transition regularity, coverage,
   coordinate post-data, Jacobian arithmetic, termination, and normal-crossing
   compatibility.  Current `SourceProductionObligation` consumers do not
   construct these data.

6. A2 product-reduction source boundary.

   Bridge the fixed-base residual-product certificate to the source Theorem 3
   hypotheses: rank-stratum/open-chart handling, source-rank consequences,
   regular-suspension data, and analytic ideal transport if it cannot be
   avoided inside the normal-crossing certificate.

7. A5 supplied terminal-order data.

   Because the current source audit freezes Lemma 5 exactness as supplied,
   the final source theorem still needs a supplied or independently corrected
   classifier/injectivity/back-to-label package.  Do not derive it from the
   printed Eq3/Eq4/Eq5 paragraph unless a new reproduction repairs the known
   obstructions.

8. A3 deepest singular point.

   Aoyagi Theorem 4 is not inside the current citation boundary.  Either avoid
   it by proving a local/source-specific route to the needed certificate, or
   ask the operator to expand the citation policy.

## Citation Boundary

The only planned citation remains:

```text
normal-crossing-to-RLCT extraction
```

Do not silently cite Aoyagi Lemma 1, Aoyagi Theorem 4, regular-coordinate
additivity, Theorem 3 analytic transport, or Lemma 5 no-extra coverage.

## Near-Term Controller Direction

- Stop trying to prove source-backed A5 exactness from the printed Lemma 5
  formulas.
- Prefer thin handoff wrappers only when they consume already explicit
  supplied data.
- The next source-moving work should be A4 chart/source production or A2
  source-hypothesis/rank-stratum handling, each with a pen-and-paper
  reproduction before Lean.
