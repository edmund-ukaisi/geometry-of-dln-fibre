# Thread 06 - DLN translation

Type: formalisation. Status: active; first formula-notation slice landed.

## Task

Translate Aoyagi's notation and final formula to this repo's DLN notation
using Aoyagi's paper as the only mathematical source.

## Output contract

- Dimension/rank convention map.
- A theorem or statement card showing the local Aoyagi formula in repo notation.
- Explicit warning that Aoyagi's `theta` is RLCT order/multiplicity and should
  use a distinct Lean/display name such as `rlctOrder`.

## Controller notes

Do not consult the Lehalleur-Rimanyi source for this translation. Any later
comparison belongs outside this Aoyagi-only expedition.

## Current slice - 2026-06-22

The first A6 Lean layer is
`lean/DLNFibre/DLN/Aoyagi/FinalFormula.lean`, imported by
`lean/DLNFibre.lean`.

It translates Aoyagi Definition 3 and Theorem 2's displayed arithmetic into
source-facing notation:

- integer reduced widths `M^(s)=H^(s)-r`;
- local rank-width bridge lemmas converting integer reduced widths to Nat
  subtraction only under explicit `r <= H s` hypotheses;
- indexed selected reduced widths from `AoyagiSelectedCutpoints`;
- selected reduced-width bridge lemmas for the Nat-indexed Lemma 5 width
  accessor;
- a separate selected value set helper, not used for sums;
- `AoyagiDefinition3CeilData`, separating the selected object from the
  ceiling integer `ceilWidth` and recording `0 < ell`, `0 < a <= ell`;
- the Theorem 2 order formula as `theorem2OrderFormula`, not `theta`;
- the three displayed `lambda` formula definitions and elementary rational
  rewrites among them.

Artifacts:

- `reproduction-definition3-theorem2-translation-a6.md`;
- `reproduction-dimension-rank-convention-a6.md`;
- `statement-card-a6-final-formula-notation.md`;
- `statement-card-a6-dimension-rank-convention.md`;
- `review-final-formula-notation-a6.md`;
- `review-dimension-rank-convention-a6.md`.

Boundary: this is convention and formula bookkeeping only.  It does not prove
rank-width inequalities from a concrete matrix product, the full Definition 3
selection inequalities, existence of the ceiling datum, Lemma 4 or Lemma 5
exponent minimisation, normal crossings, pole order, or RLCT extraction.

## Current slice - 2026-06-22, Definition 3 bridge

The next A6 Lean layer is
`lean/DLNFibre/DLN/Aoyagi/Definition3Bridge.lean`, imported by
`lean/DLNFibre.lean`.

It consumes a supplied `AoyagiDefinition3CeilData` in the existing Lemma 4 and
Htilde arithmetic API:

- terminal endpoint zero;
- lower/upper Htilde terminal zero;
- penultimate upper-chain endpoint rewrite;
- finite interval-size and same-coordinate Htilde value-set count rewrites to
  `theorem2OrderFormula`;
- terminal same-coordinate singleton and supplied terminal Eq5 offset
  bookkeeping;
- Lemma 4's two-value count wrapper under supplied chain bounds and supplied
  two-value increments;
- selected-width and local equation `(4)`/`(5)` wrappers only when the strict
  source-selected inequality is supplied separately;
- local equation `(3)` wrapper only with the still-explicit one-unit slack.

Artifacts:

- `reproduction-definition3-lemma4-bridge-a6.md`;
- `statement-card-a6-definition3-bridge.md`;
- `review-definition3-bridge-a6.md`.

## Current slice - 2026-06-23, Definition 3 source-data ceiling

`lean/DLNFibre/DLN/Aoyagi/Definition3Bridge.lean` now also removes the supplied
ceiling/residue datum once selected cutpoints and `0 < ell` are supplied.

New Lean artifacts:

- `AoyagiDefinition3SourceData`;
- `AoyagiDefinition3CeilData.nonempty_of_ell_pos`;
- `AoyagiDefinition3SourceData.exists_ceilData`.

The generic constructor uses integer Euclidean division of the selected-width
sum by `ell`: if the remainder is zero it sets `aParam = ell`; otherwise it
sets `aParam` to the positive remainder.  The source-data wrapper records
value-level selected dominance, selected strict inequalities, and value-level
nonselected inequalities from Definition 3, then produces an
`AoyagiDefinition3CeilData` and carries the strict selected inequality forward.

Artifacts:

- `reproduction-definition3-source-data-ceil-a6.md`;
- `statement-card-a6-definition3-source-data-ceil.md`;
- `review-definition3-source-data-ceil-a6.md`.

Boundary: this does not construct selected cutpoints, prove the selected value
set exists for arbitrary widths, prove uniqueness, use nonselected inequalities
downstream, produce normal crossings, or extract pole order/RLCT.

## Current slice - 2026-06-22, conditional finite exponent bridge

The A6/A0 bridge layer is
`lean/DLNFibre/DLN/Aoyagi/Theorem2FiniteExponentBridge.lean`, imported by
`lean/DLNFibre.lean`.

It introduces `AoyagiTheorem2FiniteExponentFormulaHypothesis`, a supplied
boundary structure requiring the two finite equalities still owed by the
eventual normal-crossing certificate:

- `D.exponentMinimum = aoyagiTheorem2Lambda_fromCeilData L ell H r m data`;
- `D.exponentOrder = data.theorem2OrderFormula`.

Together with `AoyagiNormalCrossingExtractionHypothesis D lambda poleOrder`,
the module proves conditional wrappers for the ceiling-data, average, and
expanded displayed `lambda` formulas, plus the displayed order formula.

Artifacts:

- `reproduction-theorem2-finite-exponent-bridge-a6.md`;
- `statement-card-a6-theorem2-finite-exponent-bridge.md`;
- `review-theorem2-finite-exponent-bridge-a6.md`.

Boundary: this is final-socket composition only.  It does not produce exponent
data, prove the two finite equalities, prove source parameter provenance, prove
Definition 3 selection data, prove rank-width hypotheses, prove normal
crossings, prove Aoyagi Lemma 5 exactness/order count, prove pole order without
A0, or prove the analytic extraction theorem.

## Current slice - 2026-06-22, finite certificate bridge

The same module now also contains constructors that fill
`AoyagiTheorem2FiniteExponentFormulaHypothesis` from the A0 finite min/order
certificate API:

```text
AoyagiTheorem2FiniteExponentFormulaHypothesis.of_activePair_ratioAt_eq_of_forall_le_of_chart_minCount_eq_of_forall_le
AoyagiTheorem2FiniteExponentFormulaHypothesis.lambda_and_poleOrder_eq_fromCeilData_and_orderFormula_of_activePair_chartCount
```

The constructor takes an active coordinate whose ratio is the displayed
Theorem 2 `lambda` value, a lower bound against every active ratio, a chart
whose global-minimum count is `data.theorem2OrderFormula`, and an upper bound
against every chart count.  The pair theorem additionally requires the
explicit A0 extraction hypothesis.

Artifacts:

- `reproduction-theorem2-finite-certificate-bridge-a6.md`;
- `statement-card-a6-theorem2-finite-certificate-bridge.md`;
- `review-theorem2-finite-certificate-bridge-a6.md`.

Boundary: this does not prove chart production, unit factors,
Jacobian/prior exponent correctness, the active-ratio inequalities,
chart-count upper bounds, Lemma 5 no-extra coverage, pole order without A0,
or RLCT extraction.

## Current slice - 2026-06-22, supplied final assembly boundary

The A6 final assembly boundary is
`lean/DLNFibre/DLN/Aoyagi/Theorem2FinalAssembly.lean`, imported by
`lean/DLNFibre.lean`.

It introduces `AoyagiTheorem2SuppliedFinalBoundary`, which packages:

- selected-width provenance `m = aoyagiSelectedReducedWidths H r C`;
- `AoyagiNormalCrossingExtractionHypothesis D lambda poleOrder`;
- `AoyagiTheorem2FiniteExponentFormulaHypothesis D L ell H r m data`.

Lean then projects selected-width bookkeeping and the displayed formula
consequences.  The selected rank-width hypotheses and strict source
selected-width inequality are explicit arguments only on the auxiliary width
lemmas that use them, not fields of the final socket.

```text
selectedWidths_eq_natCast_sub
selectedWidths_nonneg
selectedWidthNat_nonneg
selectedWidth_le_pred
lambda_eq_theorem2Lambda_fromCeilData
lambda_eq_theorem2Lambda_average
lambda_eq_theorem2Lambda_expanded
poleOrder_eq_theorem2OrderFormula
lambda_and_poleOrder_eq_fromCeilData_and_orderFormula
lambda_and_poleOrder_eq_expanded_and_orderFormula
lambda_eq_theorem2Lambda_average_selectedReducedWidths
lambda_eq_theorem2Lambda_expanded_selectedReducedWidths
```

Artifacts:

- `reproduction-theorem2-final-assembly-a6.md`;
- `statement-card-a6-theorem2-final-assembly.md`;
- `review-theorem2-final-assembly-a6.md`.

Boundary: this is still a supplied final socket, not an unconditional final
theorem.  It does not prove selected cutpoint existence, Definition 3
source-selection, rank-width hypotheses from the matrix problem,
normal-crossing chart production, finite exponent formula equalities, Lemma 5
no-extra coverage/order count, pole order without A0, or the analytic
extraction theorem.

## Current slice - 2026-06-23, chart finite-certificate bridge

The chart-certificate final boundary now also has a finite-certificate
constructor in `lean/DLNFibre/DLN/Aoyagi/Theorem2FinalAssembly.lean`:

```text
AoyagiTheorem2SuppliedChartFinalBoundary.of_activePair_ratioAt_eq_of_forall_le_of_chart_minCount_eq_of_forall_le
AoyagiTheorem2SuppliedChartFinalBoundary.lambda_and_poleOrder_eq_fromCeilData_and_orderFormula_of_activePair_chartCount
```

This consumes selected-width provenance, the chart-level A0 extraction
hypothesis, an active coordinate realizing the displayed Theorem 2 `lambda`
formula, a lower bound over all active pairs, a chart whose count is the
displayed order formula, and a chart-count upper bound for every chart.  It
then constructs the chart-level final boundary and derives the same
lambda/order pair conclusion.

Artifacts:

- `reproduction-theorem2-chart-finite-certificate-bridge-a6.md`;
- `statement-card-a6-theorem2-chart-finite-certificate-bridge.md`;
- `review-theorem2-chart-finite-certificate-bridge-a6.md`.

Boundary: this is still finite final-socket composition.  It does not
construct the chart certificate, prove chart coverage, analytic unit
nonvanishing, active-ratio bounds, chart-count witnesses or upper bounds,
Lemma 5 exactness, pole order without A0, or RLCT extraction.

## Current slice - 2026-06-23, chart ratio-count bridge

The chart-certificate final boundary now also accepts chart counts stated at
the displayed candidate ratio:

```text
AoyagiTheorem2SuppliedChartFinalBoundary.of_activePair_ratioAt_eq_of_forall_le_of_countInChartAtRatio_eq_of_forall_le
AoyagiTheorem2SuppliedChartFinalBoundary.lambda_and_poleOrder_eq_fromCeilData_and_orderFormula_of_activePair_ratioCount
```

This variant first uses the supplied active-coordinate witness and all-active
lower bound to prove that the displayed Theorem 2 lambda formula is
`Cnc.exponentData.exponentMinimum`.  Only after that identification does it
turn `countInChartAtRatio displayedLambda` witnesses and upper bounds into the
displayed order formula.

Artifacts:

- `reproduction-theorem2-chart-ratio-count-bridge-a6.md`;
- `statement-card-a6-theorem2-chart-ratio-count-bridge.md`;
- `review-theorem2-chart-ratio-count-bridge-a6.md`.

Boundary: this is finite ratio-count bookkeeping only.  It does not construct
the chart certificate, prove active-ratio lower bounds, ratio-count witnesses
or upper bounds, Lemma 5 exactness, pole order without A0, or RLCT extraction.

## Current slice - 2026-06-22, terminal-order handoff

The A5-to-A6 terminal-order handoff is
`lean/DLNFibre/DLN/Aoyagi/Theorem2TerminalOrderBridge.lean`, imported by
`lean/DLNFibre.lean`.

It decomposes only the order field of
`AoyagiTheorem2FiniteExponentFormulaHypothesis`.  Instead of supplying
`D.exponentOrder = data.theorem2OrderFormula` directly, the new bridge accepts
the supplied chart/order identification

```text
D.exponentOrder = TC.terminalMinimumLabels.card
```

and then uses the existing Lemma 5 terminal-order bridge, under supplied
branch-label injectivity and supplied terminal upper bound, to derive

```text
TC.terminalMinimumLabels.card = data.theorem2OrderFormula.
```

Lean names:

```text
AoyagiLemma5SuppliedTerminalCandidateFamily.theorem2FiniteExponentFormulaHypothesis_of_terminalMinimumLabels_card
AoyagiLemma5SuppliedTerminalCandidateFamily.theorem2SuppliedFinalBoundary_of_terminalMinimumLabels_card
AoyagiLemma5SuppliedTerminalCandidateFamily.lambda_and_poleOrder_eq_fromCeilData_and_orderFormula_of_terminalMinimumLabels_card
```

Artifacts:

- `reproduction-theorem2-terminal-order-bridge-a6.md`;
- `statement-card-a6-theorem2-terminal-order-bridge.md`;
- `review-theorem2-terminal-order-bridge-a6.md`.

Boundary: the exponent-minimum formula, chart-order/terminal-label
identification, selected-width provenance, A0 extraction hypothesis,
branch-label injectivity, and terminal upper bound remain supplied.  This is
not source-backed Lemma 5 no-extra coverage, chart production, pole order
without A0, or RLCT extraction.

## Current slice - 2026-06-22, active-ratio terminal-order handoff

The same terminal-order bridge now also composes the A0 active-ratio finite
minimum certificate with the A5 terminal-order handoff.  Instead of supplying

```text
D.exponentMinimum = aoyagiTheorem2Lambda_fromCeilData ...
```

directly, the new wrappers accept:

```text
p in D.activePairs,
D.ratioAt p = aoyagiTheorem2Lambda_fromCeilData ...,
forall p' in D.activePairs,
  aoyagiTheorem2Lambda_fromCeilData ... <= D.ratioAt p'.
```

They still require the supplied chart/order equality
`D.exponentOrder = TC.terminalMinimumLabels.card`, supplied branch-label
injectivity, supplied terminal upper bound, selected-width provenance, and the
A0 extraction hypothesis where relevant.

Lean names:

```text
AoyagiLemma5SuppliedTerminalCandidateFamily.theorem2FiniteExponentFormulaHypothesis_of_activePair_terminalMinimumLabels_card
AoyagiLemma5SuppliedTerminalCandidateFamily.theorem2SuppliedFinalBoundary_of_activePair_terminalMinimumLabels_card
AoyagiLemma5SuppliedTerminalCandidateFamily.lambda_and_poleOrder_eq_of_activePair_terminalMinimumLabels_card
```

Artifacts:

- `reproduction-theorem2-active-terminal-order-bridge-a6.md`;
- `statement-card-a6-theorem2-active-terminal-order-bridge.md`;
- `review-theorem2-active-terminal-order-bridge-a6.md`.

Boundary: this reduces the final finite socket from a raw supplied exponent
minimum equality to an explicit finite active-ratio certificate.  It still
does not prove chart production, active-ratio lower bounds from source charts,
chart-order/terminal-label identification, Lemma 5 no-extra coverage, pole
order without A0, normal crossings, or RLCT extraction.

## Current slice - 2026-06-22, active chart-terminal-order handoff

The terminal-order bridge now also composes the A0 chart-count finite maximum
certificate with the active-ratio minimum and the A5 terminal-order route.
Instead of supplying

```text
D.exponentOrder = TC.terminalMinimumLabels.card
```

directly, the new wrappers accept:

```text
D.minCountInChart c = TC.terminalMinimumLabels.card,
forall c', D.minCountInChart c' <= TC.terminalMinimumLabels.card.
```

Together with the active-ratio certificate and the supplied Lemma 5
terminal-order obstruction, this fills both fields of
`AoyagiTheorem2FiniteExponentFormulaHypothesis`.

Lean names:

```text
AoyagiLemma5SuppliedTerminalCandidateFamily.theorem2FiniteExponentFormulaHypothesis_of_activePair_chartCount_terminalMinimumLabels_card
AoyagiLemma5SuppliedTerminalCandidateFamily.theorem2SuppliedFinalBoundary_of_activePair_chartCount_terminalMinimumLabels_card
AoyagiLemma5SuppliedTerminalCandidateFamily.lambda_and_poleOrder_eq_of_activePair_chartCount_terminalMinimumLabels_card
```

Artifacts:

- `reproduction-theorem2-active-chart-terminal-order-bridge-a6.md`;
- `statement-card-a6-theorem2-active-chart-terminal-order-bridge.md`;
- `review-theorem2-active-chart-terminal-order-bridge-a6.md`.

Boundary: this reduces the remaining raw chart/order equality to an explicit
finite chart-count maximum certificate.  It still does not prove chart
production, active-ratio lower bounds, chart-count upper bounds from source
charts, chart-count/terminal-label identification from source, Lemma 5
no-extra coverage, pole order without A0, normal crossings, or RLCT
extraction.

## Current slice - 2026-06-22, displayed-ratio count handoff

The bridge now has source-facing wrappers whose chart-count hypotheses are
stated at the displayed Theorem 2 lambda value rather than at
`D.exponentMinimum`.  The active-ratio minimum certificate first proves that
the displayed value is `D.exponentMinimum`; the A0 ratio-count rewrite then
turns these counts into the chartwise global-minimum counts used by
`D.exponentOrder`.

Lean names:

```text
AoyagiLemma5SuppliedTerminalCandidateFamily.theorem2FiniteExponentFormulaHypothesis_of_activePair_ratioCount_terminalMinimumLabels_card
AoyagiLemma5SuppliedTerminalCandidateFamily.theorem2SuppliedFinalBoundary_of_activePair_ratioCount_terminalMinimumLabels_card
AoyagiLemma5SuppliedTerminalCandidateFamily.lambda_and_poleOrder_eq_of_activePair_ratioCount_terminalMinimumLabels_card
```

Artifacts:

- `reproduction-theorem2-ratio-count-terminal-order-bridge-a6.md`;
- `statement-card-a6-theorem2-ratio-count-terminal-order-bridge.md`;
- `review-theorem2-ratio-count-terminal-order-bridge-a6.md`.

Boundary: this is only a ratio-count rewrite and final-socket handoff.  It
does not prove source chart counts, chart-count upper bounds, source-backed
Lemma 5 no-extra coverage, pole order without A0, normal crossings, or RLCT
extraction.

## Current slice - 2026-06-22, counted-datum terminal-order handoff

The A6 terminal-order bridge now has counted-datum classifier variants of all
four terminal-order socket levels: raw terminal-label order equality,
active-ratio minimum, active chart-count, and displayed-ratio chart-count.
Each variant keeps supplied branch-label injectivity and replaces only the raw
upper-bound input

```text
TC.terminalMinimumLabels.card <= data.theorem2OrderFormula
```

by a supplied

```text
TC.TerminalMinimumCountDatumClassifier.
```

Lean names:

```text
AoyagiLemma5SuppliedTerminalCandidateFamily.theorem2FiniteExponentFormulaHypothesis_of_terminalMinimumLabels_card_of_classifier
AoyagiLemma5SuppliedTerminalCandidateFamily.theorem2FiniteExponentFormulaHypothesis_of_activePair_terminalMinimumLabels_card_of_classifier
AoyagiLemma5SuppliedTerminalCandidateFamily.theorem2FiniteExponentFormulaHypothesis_of_activePair_chartCount_classifier
AoyagiLemma5SuppliedTerminalCandidateFamily.theorem2FiniteExponentFormulaHypothesis_of_activePair_ratioCount_classifier
AoyagiLemma5SuppliedTerminalCandidateFamily.theorem2SuppliedFinalBoundary_of_terminalMinimumLabels_card_of_classifier
AoyagiLemma5SuppliedTerminalCandidateFamily.theorem2SuppliedFinalBoundary_of_activePair_terminalMinimumLabels_card_of_classifier
AoyagiLemma5SuppliedTerminalCandidateFamily.theorem2SuppliedFinalBoundary_of_activePair_chartCount_classifier
AoyagiLemma5SuppliedTerminalCandidateFamily.theorem2SuppliedFinalBoundary_of_activePair_ratioCount_classifier
AoyagiLemma5SuppliedTerminalCandidateFamily.lambda_and_poleOrder_eq_fromCeilData_and_orderFormula_of_terminalMinimumLabels_card_of_classifier
AoyagiLemma5SuppliedTerminalCandidateFamily.lambda_and_poleOrder_eq_of_activePair_terminalMinimumLabels_card_of_classifier
AoyagiLemma5SuppliedTerminalCandidateFamily.lambda_and_poleOrder_eq_of_activePair_chartCount_classifier
AoyagiLemma5SuppliedTerminalCandidateFamily.lambda_and_poleOrder_eq_of_activePair_ratioCount_classifier
```

Artifacts:

- `reproduction-theorem2-countdatum-terminal-order-bridge-a6.md`;
- `statement-card-a6-theorem2-countdatum-terminal-order-bridge.md`;
- `review-theorem2-countdatum-terminal-order-bridge-a6.md`.

Boundary: this is finite A5-to-A6 handoff only.  It does not construct the
classifier, branch-label injectivity, back-to-label map, Eq3/Eq4/Eq5
coverage, source labels, terminal `tilde t=0`, chart production, pole order
without A0, normal crossings, or RLCT extraction.

## Current slice - 2026-06-23, chart terminal-order handoff

The chart-certificate final boundary now has A5 terminal-order handoff
variants in `lean/DLNFibre/DLN/Aoyagi/Theorem2TerminalOrderBridge.lean`.
These mirror the finite-data terminal-order wrappers but preserve
`AoyagiNormalCrossingChartCertificate` and the chart-level extraction
hypothesis:

```text
AoyagiLemma5SuppliedTerminalCandidateFamily.theorem2SuppliedChartFinalBoundary_of_activePair_chartCount_terminalMinimumLabels_card
AoyagiLemma5SuppliedTerminalCandidateFamily.theorem2SuppliedChartFinalBoundary_of_activePair_ratioCount_terminalMinimumLabels_card
AoyagiLemma5SuppliedTerminalCandidateFamily.theorem2SuppliedChartFinalBoundary_of_activePair_chartCount_classifier
AoyagiLemma5SuppliedTerminalCandidateFamily.theorem2SuppliedChartFinalBoundary_of_activePair_ratioCount_classifier
AoyagiLemma5SuppliedTerminalCandidateFamily.lambda_and_poleOrder_eq_of_chart_activePair_chartCount_terminalMinimumLabels_card
AoyagiLemma5SuppliedTerminalCandidateFamily.lambda_and_poleOrder_eq_of_chart_activePair_ratioCount_terminalMinimumLabels_card
AoyagiLemma5SuppliedTerminalCandidateFamily.lambda_and_poleOrder_eq_of_chart_activePair_chartCount_classifier
AoyagiLemma5SuppliedTerminalCandidateFamily.lambda_and_poleOrder_eq_of_chart_activePair_ratioCount_classifier
```

The wrappers consume selected-width provenance, chart-level A0 extraction, an
active-ratio minimum certificate, chart-count or displayed-ratio chart-count
data equal to `TC.terminalMinimumLabels.card`, supplied branch-label
injectivity, a uniform all-chart upper bound by
`TC.terminalMinimumLabels.card`, and either a supplied terminal upper bound or
a supplied `TerminalMinimumCountDatumClassifier`.  The finite exponent formula
field is then filled by the existing A5/A6 terminal-order bridge while the
final socket stays chart-certificate-shaped.

Artifacts:

- `reproduction-theorem2-chart-terminal-order-bridge-a6.md`;
- `statement-card-a6-theorem2-chart-terminal-order-bridge.md`;
- `review-theorem2-chart-terminal-order-bridge-a6.md`.

Boundary: this is finite A5-to-A6 handoff only.  It does not construct chart
certificates, chart coverage, active-ratio bounds, chart-count facts,
counted-datum classifiers, branch-label injectivity, Lemma 5 exactness, pole
order without A0, normal crossings, or RLCT extraction.  The next source-moving
frontier remains A4/A0 chart/source production.

## Current slice - 2026-06-22, remaining source obligations boundary map

Roadmap artifact:
`boundary-map-theorem2-remaining-source-obligations-a6.md`.
Statement card:
`statement-card-a6-theorem2-remaining-source-obligations.md`.

The boundary map records that the current final socket remains conditional.
The non-A5 source obligations are selected-cutpoint and Definition 3
provenance, normal-crossing certificate production, active-ratio lower bounds,
displayed-ratio chart counts, A4 blow-up source/chart production, A2
source-boundary handling, and A3 avoidance or policy change.  A5 terminal
exactness remains supplied or corrected-construction territory after the
source audit.

The only planned citation remains normal-crossing-to-RLCT extraction.  The map
explicitly does not cite Aoyagi Lemma 1, Aoyagi Theorem 4,
regular-coordinate additivity, A2 analytic transport, or Lemma 5 no-extra
coverage.

## Current slice - 2026-06-23, Case 2 to Theorem 2 finite formula

Reproduction:
`reproduction-case2-theorem2-finite-formula-bridge-a6.md`.
Statement card:
`statement-card-a6-case2-theorem2-finite-formula-bridge.md`.
Review artifact:
`review-case2-theorem2-finite-formula-bridge-a6.md`.

Lean now has a leaf bridge module:

```text
DLNFibre.DLN.Aoyagi.Case2Theorem2FiniteExponentBridge
```

with theorem:

```text
Case2DisplayedContinuingA0ExponentCoordinateBridge.theorem2FiniteExponentFormulaHypothesis_of_forall_le_of_centerCard_eq_fromCeilData
```

It builds `AoyagiTheorem2FiniteExponentFormulaHypothesis` from the supplied
Case 2/A0 coordinate bridge, an explicit active-ratio lower bound, a supplied
equality identifying the Case 2 center-cardinality ratio with Theorem 2's
displayed lambda formula, and a supplied order equality.

Boundary: finite composition only.  It does not prove the lower bound, lambda
identification, order equality, selected-width provenance, chart production,
analytic extraction, pole order, or RLCT.

## Current slice - 2026-06-23, Case 2 ratio-count finite formula

Reproduction:
`reproduction-case2-theorem2-ratio-count-finite-formula-bridge-a6.md`.
Statement card:
`statement-card-a6-case2-theorem2-ratio-count-finite-formula-bridge.md`.
Review artifact:
`review-case2-theorem2-ratio-count-finite-formula-bridge-a6.md`.

Lean now has a ratio-count variant:

```text
Case2DisplayedContinuingA0ExponentCoordinateBridge.theorem2FiniteExponentFormulaHypothesis_of_forall_le_of_centerCard_eq_fromCeilData_of_countInChartAtRatio_eq_of_forall_le
```

It first proves that the Case 2 center-cardinality ratio is the global finite
minimum, then uses supplied `countInChartAtRatio` data at that ratio to certify
the exponent order.  This replaces a raw order equality by explicit
finite chart-count obligations.

Boundary: the chart-count equality and all-chart upper bound remain supplied.
No chart production, active-ratio lower-bound proof, selected-width
provenance, analytic extraction, pole order, or RLCT is proved.

## Current slice - 2026-06-23, Case 2 chart-final boundary

Reproduction:
`reproduction-case2-theorem2-chart-final-bridge-a6.md`.
Statement card:
`statement-card-a6-case2-theorem2-chart-final-bridge.md`.
Review artifact:
`review-case2-theorem2-chart-final-bridge-a6.md`.

Lean now has a leaf chart-final wrapper:

```text
Case2DisplayedContinuingA0ExponentCoordinateBridge.theorem2SuppliedChartFinalBoundary_of_forall_le_of_centerCard_eq_fromCeilData_of_countInChartAtRatio_eq_of_forall_le
```

It carries the Case 2 ratio-count finite formula bridge into
`AoyagiTheorem2SuppliedChartFinalBoundary` once selected-width provenance and
the chart-level A0 extraction hypothesis are supplied.

Boundary: this is API plumbing only.  It does not construct charts, prove
coverage, prove the finite count facts, prove selected-width provenance, prove
analytic extraction, pole order, or RLCT.

## Current slice - 2026-06-23, Definition 3 source-data local wrappers

Reproduction:
`reproduction-definition3-source-data-local-wrappers-a6.md`.
Statement card:
`statement-card-a6-definition3-source-data-local-wrappers.md`.
Review artifact:
`review-definition3-source-data-local-wrappers-a6.md`.

Lean now routes the strict selected-width inequality already stored in
`AoyagiDefinition3SourceData` into the existing Definition 3 / Lemma 5 local
arithmetic wrappers:

```text
AoyagiDefinition3SourceData.selected_strict_selectedReducedWidths
AoyagiDefinition3SourceData.selectedWidth_le_pred_of_ceilData
AoyagiDefinition3SourceData.htildeLowerNat_add_one_labelBounds_of_ceilData
AoyagiDefinition3SourceData.lemma5Eq4_localData_of_ceilData
AoyagiDefinition3SourceData.lemma5Eq5_labelBounds_of_ceilData
AoyagiDefinition3SourceData.lemma5Eq3_localData_of_ceilData_and_slack
AoyagiDefinition3SourceData.exists_selectedReducedWidthCeilData_of_rankWidth
```

The final theorem is a finite provenance aggregator: with supplied Definition
3 source data and an explicit source-range rank-width hypothesis, it packages
the selected reduced-width family, the ceiling datum, Nat-width rewrites,
nonnegativity, strict selected inequality, selected-width upper bound, and
Nat-indexed selected-width nonnegativity.

Boundary: selected cutpoints, source data, and rank-width hypotheses remain
supplied.  This does not prove selected cutpoint existence, nonselected
inequalities from dimensions, Lemma 5 coverage/no-extra exactness,
normal-crossing chart production, pole order, or RLCT.

## Current slice - 2026-06-23, Definition 3 source-data final-boundary handoff

Reproduction:
`reproduction-definition3-source-data-final-boundary-a6.md`.
Statement card:
`statement-card-a6-definition3-source-data-final-boundary.md`.
Review artifact:
`review-definition3-source-data-final-boundary-a6.md`.

Lean now uses the Definition 3 source-data provenance aggregator to
existentially produce the selected-width family and ceiling datum needed by
the final-boundary structures:

```text
AoyagiDefinition3SourceData.exists_theorem2SuppliedFinalBoundary_of_rankWidth
AoyagiDefinition3SourceData.exists_theorem2SuppliedChartFinalBoundary_of_rankWidth
```

The theorems package the produced `m,data` into
`AoyagiTheorem2SuppliedFinalBoundary` or
`AoyagiTheorem2SuppliedChartFinalBoundary`, returning the same selected-width
provenance facts as the source-data aggregator.

Boundary: selected cutpoints, source data, source-range rank-width, A0
extraction, and finite exponent formula hypotheses for the produced data
remain supplied.  This does not prove active-ratio lower bounds, chart-count
facts, chart production, pole order, or RLCT.

## Current slice - 2026-06-23, Case 1 to Theorem 2 finite formula

Reproduction:
`reproduction-case1-theorem2-finite-formula-bridge-a6.md`.
Statement card:
`statement-card-a6-case1-theorem2-finite-formula-bridge.md`.
Review artifact:
`review-case1-theorem2-finite-formula-bridge-a6.md`.

Lean now has a leaf bridge module:

```text
DLNFibre.DLN.Aoyagi.Case1Theorem2FiniteExponentBridge
```

with candidate ratio

```text
Case1SelectedOldUnitA0ExponentCoordinateBridge.theorem2CandidateRatio
```

and finite-formula wrappers:

```text
Case1SelectedOldUnitA0ExponentCoordinateBridge.theorem2FiniteExponentFormulaHypothesis_of_forall_le_of_candidateRatio_eq_fromCeilData
Case1SelectedOldUnitA0ExponentCoordinateBridge.theorem2FiniteExponentFormulaHypothesis_of_forall_le_of_candidateRatio_eq_fromCeilData_of_countInChartAtRatio_eq_of_forall_le
```

They build `AoyagiTheorem2FiniteExponentFormulaHypothesis` from the supplied
selected-old Case 1/A0 coordinate bridge, an explicit active-ratio lower
bound, a supplied equality identifying the Case 1 candidate ratio with
Theorem 2's displayed lambda formula, and either a supplied order equality or
supplied chart-count facts at the Case 1 candidate ratio.

Boundary: finite composition only.  It does not prove the lower bound, lambda
identification, order equality, chart-count facts, selected-width provenance,
chart production, analytic extraction, pole order, or RLCT.

## Current slice - 2026-06-23, Case 1 chart-final boundary

Reproduction:
`reproduction-case1-theorem2-chart-final-bridge-a6.md`.
Statement card:
`statement-card-a6-case1-theorem2-chart-final-bridge.md`.
Review artifact:
`review-case1-theorem2-chart-final-bridge-a6.md`.

Lean now has a leaf chart-final wrapper:

```text
Case1SelectedOldUnitA0ExponentCoordinateBridge.theorem2SuppliedChartFinalBoundary_of_forall_le_of_candidateRatio_eq_fromCeilData_of_countInChartAtRatio_eq_of_forall_le
```

It carries the selected-old Case 1 ratio-count finite formula bridge into
`AoyagiTheorem2SuppliedChartFinalBoundary` once selected-width provenance and
the chart-level A0 extraction hypothesis are supplied.

Boundary: this is API plumbing only.  It does not construct charts, prove
coverage, prove finite count facts, prove selected-width provenance, prove
analytic extraction, pole order, or RLCT.
