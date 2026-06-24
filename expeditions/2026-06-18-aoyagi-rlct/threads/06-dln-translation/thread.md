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

## 2026-06-24 source audit - Definition 3 branch selection

Independent source auditor `Einstein the 3rd` checked Aoyagi Definition 3 and
Theorem 2 on PDF pp. 8-9 after the `(2,3,3)` and `(1,2,2)` overlap
diagnostics.  The audit is saved at
`source-audit-definition3-branch-selection-a6.md`.

Verdict: no source-backed tie-breaker is printed.  Definition 3 uses
value-level membership in the selected value set, and Theorem 2 computes from
the already chosen `ell,S_j`; pp. 8-9 do not impose minimal `ell`, maximal
`ell`, all-source selection, distinct selected values, or any canonical branch.
The equal-width example uses `ell=L`, so distinct-value/minimal-`ell`
conventions are not source-backed.

Controller consequence: keep selected source data supplied, or work in a
source-produced branch.  Do not state branch-independent finite lambda/order
payloads for arbitrary Definition 3 source-data choices unless a new source
convention is found.

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

## Current slice - 2026-06-24, Definition 3 terminal counted-datum classifier final bridge

The Definition 3 source-data handoff now has terminal counted-datum classifier
variants in `lean/DLNFibre/DLN/Aoyagi/Theorem2TerminalOrderBridge.lean`:

```text
AoyagiDefinition3SourceData.exists_theorem2SuppliedFinalBoundary_of_rankWidth_activePair_ratioCount_terminalMinimumCountDatumClassifier
AoyagiDefinition3SourceData.exists_theorem2SuppliedChartFinalBoundary_of_rankWidth_activePair_ratioCount_terminalMinimumCountDatumClassifier
```

These first use Definition 3 source data plus the explicit source-range
rank-width hypothesis to produce the selected reduced-width family and ceiling
datum.  For that produced `m,data`, a supplied terminal counted-datum
classifier, supplied branch-label injectivity, supplied active-ratio
certificate, supplied displayed-ratio chart-count certificate, and the A0
extraction hypothesis build the supplied final boundary.  The chart theorem is
the same handoff for `AoyagiTheorem2SuppliedChartFinalBoundary`.

Artifacts:

- `reproduction-definition3-terminal-countdatum-classifier-final-bridge-a6.md`;
- `statement-card-a6-definition3-terminal-countdatum-classifier-final-bridge.md`;
- `review-definition3-terminal-countdatum-classifier-final-bridge-a6.md`.

Boundary: this is finite source-data/final-socket plumbing only.  It does not
construct the counted-datum classifier, prove branch-label injectivity, prove
Eq3/Eq4/Eq5 families, prove active-ratio or chart-count facts, construct
normal-crossing charts, prove pole order without A0, or extract RLCT.

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

## Current slice - 2026-06-23, terminal-order equality bridge

Reproduction:
`reproduction-theorem2-terminal-order-equality-bridge-a6.md`.
Statement card:
`statement-card-a6-theorem2-terminal-order-equality-bridge.md`.
Review artifact:
`review-theorem2-terminal-order-equality-bridge-a6.md`.

Lean now has a terminal-order equality bridge:

```text
DLNFibre.DLN.Aoyagi.Theorem2TerminalOrderEqualityBridge
```

It accepts the exact count

```text
TC.terminalMinimumLabels.card = data.theorem2OrderFormula
```

as a first-class A6 input.  The finite formula wrappers compose this equality
with supplied equalities or finite certificates proving
`D.exponentOrder = TC.terminalMinimumLabels.card`.  The final-boundary and
chart-final wrappers then add the already explicit selected-width provenance
and A0 extraction hypotheses.

Boundary: the exact terminal count remains supplied to this module.  It does
not construct Eq5 branches, prove A5 classifier/injectivity/back-to-label
data, prove source-backed no-extra coverage, produce normal-crossing charts,
prove active-ratio lower bounds, prove chart-count facts, identify pole order
without A0, or extract RLCT.

## Current slice - 2026-06-23, Eq5 terminal-order bridge

Reproduction:
`reproduction-theorem2-eq5-terminal-order-bridge-a6.md`.
Statement card:
`statement-card-a6-theorem2-eq5-terminal-order-bridge.md`.
Review artifact:
`review-theorem2-eq5-terminal-order-bridge-a6.md`.

Lean now has

```text
DLNFibre.DLN.Aoyagi.Theorem2Eq5TerminalOrderBridge
```

with the supplied payload

```text
AoyagiLemma5SuppliedEq5EndpointBlockWidthOrderPayload
```

and displayed-ratio finite/final/chart-final wrappers ending in
`suppliedEq5EndpointBlockWidthPayload`.  The payload packages the large Eq5
endpoint block-width hypotheses, extracts

```text
TC.terminalMinimumLabels.card = data.theorem2OrderFormula,
```

and feeds that equality into the existing exact-count A6 sockets.  The
final-boundary wrappers use the same selected cutpoints `P.cut` carried by the
supplied Eq5 payload.

Boundary: supplied-boundary composition only.  This does not construct Eq5
endpoint families, prove source-backed Lemma 5 exactness, produce charts,
prove active-ratio lower bounds, prove displayed-ratio chart-count facts,
identify pole order without A0, or extract RLCT.

## Current slice - 2026-06-23, Definition 3 source-data Eq5 terminal-order bridge

Reproduction:
`reproduction-definition3-source-data-eq5-terminal-order-bridge-a6.md`.
Statement card:
`statement-card-a6-definition3-source-data-eq5-terminal-order-bridge.md`.
Review artifact:
`review-definition3-source-data-eq5-terminal-order-bridge-a6.md`.

Lean now has source-data wrappers in
`DLNFibre.DLN.Aoyagi.Theorem2Eq5TerminalOrderBridge`:

```text
AoyagiDefinition3SourceData.exists_theorem2SuppliedFinalBoundary_of_rankWidth_activePair_ratioCount_suppliedEq5EndpointBlockWidthPayload
AoyagiDefinition3SourceData.exists_theorem2SuppliedChartFinalBoundary_of_rankWidth_activePair_ratioCount_suppliedEq5EndpointBlockWidthPayload
```

They use Definition 3 source data and a source-range rank-width hypothesis to
existentially produce the selected reduced-width family and ceiling datum, then
invoke a supplied Eq5 endpoint-payload/active-ratio/chart-count callback for
that produced `m,data`.  The callback includes `P.cut = C`, so the Eq5 payload
and Definition 3 source data use the same selected cutpoints.

Boundary: source-facing finite composition only.  This does not construct
selected cutpoints, prove rank-width from matrix data, construct Eq5 endpoint
families, prove Lemma 5 exactness, prove active-ratio lower bounds, prove
displayed-ratio chart-count facts, produce normal-crossing charts, identify
pole order without A0, or extract RLCT.

## Current slice - 2026-06-24, Definition 3 ell=1 nonselected obstruction

Reproduction:
`reproduction-definition3-ell-one-nonselected-obstruction-a6.md`.
Statement card:
`statement-card-a6-definition3-ell-one-nonselected-obstruction.md`.
Review artifact:
`review-definition3-ell-one-nonselected-obstruction-a6.md`.

Lean now has:

```text
AoyagiDefinition3SourceData.reducedWidth_mem_selectedValueSet_of_ell_eq_one_rankWidth
```

Under `S : AoyagiDefinition3SourceData L 1 H r C` and explicit source-range
rank-width nonnegativity, every source-range reduced-width value lies in the
two selected values.  The proof isolates the general `ell=1` mechanism from
the `1,2,100` diagnostic: the printed nonselected upper inequality has
coefficient `ell-1=0`, forcing the selected sum to vanish, which contradicts
the strict selected inequality and selected nonnegativity.

Boundary: necessary condition only.  This does not construct selected
cutpoints, classify `ell>1`, repair Definition 3, construct Eq5 families,
prove Lemma 5 exactness, produce charts, identify pole order, or extract RLCT.

## Current slice - 2026-06-24, Definition 3 equal-width source data

Reproduction:
`reproduction-definition3-equal-width-source-data-a6.md`.
Statement card:
`statement-card-a6-definition3-equal-width-source-data.md`.
Review artifact:
`review-definition3-equal-width-source-data-a6.md`.

Lean now has:

```text
AoyagiDefinition3SourceData.exists_consecutive_of_constant_reducedWidth_pos
```

If `0 < L`, `0 < w`, and every source-range reduced width
`aoyagiReducedWidthInt H r s` for `1 <= s <= L+1` equals `w`, then there are
consecutive selected cutpoints `C.cut j = j.val+1` and
`AoyagiDefinition3SourceData L L H r C`.  This formalizes Aoyagi's
equal-width example with `ell = L`.  The strict selected inequality is
`L*w < (L+1)*w`; the nonselected fields are vacuous because the Lean structure
uses value-level selected-width membership and every source-range width value
is the selected value `w`.

Boundary: equal-width source-data constructor only.  This is not arbitrary
selected-cutpoint existence, not an `ell>1` classification, not a repair of
Definition 3's printed inequalities, not Eq5 construction or Lemma 5
exactness, and not chart production, normal crossings, pole order, or RLCT.

## Current slice - 2026-06-24, Definition 3 equal-width ceiling data

Reproduction:
`reproduction-definition3-equal-width-ceil-data-a6.md`.
Statement card:
`statement-card-a6-definition3-equal-width-ceil-data.md`.
Review artifact:
`review-definition3-equal-width-ceil-data-a6.md`.

Lean now has:

```text
AoyagiDefinition3SourceData.sourceRangeRankWidth_of_constant_reducedWidth
AoyagiDefinition3SourceData.exists_consecutive_selectedReducedWidthCeilData_of_constant_reducedWidth_pos
```

The helper proves that if `aoyagiReducedWidthInt H r s = (w : Int)` on the
source range, then `r <= H s` there.  The package theorem combines this helper
with the equal-width consecutive source-data constructor and the existing
`exists_selectedReducedWidthCeilData_of_rankWidth` theorem.  It produces
consecutive cutpoints, equal-width source data, selected reduced widths, a
Definition 3 ceiling datum, the Nat-width rewrites, nonnegativity, strict
selected inequalities, selected-width upper bounds, and `m j = w`.

Boundary: mostly packaging plus the rank-width arithmetic consequence.  It
does not compute `ceilWidth` or `aParam`, prove arbitrary Definition 3 source
data, construct Eq5 payloads, prove finite exponent formulas, produce charts,
identify pole order, or extract RLCT.

## Current slice - 2026-06-24, Definition 3 equal-width explicit ceiling data

Reproduction:
`reproduction-definition3-equal-width-explicit-ceil-data-a6.md`.
Statement card:
`statement-card-a6-definition3-equal-width-explicit-ceil-data.md`.
Review artifact:
`review-definition3-equal-width-explicit-ceil-data-a6.md`.

Lean now has:

```text
AoyagiDefinition3CeilData.equalWidthOfDecomposition
AoyagiDefinition3SourceData.exists_consecutive_explicitCeilData_of_constant_reducedWidth_decomposition
```

The first constructor is the finite arithmetic from Aoyagi's equal-width
example: for `w = L*q + a` with `0 < a <= L`, the constant selected-width
family has `ceilWidth = w + q + 1` and `aParam = a`.  The source-facing theorem
combines this explicit datum with the equal-width consecutive source-data
constructor, returning the selected reduced-width package with explicit
`ceilWidth` and `aParam` fields.

Boundary: equal-width finite arithmetic only.  This does not prove arbitrary
Definition 3 source-data existence, uniqueness of the ceiling datum, existence
of the positive-remainder decomposition for every `L,w`, Eq5 payloads, finite
exponent formulas, chart production, normal crossings, pole order, or RLCT.

## Current slice - 2026-06-24, Definition 3 all-source selected source data

Reproduction:
`reproduction-definition3-all-source-selected-source-data-a6.md`.
Statement card:
`statement-card-a6-definition3-all-source-selected-source-data.md`.
Review artifact:
`review-definition3-all-source-selected-source-data-a6.md`.

Lean now has:

```text
AoyagiDefinition3SourceData.exists_consecutive_of_all_selected_strict
```

It chooses consecutive cutpoints `C.cut j = j.val+1` and proves
`AoyagiDefinition3SourceData L L H r C` from the strict all-source selected
inequality

```text
(L : Int) * M^(s) < sum_j M^(j.val+1)
```

for every source-range `s`.  This removes the constant-width assumption from
the equal-width source-data lane.  The nonselected clauses are vacuous because
every source-range reduced-width value belongs to the selected value image.

Boundary: restricted source-data constructor only.  It does not prove
arbitrary selected-cutpoint existence, classify Definition 3, produce a
ceiling datum, construct Eq5 payloads, produce charts, identify pole order, or
extract RLCT.

## Current slice - 2026-06-24, Definition 3 all-source selected ceiling data

Reproduction:
`reproduction-definition3-all-source-ceil-data-a6.md`.
Statement card:
`statement-card-a6-definition3-all-source-ceil-data.md`.
Review artifact:
`review-definition3-all-source-ceil-data-a6.md`.

Lean now has:

```text
AoyagiDefinition3SourceData.exists_consecutive_selectedReducedWidthCeilData_of_all_selected_strict_rankWidth
```

It combines the all-source selected source-data constructor with the existing
rank-width selected reduced-width ceiling-data package.  Under source-range
rank-width and the strict all-source selected inequality, consecutive
cutpoints produce `S : AoyagiDefinition3SourceData L L H r C`, selected
reduced widths `m`, and a Definition 3 ceiling datum `data`, with the Nat-width
rewrites, nonnegativity, strict selected inequalities, selected upper bounds,
and Nat selected-width nonnegativity already used by later A6 sockets.

Boundary: provenance packaging only.  Rank-width remains explicit.  There is
no closed-form `ceilWidth`/`aParam`, arbitrary selected-cutpoint existence,
Definition 3 classification, Eq5 construction, chart production, pole order,
or RLCT extraction.

## Current slice - 2026-06-24, Definition 3 all-source source-rank ceiling data

Reproduction:
`reproduction-definition3-all-source-source-rank-ceil-data-a6.md`.
Statement card:
`statement-card-a6-definition3-all-source-source-rank-ceil-data.md`.
Review artifact:
`review-definition3-all-source-source-rank-ceil-data-a6.md`.

Lean now has:

```text
AoyagiDefinition3SourceData.exists_consecutive_selectedReducedWidthCeilData_of_all_selected_strict_sourceRankStratum
```

It is the source-rank-stratum version of the all-source ceiling-data package.
The theorem derives source-range rank-width from
`paperEndpointFixedBaseSourceRankStratum` and the dimension convention
`H(k.val+1)=finrank(W k)`, then invokes the all-source strict/rank-width
package.  The strict all-source selected inequality remains explicit.

Boundary: one source-rank provenance wrapper only.  Do not clone it into
final-socket variants without a downstream consumer.  It does not prove the
strict inequality, exact-rank openness, chart coverage, closed-form ceiling
data, Eq5 payloads, finite exponent formulas, pole order, or RLCT.

## Current slice - 2026-06-24, Definition 3 nonconstant `(1,2,2)` example

Reproduction:
`reproduction-definition3-nonconstant-one-two-two-example-a6.md`.
Statement card:
`statement-card-a6-definition3-nonconstant-one-two-two-example.md`.
Review artifact:
`review-definition3-nonconstant-one-two-two-example-a6.md`.

Lean now has:

```text
AoyagiDefinition3SourceData.exists_consecutive_nonconstant_widths_one_two_two_selectedReducedWidthCeilData
```

It proves that for `L=2`, `r=0`, and source-range reduced widths `(1,2,2)`,
consecutive all-source cutpoints produce Definition 3 source data, selected
reduced widths, and a Definition 3 ceiling datum.  The returned selected-width
family has `m 0 = 1`, `m 1 = 2`, `m 2 = 2`, so `m 0 != m 1`.  This witnesses
that the all-source selected constructor is broader than the equal-width lane
while complementing the existing negative `(1,2,100)` guardrail.

Boundary: diagnostic/example theorem only.  It does not prove arbitrary
source-data existence, classify Definition 3, prove uniqueness of cutpoints or
ceiling data, compute closed-form `ceilWidth`/`aParam`, construct Eq5
payloads, produce charts, identify pole order, or extract RLCT.

## Current slice - 2026-06-24, Definition 3 three-width triangle constructor

Reproduction:
`reproduction-definition3-three-width-triangle-a6.md`.
Statement card:
`statement-card-a6-definition3-three-width-triangle.md`.
Review artifact:
`review-definition3-three-width-triangle-a6.md`.

Lean now has:

```text
AoyagiDefinition3SourceData.exists_consecutive_three_widths_selectedReducedWidthCeilData_of_triangle_rankWidth
```

For `L=2`, if the three source-range reduced widths are `w1,w2,w3` and the
three strict triangle inequalities `2*w_i < w1+w2+w3` hold, consecutive
all-source cutpoints produce Definition 3 source data, selected reduced widths,
and a Definition 3 ceiling datum under the explicit source-range rank-width
hypothesis.  The theorem also returns `m 0=w1`, `m 1=w2`, and `m 2=w3`.

Boundary: small all-source constructor only.  It generalises the `(1,2,2)`
example, but it does not prove arbitrary selected-cutpoint/source-data
existence, classify Definition 3 profiles, compute closed-form ceiling data,
construct Eq5 payloads, produce charts, identify pole order, or extract RLCT.

## Current slice - 2026-06-24, Definition 3 `L=2` pairwise-distinct classification

Reproduction:
`reproduction-definition3-l-eq-two-pairwise-distinct-classification-a6.md`.
Statement card:
`statement-card-a6-definition3-l-eq-two-pairwise-distinct-classification.md`.
Review artifact:
`review-definition3-l-eq-two-pairwise-distinct-classification-a6.md`.

Lean now has:

```text
AoyagiDefinition3SourceData.ell_eq_two_of_L_eq_two_rankWidth_pairwiseDistinct
AoyagiDefinition3SourceData.cut_eq_consecutive_of_L_eq_two
AoyagiDefinition3SourceData.exists_sourceData_iff_allSourceStrict_of_L_eq_two_rankWidth_pairwiseDistinct
```

For `L=2`, source-range rank-width and pairwise distinct source-range reduced
widths force any Definition 3 source-data witness to have `ell=2` and
consecutive cutpoints.  Therefore source-data existence is equivalent to the
all-source strict selected inequalities.

Boundary: finite Definition 3 structure only.  It does not classify
repeated-width profiles, compute closed-form ceiling data, construct Eq5
payloads, produce charts, identify pole order, or extract RLCT.

## Current slice - 2026-06-24, Theorem 2 source-rank regular-shift bridge

Reproduction:
`reproduction-theorem2-source-rank-regular-shift-bridge-a6.md`.
Statement card:
`statement-card-a6-theorem2-source-rank-regular-shift-bridge.md`.
Review artifact:
`review-theorem2-source-rank-regular-shift-bridge-a6.md`.

Lean now has:

```text
AoyagiDefinition3SourceData.exists_theorem2SuppliedFinalBoundary_of_sourceRankStratum_regularVariableCountShift
AoyagiDefinition3SourceData.exists_theorem2SuppliedChartFinalBoundary_of_sourceRankStratum_regularVariableCountShift
```

These compose Definition 3 source data, A2 source-rank-stratum rank-width
provenance, and the finite regular-variable shift into the existing supplied
final sockets for the shifted exponent datum or shifted chart certificate.  The
extraction hypothesis is explicitly for the shifted object, and the reduced
minimum-plus-regular-term and reduced order obligations remain supplied.

Boundary: source-facing final-socket composition only.  This is not
regular-suspension construction, analytic ideal transport, Aoyagi Lemma 1,
exact-rank openness, normal-crossing chart production, active-ratio/chart-count
proof, pole order, or RLCT.

## Current slice - 2026-06-24, Theorem 2 rank-width regular-shift bridge

Reproduction:
`reproduction-theorem2-rank-width-regular-shift-bridge-a6.md`.
Statement card:
`statement-card-a6-theorem2-rank-width-regular-shift-bridge.md`.
Review artifact:
`review-theorem2-rank-width-regular-shift-bridge-a6.md`.

Lean now has a rank-width-level bridge in
`DLNFibre.DLN.Aoyagi.Theorem2RankWidthRegularShiftBridge`:

```text
AoyagiDefinition3SourceData.exists_theorem2SuppliedFinalBoundary_of_rankWidth_regularVariableCountShift
AoyagiDefinition3SourceData.exists_theorem2SuppliedChartFinalBoundary_of_rankWidth_regularVariableCountShift
```

This is the actual source-hypothesis reduction under the previous source-rank
regular-shift wrapper.  It takes Definition 3 source data and source-range
rank-width `hr` directly, uses `hr` both for selected-width side facts and for
the endpoint bounds in the finite regular-variable shift, and keeps the
shifted extraction hypothesis plus reduced minimum/order obligations supplied.

`Theorem2SourceRankRegularShiftBridge.lean` now derives `hr` from the A2
source-rank stratum and delegates to this rank-width bridge.

Boundary: finite/final-socket composition only.  This does not construct
regular-suspension charts, analytic ideal transport, Aoyagi Lemma 1,
normal-crossing charts, active-ratio lower bounds, chart-count facts, pole
order, or RLCT.

## 2026-06-24 Theorem 2 supplied regular-suspension final bridge

The regular-variable final handoff is now being restated through the supplied
full-certificate boundary rather than the synthetic shifted certificate.  The
source-data/rank-width layer produces `m,data` as before.  The supplied
regular-suspension certificate then gives the existing chart-final socket for
`Cfull` exactly, with extraction applied to `Cfull`.

Lean now has:

```text
AoyagiDefinition3SourceData.exists_theorem2SuppliedChartFinalBoundary_of_rankWidth_suppliedRegularSuspension
AoyagiDefinition3SourceData.exists_theorem2SuppliedChartFinalBoundary_of_sourceRankStratum_suppliedRegularSuspension
```

Artifacts:
`reproduction-theorem2-regular-suspension-final-bridge-a6.md` and
`statement-card-a6-theorem2-regular-suspension-final-bridge.md`.
Review artifact:
`review-theorem2-regular-suspension-final-bridge-a6.md`.

Boundary: chart-level final-socket composition only.  It does not construct
`Cfull`, prove the abstract regular-suspension predicates, analytic ideal
transport, Aoyagi Lemma 1, regular-coordinate additivity, normal-crossing
charts, active-ratio lower bounds, chart-count facts, pole order, or RLCT
beyond the supplied extraction hypothesis for `Cfull`.

## Current slice - 2026-06-24, Definition 3 positive-remainder ceiling data

Reproduction:
`reproduction-definition3-positive-remainder-ceil-data-a6.md`.
Statement card:
`statement-card-a6-definition3-positive-remainder-ceil-data.md`.
Review artifact:
`review-definition3-positive-remainder-ceil-data-a6.md`.

Lean now has:

```text
AoyagiDefinition3CeilData.ofSelectedSumPositiveRemainder
```

This pure finite-arithmetic constructor turns a supplied positive-remainder
decomposition

```text
sum_j m_j = ell * ceilPred + a,        0 < a <= ell
```

into `AoyagiDefinition3CeilData ell m` with
`ceilWidth = ceilPred + 1` and `aParam = a`.  It is the general version of the
ceiling/residue arithmetic behind Definition 3 and the equal-width explicit
constructor, but it does not add a source-facing wrapper until a downstream
theorem needs the explicit fields.

Boundary: finite ceiling/residue arithmetic only.  This does not prove
uniqueness, automatic quotient/remainder construction, selected-cutpoint
existence, Definition 3 classification, Eq5 payloads, chart production, pole
order, normal crossings, or RLCT.

## Current slice - 2026-06-24, Definition 3 `L=2` repeated-width classification

Reproduction:
`reproduction-definition3-l-eq-two-repeated-width-classification-a6.md`.
Statement card:
`statement-card-a6-definition3-l-eq-two-repeated-width-classification.md`.
Review artifact:
`review-definition3-l-eq-two-repeated-width-classification-a6.md`.

Lean now has:

```text
AoyagiDefinition3SourceData.reducedWidth_mem_selectedValueSet_of_ell_eq_one
AoyagiDefinition3SourceData.of_ell_eq_one_selectedValueSet_covers
AoyagiDefinition3SourceData.exists_ell_one_of_L_eq_two_positive_repeated
AoyagiDefinition3SourceData.exists_sourceData_iff_repeatedPositive_or_triangle_of_L_eq_two
```

For `L=2`, source-data existence is now classified without rank-width
hypotheses.  Either all three reduced-width values are positive and at least
two are equal, in which case an `ell=1` selected value set covers all three
source values, or the three all-source triangle inequalities hold, in which
case `ell=2` and all source layers are selected.  The old rank-width
`ell=1` necessary-condition theorem remains as a compatibility wrapper over
the new rank-width-free theorem.

Boundary: finite Definition 3 source-data structure only.  This does not
classify `L>2`, produce source data from concrete matrices, package ceiling
data, construct Eq5 payloads, produce charts, identify pole order, prove
normal crossings, or extract RLCT.

## Queued candidate - 2026-06-24, `L=2` all-source triangle formula package

An xhigh explorer recommended the next A6 slice after the `L=2`
classification: add an explicit all-source triangle formula package in
`Definition3Bridge.lean`, with a supplied positive-remainder decomposition

```text
w1 + w2 + w3 = 2 * ceilPred + a,    0 < a <= 2.
```

The target should reuse the landed all-source triangle source-data/ceiling
package and `AoyagiDefinition3CeilData.ofSelectedSumPositiveRemainder`, then
project explicit fields such as `ceilWidth = ceilPred + 1`, `aParam = a`, the
order formula `a * (2 - a) + 1`, the selected pair sum
`w1*w2 + w1*w3 + w2*w3`, and the corresponding Theorem 2 lambda expression.

Boundary: rank-width-level finite formula package only.  Do not add a
source-rank or final-socket wrapper without a concrete consumer.  Do not
attempt the repeated-positive `ell=1` branch in this slice; its selected pair
is noncanonical and needs a separate case split.

Outcome: landed and reviewed.  Lean now has

```text
AoyagiDefinition3SourceData.exists_consecutive_three_widths_theorem2Formula_of_triangle_remainder_rankWidth
```

The theorem constructs consecutive all-source cutpoints, explicit
positive-remainder ceiling data, Nat-width/nonnegativity/strictness
provenance, `m=(w1,w2,w3)`, the order formula, the selected pair sum, and the
corresponding finite Theorem 2 lambda expression.  It remains exactly the
all-source triangle branch and proves no source-rank wrapper, final socket,
repeated-positive branch, Eq5 payload, chart construction, pole order, or
RLCT.

Artifacts:
`reproduction-definition3-l-eq-two-triangle-formula-a6.md`,
`statement-card-a6-definition3-l-eq-two-triangle-formula.md`, and
`review-definition3-l-eq-two-triangle-formula-a6.md`.

## Current slice - 2026-06-24, `L=2`, `ell=1` selected-pair formula package

Reproduction:
`reproduction-definition3-l-eq-two-ell-one-selected-pair-formula-a6.md`.
Statement card:
`statement-card-a6-definition3-l-eq-two-ell-one-selected-pair-formula.md`.
Review:
`review-definition3-l-eq-two-ell-one-selected-pair-formula-a6.md`.

Lean now has:

```text
AoyagiDefinition3SourceData.exists_ell_one_selectedPair_theorem2Formula_of_cover_remainder_rankWidth
```

The theorem exposes the selected pair `C : AoyagiSelectedCutpoints 1` and, from
positive selected values, selected-value cover, rank-width, and
`u+v=ceilPred+1`, constructs source data, selected widths, explicit
remainder-one ceiling data, Nat-width/nonnegativity/strictness provenance, the
order formula `1`, the pair sum `u*v`, and the finite Theorem 2 lambda
expression `regularTerm + u*v/2`.

Boundary: finite selected-pair formula packaging only.  It does not choose a
canonical pair from a repeated-width disjunction, add source-rank or final
wrappers, construct Eq5 payloads or charts, prove normal crossings, identify
pole order, or extract RLCT.

## Current slice - 2026-06-24, `ell=1` automatic ceiling and `L=2` repeated-positive formula

Reproductions:
`reproduction-definition3-ell-one-automatic-ceil-formula-a6.md` and
`reproduction-definition3-l-eq-two-repeated-positive-formula-a6.md`.
Statement card:
`statement-card-a6-definition3-l-eq-two-repeated-positive-formula.md`.
Review:
`review-definition3-l-eq-two-repeated-positive-formula-a6.md`.

Lean now has:

```text
AoyagiDefinition3SourceData.exists_ell_one_selectedPair_theorem2Formula_of_cover_rankWidth
AoyagiDefinition3SourceData.exists_ell_one_theorem2Formula_of_L_eq_two_positive_repeated_rankWidth
```

The first theorem removes the unnecessary remainder input from the exposed
`ell=1` selected-pair formula package.  For selected values `u,v`, it constructs
the Definition 3 ceiling datum directly with `ceilWidth = u+v` and `aParam=1`,
then proves order `1`, pair sum `u*v`, and finite lambda
`regularTerm+u*v/2`.

The second theorem uses the positive repeated-width branch for `L=2` to choose
an `ell=1` selected pair by cases: `w1=w2` selects `(1,3)`, while `w1=w3` and
`w2=w3` select `(1,2)`.  It returns the selected cutpoints and values
existentially, so it does not assert a canonical selected pair.

The older
`AoyagiDefinition3SourceData.exists_ell_one_theorem2Formula_of_L_eq_two_positive_repeated_remainder_rankWidth`
remains as a compatibility theorem for callers that already provide a
branch-compatible `ceilPred` equation.

Boundary: finite Definition 3/Theorem 2 formula arithmetic only.  This does not
add a source-rank wrapper or final socket, construct Eq5 payloads or charts,
prove normal crossings, identify pole order, or extract RLCT.

## Current slice - 2026-06-24, general `L`, `ell=1` selected-pair formula

Reproduction:
`reproduction-definition3-ell-one-selected-pair-cover-formula-general-a6.md`.
Statement card:
`statement-card-a6-definition3-ell-one-selected-pair-cover-formula-general.md`.
Review:
`review-definition3-ell-one-selected-pair-cover-formula-general-a6.md`.

Lean now has:

```text
AoyagiDefinition3SourceData.exists_ell_one_selectedPair_theorem2Formula_of_cover_rankWidth_general
```

This lifts the exposed selected-pair formula from `L=2` to arbitrary source
depth `L`.  The theorem keeps the selected pair `C : AoyagiSelectedCutpoints 1`
as input, assumes positive selected values, value-level cover of all
source-range reduced widths, and source-range rank-width, then constructs
Definition 3 source data, selected widths, the direct `ell=1` ceiling datum
`ceilWidth=u+v`, `aParam=1`, Nat-width/nonnegativity/strictness provenance,
order formula `1`, pair sum `u*v`, and finite lambda
`aoyagiTheorem2RegularTerm L H r + u*v/2`.

Boundary: finite selected-pair formula packaging only.  It does not choose a
canonical selected pair, assert branch-independent payloads for arbitrary
Definition 3 source-data choices, add source-rank or final wrappers, construct
Eq5 payloads or charts, prove normal crossings, identify pole order, or
extract RLCT.

## Current slice - 2026-06-24, `ell=1` ceiling-data simplification

Reproduction:
`reproduction-definition3-ell-one-ceil-data-simplification-a6.md`.
Statement card:
`statement-card-a6-definition3-ell-one-ceil-data-simplification.md`.
Review:
`review-definition3-ell-one-ceil-data-simplification-a6.md`.

Lean now has:

```text
AoyagiDefinition3CeilData.aParam_eq_one_of_ell_eq_one
AoyagiDefinition3CeilData.selectedSum_eq_ceilWidth_of_ell_eq_one
AoyagiDefinition3CeilData.ceilWidth_eq_selectedSum_of_ell_eq_one
AoyagiDefinition3CeilData.theorem2OrderFormula_eq_one_of_ell_eq_one
AoyagiDefinition3CeilData.theorem2Lambda_fromCeilData_eq_regularTerm_add_pairSum_half_of_ell_eq_one
AoyagiDefinition3CeilData.theorem2Lambda_fromCeilData_eq_regularTerm_add_selectedPair_half_of_ell_eq_one
```

These are finite arithmetic facts for any supplied
`AoyagiDefinition3CeilData 1 m`: the residue parameter is forced to be `1`,
the selected sum is the ceiling integer, the order formula is `1`, and the
finite lambda formula is the regular term plus half the selected pair sum.  If
`m 0=u` and `m 1=v`, this becomes `regularTerm+u*v/2`.

Boundary: this does not construct selected cutpoints or source data, choose a
branch, add final-socket wrappers, construct Eq5 payloads or charts, prove
normal crossings, identify pole order, or extract RLCT.

## Current slice - 2026-06-24, `L=2` triangle parity formula package

Reproduction:
`reproduction-definition3-l-eq-two-triangle-parity-formula-a6.md`.
Statement card:
`statement-card-a6-definition3-l-eq-two-triangle-parity-formula.md`.
Review:
`review-definition3-l-eq-two-triangle-parity-formula-a6.md`.

Lean now has:

```text
AoyagiDefinition3SourceData.exists_consecutive_three_widths_theorem2Formula_of_triangle_odd_rankWidth
AoyagiDefinition3SourceData.exists_consecutive_three_widths_theorem2Formula_of_triangle_even_rankWidth
```

These are parity refinements of the all-source `L=2`, `ell=2` triangle formula
package.  The odd-total theorem derives the positive-remainder data
`ceilPred=T/2`, `aParam=1`, so `ceilWidth=T/2+1` and order `2`.  The even-total
theorem uses `ceilPred=T/2-1`, `aParam=2`, so `ceilWidth=T/2` and order `1`.
Both retain the all-source cutpoint construction, selected-width provenance,
pair-sum formula, and finite Theorem 2 lambda expression.

Boundary: finite Definition 3/Theorem 2 parity arithmetic only.  This does not
classify `L>2`, choose between repeated-positive and triangle branches, add a
source-rank wrapper or final socket, construct Eq5 payloads or charts, prove
normal crossings, identify pole order, or extract RLCT.

## Current slice - 2026-06-24, `L=2` branch formula disagreement diagnostic

Reproduction:
`reproduction-definition3-l-eq-two-branch-formula-disagreement-a6.md`.
Statement card:
`statement-card-a6-definition3-l-eq-two-branch-formula-disagreement.md`.
Review:
`review-definition3-l-eq-two-branch-formula-disagreement-a6.md`.

Lean now has:

```text
AoyagiDefinition3SourceData.exists_L_eq_two_two_three_three_formula_disagreement
```

This theorem records a concrete overlap diagnostic for the printed Definition
3 conditions as currently formalised.  For `L=2`, `r=0`, and reduced widths
`(2,3,3)`, the `ell=1` repeated-positive branch and the `ell=2` all-source
triangle branch both produce valid source-data packages for the same concrete
`H`.  Their finite Theorem 2 lambda formula values differ:

```text
lambda_ell1 = 3,
lambda_ell2 = 5/2.
```

Both finite order formulas are `1`.  An xhigh scout also checked the general
overlap arithmetic and found that a branch-agreement theorem would be false.

Boundary: finite Definition 3/Theorem 2 formula diagnostics only.  This is not
a correction of Aoyagi's theorem, not an analytic RLCT ambiguity claim, and not
chart production, Eq5 payload construction, normal crossings, pole order, or
RLCT extraction.

## Current slice - 2026-06-24, `L=2` branch order disagreement diagnostic

Reproduction:
`reproduction-definition3-l-eq-two-order-disagreement-a6.md`.
Statement card:
`statement-card-a6-definition3-l-eq-two-order-disagreement.md`.
Review:
`review-definition3-l-eq-two-order-disagreement-a6.md`.

Lean now has:

```text
AoyagiDefinition3SourceData.exists_L_eq_two_one_two_two_order_disagreement
```

For `L=2`, `r=0`, and reduced widths `(1,2,2)`, the `ell=1`
repeated-positive branch and the `ell=2` all-source triangle branch both
produce valid source-data packages for the same concrete `H`.  Their finite
Theorem 2 lambda formula values agree, but their finite order formulas differ:

```text
lambda_ell1 = lambda_ell2 = 1,
order_ell1 = 1,
order_ell2 = 2.
```

Boundary: finite Definition 3/Theorem 2 formula diagnostics only.  This is not
a pole-order theorem, not an analytic RLCT ambiguity claim, and not chart
production, Eq5 payload construction, normal crossings, pole order, or RLCT
extraction.
