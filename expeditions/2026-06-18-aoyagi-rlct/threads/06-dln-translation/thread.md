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
