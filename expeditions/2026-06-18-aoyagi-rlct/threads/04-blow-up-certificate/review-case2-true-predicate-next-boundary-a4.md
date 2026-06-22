# Review - Case 2 true-predicate next boundary

Date: 2026-06-22.

Reviewer: xhigh API/source reviewer `Poincare the 2nd`, with Lean API scout
`Zeno the 2nd` agreeing on the formal shape.

## Verdict

Pass after naming fix.

## Findings

The original draft name

```text
SourceProductionObligation.of_formulaSuccessor_transportTerminalRows_trivialNextChartFamily
```

was too easy to read as saying that a trivial next chart family had been
constructed.  The proof only fills an existential boundary with `True`
predicates.  The theorem was renamed to

```text
SourceProductionObligation.of_formulaSuccessor_transportTerminalRows_truePredicateNextBoundary
```

and the exact-boundary helper

```text
Case2ResidualBlockChartFamilyBoundary.continuingSuccessorBoundary_exists_truePredicates
```

was added.  The docs now use "true-predicate next boundary" rather than
"trivial next chart family" in theorem-facing prose.

## Soundness

The Lean statements are sound for the current API.  `SelectedEntryChartFamilyBoundary`
only asks for implications into existentially chosen predicates, so choosing
`True` for both chart and transition regularity proves the existential
boundary.  This is vacuous in the intended geometric sense, but honest as a
statement about the current type.

## Source Fidelity

The source check of Aoyagi pp. 19-22 found the displayed Case 2 `Q/P`
calculation followed by the sentence that the induction continues.  It did not
find construction of a successor affine atlas, chart coverage, transition
regularity, successor source data, or suffix production.  The reproduction and
statement card state this boundary explicitly.

## Residual Risk

Downstream users could still misuse the `exists_trivial` lemmas as chart
production if they ignore the names and docstrings.  Any later theorem that
needs real geometric regularity should strengthen the boundary to fixed
intended predicates or concrete chart data before using it.
