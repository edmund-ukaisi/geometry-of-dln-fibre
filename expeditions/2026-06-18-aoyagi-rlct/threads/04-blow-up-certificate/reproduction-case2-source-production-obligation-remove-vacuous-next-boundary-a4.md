# Reproduction - Case 2 source-production obligation removes vacuous next boundary

Date: 2026-06-22.

Status: API hardening after source/API audit.  This is not chart/source
production.

## Source Anchor

Aoyagi PDF pp. 19-22 constructs the displayed Case 2 selected pivot chart,
defines `Q`, `P`, and `C'_J^(S+1)=Q^-1 C_J^(S+1)`, and then says that in the
continuing branch the inductive statement holds with `J` increased by one.
The source does not construct a successor atlas, transition regularity data,
coverage, a source-produced full successor `C'^(S+1)`, or a source-produced
suffix.

The previous Lean interface

```text
SourceProductionObligation
```

included a field

```text
continuing_suppliedNextChartFamily :
  forall hnext, exists ChartRegularNext TransitionRegularNext,
    Case2ResidualBlockChartFamilyBoundary n S (J+1)
      ChartRegularNext TransitionRegularNext
```

but the follow-up API audit proved this existential is always inhabited by
choosing both predicates to be `True`.  Therefore it did not encode any real
Aoyagi source-production datum.

## Change

Remove the `continuing_suppliedNextChartFamily` field from
`SourceProductionObligation`.

Add the canonical formula-level constructor

```text
SourceProductionObligation.of_formulaSuccessor_transportTerminalRows
```

which chooses

```text
Csucc = case2DisplayedSourceSuccessorFollowingFactor ...
Cterm = case2DisplayedSourceTerminalTransportedRows ...
```

and fills only the remaining meaningful finite payload fields:

- formula equality for `Csucc`;
- continuing weighted successor-following frontier under `hnext`;
- actual-width stopped source-suffix payload and relabelled certificates;
- row-exhausted transported-prefix source-suffix payload.

The old names

```text
SourceProductionObligation.of_formulaSuccessor_transportTerminalRows_suppliedNextChartFamily
SourceProductionObligation.of_formulaSuccessor_transportTerminalRows_truePredicateNextBoundary
```

were removed from the current Lean API rather than retained as compatibility
wrappers with ignored arguments.  Their supplied/true-predicate
next-boundary data is no longer part of the obligation.

## Interpretation

This is a bedrock correction: the obligation no longer records a vacuous field
as if it were source-production data.  The hard A4 frontier is unchanged:
source production of the successor following object or full following product,
suffix production/inheritance, meaningful chart coverage and transition
regularity, coordinate derivation of corrected post-data, Jacobian arithmetic,
normal crossings, pole order, termination, and RLCT remain open.

## Nonclaims

This change does not prove Aoyagi's continuing induction theorem.  It does not
construct an affine blow-up atlas, prove coverage, prove transition
regularity, source-produce `Csucc` or `C'^(S+1)`, produce suffix factors,
derive corrected post-data from coordinates, prove normal crossings, prove
pole order, or compute RLCT.

## Kill Conditions

- Do not treat removal of the vacuous field as progress on chart production.
- Do not reintroduce compatibility wrappers with ignored next-boundary
  arguments as evidence for a source-produced next chart family.
- If a later theorem needs geometric chart regularity, introduce fixed
  intended predicates or concrete chart data rather than an existential over
  arbitrary predicates.
