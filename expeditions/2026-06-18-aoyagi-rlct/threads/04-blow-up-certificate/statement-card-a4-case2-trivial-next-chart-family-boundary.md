# Statement Card - A4 Case 2 True-Predicate Next Boundary

## Lean Names

- `DLNFibre.DLN.Aoyagi.SelectedEntryChartFamilyBoundary.exists_trivial`
- `DLNFibre.DLN.Aoyagi.Case2ResidualBlockChartFamilyBoundary.exists_trivial`
- `DLNFibre.DLN.Aoyagi.Case2ResidualBlockChartFamilyBoundary.continuingSuccessorBoundary_exists_truePredicates`

## Claim

The historical existential next chart-family boundary was formally inhabited
by choosing trivial regularity predicates.  This showed that the field did not
encode source production, and the field has since been removed from
`SourceProductionObligation`.

## Inputs

The same inputs as the canonical formula-level constructor:

- a displayed supplied Case 2 chart-family boundary `data`;
- residual source coordinates;
- source following factor `C`;
- source suffix factors `Ctail`;
- suffix layer bound `S+1 <= L`.

No source-produced next chart-family data was used: the audit filled the
existential with `True` predicates.

## Output

Historically, the audit produced a `SourceProductionObligation` with

```text
Csucc = case2DisplayedSourceSuccessorFollowingFactor ...
Cterm = case2DisplayedSourceTerminalTransportedRows ...
```

In the superseded API, the removed field was inhabited by
`Case2ResidualBlockChartFamilyBoundary.continuingSuccessorBoundary_exists_truePredicates`.
The live API no longer has that field or the true-predicate constructor wrapper.

## Nonclaims

This is not a geometric chart-family theorem.  It does not construct an affine
blow-up atlas, prove meaningful chart or transition regularity, source-produce
`Csucc`, produce suffixes, prove coverage, derive corrected post-data, prove
normal crossings, pole order, termination, or RLCT.

## Review

Passed after naming fix:
`review-case2-true-predicate-next-boundary-a4.md`.
