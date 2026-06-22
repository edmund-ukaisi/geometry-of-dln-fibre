# Statement Card - A4 Case 2 True-Predicate Next Boundary

## Lean Names

- `DLNFibre.DLN.Aoyagi.SelectedEntryChartFamilyBoundary.exists_trivial`
- `DLNFibre.DLN.Aoyagi.Case2ResidualBlockChartFamilyBoundary.exists_trivial`
- `DLNFibre.DLN.Aoyagi.Case2ResidualBlockChartFamilyBoundary.continuingSuccessorBoundary_exists_truePredicates`

## Claim

The current existential chart-family boundary is formally inhabited by choosing
trivial regularity predicates.  Consequently the canonical formula-level
`SourceProductionObligation` can be constructed without a separately supplied
next-boundary witness.

## Inputs

The same inputs as the canonical formula-level constructor:

- a displayed supplied Case 2 chart-family boundary `data`;
- residual source coordinates;
- source following factor `C`;
- source suffix factors `Ctail`;
- suffix layer bound `S+1 <= L`.

No source-produced next chart-family data is required because the theorem fills
that existential with `True` predicates.

## Output

A `SourceProductionObligation` with

```text
Csucc = case2DisplayedSourceSuccessorFollowingFactor ...
Cterm = case2DisplayedSourceTerminalTransportedRows ...
```

and the continuing next chart-family field filled by
`Case2ResidualBlockChartFamilyBoundary.continuingSuccessorBoundary_exists_truePredicates`.

## Nonclaims

This is not a geometric chart-family theorem.  It does not construct an affine
blow-up atlas, prove meaningful chart or transition regularity, source-produce
`Csucc`, produce suffixes, prove coverage, derive corrected post-data, prove
normal crossings, pole order, termination, or RLCT.

## Review

Passed after naming fix:
`review-case2-true-predicate-next-boundary-a4.md`.
