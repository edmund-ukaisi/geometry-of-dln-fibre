# Statement card - A4 Case 2 source-production obligation canonical formula

## Lean Artifact

File:

- `lean/DLNFibre/DLN/Aoyagi/BlowupArithmetic.lean`

Name:

- `DLNFibre.DLN.Aoyagi.Case2DisplayedSuppliedChartFamilyBoundary.SourceProductionObligation.of_formulaSuccessor_transportTerminalRows_suppliedNextChartFamily`

## Statement

Given a displayed Case 2 supplied boundary and an explicitly supplied
continuing next chart-family boundary, the canonical formula-level successor
factor and transported terminal-row matrix satisfy the supplied
`SourceProductionObligation` interface.

## Proved

The theorem chooses
`Csucc = case2DisplayedSourceSuccessorFollowingFactor ... C` and
`Cterm = case2DisplayedSourceTerminalTransportedRows ... C`.  The existing
frontier package supplies the branch payloads; the supplied next chart-family
field supplies the remaining continuing chart-family obligation.  Actual-width
terminal original-row equality first uses that transported rows are original
rows of the formula-level successor factor, then uses actual-width collapse of
that factor to the old source factor.  Row-exhausted terminal transported-row
equality is reflexive.

## Assumed

The displayed supplied boundary, source following factor and source suffix
data, and the continuing next chart-family boundary at `(S,J+1)` under
`J+2 <= prefixMinNat n (S+1)`.

## Cited

None.  This is finite interface assembly.

## Deferred

Constructing the continuing next chart-family boundary, source production of
the successor object from chart coordinates, suffix production, chart coverage,
transition regularity, coordinate derivation of corrected post-data, Jacobian
arithmetic, normal crossings, pole order, termination, and RLCT extraction.

## Review

Xhigh reviewer Huygens the 2nd passed the slice after two documentation
precision fixes: the theorem gives a canonical inhabitant for specific
formula-level choices rather than changing the general interface, and the
actual-width row argument has a two-step transported-row then collapse proof.

## Verification

Focused Lean, aggregate build, sorry scan, and diff check pass:

```text
cd lean && lake env lean DLNFibre/DLN/Aoyagi/BlowupArithmetic.lean
cd lean && lake build DLNFibre
cd lean && scripts/sorries
git diff --check
```

`scripts/sorries` reports `0 sorry`, `0 #exit`, `0 native_decide`, and
`0 axiom`.  The full build reports only pre-existing Core warnings.
