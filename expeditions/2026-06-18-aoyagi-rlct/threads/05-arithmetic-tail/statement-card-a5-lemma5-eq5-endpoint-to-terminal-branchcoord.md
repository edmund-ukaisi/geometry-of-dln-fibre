# Statement card - A5 Lemma 5 Eq5 endpoint-to-terminal branch coordinates

## Lean Names

- `DLNFibre.DLN.Aoyagi.AoyagiLemma5SuppliedTerminalCandidateFamily.branchCoord_of_toNonbase_eq_eq5EndpointCoverage`
- `DLNFibre.DLN.Aoyagi.AoyagiLemma5SuppliedTerminalCandidateFamily.branchBlock_of_toNonbase_eq_eq5EndpointCoverage_leftEndpoint`

## Claim

If a supplied terminal-candidate family's nonbase supplied family is explicitly
equal to the strictest supplied Eq5 endpoint constructor, then the endpoint
constructor's branch-coordinate correctness transports to the terminal
family's nonbase branch sets.  With the separate supplied left-endpoint
formula for `branchS`, the terminal branch labels lie in the selected block
needed by the existing branch-label injection wrappers.

## Proved

Lean proves the coordinate transport

```text
branchCoord b = j
```

for every `b in TC.family.branches j`, and then derives

```text
cut.block j (TC.branchLabel (some b)).1.
```

The proof uses only the explicit nonbase-family equality, the endpoint
constructor branch-coordinate theorem, and the existing
`branchBlock_of_branchCoord_leftEndpoint` adapter.

## Assumed

The supplied terminal-candidate family, supplied selected cutpoints, supplied
strict Eq5 endpoint constructor data, explicit equality

```text
TC.family.toAoyagiLemma5SuppliedNonbaseFamily =
  ofEq5AlphaIndexedEndpointCoverage_of_alphaInjective_branchCoord ...
```

and the supplied terminal `branchS` left-endpoint formula.

## Deferred

Eq5 branch construction, source production of endpoint records, source-label
legality, base-filter survival for source records, terminal Eq5 payload
coverage, terminal `(p, alpha)` injectivity, direct counted-datum
back-to-label construction, source-backed no-extra terminal-minimum coverage,
Lemma 5 order count, pole order, normal crossings, and RLCT extraction.

## Cited

None; this is finite Lean bookkeeping over supplied hypotheses and previously
formalized definitions.

## Verification

Focused Lean check:

```text
cd lean && lake env lean DLNFibre/DLN/Aoyagi/Lemma5Eq5TerminalClassifier.lean
```

## Review

xhigh review passed.  Review artifact:
`review-lemma5-eq5-endpoint-strict-filtered-and-terminal-branchcoord-a5.md`.
