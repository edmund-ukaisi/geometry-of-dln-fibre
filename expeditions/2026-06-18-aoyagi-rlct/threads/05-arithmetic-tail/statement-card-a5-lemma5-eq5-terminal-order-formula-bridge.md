# Statement card - A5 Lemma 5 Eq5 terminal order formula bridge

## Lean Name

- `DLNFibre.DLN.Aoyagi.AoyagiLemma5SuppliedTerminalCandidateFamily.terminalMinimumLabels_card_eq_theorem2OrderFormula_of_eq5EndpointFamily_branchCoordVal_blockWidth_cardSqueeze`

## Claim

For a terminal-candidate family whose nonbase family is explicitly the
strictest supplied Eq5 endpoint family, the existing block-width cardinal
squeeze count rewrites to Aoyagi Theorem 2's final order notation.

## Proved

Lean proves

```text
TC.terminalMinimumLabels.card = data.theorem2OrderFormula
```

for `data : AoyagiDefinition3CeilData (N+1) m`, after specializing the Eq5
parameters to

```text
a = data.aParam,
M = data.ceilWidth.
```

The proof uses `data.aParam_le` as the endpoint-cardinality theorem's
`a <= N+1` input and `data.selectedSum_eq` as the selected-sum input.  The
final step unfolds
`data.theorem2OrderFormula = data.aParam * (N+1-data.aParam) + 1`.

## Assumed

All hypotheses of the existing Eq5 endpoint-family block-width cardinal squeeze
remain explicit: the terminal Eq5 source-vector payloads, terminal-label block
data, blockwise actual-width dominance, source selected-width inequality,
terminal `(p, alpha)` injectivity, endpoint-family equality, endpoint branch
coordinate/value data, branch source/value label synchronization, nonbase
terminal inequalities, and the terminal-endpoint base label.

## Deferred

Source construction of the Eq5 endpoint family, terminal Eq5 payload coverage,
source proof of terminal `(p, alpha)` injectivity, proof of the endpoint-family
equality from Aoyagi's source, branch-label injectivity/no-extra coverage,
the full Lemma 5 order-count theorem, pole order, normal crossings, and RLCT
extraction.

## Cited

None.  This is finite Lean bookkeeping over previously formalized definitions
and supplied hypotheses.

## Verification

Focused Lean check and full library checks pass:

```text
cd lean && scripts/lb DLNFibre.DLN.Aoyagi.Lemma5Eq5TerminalOrderBridge
cd lean && scripts/lb
cd lean && scripts/sorries
git diff --check
```

`scripts/sorries` reports `0 sorry`, `0 #exit`, `0 native_decide`, and
`0 axiom`.  The full build reports only pre-existing Core/style warnings.

## Review

xhigh review passed.  Review artifact:
`review-lemma5-eq5-terminal-order-formula-bridge-a5.md`.
