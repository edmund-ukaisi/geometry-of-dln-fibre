# Statement card - A6 Definition 3 Eq5 hlast bridge

Status: Lean bridge landed.

Reproduction:
`reproduction-definition3-eq5-hlast-bridge-a6.md`.

Independent review:
`review-definition3-eq5-hlast-bridge-a6.md`.

## Target

Derive the Eq5 terminal-order endpoint source-range hypothesis

```text
C.point (N+1) <= L+1
```

from `AoyagiDefinition3SourceData.cut_le`, and remove the duplicated `hlast`
input from the Definition 3 Eq5 terminal-order wrapper.

## Intended Lean Names

```text
AoyagiDefinition3SourceData.lastPoint_le
AoyagiLemma5SuppliedTerminalCandidateFamily.terminalMinimumLabels_card_eq_theorem2OrderFormula_of_eq5EndpointFamily_branchCoordVal_blockWidth_cardSqueeze_of_definition3SourceData
```

## Boundary

The bridge should still leave actual-width/block dominance, Eq5 endpoint-family
payloads, injectivity, branch synchronisation, and terminal-family data
explicit.

No selected-cutpoint existence, no Definition 3 source-data existence, no Eq5
construction, no Lemma 5 exactness, no chart production, no normal crossings,
no pole order, and no RLCT.

## Lean Status

Implemented in:

```text
lean/DLNFibre/DLN/Aoyagi/Definition3Bridge.lean
lean/DLNFibre/DLN/Aoyagi/Lemma5Eq5TerminalOrderDefinition3Bridge.lean
```

Focused build passed:

```text
cd lean && scripts/lb DLNFibre.DLN.Aoyagi.Lemma5Eq5TerminalOrderDefinition3Bridge
```
