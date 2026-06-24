# Statement card - A6 Definition 3 Eq5 hsource bridge

Status: Lean bridge landed.

Reproduction:
`reproduction-definition3-eq5-hsource-bridge-a6.md`.

Independent review:
`review-definition3-eq5-hsource-bridge-a6.md`.

## Target

Derive the Eq5 terminal-order strict selected-width source inequality from
`AoyagiDefinition3SourceData` and the equality

```text
m = aoyagiSelectedReducedWidths H r C.
```

## Intended Lean Names

```text
AoyagiDefinition3SourceData.selected_strict_of_eq_selectedReducedWidths
AoyagiLemma5SuppliedTerminalCandidateFamily.terminalMinimumLabels_card_eq_theorem2OrderFormula_of_eq5EndpointFamily_branchCoordVal_blockWidth_cardSqueeze_of_definition3SourceData
```

## Boundary

The bridge should leave actual-width/block dominance, Eq5 endpoint-family
payloads, injectivity, and terminal-family data explicit.

No selected-cutpoint existence, no Eq5 construction, no Lemma 5 exactness, no
chart production, no normal crossings, no pole order, and no RLCT.

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
