# Statement card - A4 Case 2 fixed-center stopped produced payloads

Date: 2026-07-02.

Status: formalisation-ready narrow slice.

## Lean Targets

Add three stopped subcase constructors:

```text
case2AllPivotActualWidthStoppedProducedBranchPayload_of_currentCenterSourceInput

case2AllPivotRowExhaustedTerminalLastProducedBranchPayload_of_currentCenterSourceInput

case2AllPivotRowExhaustedSourceSuffixProducedBranchPayload_of_currentCenterSourceInput
```

Each should construct a

```text
SelectedEntryProducedBranchPayload
  (selectedEntryAllPivotAnalyticAtlasContext hcenter chartEquiv)
  (AoyagiRecurrenceBranchState L n Real)
```

for the fixed current center

```text
case2ResidualBlockPivotEntries n s.S s.J
```

using a supplied public chart equivalence

```text
Fin (case2ResidualBlockPivotEntries n s.S s.J).card
  ~= (case2ResidualBlockPivotEntries n s.S s.J : Type).
```

## Required Inputs

All three constructors take:

- `s : AoyagiRecurrenceBranchState L n Real`;
- `input : Case2AllPivotDisplayedSourceInput s t numerator leastValue`;
- a stopped subcase guard;
- the finite stopped source data's auxiliary matrices/families;
- a chart equivalence for the current residual-block center.

The active pivot bound is extracted from the stopped guard:

- actual-width: `hguard.1`;
- terminal-last row-exhausted: `hguard.1.1`;
- source-suffix row-exhausted: `hguard.1.1`.

## Payload Fields

Each payload must use:

- `branchState := s`;
- the displayed pivot chart through the supplied `chartEquiv`;
- the source chart point built from `input.u` and `input.residual`;
- universal chart-domain and source-domain witnesses;
- `producedParam` definitionally equal to the chart map at the produced point;
- the corresponding non-placeholder stopped `sourceData`;
- the corresponding `.of_sourceInput` stopped `producedSourceData`.

The record does not contain a field proving compatibility between
`producedParam` and the finite `producedSourceData` package.

The row-exhausted stopped source-data records must remain genuine `Type`
packages: they store the supplied row family and tail matrices as data, not
only the proposition-valued frontier theorem.

## Boundary

This is not the full `sourceProduction` field and not
`SelectedEntryAtlasProducedBranchData`.  It produces three stopped payload
constructors under their existing finite source-data guards.  The two
row-exhausted APIs are not asserted to be disjoint: the source-suffix guard
`s.S + 1 <= L` overlaps the terminal-last equality `s.S + 1 = L`.  A total
row-exhausted payload over the weaker semantic row-exhausted stopped guard
remains separate.

## Checks

Focused direct Lean check for the payload module, full local `lake build
DLNFibre`, `lean/scripts/sorries`, `git diff --check`, and xhigh review are
required before banking.
