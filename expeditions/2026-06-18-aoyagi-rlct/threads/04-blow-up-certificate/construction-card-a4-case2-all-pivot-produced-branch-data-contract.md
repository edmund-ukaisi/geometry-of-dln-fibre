# Construction card - A4 Case 2 all-pivot produced-branch-data contract

Date: 2026-07-02.

Status: frontier contract; no Lean theorem proposed in this packet.

## Target Socket

After the all-pivot shell and recurrence-termination adapter, the remaining
field in the recurrence-aware producer is:

```text
sourceProduction :
  SelectedEntryAtlasProducedBranchData
    (selectedEntryAllPivotAnalyticAtlasContext hcenter chartEquiv)
    (AoyagiRecurrenceBranchState L n alpha)
```

The adapter

```text
selectedEntryAllPivotSuppliedAnalyticAtlasProducerWithRecurrenceTermination
```

will consume this field directly.  The next useful A4 work is therefore not a
new producer wrapper.  It is a source-backed construction of the three guard
predicates, three branch payloads, and state laws required by
`SelectedEntryAtlasProducedBranchData`, plus the companion guard-completeness
and continuing-child recurrence data needed by the branch-progress bridge.

## Guard Contract

For a recurrence branch state `s`, start from the displayed Case 2 guard split
on the forgotten support state `s.toIntroducedState`:

```text
continuingGuard s :=
  AoyagiIntroducedLabelBranchState.case2DisplayedContinuingGuard
    s.toIntroducedState

actualWidthStoppedGuard s :=
  AoyagiIntroducedLabelBranchState.case2DisplayedActualWidthStoppedGuard
    s.toIntroducedState

rowExhaustedStoppedGuard s :=
  AoyagiIntroducedLabelBranchState.case2DisplayedRowExhaustedStoppedGuard
    s.toIntroducedState
```

In old-state notation these are:

```text
continuing:
  J + 2 <= prefixMinNat n (S + 1)

actual-width stopped:
  n (S + 1) = J + 1

row-exhausted stopped:
  prefixMinNat n S = J + 1
```

The active guard is:

```text
J + 1 <= prefixMinNat n (S + 1)
```

and the existing finite frontier theorem supplies guard completeness from this
active guard.  For `SelectedEntryAtlasProducedBranchData`, use the
active-refined guards:

```text
activeContinuingGuard s :=
  activeGuard s and continuingGuard s

activeActualWidthStoppedGuard s :=
  activeGuard s and actualWidthStoppedGuard s

activeRowExhaustedStoppedGuard s :=
  activeGuard s and rowExhaustedStoppedGuard s
```

The active conjunct is required because producer payload functions are total
over their guards.  The stopped equalities alone do not assert that the
selected pivot is present.  The stopped guards are not required to be
exclusive.

## Payload Contract

Each branch must produce a real `SelectedEntryProducedBranchPayload`, not a
propositional placeholder:

```text
branchState : AoyagiRecurrenceBranchState L n alpha
producedChart : Fin C.numCharts
producedPoint : C.ChartPoint producedChart
producedPoint_mem_chartDomain :
  producedPoint in ctx.chartDomain producedChart
producedParam : Param
producedParam_eq_chartMap :
  producedParam = C.chartMap producedChart producedPoint
producedParam_mem_sourceDomain :
  producedParam in ctx.sourceDomain
sourceData : Type
producedSourceData : sourceData
```

The state laws must be literal:

```text
(continuingPayload s h).branchState = s
(actualWidthStoppedPayload s h).branchState = s
(rowExhaustedStoppedPayload s h).branchState = s
```

The `sourceData` fields must differ by branch.

Continuing source data must include:

- the displayed Case 2 selected-pivot chart with scalar `u`;
- the substitutions `b'_i = u b_i`;
- the regular `Q` and `P` transformations;
- the transported following factor `C'_J^(S+1) = Q^-1 C_J^(S+1)`;
- the cleared block `D'''_J` with lower-right successor block;
- successor recurrence data over `(S,J+1)`;
- a proof that the produced successor is the same-stage child used by the
  recurrence progress bridge.

Actual-width stopped source data must include the terminal/suffix data for the
case where the actual next width has ended:

```text
n (S + 1) = J + 1
```

This is the branch where the lower-right block has no next actual-width column.
Its terminal payload is not interchangeable with the row-exhausted payload.

Row-exhausted stopped source data must include the terminal/suffix data for the
case where the current prefix rows have ended:

```text
prefixMinNat n S = J + 1
```

This is the branch where the current prefix block is exhausted.  Its payload
must keep the row/column orientation and transported product data explicit.
The transported source-suffix payload is only a suffix-refined subcase: it also
requires `S + 1 <= L`.  A final-stage row-exhausted/no-suffix state needs a
separate terminal treatment or a branch invariant excluding it.  The current
finite source-data layer now exposes the existing terminal-last treatment for
the subcase `S + 1 = L`; it is still not a complete
`SelectedEntryProducedBranchPayload`.

The displayed source-chart recurrence data is valued in the coefficient ring
of the chart variables.  Therefore a source-backed recurrence producer must
either specialize the generic branch parameter `alpha` to that value type,
eventually `ℝ` for the signed-box atlas, or carry an explicit transport from
displayed pivot values into `alpha`.

## Center Alignment

The all-pivot context is built from one fixed finite center:

```text
selectedEntryAllPivotAnalyticAtlasContext hcenter chartEquiv
```

A Case 2 branch state `(S,J)` has its natural center:

```text
case2ResidualBlockPivotEntries n S J
```

Therefore a full recurrence-wide source-production theorem cannot silently use
one fixed center while `S` and `J` vary.  A correct implementation must choose
one of the following:

1. a local fixed-state producer whose active branch states all have the same
   residual-block center;
2. an explicit center-alignment field tying every active `s` to the fixed
   `center`;
3. a new dependent/global producer interface with chart certificates indexed by
   branch state.

Without one of these, the produced chart and produced source point do not live
in the chart certificate required by the all-pivot producer.

## Existing Lean Inputs

The packet may use these as established inputs:

- `SelectedEntryAtlasProducedBranchData` and
  `SelectedEntryProducedBranchPayload` in
  `lean/DLNFibre/DLN/Aoyagi/SelectedEntryAnalyticAtlasProducer.lean`;
- `selectedEntryAllPivotSuppliedAnalyticAtlasProducer` in
  `lean/DLNFibre/DLN/Aoyagi/SelectedEntryAllPivotProducerShell.lean`;
- `selectedEntryAllPivotSuppliedAnalyticAtlasProducerWithRecurrenceTermination`
  in
  `lean/DLNFibre/DLN/Aoyagi/SelectedEntryAllPivotProducerTermination.lean`;
- displayed Case 2 guard/progress definitions in
  `lean/DLNFibre/DLN/Aoyagi/BlowupBranchProgress.lean`;
- the concrete displayed Case 2 A0 source-production payload in
  `lean/DLNFibre/DLN/Aoyagi/SelectedEntryAnalyticAtlasCase2FinalBridge.lean`;
- the finite all-pivot coverage, regularity, transition, unit, and
  Jacobian/volume data already assembled by the shell.

These inputs do not construct the missing source-production payloads.

## Source Support

Aoyagi PDF pp. 19-22 support the displayed Case 2 local algebra: selected
pivot chart, `b'_i = u b_i`, regular `Q` and `P`, the transported following
factor, the cleared block `D'''_J`, the product identity, and the prose
continue/stop split.

They do not supply global chart tokens, analytic source domains, atlas
coverage, overlap maps, volume-form compatibility, or produced successor and
terminal payload records.  Those must be constructed as additional elementary
infrastructure before Lean can fill `sourceProduction`.

## Kill Conditions

Reject the construction if it:

- sets any guard to `True` or `False` to make the record easy to inhabit;
- uses `sourceData := Unit`;
- fills source production via `SourceProductionObligation`;
- uses a fixed all-pivot center while branch states range over changing
  `(S,J)` without a center-alignment field;
- merges the actual-width stopped and row-exhausted stopped payloads;
- treats a progress child as proof that source data realizes the child;
- claims analytic atlas existence, normal crossings, pole order, or RLCT
  extraction.

## Next Lean Shape

The first useful Lean step, if this packet is implemented, is not a final
producer theorem.  It should introduce branch-specific source-data structures
with non-placeholder fields:

```text
Case2AllPivotContinuingProducedSourceData
Case2AllPivotActualWidthStoppedProducedSourceData
Case2AllPivotRowExhaustedSourceSuffixProducedSourceData
```

Only after those structures are inhabited source-faithfully should Lean build
the `SelectedEntryAtlasProducedBranchData` record and feed it to the
recurrence-aware all-pivot producer.
