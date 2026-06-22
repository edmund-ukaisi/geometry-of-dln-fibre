# Statement card - A0 normal-crossing finite certificates

## Lean Names

File:

- `lean/DLNFibre/DLN/Aoyagi/NormalCrossingInterface.lean`

Names:

- `DLNFibre.DLN.Aoyagi.AoyagiNormalCrossingExponentData.exponentMinimum_eq_of_mem_activeRatios_of_forall_le`
- `DLNFibre.DLN.Aoyagi.AoyagiNormalCrossingExponentData.exponentMinimum_eq_of_activePair_ratioAt_eq_of_forall_le`
- `DLNFibre.DLN.Aoyagi.AoyagiNormalCrossingExponentData.exponentOrder_eq_of_mem_chartMinCounts_of_forall_le`
- `DLNFibre.DLN.Aoyagi.AoyagiNormalCrossingExponentData.exponentOrder_eq_of_chart_minCount_eq_of_forall_le`
- `DLNFibre.DLN.Aoyagi.AoyagiNormalCrossingExponentData.exponentOrder_eq_of_forall_le_of_exists_chart_minCount_eq`

## Claim

For supplied finite normal-crossing exponent data, Lean can certify the finite
minimum and finite order count from standard finite min/max hypotheses:

```text
q in activeRatios and q lower-bounds activeRatios
```

for the exponent minimum, and

```text
q in chartMinCounts and q upper-bounds chartMinCounts
```

for the exponent order.

## Proved

Pure finite `Finset.min'` and `Finset.max'` bookkeeping.  The active-coordinate
and realizing-chart wrappers convert the source-facing certificate shape into
set-membership certificate shape.

## Assumed

The normal-crossing exponent data `D`, including a nonempty active coordinate
set.  Any candidate value must be supplied with its active-ratio membership or
active-coordinate witness.  Any candidate order must be supplied with its
chart-count membership or realizing chart.

## Deferred

Chart production, normal crossings, active-ratio inequalities from blow-up
recursion, chartwise count identification with Lemma 5 terminal labels, pole
order without A0 extraction, and RLCT extraction.

## Cited

None in the finite lemmas.  The analytic extraction theorem remains cited only
through `AoyagiNormalCrossingExtractionHypothesis`.

## Verification

Focused Lean, module, aggregator, full-library, sorry, and diff checks passed:

```text
cd lean && lake env lean DLNFibre/DLN/Aoyagi/NormalCrossingInterface.lean
cd lean && lake build DLNFibre.DLN.Aoyagi.NormalCrossingInterface
cd lean && lake env lean DLNFibre.lean
cd lean && lake build DLNFibre
cd lean && scripts/sorries
git diff --check
```

`scripts/sorries` reports `0 sorry`, `0 #exit`, `0 native_decide`, and
`0 axiom`.  The full build reports only pre-existing Core warnings.

Independent xhigh review passed:
`review-normal-crossing-finite-certificates-a0.md`.
