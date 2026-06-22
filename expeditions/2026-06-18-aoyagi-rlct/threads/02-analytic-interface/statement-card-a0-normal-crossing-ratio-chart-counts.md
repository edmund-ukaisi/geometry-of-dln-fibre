# Statement card - A0 normal-crossing ratio chart counts

## Lean Names

File:

- `lean/DLNFibre/DLN/Aoyagi/NormalCrossingInterface.lean`

Names:

- `DLNFibre.DLN.Aoyagi.AoyagiNormalCrossingExponentData.coordsInChartAtRatio`
- `DLNFibre.DLN.Aoyagi.AoyagiNormalCrossingExponentData.countInChartAtRatio`
- `DLNFibre.DLN.Aoyagi.AoyagiNormalCrossingExponentData.minCoordsInChart_eq_coordsInChartAtRatio_of_exponentMinimum_eq`
- `DLNFibre.DLN.Aoyagi.AoyagiNormalCrossingExponentData.minCountInChart_eq_countInChartAtRatio_of_exponentMinimum_eq`
- `DLNFibre.DLN.Aoyagi.AoyagiNormalCrossingExponentData.exponentOrder_eq_of_countInChartAtRatio_eq_of_forall_le`

## Claim

Chart counts stated at a candidate ratio can be rewritten to the existing
global-minimum chart counts once that candidate ratio is proved to be
`D.exponentMinimum`.

## Proved

For any supplied ratio `q`, if `D.exponentMinimum = q`, then:

```text
D.minCoordsInChart c = D.coordsInChartAtRatio q c
D.minCountInChart c = D.countInChartAtRatio q c
```

If one chart realizes a candidate count at `q` and every chart count at `q` is
bounded above by that candidate count, then `D.exponentOrder` equals that
candidate count.

## Assumed

The normal-crossing exponent data `D`; the equality `D.exponentMinimum = q`;
the chart-count witness; and the all-chart upper bound.

## Deferred

Normal-crossing chart production, source proof of the candidate-ratio minimum,
source proof of chart-count witnesses or upper bounds, pole order without A0,
normal crossings, and RLCT extraction.

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
`review-normal-crossing-ratio-chart-counts-a0.md`.
