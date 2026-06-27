Short answer: your rate-direct reframe is sound. In this worktree it is already written, but not imported/tracked, as [RouteMFlatStructV.lean](/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/agent-a008af4c8473e3063/lean/DLNFibre/DLN/RLCT/Validate/RouteMFlatStructV.lean:42). It proves `C0_eq_one_gen`, `hC0_struct_gen`, `phiFlatStructV`, `UvalStructV`, and `routeMCore_phiFlatStructV`.

One target correction: an unconditional `nodeChartGeneral M : NodeAchieverChart M` is false if `minAdm M = 0`, because `NodeAchieverChart` contains `hpos : 1 ≤ minAdm M`. The usable target is:

```lean
noncomputable def nodeChartGeneral (M : Fin (L+1) → ℕ) (hpos : 1 ≤ minAdm M) :
  NodeAchieverChart M := ...
```

**Answers**

1. **Rate-direct is sound.** `routeMCore_phiGen` is universal in both the scalar `u` and the block data `B`; it has no independence hypothesis. Instantiating
`u := x p` and `B := genBlkFlatStruct M t ha x` is valid even though `x p` may also occur among the coordinates read by `B`. The telescope proves
`prod = u • H(u,B)`, so after substitution it proves `prod = (x p) • H(x p, B x)`. No algebraic trap.

2. **For DET, keep OPTION-1.** Directly differentiating `chartParamsGen ∘ genBlkFlatStruct` will recreate the same Schur/LDU/chain triangularization, but inside a dependent `Params` derivative with opaque `Text/Wext` casts. That is more Lean pain than the existing `ChartFactor` route. The clean move is to generalize `phiFlat_abs_det_of_factored` from old `phiFlat` to an arbitrary target `phi`, then instantiate with:
```lean
hmapV : composeFold fs = phiFlatStructV M t ha hN
```
So the bridge is still needed, but only for det/cov compatibility.

3. **Threshold is unchanged, but `leafH` must be honest.** Yes: with `nodeLeafK N p`, all spectator axes have `k = 0`, hence ratio `⊤`; `nodeChart_thresholdLe` only uses `leafH p = minAdm M - 1`. But you cannot set spectator exponents to zero unless the actual determinant has no spectator monomial. `(4,4,2,2)` is special. `(3,3,4)` already forces a spectator factor `|u 1|²`, and `(3,3,3,3)` forces more. General Schur/LDU descent genuinely contributes LDU/Schur spectator powers, so `leafH` must carry them.

4. **Minimal build sequence.**
- Import/bank `RouteMFlatStructV`.
- Supply achiever data: `t`, `StructAdm M t`, `hN : 0 < routeMAmbient M`, active set with `active.card = minAdm M`.
- Build `structFactors M t ha hN : List (ChartFactor N)`.
- Prove the crux:
```lean
composeFold structFactors = phiFlatStructV M t ha hN
```
- Prove factor-product bookkeeping:
```lean
((foldDerivList structFactors u).map detAbs).prod
  = ∏ j, |u j| ^ leafH j
```
using radial/Schur/LDU/chain det lemmas.
- Prove cov by c-o-v on the finite punctured set, then add back extra spectator zero slices as null.
- Assemble `NodeAchieverChart`, then discharge `routeMCore_box_diverges_achiever` via `routeMCore_box_diverges_of_nodeChart`.

The single riskiest sublemma is the function-ext bridge `composeFold = phiFlatStructV`, preferably proved after applying `paramsEquivFlat.symm` and comparing `Params` layer-by-layer. It must align factor order, prefix states, `chainUnitMap`, and the `Text/Wext` casts. Everything else is downstream bookkeeping.