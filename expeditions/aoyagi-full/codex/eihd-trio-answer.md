# Codex (xhigh) consult — eIn/eOut/hD architecture for hDtot

**Verdict:** use **(c)**, but prove it through named block projection lemmas. Avoid flat standard basis ext entirely.

For `hD`, keep the wrapper’s original shape:

```lean
T := (eOut : E →ₗ[ℝ] StairProd V 2) ∘ₗ Dtot ha y₀ ∘ₗ
       (eIn.symm : StairProd V 2 →ₗ[ℝ] E)
```

Then prove `T = stairMap V 2 f c` by `LinearMap.ext` over arbitrary
`x : StairProd V 2`, `rcases x` as `(v0, (v1, ()))`, and `Prod.ext` the components. This keeps both input and output in semantic block coordinates. Do **not** prove
`Dtot ∘ eIn.symm = eOut.symm ∘ stairMap`; that pushes the output back to flat coordinates and reintroduces the output `Params`/`FlatIdx` reindex fight.

Even better: define the coupling from the actual off-diagonal block:

```lean
c.1 v0 := (projV1 (T (inclV0 v0)), 0)
```

Then you only need real content for:

```lean
projV0 ∘ T ∘ inclV0 = f 0
projV0 ∘ T ∘ inclV1 = 0
projV1 ∘ T ∘ inclV1 = f 1
```

The `V0 → V1` block is determinant-invisible, so do not identify it unless another theorem needs it. This matches the two-sided wrapper in [RouteMHDtotConj.lean](/home/ubuntu/workspace/genm-eihd-wt/lean/DLNFibre/DLN/RLCT/Validate/RouteMHDtotConj.lean:51) and the keystone in [RouteMStairTwoSided.lean](/home/ubuntu/workspace/genm-eihd-wt/lean/DLNFibre/DLN/RLCT/Validate/RouteMStairTwoSided.lean:69).

For `J00`, yes: define

```lean
f 0 := schurFrameDeriv
  (readX M (tach M) ha y₀ ⟨0, by decide⟩)
  (readK M (tach M) ha y₀ ⟨0, by decide⟩)
  (readN M (tach M) ha y₀ ⟨0, by decide⟩)
```

and prove the block by composing the banked chain rule in [RouteMProjV0Gate.lean](/home/ubuntu/workspace/genm-eihd-wt/lean/DLNFibre/DLN/RLCT/Validate/RouteMProjV0Gate.lean:291) with `flatBlockLE.symm`. The useful normalization lemma is:

```lean
((flatBlockLE hr hc).symm : _ →ₗ[ℝ] _) ∘ₗ
  (fderiv ℝ (fun z => flatBlock hr hc z) z₀).toLinearMap
= LinearMap.id
```

or prove it via an intermediate

```lean
(fderiv ℝ (fun z => flatBlock hr hc z) z₀).toLinearMap = flatBlockLin hr hc
```

then close with `LinearEquiv.symm_apply_apply` / the round trips in [RouteMFlatBlockLE.lean](/home/ubuntu/workspace/genm-eihd-wt/lean/DLNFibre/DLN/RLCT/Validate/RouteMFlatBlockLE.lean:147). After that, `gate_schurCore_eq` gives the exact `schurFrameDeriv`.

Coherence: requiring the **same** `ρ` for `eIn` and `eOut` is the wrong invariant. Input and output are different semantic index spaces. The right invariants are:

```lean
-- input-side
(eIn δ).1 = slotReadV0 ha δ

-- output-side
(eOut ((paramsEquivFlatCLE M) P)).1 =
  (flatBlockLE hr hc).symm (layer0ParamsRead P)
```

plus the chart bridge:

```lean
layer0ParamsRead (BparamsLeaf ha y) = layer0SchurMap ha hr hc y
```

from `BparamsLeaf_layer0_entry`.

A green-but-wrong reindex can hide if you only prove determinant facts, or if `eOut` reads the layer-0/chain layer through a volume-preserving but semantically wrong permutation. `hreg` will not catch that. The exact map equality `hD`, especially `J00` and `J01 = 0`, is the check.

I do not see a hidden new-math gap in `J00`; it is bounded plumbing. The remaining real risk is output-side orientation for `V1`: `chainUnitMap` expects `(W, C) ↦ (W, C - N*W)`, while `chainA` outputs rows as kept block then lift block. Make `eOut` split/reorder the layer-1 Params matrix to `(W, kept)` explicitly, or the determinant can stay green while `hD` is wrong.
