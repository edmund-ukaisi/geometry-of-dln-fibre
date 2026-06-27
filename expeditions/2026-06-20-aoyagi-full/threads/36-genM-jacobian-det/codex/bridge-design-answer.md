      =
    chartParamsGen (x p) M t (genBlkFlatStructParams ((paramsEquivFlat M).symm x)) hle := by
  funext s
  -- one layer case split; no opaque-width flat-coordinate induction
```

The determinant side remains:

```lean
composeFold_abs_det_leafH fs leafH x hdet
```

where `hdet` is assembled from `radialFactor_abs_det`, `lduCoreD_abs_det`, `schurFrameD_abs_det`, and chain det `1`.

**Important Chain Correction**

The chain factor must be semantic in `N_s`.

A fixed-`N` factor

```lean
chainChartFactor Nblk E
```

cannot build the general `chainA_s = [C_{s+1} - N_s W_s ; W_s]` if `N_s` is a coordinate. For the bridge, use a variable-`N` chain block:

```lean
chainVarMap (N, W, C) = (N, W, C - N * W)
```

with derivative

```lean
(dN, dW, dC) ↦ (dN, dW, dC - N*dW - dN*W)
```

and determinant `1` by triangularity. This is still a `conjBlockFactor`, just with block type containing `N` as a read/write identity component. The fixed-`N` banked lemma is useful intuition, but the semantic factor should leave `N_s` available and unchanged.

**Factor Order**

Because `composeFold fs = f₀ ∘ f₁ ∘ ...`, the **rightmost** factor runs first.

Chronological execution should be:

```text
radial first
then deepest-to-shallowest:

build C_{s+1}
then apply chain_s
```

More concretely, for descending `s`:

```text
radial
ldu_{deep}
schur_{deep}       -- creates C_{deep}
chain_{deep-1}     -- reads C_deep and raw N_{deep-1}, W_{deep-1}

ldu_{deep-1}
schur_{deep-1}
chain_{deep-2}

...
```

So the actual Lean list is the reverse chronological list. Schematically:

```lean
fs =
  shallowCluster ++ ... ++ deepCluster ++ [radialFactor active p]
```

with each cluster ordered in the list as the reverse of execution, e.g.

```lean
[chain_s, schur_s, ldu_s]
```

so execution is:

```text
ldu_s → schur_s → chain_s
```

The nesting does **not** break the fold. It is exactly what `foldr` is good for: after the deeper suffix has built `C_{s+1}`, the next chain factor reads that prefix state and writes `A_s`.

The cleanest design is therefore:

1. define structural `Params` split CLEs;
2. define factors via `paramsConjBlockFactor`;
3. use variable-`N` chain factors;
4. order factors deepest-first in execution, hence reverse in the `fs` list;
5. prove the bridge at `Params` level by `funext s` and local block simp lemmas.
