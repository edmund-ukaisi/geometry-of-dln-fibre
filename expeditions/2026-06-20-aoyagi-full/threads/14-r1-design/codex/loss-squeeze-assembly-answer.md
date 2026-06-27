**Ranking**

1. **(a) `endpoint_telescoping` route.** Cleanest and load-bearing. It reuses the proven product telescope, then uses `conjugation_frobenius_comparable`, then `dlnLoss_block_squeeze`. Biggest risk: the per-layer bridge
   `framedParams H r hr hL (split w) s = P_s * (paramsSymm w) s * Q_s`.
   This is not supplied by `endpoint_telescoping`; it is an input to it.

2. **(other) Package (a) as a framed-loss lemma.** Same math, better API:
   `framed_loss_squeeze_of_frame_read` taking `hframe`, endpoint units, leak, block/core IDs. Biggest risk is only API churn. This is a good refactor after the cert lands.

3. **(b) Separate per-w frame-conjugation proof.** Worse than (a): it reproves the dependent `prodAux` telescope/cast work already banked. Biggest risk: duplicating the exact endpoint-cast pain.

4. **(c) Direct raw `N := prod(paramsSymm w) - B`.** Not viable in general. `dlnLoss_block_squeeze` wants the block-normal residual against `blockdiag[1,0]`. Raw `B` is not gauge-normalized unless endpoint frames are identity. This only works in the special already-normalized case.

**Top Skeleton**

Use route **(a)**, but first expose fixed endpoint frames/inverses, not per-w existential endpoints.

```lean
let wstar := (paramsEquivFlat H) (deepestPoint H r B hB hr hL)
let paramsSymm := (paramsEquivFlat H).symm
let P s := (deepestPoint_frame H r B hB hr hL s).1
let Q s := (deepestPoint_frame H r B hB hr hL s).2
```

For constants, after endpoint inverse extraction:

```lean
let α := 2 * (1 + t^2)
let β := 2 + 2*t^2
let K  := (∑ i, ∑ k, (P0 i k)^2)  * (∑ j, ∑ k, (QL k j)^2)
let Ki := (∑ i, ∑ k, (Pi0 i k)^2) * (∑ j, ∑ k, (QiL k j)^2)

c₁ := (α * K)⁻¹
c₂ := Ki * β
```

Need `0 < K`, `0 < Ki` from endpoint invertibility; API for extracting inverses from `IsUnit` should be verified.

Choose `V ∈ 𝓝 0` in split-coordinates where:

- all pivot blocks are invertible;
- the cutoff Schur shear equals the honest Schur correction;
- the leak estimate holds for fixed `t`;
- the block/core identifications are valid.

Then set:

```lean
U := split ⁻¹' V
```

and use `split.continuous.continuousAt` plus `hsplit_base` to get `U ∈ 𝓝 wstar`.

For `w ∈ U`, set:

```lean
q := split w
A := paramsSymm w
C := framedParams H r hr hL q
```

Chain:

1. **Frame bridge cert** gives `hframe : ∀ s, C s = P s * A s * Q s`.

2. **`endpoint_telescoping`** plus #95 interface facts gives:
   `prod H C = P0 * prod H A * QL`.

3. Basepoint version gives the framed target:
   `D = P0 * B * QL = blockdiag[1,0]` after reindexing.

4. **`conjugation_frobenius_comparable`** compares
   `∑(prod A - B)^2` with `∑(prod C - D)^2`.

5. **`dlnLoss_block_squeeze`** applies to the reindexed framed residual with blocks
   `(P00 - 1, P01, P10, P11)` and the local leak bound.

6. Identify
   `∑E² + ‖Rcore‖² = Φ w`:
   regular part by `hregval` plus sum-square permutation invariance of `regResidualPack`; core part by `hcoreabs` and the Schur/core definition. Nonnegativity uses sum-of-squares plus `deepestCoreF_nonneg` (verify).

**Cert Call**

The one sub-obligation most likely to need a pen-and-paper/Codex cert is:

```lean
framedParams_split_eq_frame_raw :
  ∀ w s,
    framedParams H r hr hL (split w) s
      = P s * ((paramsEquivFlat H).symm w) s * Q s
```

or the corrected version for the actual framed split.

Reason: with the current described `split` as translation plus role reindex, this is not a leaf consequence of `framedParams`; it is the semantic assertion that the split coordinates are the fixed-frame gauge coordinates. Endpoint telescoping only consumes it. The leak bound and block decomposition are finite-dimensional algebra/local-continuity leaves by comparison.