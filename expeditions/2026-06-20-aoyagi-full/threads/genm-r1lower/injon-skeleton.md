# injOn build skeleton (genm-r1lower, the named-risk leg — BOUNDED, multi-lemma)

Scope CONFIRMED BOUNDED (Codex xhigh + source; `codex/injon-scope-*`). Peel `pbo` first → radial
coupling gone → `InjOn (BchartLeaf ∘ kLDU)` is the OFF-radial block-by-block TRIANGULAR recovery.

## The sequence (each a stated atom; #1 reduction MACHINE-CHECKED below)

### Atom #1 — `kLens` injective off q-pivots (the single-block LDU recovery)

The reduction to LDU-product uniqueness is VERIFIED (compiles, scratch `/tmp/klens_inj.lean`):

```
example {t : ℕ} (K K' : Matrix (Fin t) (Fin t) ℝ)
    (hq : ∀ i, (matrixSplit K).2.1 i ≠ 0)
    (hk : kLens K = kLens K') : K = K' := by
  rw [kLens, kLens] at hk
  have hldu : lduCoreMap (matrixSplit K) = lduCoreMap (matrixSplit K') := matrixSplit.symm.injective hk
  rw [lduCoreMap, lduCoreMap] at hldu
  have hprod : (1 + lowMatL (matrixSplit K).1) * Matrix.diagonal (matrixSplit K).2.1
        * (1 + upMatL (matrixSplit K).2.2)
      = (1 + lowMatL (matrixSplit K').1) * Matrix.diagonal (matrixSplit K').2.1
        * (1 + upMatL (matrixSplit K').2.2) := matrixSplit.injective hldu
  -- REMAINING: LDU-product uniqueness — from hprod + hq conclude matrixSplit K = matrixSplit K'
  --   (then matrixSplit.injective closes K = K'). This is LU-uniqueness for unit-triangular factors
  --   with nonzero diagonal. matrixSplit reads RAW entries (RouteMSchurFrameDet:366), so genuine.
  sorry
```

The LDU-product uniqueness (the `sorry`): `(1+L)·diag(q)·(1+U) = (1+L')·diag(q')·(1+U')`, `q_i≠0` ⟹
`L=L', q=q', U=U'`. Standard but no Mathlib lemma directly usable. Routes: (a) multiply out + induct on
the staircase (the unit-triangular factors are det-1, `unitLow_det`/`unitUp_det` banked); (b) the diagonal
of the product reads `q_i` modulo strictly-lower×strictly-upper cross terms — recover `q` from the diagonal
+ already-recovered off-diag, triangular. Candidate for a focused sub-build or cast-specialist if it fights.

### Atom #2 — X/N/E + leaf linear recovery from the `Agen 1 …` Schur-frame blocks

`BchartLeaf = paramsEquivFlat ∘ chartParamsGen 1 …`. `paramsEquivFlat` is an injective (linear) Equiv.
`chartParamsGen 1` recovery: from the per-layer matrices recover the residual coords. Triangular:
K recovered (atom #1), then X via fwd-subst (X = (X·K)·K⁻¹ from the Schur block `Bmat = [K; XK]`), then
N/E/leaf linear reads. Uses `Agen_congr`, `schurFrameProd_u_to_E` (banked, `RouteMLeafBData`).

### Atom #3 — `interiorLive_injOn` assembly

`interiorLivePhi = (BchartLeaf ∘ kLDU) ∘ pbo` (the hmap-for-B' factorization, verified). Via
`Set.InjOn.comp`: peel `pbo` (banked `pivotBlowupOn_injOn` off `{leafPivot=0}`), then
`InjOn (BchartLeaf ∘ kLDU)` on `pbo '' S` via atoms #1+#2. The set `S` = `{u leafPivot ≠ 0 ∧ ∀j∈E, u j≠0}`,
`E = interiorLive_E` (the q-pivot axes). MapsTo bookkeeping: `pbo '' S` keeps the q-pivots nonzero (kLDU
leaves them as the active-set scaling).
