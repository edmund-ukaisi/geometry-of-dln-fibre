# The role-respecting slot↔index map for gaugeDecode (crux2 → cobuild, 2026-06-23)

cobuild owns `gaugeDecode`; crux2 owns the `FlatIdx → slot` map. This is the exact map, read off the
COMMITTED `DeepestSplitReindex.lean` machinery (`rThresholdSplit`, `layerEntrySplit`, `roleSplitIdx`,
`deepestRoleIndexEquiv`) — nothing new to build, the encoding is already in Lean; this documents it so
gaugeDecode matches.

## The decode chain (committed, DeepestSplitReindex.lean)

A flat index `f : Fin (flatDim H)` decodes through:

1. `Fintype.equivFin (FlatIdx H)`: `Fin (flatDim H) ≃ FlatIdx H`.
2. `flatIdxLayerProd` (:158): `FlatIdx H ≃ Σ s : Fin L, (Fin (H s.castSucc) × Fin (H s.succ))`. So `f`
   becomes `(s, i, j)` — layer `s : Fin L`, row `i : Fin (H s.castSucc)`, col `j : Fin (H s.succ)`.
3. `layerEntrySplit r (H s.castSucc) (H s.succ)` (:147): the `r`-threshold block decode on `(i, j)` —
   - `i < r ∧ j < r`     → **X_s** block, position `(i, j) : Fin r × Fin r`
   - `i < r ∧ j ≥ r`     → **Y_s** block, position `(i, j−r) : Fin r × Fin (H s.succ − r)`
   - `i ≥ r ∧ j < r`     → **Z_s** block, position `(i−r, j) : Fin (H s.castSucc − r) × Fin r`
   - `i ≥ r ∧ j ≥ r`     → **T_s** block, position `(i−r, j−r) : Fin (H s.castSucc − r) × Fin (H s.succ − r)`
   (the `rThresholdSplit r a`: `i ↦ inl i` if `i<r`, else `inr (i−r)`.)
4. `roleSplitIdx` (:174): collects {X_s, Y_s, Z_s : all s} on the LEFT (`RegGaugeIdx`), {T_s : all s} on
   the RIGHT (`= FlatIdx (deepestM H r)`, the CORE slot).
5. `deepestRoleIndexEquiv` (:214): `Fin (flatDim H) ≃ Fin nReg ⊕ (Fin (flatDim deepestM) ⊕ Fin nGauge)` —
   splits `RegGaugeIdx` into `Fin nReg ⊕ Fin nGauge` (the reg/gauge `Fin`-partition, via
   `finSumFinEquiv` on `card_regGaugeIdx`).

## The three roles (the partition you asked for)

- **CORE** (`= FlatIdx (deepestM H r)`, the middle summand): the **T_s blocks for ALL s** —
  `(i ≥ r ∧ j ≥ r)`. This is the reduced-chain index (`coreAbsorb`'s domain; `deepestCoreF` reads it).
  Precision pin: core = exactly the `T_s` blocks, NOTHING else.

- **REG** (`Fin nReg`, the g125 generators, `nReg = r(H⁰ + Hᴸ − r)`): the BOUNDARY X/Y/Z generators —
  - all `X_s` (the (i<r, j<r) blocks, all layers) — these contribute the **X-sum** generator `Σ_s X_s`
    (g125: the single (0,0)-corner reg generator; L=3 `g0 = w0+w4+w8`),
  - `Y_L` (last-layer Y, s = L−1: the (i<r, j≥r) block),
  - `Z_1` (first-layer Z, s = 0: the (i≥r, j<r) block).
  (Count: `r² + r(Hᴸ−r) + (H⁰−r)r = r(H⁰+Hᴸ) − r² = nReg`. ✓ #91/g125.)

- **GAUGE/SPECTATOR** (`Fin nGauge`): the INTERIOR Y/Z + the redundant X directions — `Y_s` for s≠L−1,
  `Z_s` for s≠0 (and the X-block directions beyond the single X-sum pivot). These are the gauge freedoms
  the spectator slot carries; `regStraighten`/`deepestEPivot` read them (the interior X_s feed the X-sum).

## CAVEAT (the reg-vs-gauge split within X/Y/Z)

`RegGaugeIdx` (step 4) collects ALL X_s/Y_s/Z_s into ONE bucket; the reg-vs-gauge SPLIT within it
(step 5's `Fin nReg ⊕ Fin nGauge`) is via `card_regGaugeIdx` + `finSumFinEquiv` — a CARDINALITY split,
not a per-block role tag. So `deepestRoleIndexEquiv` gives you the reg/gauge `Fin`-partition by COUNT,
but the SEMANTIC "which X/Y/Z entries are the g125 reg generators" (X-sum / Y_L / Z_1) is the content of
#91/g125, NOT read off `deepestRoleIndexEquiv` directly. For `gaugeDecode`'s reshape this is fine — you
reshape (q.1 : reg-coords, q.2.2 : gauge-coords) back to PerLayerGaugeBlocks via `regGaugeSlotEquiv`
(#78, the `(Fin nReg → ℝ) × (Fin nGauge → ℝ) ≃ₜ (RegGaugeIdx → ℝ)` accessor) — feed `(q.1, q.2.2)`, read
per layer s: `X_s = g⟨s, inl (inl (i,j))⟩`, `Y_s = g⟨s, inl (inr (i,j))⟩`, `Z_s = g⟨s, inr (i,j)⟩`.
That accessor (regGaugeSlotEquiv) is the slot→block reshape you build gaugeDecode against; the T-core is
`(split w).2.1` directly (`FlatIdx (deepestM)`).

## IsGaugeSliceDecode (your obligations, both discharge off this map)

- `continuous`: gaugeDecode is a coordinate reshape (the `regGaugeSlotEquiv` ≃ₜ + block projections) ✓.
- `basepoint`: split 0 ↦ all slots 0 ↦ all blocks (X/Y/Z/T) = 0 ✓ (the equivs are linear, 0↦0).
