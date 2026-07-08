**1. Role Partition**

Assume `L ≥ 2`; for `L = 1`, first and last coincide and the boundary cases must be merged.

| layer `s` | `₁₁` | `₁₂` | `₂₁` | `₂₂` |
|---|---|---|---|---|
| `s = 0` | SPEC | SPEC | REG | CORE |
| `0 < s < L-1` | SPEC | SPEC | SPEC | CORE |
| `s = L-1` | REG | REG | SPEC | CORE |

DOF check:  
`REG = (H₀-r)r + r² + r(H_L-r) = r(H₀+H_L-r) = nReg`.  
`CORE = Σ_s (H_s-r)(H_{s+1}-r) = flatDim (H-r)`.  
All interior non-`₂₂` blocks are SPEC; they do not contribute to `nReg`.

**2. Chart Consistency**

Yes, algebraically, but phrase it as a partition of the **chart-output/raw `Q` coordinates**, not of the original input chain `C`. `schurChartRawGen` packs `Q 0 .₂₁ = (P_L)₂₁` and `Q (L-1).₁₁,₁₂ = (P_L)₁₁,₁₂`, so these are exactly the three regular product corners read by `recoverProductGen`. The interior `₁₁/₁₂/₂₁` blocks are inverse-reconstruction/bookkeeping coordinates; `recoverProductGen` ignores them, so SPEC is correct. Lean effort: proving this is mostly dependent-`Fin` readback plumbing, not new algebra.

**3. Slice Value**

Confirmed, with one caveat on dependencies. At `p = 0`, the regular product-corner residuals vanish and the rank-`r` target gives Schur-zero, so the `₂₂` residual is `blockDiagProd Q L = ∏_s Q_s.₂₂`. For `Q = schurChartRawGen C L`, this is `∏_s R_s = blockSchur (partProd C L)` by `blockDiagProd_schurChartRawGen` plus `blockSchur_partProd_asym_fold`, and as core coordinates it is exactly `dlnLoss (H-r)` on the `₂₂` chain. No algebra gap; Lean still needs the general core-readback alignment and target Schur-zero corner facts.

**4. Build Order**

1. Define `RegIdxGen/CoreIdxGen/SpecIdxGen`; reuse `FlatIdx`, `paramsEquivFlat`, `deepestNReg`; prove `card_RegIdxGen = r*(H 0 + H (Fin.last L)-r)`.

2. Build `roleEquivGen` using the pivot family `ι` and `sumSplit`; prove reg/core/spec readbacks. Hardest step: this dependent first/interior/last classifier and core alignment.

3. Build `splitMPGen` and `splitHomeoGen` via the existing `CoreSplitMP.splitOfPartition` pattern; prove MP, measurable embedding, zero, `ContDiff` inverse.

4. Reuse `blockFlatEquivGen` for flat-to-block coordinates; do not re-port the block model. Compose with `schurChartRawGen` and reuse `contDiffAt_schurChartRawGen_entry`.

5. Define `qResidGen` from `recoverProductGen`’s `₂₂` residual; prove `ContDiff` using matrix operations and bumped inverse.

6. Prove the germ split using `recoverProductGen_schurChartRawGen`: regular sum from REG readbacks, residual sum from `qResidGen`, SPEC ignored.

7. Prove slice `hfact` using `blockDiagProd_schurChartRawGen`, `blockSchur_partProd_asym_fold`, core readback, then wire `e`, `hfact`, `hRne` into the residual ≥-leg consumer.