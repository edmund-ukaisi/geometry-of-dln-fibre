**Sub-Lemma Skeleton**

1. **`deepest_regular_core_r0`**  
   `r = 0 → rlctAt H (dlnLoss H B) (deepestPoint H 0 B hB hr hL) = rlctAtOn (dlnLoss H 0) (0 : Params H)`  
   Engine: `Matrix.rank_eq_zero` / local `rank_zero_eq_zero` verify export, `deepestPoint_isDeep`, `rlctAtOn_eq_rlctAt`. Difficulty S.

2. **`deepestPoint_is_rank_exact`**  
   `(deepestPoint_isDeep H r B hB hr hL).2 : ∀ s : Fin L, ((deepestPoint ...) s).rank = r`  
   Engine: already green theorem `deepestPoint_isDeep`. Difficulty S.

3. **`deepest_gauge_chart_exists`**  
   `∃ Γ : DeepestGaugeChart H r B hB hr hL, True`  
   Engine: new heavy algebra from Aoyagi Thm 3 + `block_elimination`/rank-exact layer bases. Difficulty L/XL.

4. **`deepest_loss_in_gauge_coords`**  
   From `Γ`: pullback germ of `dlnLoss H B` equals  
   `fun x => (∑ i, reg Γ x i ^ 2) + (Real.sqrt (dlnLoss M 0 (red Γ x)))^2`, up to the chart unit/Jacobian routing.  
   Engine: new exact block-product algebra; `dlnLoss_nonneg` for `sqrt_sq`. Difficulty L.

5. **`deepest_nonMP_chart_transport_unit`**  
   `rlctAt ... = rlctAtOn (pulledBackLoss Γ) 0` for the non-MP chart, with bounded positive Jacobian unit explicit.  
   Engine: `weightedThreshold_transport` verify use-site + bounded-unit peel; do not use `rlctAtOn_comp_homeomorph` except for MP linear/flat pieces. Difficulty M.

6. **`deepest_regular_smooth_split`**  
   `rlctAtOn (fun p : (Fin nReg → ℝ) × Y => (∑ i, p.1 i^2) + G p.2^2) (0,y0) = nReg/2 + rlctAtOn (fun y => G y^2) y0`  
   Engine: `rlct_additive_smooth_block`; `G := sqrt ∘ dlnLoss M 0`. Difficulty M.

7. **`deepest_reduced_core_identification`**  
   `rlctAtOn (fun y => (Real.sqrt (dlnLoss M 0 y))^2) (0 : Params M) = rlctAtOn (dlnLoss M 0) 0`  
   Engine: `dlnLoss_nonneg`, `rlctAtOn_germ_local`, `paramsEquivFlat`/`rlctAtOn_comp_homeomorph` only for MP flat transport. Difficulty S/M.

**Pinned Chart Interface**

```lean
structure DeepestGaugeChart ... where
  M : Fin (L+1) → ℕ := fun s => H s - r
  nReg : ℕ := r * (H 0 + H (Fin.last L) - r)
  nGauge : ℕ
  split :
    (Fin (flatDim H) → ℝ) ≃ₜ
      ((Fin nReg → ℝ) × ((Fin (flatDim M) → ℝ) × (Fin nGauge → ℝ)))
  chart : (Fin (flatDim H) → ℝ) ≃ₜ (Fin (flatDim H) → ℝ)
  Dchart : (Fin (flatDim H) → ℝ) →
    ((Fin (flatDim H) → ℝ) →L[ℝ] (Fin (flatDim H) → ℝ))
  chart_zero :
    (paramsEquivFlat H).symm (chart 0) = deepestPoint H r B hB hr hL
  hasDeriv : ∀ x, HasFDerivAt chart (Dchart x) x
  jac_unit :
    ∃ U ∈ 𝓝 (0 : Fin (flatDim H) → ℝ), ∃ a b, 0 < a ∧
      ∀ x ∈ U, a ≤ |(Dchart x).det| ∧ |(Dchart x).det| ≤ b
  loss_form :
    (fun x => dlnLoss H B ((paramsEquivFlat H).symm (chart x))) =ᶠ[𝓝 0]
      fun x =>
        let q := split x
        (∑ i, q.1 i ^ 2) +
          dlnLoss M 0 ((paramsEquivFlat M).symm q.2.1)
```

**Hardest Piece**

`deepest_gauge_chart_exists` + `deepest_loss_in_gauge_coords`. It should be decomposed further and needs a pp-hall exact-algebra certificate: bases/block pivots, triangular solve, product-block identity, determinant unit, and spectator-coordinate accounting.

**Scope Cut**

Best cut: prove the chart for `w0` with `IsDeepLayers H r B w0`, then apply `deepestPoint_isDeep`. A 2-factor block multiplication lemma folded over `L` should reduce algebra expansion.

**r=0**

Clean: `hB : B.rank = 0` gives `B = 0`; rank-exact zero layers force `deepestPoint = 0`; `M = H`, `nReg = 0`; finish by `rlctAtOn_eq_rlctAt`.