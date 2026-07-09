import DLNFibre.DLN.RLCT.Validate.D1GeSeam
import DLNFibre.DLN.RLCT.Validate.D1L2PhiExplClose

/-!
# `DLNFibre.DLN.RLCT.Validate.D1GeHAtVClose` — final close Part A: the general-`L` `hAtV` producer

The general-`L` port of the L = 2 `d1ge_L2_hAtV_explicit_close` (`D1L2ExplChartClose2`): at an
optimal
`v` (`prod H v = B`, `B.rank = r`, `r < H` everywhere) the D1 `≥`-leg per-point producer bound
holds,

    ∃ P : Params (H − r), (nRegGen H r)/2 + rlctAtOn (dlnLoss (H − r) 0) P ≤ rlctAt H (dlnLoss H B)
v.

Assembles the banked pieces: the common pivot (`prefixPivotDomGen`), the corner-elimination chart
germ
(`schur_loss_germ_gen_at_pivot`) + flat chart-transfer (`dln_hchart_flat`), the readout↔residual
seam
(`schurReadout_germ_eq_gen`) + the split homeomorphism (`rlctAtOn_comp_homeomorph`), the
bump-globalised
matrix inverse `G` (`exists_contDiff_matrixInv_eventuallyEq`) with the pivot corner facts, the
Schur-zero
(`Core.schur_complement_zero_of_rank_le`), then the residual consumer
`d1ge_hAtV_of_qResid_chart_genL`
(gfgh, which internalises the `e`/slice/`hRne` reconstruction). Part B (the deepest-side value + the
wired `≥`-leg obligation) is the controller's.
-/

open Matrix Filter MeasureTheory
open scoped ENNReal Topology BigOperators
namespace DLNFibre.DLN.RLCT

variable {L : ℕ}

set_option maxHeartbeats 1000000 in
/-- **The general-`L` D1 `≥`-leg `hAtV` producer at an optimal `v`.** Direct mirror of
`d1ge_L2_hAtV_explicit_close`; the `e`/slice/`hRne` reconstruction is internalised by the residual
consumer `d1ge_hAtV_of_qResid_chart_genL`, so this produces the chart-transfer `hchart` (germ +
seam +
split homeo) and the `G`/corner/Schur-zero data. -/
theorem d1ge_hAtV_explicit_close_gen (H : Fin (L + 1) → ℕ) (r : ℕ)
    (B : Matrix (Fin (H 0)) (Fin (H (Fin.last L))) ℝ) (v : Params H)
    (hopt : prod H v = B) (hB : B.rank = r) (hpos : ∀ s : Fin (L + 1), r < H s) (hL : 1 ≤ L) :
    ∃ P : Params (fun s => H s - r),
      (nRegGen H r : ℝ≥0∞) / 2
          + rlctAtOn (fun A : Params (fun s => H s - r) =>
              dlnLoss (fun s => H s - r)
                (0 : Matrix (Fin ((fun s => H s - r) 0))
                  (Fin ((fun s => H s - r) (Fin.last L))) ℝ) A)
              P
        ≤ rlctAt H (dlnLoss H B) v := by
  classical
  obtain ⟨last, rfl⟩ : ∃ last, L = last + 1 := ⟨L - 1, by omega⟩
  have hrle : ∀ s : Fin (last + 1 + 1), r ≤ H s := fun s => (hpos s).le
  obtain ⟨ι, hι, hdet⟩ := prefixPivotDomGen H r hrle v B hopt hB
  set hr : ∀ s : Fin (last + 1 + 1), r ≤ H s := r_le_H_gen ι hι with hrdef
  have hvsymm : (paramsEquivFlatLinear H).symm ((paramsEquivFlat H) v) = v := by
    rw [paramsEquivFlatLinear_symm_coe_gen]; exact (paramsEquivFlat H).symm_apply_apply v
  -- the prefix pivots on `genChain … v`.
  have hPart : ∀ k, k ≤ last + 1 →
      ((partProd (genChain H r hr ι hι v) k).toBlocks₁₁).det ≠ 0 := fun k hk => hdet k (by omega)
  -- the germ + flat chart transfer.
  obtain ⟨Φ, f', hcd, hfd, hfix, hg⟩ := schur_loss_germ_gen_at_pivot H r hr B v ι hι hPart
  set P₀ := blockFlatEquivGen H r ι hι ((paramsEquivFlat H) v) with hP0
  set C₀ := schurChartRawSelfGen H r hr ι hι P₀ with hC0
  set Br := Matrix.reindex (sumSplit (ι 0) (hι 0)).symm
    (genChainCol H r hr ι hι (last + 1) (Nat.lt_succ_self _)) B with hBrdef
  have hrlct : rlctAt H (dlnLoss H B) v = rlctAtOn (schurReadoutF_gen H r hr ι hι C₀ Br) 0 :=
    dln_hchart_flat H B v _ Φ f' hcd hfd hfix hg
  -- `Br = partProd (genChain … v) (last+1)`; its pivot corners are the prefix minors.
  have hBrpp : Br = partProd (genChain H r hr ι hι v) (last + 1) := by
    rw [hBrdef, ← hopt]; exact reindex_prod_eq_genPartProd H r hr ι hι v
  have hbtc : ∀ k, k < last + 1 →
      blockToChainGen H r hr ι hι P₀ k = genChain H r hr ι hι v k := fun k hk => by
    rw [hP0, blockToChainGen_blockFlatEquivGen H r hr ι hι _ k hk, hvsymm]
  have hppeq : partProd (blockToChainGen H r hr ι hι P₀) (last + 1)
      = partProd (genChain H r hr ι hι v) (last + 1) :=
    partProd_congr _ _ (last + 1) (fun k hk => hbtc k hk)
  have hC0chain : ∀ k, k < last + 1 → blockToChainGen H r hr ι hι C₀ k
      = schurChartRawGen (blockToChainGen H r hr ι hι P₀) (last + 1) k := fun k hk => by
    rw [hC0]; simp only [schurChartRawSelfGen]
    exact blockToChainGen_chainToBlockGen H r hr ι hι _ k hk
  -- the three pivot corner facts (`blockToChainGen C₀` corners = `Br` corners).
  have h11 : (blockToChainGen H r hr ι hι C₀ last).toBlocks₁₁ = Br.toBlocks₁₁ := by
    rw [hC0chain last (by omega), schurChartRawGen_toBlocks₁₁, hppeq]
    exact congrArg Matrix.toBlocks₁₁ hBrpp.symm
  have h12 : (blockToChainGen H r hr ι hι C₀ last).toBlocks₁₂ = Br.toBlocks₁₂ := by
    rw [hC0chain last (by omega), schurChartRawGen_toBlocks₁₂, hppeq]
    exact congrArg Matrix.toBlocks₁₂ hBrpp.symm
  have h21 : (blockToChainGen H r hr ι hι C₀ 0).toBlocks₂₁ = Br.toBlocks₂₁ := by
    rw [hC0chain 0 (by omega), schurChartRawGen_toBlocks₂₁_zero, hppeq]
    exact congrArg Matrix.toBlocks₂₁ hBrpp.symm
  -- the pivot minor is nonsingular.
  have hBr11det : (Br.toBlocks₁₁).det ≠ 0 := by
    rw [hBrpp]; exact hdet (last + 1) (Nat.lt_succ_self _)
  -- the bump-globalised inverse `G`.
  obtain ⟨G, hGcd, hGeq⟩ := exists_contDiff_matrixInv_eventuallyEq Br.toBlocks₁₁ hBr11det
  have hGeval : G (Br.toBlocks₁₁) = (Br.toBlocks₁₁)⁻¹ := hGeq.eq_of_nhds
  -- Schur-zero for `Br` (from `B.rank ≤ r`).
  have hrank : (Matrix.fromBlocks Br.toBlocks₁₁ Br.toBlocks₁₂ Br.toBlocks₂₁ Br.toBlocks₂₂).rank
      ≤ r := by rw [Matrix.fromBlocks_toBlocks, hBrdef, Matrix.rank_reindex]; exact hB.le
  letI : Invertible (Br.toBlocks₁₁) := invertibleOfDetNeZero hBr11det
  have hschur : Br.toBlocks₂₂ = Br.toBlocks₂₁ * (Br.toBlocks₁₁)⁻¹ * Br.toBlocks₁₂ := by
    have := Core.schur_complement_zero_of_rank_le Br.toBlocks₁₁ Br.toBlocks₁₂ Br.toBlocks₂₁
      Br.toBlocks₂₂ hrank
    rwa [Matrix.invOf_eq_nonsing_inv] at this
  -- the chart-transfer `hchart` (germ readout → seam split → split-homeo change of variable).
  have hchart : rlctAt H (dlnLoss H B) v
      = rlctAtOn (fun p : (Fin (nRegGen H r) → ℝ)
          × ((Fin (flatDim (fun s => H s - r)) → ℝ) × (Fin (specDimGen ι hι hL) → ℝ)) =>
            (∑ i, p.1 i ^ 2) + (∑ i, qResidGen ι hι hL C₀ Br.toBlocks₂₂ G p i ^ 2))
        ((0 : Fin (nRegGen H r) → ℝ),
          (0 : (Fin (flatDim (fun s => H s - r)) → ℝ) × (Fin (specDimGen ι hι hL) → ℝ))) := by
    rw [hrlct, rlctAtOn_congr_germ _ _ _
      (schurReadout_germ_eq_gen ι hι hL C₀ Br G hGeq h11 h12 h21)]
    have hcomp := rlctAtOn_comp_homeomorph (splitHomeoGen ι hι hL)
      (measurePreserving_splitHomeoGen ι hι hL) (measurableEmbedding_splitHomeoGen ι hι hL)
      (fun p : (Fin (nRegGen H r) → ℝ)
          × ((Fin (flatDim (fun s => H s - r)) → ℝ) × (Fin (specDimGen ι hι hL) → ℝ)) =>
        (∑ i, p.1 i ^ 2) + (∑ i, qResidGen ι hι hL C₀ Br.toBlocks₂₂ G p i ^ 2))
      (0 : Fin (flatDim H) → ℝ)
    rw [splitHomeoGen_zero] at hcomp
    exact hcomp
  exact d1ge_hAtV_of_qResid_chart_genL ι hι hL B v hpos C₀ Br G hGcd hGeval h11 h12 h21 hschur
    hchart

end DLNFibre.DLN.RLCT
