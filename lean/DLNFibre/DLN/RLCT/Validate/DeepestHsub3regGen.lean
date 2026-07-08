import DLNFibre.DLN.RLCT.Validate.DeepestFinBridgeGen
import DLNFibre.DLN.RLCT.Validate.DeepestGaugeConstruction

/-!
# `DLNFibre.DLN.RLCT.Validate.DeepestHsub3regGen` — the concrete general-`L` reg-preservation (`hsub3reg`)

Item 1 of the cert §6 build order for #120 `hstep2`. Assembles the banked `Fin`-side bridge
(`DeepestFinBridgeGen.reindexECol_regBlocks_eq_of_chain_movedC`, which transports the abstract
Invariant A of `regBlocks_movedC` to the DLN framed products, conditional on the abstract move identity)
onto the direct residual expansion `deepestEFull_sq_sum_eq_blocks` (`DeepestGaugeConstruction`) to prove
the concrete reg-preservation germ: under the joint move (encoded abstractly as the chain identity
`deepestChain (framedParamsPivot Aψ) = movedC (deepestChain (framedParamsPivot Aq)) (Z0edit0 …)`), the
`deepestEFull²`-sum reg energy is invariant.

## The two pieces

* **Item 1(a) — the pivot-column reconciliation.** `deepestEFull_sq_sum_eq_blocks` reads the residual
  blocks off `reindex (rThr 0) (pivotThresholdSplit … J) (prod …)`; the bridge produces block agreements
  off `reindex (rThr 0) (deepestChainCol L) (prod …)`. At `J = frontEmbed` the pivot split IS the
  threshold split (`pivotThresholdSplit_frontEmbed`), and the last-layer threshold split reconciles with
  `deepestChainCol L` up to a fixed `finCongr` on the reduced-width (`inr`) columns
  (`deepestChainWidth H L = H (Fin.last L)`). The `{11,21}` inl-column blocks transfer directly; the
  `{12}` inr-column block transfers via the reduced-width relabel — SAME relabel for `Aψ` and `Aq`, so
  agreement survives.

* **Item 1(b) — the direct residual route.** `deepestEFull_sq_sum_eq_blocks` expresses
  `∑ deepestEFull(q)²` as the sum of squares of the `{11−1, 12, 21}` residual blocks of the FRAMED
  product `prod (framedParamsPivot … q)` (NOT the raw decode), so once the three blocks agree between the
  moved and base points the sums are equal — the `endpointP0/endpointQL` frame machinery
  (`resid_regBlocks_eq_of_mid_agree`) is unnecessary on this route.

## Status
Conditional on the abstract move identity (`hmove`, the concrete `psiSplitRawGen` design — Item 2) and
the base-chain pivot/partial-pivot/pivot-mix `IsUnit` hypotheses (satisfiable near the deepest point, the
`corM`-corner tail). Pure `Matrix`/`Equiv`/`Ring` algebra over `ℝ`. No `deepestSplit` analysis.
-/

open Matrix
namespace DLNFibre.DLN.RLCT

set_option linter.unusedSectionVars false

variable {L : ℕ}

/-! ## Item 1(a) — the pivot-front / deepestChainCol column reconciliation -/

/-- The chain width at the last index is the last-layer width (`min L L = L`). -/
theorem deepestChainWidth_last (H : Fin (L + 1) → ℕ) :
    deepestChainWidth H L = H (Fin.last L) := by
  rw [deepestChainWidth]
  congr 1
  apply Fin.ext
  simp [Fin.val_last]

/-- The last-layer threshold split's `inl` inverse coincides with `deepestChainCol L`'s (both select the
first `r` columns). Stated across the defeq widths `H (Fin.last L)` / `H ⟨L, Nat.lt_succ_self L⟩`. -/
theorem chainCol_symm_inl_eq (H : Fin (L + 1) → ℕ) (r : ℕ)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (j : Fin r) :
    (deepestChainCol H r hr L (Nat.lt_succ_self L)).symm (Sum.inl j)
      = (rThresholdSplit r (H (Fin.last L)) (hr (Fin.last L))).symm (Sum.inl j) := by
  rw [deepestChainCol, Equiv.symm_trans_apply, deepestChainSplit, rThresholdSplit_symm_inl,
    rThresholdSplit_symm_inl, finCongr_symm, finCongr_apply]
  apply Fin.ext
  simp [Fin.castLE, Fin.cast]

/-- The last-layer threshold split's `inr` inverse coincides with `deepestChainCol L`'s, up to the
reduced-width relabel `finCongr` (`H (Fin.last L) − r = deepestChainWidth H L − r`). -/
theorem chainCol_symm_inr_eq (H : Fin (L + 1) → ℕ) (r : ℕ)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (j : Fin (deepestChainWidth H L - r)) :
    (deepestChainCol H r hr L (Nat.lt_succ_self L)).symm (Sum.inr j)
      = (rThresholdSplit r (H (Fin.last L)) (hr (Fin.last L))).symm
          (Sum.inr (finCongr (by rw [deepestChainWidth_last]) j)) := by
  rw [deepestChainCol, Equiv.symm_trans_apply, deepestChainSplit, rThresholdSplit_symm_inr,
    rThresholdSplit_symm_inr, finCongr_symm, finCongr_apply]
  apply Fin.ext
  simp [Fin.cast]

/-- The `{11}` residual block of the pivot-front reindex equals the `deepestChainCol L` one (uniform in
`A`): both read `inl` columns, which agree. -/
theorem pivotFront_toBlocks₁₁_eq_chainCol (H : Fin (L + 1) → ℕ) (r : ℕ)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (A : Params H) :
    (Matrix.reindex (rThresholdSplit r (H 0) (hr 0))
        (rThresholdSplit r (H (Fin.last L)) (hr (Fin.last L))) (prod H A)).toBlocks₁₁
      = (Matrix.reindex (rThresholdSplit r (H 0) (hr 0))
          (deepestChainCol H r hr L (Nat.lt_succ_self L)) (prod H A)).toBlocks₁₁ := by
  funext i j
  simp only [Matrix.toBlocks₁₁, Matrix.reindex_apply, Matrix.submatrix_apply, Matrix.of_apply]
  congr 1

/-- The `{21}` residual block of the pivot-front reindex equals the `deepestChainCol L` one (`inl`
column). -/
theorem pivotFront_toBlocks₂₁_eq_chainCol (H : Fin (L + 1) → ℕ) (r : ℕ)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (A : Params H) :
    (Matrix.reindex (rThresholdSplit r (H 0) (hr 0))
        (rThresholdSplit r (H (Fin.last L)) (hr (Fin.last L))) (prod H A)).toBlocks₂₁
      = (Matrix.reindex (rThresholdSplit r (H 0) (hr 0))
          (deepestChainCol H r hr L (Nat.lt_succ_self L)) (prod H A)).toBlocks₂₁ := by
  funext i j
  simp only [Matrix.toBlocks₂₁, Matrix.reindex_apply, Matrix.submatrix_apply, Matrix.of_apply]
  congr 1

/-- The `{12}` residual block of the pivot-front reindex is the `deepestChainCol L` one with its `inr`
columns relabelled by the reduced-width `finCongr` (`H (Fin.last L) − r = deepestChainWidth H L − r`). -/
theorem pivotFront_toBlocks₁₂_eq_chainCol (H : Fin (L + 1) → ℕ) (r : ℕ)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (A : Params H) :
    (Matrix.reindex (rThresholdSplit r (H 0) (hr 0))
        (rThresholdSplit r (H (Fin.last L)) (hr (Fin.last L))) (prod H A)).toBlocks₁₂
      = ((Matrix.reindex (rThresholdSplit r (H 0) (hr 0))
          (deepestChainCol H r hr L (Nat.lt_succ_self L)) (prod H A)).toBlocks₁₂).submatrix id
          (finCongr (by rw [deepestChainWidth_last])) := by
  funext i j
  simp only [Matrix.toBlocks₁₂, Matrix.reindex_apply, Matrix.submatrix_apply, Matrix.of_apply, id_eq]
  congr 1

/-! ## Item 1(b) — the reg-energy invariance under the abstract move (conditional `hsub3reg`) -/

/-- **The concrete general-`L` reg-preservation germ, conditional on the abstract move identity.** If the
abstract chain of the framed moved point `q₁` is the joint move (`movedC … (Z0edit0 …)`) of the abstract
chain of the framed base point `q₂` (the `hmove` identity — the concrete `psiSplitRawGen` design, Item 2),
and the base chain satisfies the pivot / partial-pivot / pivot-mix `IsUnit` hypotheses (satisfiable near
the deepest point), then the `deepestEFull²`-sum reg energy is invariant: `∑ deepestEFull(q₁)² =
∑ deepestEFull(q₂)²`. Combines the banked `Fin`-side transport
(`reindexECol_regBlocks_eq_of_chain_movedC`, giving the residual-block agreements at the
`deepestChainCol L` split) with the direct residual expansion (`deepestEFull_sq_sum_eq_blocks`) via the
`J = frontEmbed` pivot-column reconciliation (`pivotFront_toBlocks·_eq_chainCol`). This is the algebraic
heart of `hsub3reg`, isolating the remaining geometry to exactly the move identity. -/
theorem deepestEFull_sq_sum_eq_of_chain_movedC (H : Fin (L + 1) → ℕ) (r : ℕ)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L)
    (J : Fin r ↪ Fin (H (Fin.last L))) (hJfront : J = frontEmbed H r hr)
    (Pf : (s : Fin L) → Matrix (Fin (H s.castSucc)) (Fin (H s.castSucc)) ℝ)
    (Qf : (s : Fin L) → Matrix (Fin (H s.succ)) (Fin (H s.succ)) ℝ)
    (q₁ q₂ : DeepestSplit H r (deepestNGauge H r))
    (hmove : deepestChain H r hr (framedParamsPivot H r hr hL J Pf Qf q₁)
        = movedC (deepestChain H r hr (framedParamsPivot H r hr hL J Pf Qf q₂))
            (Z0edit0 (deepestChain H r hr (framedParamsPivot H r hr hL J Pf Qf q₂)) L))
    (hP : ∀ k, IsUnit (partProd (deepestChain H r hr
        (framedParamsPivot H r hr hL J Pf Qf q₂)) k).toBlocks₁₁)
    (hA : ∀ k, IsUnit (deepestChain H r hr
        (framedParamsPivot H r hr hL J Pf Qf q₂) k).toBlocks₁₁)
    (hN : ∀ k, IsUnit (nMix (deepestChain H r hr
        (framedParamsPivot H r hr hL J Pf Qf q₂)) k)) :
    (∑ i, (deepestEFull H r hr hL J Pf Qf q₁ i) ^ 2)
      = ∑ i, (deepestEFull H r hr hL J Pf Qf q₂ i) ^ 2 := by
  subst hJfront
  obtain ⟨h11, h12, h21⟩ := reindexECol_regBlocks_eq_of_chain_movedC H r hr hL
    (framedParamsPivot H r hr hL (frontEmbed H r hr) Pf Qf q₂)
    (framedParamsPivot H r hr hL (frontEmbed H r hr) Pf Qf q₁) hmove hP hA hN
  rw [deepestEFull_sq_sum_eq_blocks H r hr hL (frontEmbed H r hr) Pf Qf q₁,
    deepestEFull_sq_sum_eq_blocks H r hr hL (frontEmbed H r hr) Pf Qf q₂,
    pivotThresholdSplit_frontEmbed H r hr]
  simp only [pivotFront_toBlocks₁₁_eq_chainCol, pivotFront_toBlocks₂₁_eq_chainCol,
    pivotFront_toBlocks₁₂_eq_chainCol]
  rw [h11, h12, h21]

end DLNFibre.DLN.RLCT
