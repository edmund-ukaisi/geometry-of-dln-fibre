import DLNFibre.DLN.RLCT.Validate.DeepestFramedBoundaryDecode

/-!
# `DLNFibre.DLN.RLCT.Validate.DeepestHmoveGen` — the full general-`L` move identity `hmove` (#120 item 2)

Assembles the interior half (`psiSplitRawGen_deepestChain_interior`, `DeepestPsiSplitRawGenMove`) and the
two boundary halves (`psiSplitRawGen_deepestChain_firstLayer` / `_lastLayer`, `DeepestFramedBoundaryDecode`)
into the full function-level move identity

  `deepestChain (framedParamsPivot (psiSplitRawGen q)) = movedC (deepestChain (framedParamsPivot q)) (Z0edit0 …)`

by `funext s; by_cases s < L`: interior/boundary layers dispatch to the three per-layer identities, and the
tail (`s ≥ L`, the block-normal corner default) collapses via `movedC_tail` (the moved edits vanish there,
so `movedC C Z0edit s = C s`, and `deepestChain` is parameter-independent at the tail). This is the exact
`hmove` hypothesis `deepestEFull_sq_sum_eq_of_chain_movedC` (`DeepestHsub3regGen`) consumes for `hsub3reg`.
-/

open Matrix
namespace DLNFibre.DLN.RLCT

set_option linter.unusedSectionVars false

variable {L : ℕ}

/-! ## Tail block-vanishing of the abstract chain (`s ≥ L`, the block-normal corner) -/

/-- The tail `(2,1)` block is zero (`s ≥ L`, the corner default reads `0` off the diagonal). -/
theorem deepestChain_tail_toBlocks₂₁ (H : Fin (L + 1) → ℕ) (r : ℕ)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (A : Params H) (s : ℕ) (hs : ¬ s < L) :
    (deepestChain H r hr A s).toBlocks₂₁ = 0 := by
  funext i j
  rw [deepestChain, deepestChainLayer, dif_neg hs]
  simp only [Matrix.toBlocks₂₁, Matrix.reindex_apply, Matrix.submatrix_apply, deepestChainSplit,
    rThresholdSplit_symm_inr, rThresholdSplit_symm_inl, Matrix.of_apply, Matrix.zero_apply]
  rw [if_neg (by omega)]

/-- The tail `(2,2)` block is zero (`s ≥ L`). -/
theorem deepestChain_tail_toBlocks₂₂ (H : Fin (L + 1) → ℕ) (r : ℕ)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (A : Params H) (s : ℕ) (hs : ¬ s < L) :
    (deepestChain H r hr A s).toBlocks₂₂ = 0 := by
  funext i j
  rw [deepestChain, deepestChainLayer, dif_neg hs]
  simp only [Matrix.toBlocks₂₂, Matrix.reindex_apply, Matrix.submatrix_apply, deepestChainSplit,
    rThresholdSplit_symm_inr, Matrix.of_apply, Matrix.zero_apply]
  rw [if_neg (by omega)]

/-! ## The moved chain at the tail collapses to the original -/

section MovedTail
variable {r : Type*} [Fintype r] [DecidableEq r] {α : Type*} [CommRing α]
  {m : ℕ → Type*} [∀ i, Fintype (m i)] [∀ i, DecidableEq (m i)]

/-- **The moved chain agrees with the original off the used prefix.** For a layer `s ≥ 1` whose `(2,1)` and
`(2,2)` blocks vanish (the block-normal corner default), the moved edits are trivial and
`movedC C Z0edit s = C s`. Consumed by the `hmove` tail case. -/
theorem movedC_tail (C : (s : ℕ) → Matrix (r ⊕ m s) (r ⊕ m (s + 1)) α)
    (Z0edit : Matrix (m 0) r α) (s : ℕ) (hs : 1 ≤ s)
    (h21 : (C s).toBlocks₂₁ = 0) (h22 : (C s).toBlocks₂₂ = 0) :
    movedC C Z0edit s = C s := by
  have hbs : blockSchur (C s) = 0 := by
    rw [blockSchur, h21, h22, Matrix.zero_mul, Matrix.zero_mul, sub_zero]
  have hst : schurTilde C s = 0 := by rw [schurTilde, hbs, Matrix.mul_zero]
  have hue : upEdit C s = 0 := by rw [upEdit, hbs, hst, sub_zero, Matrix.mul_zero]
  obtain ⟨n, rfl⟩ : ∃ n, s = n + 1 := ⟨s - 1, by omega⟩
  have hmy : movedY C (n + 1) = (C (n + 1)).toBlocks₁₂ := by rw [movedY, hue, add_zero]
  have hmz : movedZ C Z0edit (n + 1) = (C (n + 1)).toBlocks₂₁ := rfl
  have hmt : movedT C Z0edit (n + 1) = 0 := by
    rw [movedT, hst, zero_add, hmz, h21, Matrix.zero_mul, Matrix.zero_mul]
  rw [movedC, hmy, hmz, hmt]
  conv_rhs => rw [← Matrix.fromBlocks_toBlocks (C (n + 1)), h22]

end MovedTail

/-! ## The full move identity -/

/-- **The general-`L` move identity `hmove`.** The framed abstract chain of the joint move `psiSplitRawGen`
is the abstract moved chain `movedC` of the base chain (with the `Z0edit0` down-override). Proof:
`funext s; by_cases s < L` — interior layers via the banked interior identity (`hInterior`-trivial frames),
the two boundary layers via the frame-dependent boundary identities, and the tail (`s ≥ L`) via
`movedC_tail`. The IsUnit / triangularity bundle facts (from `deepestPoint_frame_pivot_triangular_exists`)
are threaded as hypotheses. -/
theorem psiSplitRawGen_deepestChain_hmove (H : Fin (L + 1) → ℕ) (r : ℕ)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L) (hL2 : 2 ≤ L)
    (J : Fin r ↪ Fin (H (Fin.last L))) (hJfront : J = frontEmbed H r hr)
    (Pf : (s : Fin L) → Matrix (Fin (H s.castSucc)) (Fin (H s.castSucc)) ℝ)
    (Qf : (s : Fin L) → Matrix (Fin (H s.succ)) (Fin (H s.succ)) ℝ)
    (q : DeepestSplit H r (deepestNGauge H r))
    (hQf0 : Qf (firstLayer hL) = 1) (hPfL : Pf (lastLayer hL) = 1)
    (hPunit : IsUnit (Pf (firstLayer hL))) (hQunit : IsUnit (Qf (lastLayer hL)))
    (hPtri : (Matrix.reindex (rThresholdSplit r (H (firstLayer hL).castSucc) (hr _))
        (rThresholdSplit r (H (firstLayer hL).castSucc) (hr _)) (Pf (firstLayer hL))).toBlocks₁₂ = 0)
    (hP22 : (Matrix.reindex (rThresholdSplit r (H (firstLayer hL).castSucc) (hr _))
        (rThresholdSplit r (H (firstLayer hL).castSucc) (hr _)) (Pf (firstLayer hL))).toBlocks₂₂ = 1)
    (hQtri : (Matrix.reindex (rThresholdSplit r (H (lastLayer hL).succ) (hr _))
        (rThresholdSplit r (H (lastLayer hL).succ) (hr _)) (Qf (lastLayer hL))).toBlocks₂₁ = 0)
    (hQ22 : (Matrix.reindex (rThresholdSplit r (H (lastLayer hL).succ) (hr _))
        (rThresholdSplit r (H (lastLayer hL).succ) (hr _)) (Qf (lastLayer hL))).toBlocks₂₂ = 1)
    (hInterior : ∀ s : Fin L, 0 < (s : ℕ) → (s : ℕ) + 1 < L →
      Pf s = 1 ∧ Qf s = 1) :
    deepestChain H r hr (framedParamsPivot H r hr hL J Pf Qf (psiSplitRawGen H r hr hL J Pf Qf q))
      = movedC (deepestChain H r hr (framedParamsPivot H r hr hL J Pf Qf q))
          (Z0edit0 (deepestChain H r hr (framedParamsPivot H r hr hL J Pf Qf q)) L) := by
  funext s
  by_cases hsL : s < L
  · -- `s < L`: interior or boundary layer.
    set s' : Fin L := ⟨s, hsL⟩ with hs'
    have hsval : (s' : ℕ) = s := rfl
    by_cases hfirst : s' = firstLayer hL
    · have hseq : s = (firstLayer hL : ℕ) := by rw [← hsval, hfirst]
      rw [hseq]
      exact psiSplitRawGen_deepestChain_firstLayer H r hr hL hL2 J Pf Qf q hQf0 hPunit hPtri hP22
    · by_cases hlast : s' = lastLayer hL
      · have hseq : s = (lastLayer hL : ℕ) := by rw [← hsval, hlast]
        rw [hseq]
        exact psiSplitRawGen_deepestChain_lastLayer H r hr hL hL2 J hJfront Pf Qf q hPfL hQunit
          hQtri hQ22
      · -- interior layer.
        have hpos : 0 < (s' : ℕ) := by
          rcases Nat.eq_zero_or_pos (s' : ℕ) with h0 | h0
          · exact absurd (Fin.ext (by simp [firstLayer, h0]) : s' = firstLayer hL) hfirst
          · exact h0
        have hlt : (s' : ℕ) + 1 < L := by
          rcases Nat.lt_or_ge ((s' : ℕ) + 1) L with h | h
          · exact h
          · exact absurd (Fin.ext (by simp only [lastLayer]; have := s'.isLt; omega) : s' = lastLayer hL)
              hlast
        obtain ⟨hP1, hQ1⟩ := hInterior s' hpos hlt
        have := psiSplitRawGen_deepestChain_interior H r hr hL J Pf Qf q s' hfirst hlast hP1 hQ1
        rw [hsval] at this
        exact this
  · -- tail `s ≥ L`: the block-normal corner, moved chain agrees with the original.
    have htail : deepestChain H r hr (framedParamsPivot H r hr hL J Pf Qf
          (psiSplitRawGen H r hr hL J Pf Qf q)) s
        = deepestChain H r hr (framedParamsPivot H r hr hL J Pf Qf q) s := by
      rw [deepestChain, deepestChainLayer, dif_neg hsL, deepestChain, deepestChainLayer, dif_neg hsL]
    rw [htail]
    exact (movedC_tail (deepestChain H r hr (framedParamsPivot H r hr hL J Pf Qf q))
      (Z0edit0 (deepestChain H r hr (framedParamsPivot H r hr hL J Pf Qf q)) L) s (by omega)
      (deepestChain_tail_toBlocks₂₁ H r hr _ s hsL)
      (deepestChain_tail_toBlocks₂₂ H r hr _ s hsL)).symm

end DLNFibre.DLN.RLCT
