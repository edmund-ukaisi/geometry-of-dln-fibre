import DLNFibre.DLN.RLCT.Validate.D1GeSchurResidual

/-!
# `DLNFibre.DLN.RLCT.Validate.D1GeSeam` — the Schur-readout germ identity (piece iv seam)

The seam reconciling geleg8's block-chart Frobenius readout `schurReadoutF_gen` (`D1GeGlobalize`)
with the explicit `₂₂` Schur residual `qResidGen` (`D1GeSchurResidual`). The general-`L` port of the
L = 2 `schurReadout_germ_eq` (`D1L2ExplChartClose2`):

    schurReadoutF_gen … C₀ Br =ᶠ[𝓝 0]
      fun x => (∑ i, (splitMPGen … x).1 i ²) + ∑ i, (qResidGen … C₀ Br.toBlocks₂₂ G (splitMPGen …
x)) i ²

Near the flat origin the readout splits into the regular `∑ p²` (the three regular block corners of
`recoverProductGen`, = the `splitMPGen` reg coordinates via `reg_readback_gen` + shift-zero) plus
the
`₂₂` Schur residual `∑ qResidGen²` (the `M11⁻¹ → G` bump-swap, valid near the base pivot). The reg
corners come through `blockToChainGen` at `deepestChainWidth`, so the ₁₂/₂₁ match reindexes the
chain
widths against the `H`-width reg readbacks (the `vertexInr` bridge, absent at L = 2).
-/

open Matrix Filter
open scoped Topology BigOperators
namespace DLNFibre.DLN.RLCT

section Helpers
variable {L : ℕ} {H : Fin (L + 1) → ℕ} {r : ℕ}
  (ι : (v : Fin (L + 1)) → Fin r → Fin (H v)) (hι : ∀ v, Function.Injective (ι v)) (hL : 1 ≤ L)

/-- **`qBlockGen` at a `splitMPGen` point re-centres to `blockFlatEquivGen x + C₀`.** General-`L`
port of `qBlock_splitMP`. -/
theorem qBlockGen_splitMPGen (C₀ : BlockParamsGen H r) (x : Fin (flatDim H) → ℝ) :
    qBlockGen ι hι hL C₀ (splitMPGen ι hι hL x) = blockFlatEquivGen H r ι hι x + C₀ := by
  rw [qBlockGen, ← splitHomeoGen_apply, Homeomorph.symm_apply_apply]

/-- **The regular sum-of-squares readback** (general `L`): `∑ (splitMPGen x).1²` is the three
regular
block corners of `blockFlatEquivGen x` — first layer's `₂₁`, last layer's `₁₁`/`₁₂` (the last column
`finCongr`-cast to the `H (last L)` width). General-`L` port of `reg_readback`. -/
theorem reg_readback_gen (x : Fin (flatDim H) → ℝ) :
    ∑ i, (splitMPGen ι hι hL x).1 i ^ 2
      = (∑ a : Fin (H 0 - r), ∑ k : Fin r,
            ((blockFlatEquivGen H r ι hι x (firstLayer hL)).toBlocks₂₁ a k) ^ 2)
        + ((∑ k : Fin r, ∑ k' : Fin r,
              ((blockFlatEquivGen H r ι hι x (lastLayer hL)).toBlocks₁₁ k k') ^ 2)
          + (∑ k : Fin r, ∑ b : Fin (H (Fin.last L) - r),
              ((blockFlatEquivGen H r ι hι x (lastLayer hL)).toBlocks₁₂ k
                (finCongr (by rw [H_lastLayer_succ H hL]) b)) ^ 2)) := by
  have hstep : ∀ i : Fin (nRegGen H r), (splitMPGen ι hι hL x).1 i
      = x (Fintype.equivFin (FlatIdx H)
          (roleEquivGen ι hι hL (Sum.inl (regEquivFinGen ι hι i)))) := by
    intro i; rw [splitMPGen_reg, e_idxGen_reg]
  simp_rw [hstep]
  rw [Equiv.sum_comp (regEquivFinGen ι hι)
    (fun ρ => (x (Fintype.equivFin (FlatIdx H)
      (roleEquivGen ι hι hL (Sum.inl ρ)))) ^ 2)]
  simp only [Fintype.sum_sum_type, Fintype.sum_prod_type, reg_entry_first₂₁_gen,
    reg_entry_last₁₁_gen, reg_entry_last₁₂_gen]
  rw [Finset.sum_add_distrib]

end Helpers

/-! ## The seam — `schurReadout_germ_eq_gen` -/

set_option maxHeartbeats 1000000 in
/-- **The general-`L` Schur-readout germ identity.** Near the flat origin, the block-chart Frobenius
readout `schurReadoutF_gen` splits into the regular `∑ p²` (the three regular block corners of
`recoverProductGen`, = the `splitMPGen` reg coordinates via `reg_readback_gen` + the shift-zero
corner
facts `h11/h12/h21`) plus the `₂₂` Schur residual `∑ qResidGen²` (the `M11⁻¹ → G` bump-swap, valid
near the base pivot `Br.toBlocks₁₁`). General-`L` port of `schurReadout_germ_eq`
(`D1L2ExplChartClose2`);
the reg corners come through `blockToChainGen` at `deepestChainWidth`, so the ₁₂/₂₁ match reindexes
the
chain widths against the `H`-width reg readbacks (`vertexInr`). -/
theorem schurReadout_germ_eq_gen {last : ℕ} {H : Fin (last + 1 + 1) → ℕ} {r : ℕ}
    (ι : (v : Fin (last + 1 + 1)) → Fin r → Fin (H v)) (hι : ∀ v, Function.Injective (ι v))
    (hL : 1 ≤ last + 1) (C₀ : BlockParamsGen H r)
    (Br : Matrix (Fin r ⊕ Fin (deepestChainWidth H 0 - r))
      (Fin r ⊕ Fin (deepestChainWidth H (last + 1) - r)) ℝ)
    (G : Matrix (Fin r) (Fin r) ℝ → Matrix (Fin r) (Fin r) ℝ)
    (hGinv : G =ᶠ[𝓝 (Br.toBlocks₁₁)] (fun M => M⁻¹))
    (h11 : (blockToChainGen H r (r_le_H_gen ι hι) ι hι C₀ last).toBlocks₁₁ = Br.toBlocks₁₁)
    (h12 : (blockToChainGen H r (r_le_H_gen ι hι) ι hι C₀ last).toBlocks₁₂ = Br.toBlocks₁₂)
    (h21 : (blockToChainGen H r (r_le_H_gen ι hι) ι hι C₀ 0).toBlocks₂₁ = Br.toBlocks₂₁) :
    schurReadoutF_gen H r (r_le_H_gen ι hι) ι hι C₀ Br
      =ᶠ[𝓝 (0 : Fin (flatDim H) → ℝ)]
        fun x => (∑ i, (splitMPGen ι hι hL x).1 i ^ 2)
          + ∑ i, (qResidGen ι hι hL C₀ Br.toBlocks₂₂ G (splitMPGen ι hι hL x)) i ^ 2 := by
  classical
  set b := blockFlatEquivGen H r ι hι with hb
  -- width bridge (`H (last L)` = `H lastLayer.succ`).
  have hwlast : H (Fin.last (last + 1)) - r = H (lastLayer hL).succ - r := by
    rw [H_lastLayer_succ H hL]
  -- continuity of the base pivot `M11(x)` and its value at `0`.
  have hbc : Continuous (fun x => b x) := b.continuous
  have hcont11 : Continuous
      (fun x => (blockToChainGen H r (r_le_H_gen ι hι) ι hι (b x + C₀) last).toBlocks₁₁) := by
    refine continuous_matrix (fun i j => ?_)
    have heq : (fun x => (blockToChainGen H r (r_le_H_gen ι hι) ι hι (b x + C₀) last).toBlocks₁₁
          i j)
        = fun x => ((b x + C₀) ⟨last, by omega⟩) (Sum.inl i) (Sum.inl j) := by
      funext x; rw [blockToChainGen_toBlocks₁₁ ι hι (b x + C₀) last (by omega)]; rfl
    rw [heq]
    exact ((continuous_apply (⟨last, by omega⟩ : Fin (last + 1))).comp
      (hbc.add continuous_const)).matrix_elem (Sum.inl i) (Sum.inl j)
  have hM11val : (blockToChainGen H r (r_le_H_gen ι hι) ι hι (b 0 + C₀) last).toBlocks₁₁
      = Br.toBlocks₁₁ := by rw [map_zero, zero_add]; exact h11
  have hswap : ∀ᶠ x in 𝓝 (0 : Fin (flatDim H) → ℝ),
      G ((blockToChainGen H r (r_le_H_gen ι hι) ι hι (b x + C₀) last).toBlocks₁₁)
        = ((blockToChainGen H r (r_le_H_gen ι hι) ι hι (b x + C₀) last).toBlocks₁₁)⁻¹ :=
    (hcont11.tendsto' _ _ hM11val).eventually hGinv
  -- a generic `Sum × Sum` sum-of-squares split.
  have hsplit : ∀ (M : Matrix (Fin r ⊕ Fin (deepestChainWidth H 0 - r))
        (Fin r ⊕ Fin (deepestChainWidth H (last + 1) - r)) ℝ),
      (∑ A, ∑ BB, (M A BB) ^ 2)
        = (∑ k : Fin r, ∑ k' : Fin r, (M (Sum.inl k) (Sum.inl k')) ^ 2)
          + (∑ k : Fin r, ∑ b : Fin (deepestChainWidth H (last + 1) - r),
              (M (Sum.inl k) (Sum.inr b)) ^ 2)
          + ((∑ a : Fin (deepestChainWidth H 0 - r), ∑ k : Fin r,
                (M (Sum.inr a) (Sum.inl k)) ^ 2)
            + (∑ a : Fin (deepestChainWidth H 0 - r),
                ∑ b : Fin (deepestChainWidth H (last + 1) - r),
                (M (Sum.inr a) (Sum.inr b)) ^ 2)) := by
    intro M
    rw [Fintype.sum_sum_type]
    simp only [Fintype.sum_sum_type]
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
  filter_upwards [hswap] with x hx
  set Q := blockToChainGen H r (r_le_H_gen ι hι) ι hι (b x + C₀) with hQ
  -- the `₂₂` residual sum equals the readout's `₂₂` corner (via `qResid_sq_sum_gen` + the swap).
  have hq22 : ∑ i, (qResidGen ι hι hL C₀ Br.toBlocks₂₂ G (splitMPGen ι hι hL x)) i ^ 2
      = ∑ a : Fin (deepestChainWidth H 0 - r),
          ∑ bb : Fin (deepestChainWidth H (last + 1) - r),
          ((Q 0).toBlocks₂₁ * (Q last).toBlocks₁₁⁻¹ * (Q last).toBlocks₁₂
            + blockDiagProd Q (last + 1) - Br.toBlocks₂₂) a bb ^ 2 := by
    rw [qResid_sq_sum_gen]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun bb _ => ?_
    simp only [qResidMatGen, qChainGen, qBlockGen_splitMPGen, ← hb, ← hQ]
    change ((Q 0).toBlocks₂₁ * G (Q last).toBlocks₁₁ * (Q last).toBlocks₁₂
          + blockDiagProd Q (last + 1) - Br.toBlocks₂₂) a bb ^ 2
        = ((Q 0).toBlocks₂₁ * (Q last).toBlocks₁₁⁻¹ * (Q last).toBlocks₁₂
          + blockDiagProd Q (last + 1) - Br.toBlocks₂₂) a bb ^ 2
    rw [hx]
  -- the four block entries of `recoverProductGen Q last − Br`.
  have hRw11 : ∀ (k k' : Fin r),
      (recoverProductGen Q last - Br) (Sum.inl k) (Sum.inl k')
        = (b x (lastLayer hL)).toBlocks₁₁ k k' := fun k k' => by
    rw [Matrix.sub_apply, recoverProductGen, Matrix.fromBlocks_apply₁₁,
      show Br (Sum.inl k) (Sum.inl k')
          = (blockToChainGen H r (r_le_H_gen ι hι) ι hι C₀ last).toBlocks₁₁ k k'
        from congrFun (congrFun h11.symm k) k', hQ,
      blockToChainGen_toBlocks₁₁ ι hι (b x + C₀) last (by omega),
      blockToChainGen_toBlocks₁₁ ι hι C₀ last (by omega)]
    simp only [Pi.add_apply, Matrix.toBlocks₁₁, Matrix.add_apply, Matrix.of_apply,
      add_sub_cancel_right]
    rfl
  have hRw12 : ∀ (k : Fin r) (bcol : Fin (deepestChainWidth H (last + 1) - r)),
      (recoverProductGen Q last - Br) (Sum.inl k) (Sum.inr bcol)
        = (b x (lastLayer hL)).toBlocks₁₂ k ((vertexInr ι hι (last + 1) (by omega)).symm bcol) :=
      fun k bcol => by
    rw [Matrix.sub_apply, recoverProductGen, Matrix.fromBlocks_apply₁₂,
      show Br (Sum.inl k) (Sum.inr bcol)
          = (blockToChainGen H r (r_le_H_gen ι hι) ι hι C₀ last).toBlocks₁₂ k bcol
        from congrFun (congrFun h12.symm k) bcol, hQ,
      blockToChainGen_toBlocks₁₂ ι hι (b x + C₀) last (by omega),
      blockToChainGen_toBlocks₁₂ ι hι C₀ last (by omega)]
    simp only [Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.refl_symm, Equiv.refl_apply,
      Pi.add_apply, Matrix.toBlocks₁₂, Matrix.add_apply, Matrix.of_apply, add_sub_cancel_right]
    rfl
  have hRw21 : ∀ (a : Fin (deepestChainWidth H 0 - r)) (k : Fin r),
      (recoverProductGen Q last - Br) (Sum.inr a) (Sum.inl k)
        = (b x (firstLayer hL)).toBlocks₂₁ ((vertexInr ι hι 0 (by omega)).symm a) k := fun a k => by
    rw [Matrix.sub_apply, recoverProductGen, Matrix.fromBlocks_apply₂₁,
      show Br (Sum.inr a) (Sum.inl k)
          = (blockToChainGen H r (r_le_H_gen ι hι) ι hι C₀ 0).toBlocks₂₁ a k
        from congrFun (congrFun h21.symm a) k, hQ,
      blockToChainGen_toBlocks₂₁ ι hι (b x + C₀) 0 (by omega),
      blockToChainGen_toBlocks₂₁ ι hι C₀ 0 (by omega)]
    simp only [Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.refl_symm, Equiv.refl_apply,
      Pi.add_apply, Matrix.toBlocks₂₁, Matrix.add_apply, Matrix.of_apply, add_sub_cancel_right]
    rfl
  -- match the reg blocks (₁₂/₂₁ reindexed by `vertexInr` to the `H`-width readbacks).
  have hE12 : (∑ k : Fin r, ∑ bcol : Fin (deepestChainWidth H (last + 1) - r),
        ((recoverProductGen Q last - Br) (Sum.inl k) (Sum.inr bcol)) ^ 2)
      = ∑ k : Fin r, ∑ bcol : Fin (H (Fin.last (last + 1)) - r),
          ((b x (lastLayer hL)).toBlocks₁₂ k (finCongr hwlast bcol)) ^ 2 := by
    refine Finset.sum_congr rfl fun k _ => ?_
    refine Fintype.sum_equiv
      (((vertexInr ι hι (last + 1) (by omega)).symm).trans (finCongr hwlast).symm) _ _
      (fun bcol => ?_)
    rw [hRw12]
    congr 2
  have hE21 : (∑ a : Fin (deepestChainWidth H 0 - r), ∑ k : Fin r,
        ((recoverProductGen Q last - Br) (Sum.inr a) (Sum.inl k)) ^ 2)
      = ∑ a : Fin (H 0 - r), ∑ k : Fin r,
          ((b x (firstLayer hL)).toBlocks₂₁ a k) ^ 2 := by
    refine Fintype.sum_equiv (vertexInr ι hι 0 (by omega)).symm _ _ (fun a => ?_)
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [hRw21]
  -- assemble.
  rw [schurReadoutF_gen, ← hQ, hsplit (recoverProductGen Q last - Br), reg_readback_gen ι hι hL x,
    hq22]
  simp_rw [hRw11]
  rw [hE12, hE21]
  abel

end DLNFibre.DLN.RLCT
