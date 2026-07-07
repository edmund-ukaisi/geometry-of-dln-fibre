import DLNFibre.DLN.RLCT.Validate.DeepestL2ConjReg

/-!
# `DLNFibre.DLN.RLCT.Validate.DeepestDeepBlkBoundaryGen` — general-`L` deepest-block boundary (#120 `hstep2`, item 4)

The general-`L` lift of the `L = 2` `deepBlk_boundary_of_L2` / `deepBlkA_isUnit_of_L2`
(`DeepestDiffeoBridgeL2Conj` / `DeepestL2ConjReg`), supplying the Θ-side `hbdy`/`hDA` hypotheses of the
assembled bridge `deepest_diffeo_bridge_gen_assembled` (`DeepestDiffeoBridgeGenConj`).

At the deepest point every **interior** layer (`0 < s`, `s + 1 < L`) IS the block-normal corner
`diag(I_r, 0)` (`deepestPoint_interior_eq_corM`), so there the reindexed off-diagonal blocks vanish
(`deepBlkY_s = 0`, since `toBlocks₁₂` reads columns `≥ r` and the corner has no support there) and the
pivot block is the identity (`deepBlkA_s = I_r`, hence a unit). Combined with the two **boundary**
layers — layer 0 (`deepBlkY_0 = 0` via `deepBlkY_layer0_zero`; pivot unit via `deepBlkA0_isUnit_of_htop`)
and layer `L−1` (`deepBlkZ_{L−1} = 0` via `deepBlkZ_layerLast_zero`; pivot unit via
`deepBlkA_last_isUnit_of_bundle`) — this discharges the general `hbdy : ∀ s, deepBlkY_s = 0 ∨
deepBlkZ_s = 0` (`deepBlk_boundary_gen`) and `hDA : ∀ s, IsUnit (deepBlkA_s)` (`deepBlkA_isUnit_gen`).
-/

open Matrix
namespace DLNFibre.DLN.RLCT

variable {L : ℕ}

/-- **Interior deepest layers vanish at columns `≥ r`.** For a strict-interior layer the deepest point
is the corner `diag(I_r, 0)` (`deepestPoint_interior_eq_corM`), which is `0` at any column `≥ r`. -/
theorem deepestPoint_interior_cols_vanish (H : Fin (L + 1) → ℕ) (r : ℕ)
    (B : Matrix (Fin (H 0)) (Fin (H (Fin.last L))) ℝ) (hB : B.rank = r)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L) (s : Fin L)
    (hpos : 0 < (s : ℕ)) (hlt : (s : ℕ) + 1 < L)
    (i : Fin (H s.castSucc)) (j : Fin (H s.succ)) (hj : r ≤ (j : ℕ)) :
    deepestPoint H r B hB hr hL s i j = 0 := by
  rw [deepestPoint_interior_eq_corM H r B hB hr hL s hpos hlt]
  simp only [Matrix.of_apply]
  rw [if_neg]
  rintro ⟨heq, hlt'⟩; omega

/-- **`deepBlkY_s = 0` at interior layers** (`0 < s`, `s+1 < L`): `toBlocks₁₂` reads columns `≥ r`,
which the corner kills. Mirrors `deepBlkY_layer0_zero` with the interior corner in place of the
boundary col-vanishing. -/
theorem deepBlkY_interior_zero (H : Fin (L + 1) → ℕ) (r : ℕ)
    (B : Matrix (Fin (H 0)) (Fin (H (Fin.last L))) ℝ) (hB : B.rank = r)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L) (s : Fin L)
    (hpos : 0 < (s : ℕ)) (hlt : (s : ℕ) + 1 < L) :
    deepBlkY H r B hB hr hL s = 0 := by
  funext i j
  change (deepestPoint H r B hB hr hL s)
      ((rThresholdSplit r (H s.castSucc) (hr s.castSucc)).symm (Sum.inl i))
      ((rThresholdSplit r (H s.succ) (hr s.succ)).symm (Sum.inr j)) = 0
  rw [rThresholdSplit_symm_inr]
  exact deepestPoint_interior_cols_vanish H r B hB hr hL s hpos hlt _ _ (by simp)

/-- **`deepBlkA_s = I_r` at interior layers** (`0 < s`, `s+1 < L`): the reindexed corner's `(1,1)`
block is the identity (rows/cols `< r`, where the corner is `diag(I_r,·)`). -/
theorem deepBlkA_interior_eq_one (H : Fin (L + 1) → ℕ) (r : ℕ)
    (B : Matrix (Fin (H 0)) (Fin (H (Fin.last L))) ℝ) (hB : B.rank = r)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L) (s : Fin L)
    (hpos : 0 < (s : ℕ)) (hlt : (s : ℕ) + 1 < L) :
    deepBlkA H r B hB hr hL s = 1 := by
  apply Matrix.ext; intro i k
  change (Matrix.reindex (rThresholdSplit r (H s.castSucc) (hr s.castSucc))
      (rThresholdSplit r (H s.succ) (hr s.succ)) (deepestPoint H r B hB hr hL s)).toBlocks₁₁ i k
    = (1 : Matrix (Fin r) (Fin r) ℝ) i k
  simp only [Matrix.toBlocks₁₁, Matrix.reindex_apply, Matrix.submatrix_apply, Matrix.of_apply,
    rThresholdSplit_symm_inl]
  rw [deepestPoint_interior_eq_corM H r B hB hr hL s hpos hlt]
  simp only [Matrix.of_apply, Matrix.one_apply, Fin.val_castLE]
  by_cases h : i = k
  · subst h; simp [i.isLt]
  · rw [if_neg (fun hc => h (Fin.ext hc.1)), if_neg h]

/-- **`IsUnit (deepBlkA_s)` at interior layers** (the corner pivot is `I_r`). -/
theorem deepBlkA_interior_isUnit (H : Fin (L + 1) → ℕ) (r : ℕ)
    (B : Matrix (Fin (H 0)) (Fin (H (Fin.last L))) ℝ) (hB : B.rank = r)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L) (s : Fin L)
    (hpos : 0 < (s : ℕ)) (hlt : (s : ℕ) + 1 < L) :
    IsUnit (deepBlkA H r B hB hr hL s) := by
  rw [deepBlkA_interior_eq_one H r B hB hr hL s hpos hlt]; exact isUnit_one

/-- **The general-`L` boundary hypothesis `hbdy`** (`∀ s, deepBlkY_s = 0 ∨ deepBlkZ_s = 0`). Layer 0:
`deepBlkY_0 = 0`; interior: `deepBlkY_s = 0` (corner); layer `L−1`: `deepBlkZ_{L−1} = 0`. -/
theorem deepBlk_boundary_gen (H : Fin (L + 1) → ℕ) (r : ℕ)
    (B : Matrix (Fin (H 0)) (Fin (H (Fin.last L))) ℝ) (hB : B.rank = r)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L) (hL2 : 2 ≤ L) :
    ∀ s : Fin L, deepBlkY H r B hB hr hL s = 0 ∨ deepBlkZ H r B hB hr hL s = 0 := by
  intro s
  rcases Nat.eq_zero_or_pos (s : ℕ) with hs0 | hspos
  · exact Or.inl (deepBlkY_layer0_zero H r B hB hr hL hL2 s hs0)
  · rcases Nat.lt_or_ge ((s : ℕ) + 1) L with hlt | hge
    · exact Or.inl (deepBlkY_interior_zero H r B hB hr hL s hspos hlt)
    · have hlast : (s : ℕ) + 1 = L := by have := s.isLt; omega
      exact Or.inr (deepBlkZ_layerLast_zero H r B hB hr hL hL2 s hlast)

/-- **The general-`L` pivot-unit hypothesis `hDA`** (`∀ s, IsUnit (deepBlkA_s)`). Layer 0 via
`deepBlkA0_isUnit_of_htop` (row-WLOG `htop`); interior via the corner (`deepBlkA_s = I_r`); layer `L−1`
via `deepBlkA_last_isUnit_of_bundle` (the block-triangular pivot bundle `hcorner`/`hQUpper`). -/
theorem deepBlkA_isUnit_gen (H : Fin (L + 1) → ℕ) (r : ℕ)
    (B : Matrix (Fin (H 0)) (Fin (H (Fin.last L))) ℝ) (hB : B.rank = r)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L) (hL2 : 2 ≤ L)
    (htop : (B.submatrix (Fin.castLE (hr 0) : Fin r → Fin (H 0))
        (id : Fin (H (Fin.last L)) → Fin (H (Fin.last L)))).rank = r)
    (J : Fin r ↪ Fin (H (Fin.last L))) (hJfront' : J = frontEmbed H r hr)
    (Qf : (s : Fin L) → Matrix (Fin (H s.succ)) (Fin (H s.succ)) ℝ)
    (hcorner : Matrix.reindex (rThresholdSplit r (H (lastLayer hL).castSucc) (hr _))
        (pivotThresholdSplit r (H ((lastLayer hL).succ)) (hr _) (pivotJSucc H r hL J))
        ((deepestPoint H r B hB hr hL (lastLayer hL)) * Qf (lastLayer hL))
      = Matrix.fromBlocks (1 : Matrix (Fin r) (Fin r) ℝ) 0 0 0)
    (hQUpper : (Matrix.reindex
        (pivotThresholdSplit r (H ((lastLayer hL).succ)) (hr _) (pivotJSucc H r hL J))
        (pivotThresholdSplit r (H ((lastLayer hL).succ)) (hr _) (pivotJSucc H r hL J))
        (Qf (lastLayer hL))).toBlocks₂₁ = 0) :
    ∀ s : Fin L, IsUnit (deepBlkA H r B hB hr hL s) := by
  intro s
  rcases Nat.eq_zero_or_pos (s : ℕ) with hs0 | hspos
  · have hsf : s = (⟨0, by omega⟩ : Fin L) := Fin.ext hs0
    rw [hsf]; exact deepBlkA0_isUnit_of_htop H r B hB hr hL hL2 htop
  · rcases Nat.lt_or_ge ((s : ℕ) + 1) L with hlt | hge
    · exact deepBlkA_interior_isUnit H r B hB hr hL s hspos hlt
    · have hlast : s = lastLayer hL := by
        apply Fin.ext; simp only [lastLayer]; have := s.isLt; omega
      rw [hlast]; exact deepBlkA_last_isUnit_of_bundle H r B hB hr hL J hJfront' Qf hcorner hQUpper

end DLNFibre.DLN.RLCT
