import DLNFibre.DLN.RLCT.Validate.RouteMSJDeepCoverage
import DLNFibre.DLN.RLCT.Validate.RouteMSJDeepPivot

set_option linter.style.longLine false
set_option linter.unusedVariables false

/-!
# `RouteMSJCellRank` — the deep-atlas cell rank extractor + the exact rank bridge

**Thread `genm-corankrec` (aoyagi-full Stage 2), the ATLAS critical-path gate for the Route-B
(coupledBox) per-cell dispatch.** For a deep chain `H = dropHead (redChain u M)` and an atlas cell
`i : CRIndex H`, the deep-product rank `(prod H A).rank` is FIXED on the cell (constant, `= cellRank i`),
NOT merely bounded. This exact per-cell rank is what:

* dbuild's **null-disposal** consumes (a cell with `cellRank i < deepTailMin M` is contained in the
  null locus `{A | rank < deepTailMin}` — `deepFactor_rank_ge_deepTailMin_ae` — so its integral vanishes);
* the **interior/edge partition** consumes (interior `a+b ≤ cellRank i` vs edge/deep-corank
  `cellRank i < a+b`, a clean complementary trichotomy);
* the interior **hGae**/charge finiteness consumes (`cellRank i ≥ b` gives the corank-Gram full row rank).

## `cellRank` = the DEEPEST descent node's rank

The CR-path descends `level L → … → level 1 (deepest node) → level 0 (terminal)`, picking a rank `r.1`
at each node. Down the path the ranks are non-increasing (`r_{k} ≤ min(H⟨k−1⟩, r_{k+1}) ≤ r_{k+1}`), and
the deep-product rank telescopes (via `prodAux_reduce_rank_of`, each reduced factor being FULL COLUMN
RANK = its width) to the **deepest** node's `r.1`. `cellRank` reads it off by recursing to the terminal,
carrying the reduced width as the running `q` (so the terminal returns the deepest `r.1`). The top node's
`r.1` is only a LOOSE upper cap; the deepest is the exact rank.
-/

namespace DLNFibre.DLN.RLCT

open Matrix

namespace DeepAtlas

variable {L : ℕ}

/-- **The cell rank extractor.** Recurse the CR-path to the terminal, carrying the reduced width as the
running `q`; the terminal returns it — the DEEPEST node's `r.1`, which is the exact deep-product rank on
the cell (`prodAux_rank_eq_cellRank`). -/
def cellRank (H : Fin (L + 1) → ℕ) :
    (j : ℕ) → (hj : j ≤ L) → (q : ℕ) → CRPath H j hj q → ℕ
  | 0, _, q, _ => q
  | (k + 1), hk, q, ⟨r, _ρ, _κ, tail⟩ => cellRank H k (Nat.le_of_succ_le hk) r.1 tail

/-- **The cell rank of a top-level atlas index** `i : CRIndex H`. -/
def cellRankIndex (H : Fin (L + 1) → ℕ) (i : CRIndex H) : ℕ :=
  cellRank H L le_rfl (H (Fin.last L)) i

/-- **The reduced factor is FULL COLUMN RANK.** For `M` with an invertible `r×r` pivot `(ρ, κ)`, the
reduced factor `M[:,κ] · (M[ρ,κ])⁻¹` has rank exactly `r`: right-multiplication by the invertible inverse
preserves rank (`rank_mul_eq_left_of_isUnit_det`), and `M[:,κ]` (which contains the invertible `r×r`
submatrix `M[ρ,κ]`) has rank `r` (`≤ r` by width, `≥ r` by `isUnit_submatrix_le_rank`). This is the
invariant that keeps the telescoping exact. -/
theorem reduced_factor_rank {m q r : ℕ} (M : Matrix (Fin m) (Fin q) ℝ)
    (ρ : Fin r ↪ Fin m) (κ : Fin r ↪ Fin q) (hU : IsUnit (M.submatrix ρ κ)) :
    (M.submatrix (id : Fin m → Fin m) κ * (M.submatrix ρ κ)⁻¹).rank = r := by
  have hUdet : IsUnit (M.submatrix ρ κ).det := (Matrix.isUnit_iff_isUnit_det _).mp hU
  have hdet : IsUnit ((M.submatrix ρ κ)⁻¹).det := by
    rw [Matrix.det_nonsing_inv, Ring.inverse_eq_inv']
    exact isUnit_iff_ne_zero.mpr (inv_ne_zero (isUnit_iff_ne_zero.mp hUdet))
  rw [rank_mul_eq_left_of_isUnit_det _ _ hdet]
  refine le_antisymm (by simpa using Matrix.rank_le_width (M.submatrix (id : Fin m → Fin m) κ)) ?_
  have hsub : (M.submatrix (id : Fin m → Fin m) κ).submatrix ρ (Function.Embedding.refl (Fin r))
      = M.submatrix ρ κ := by
    ext a b; simp [Matrix.submatrix_apply]
  exact isUnit_submatrix_le_rank (M.submatrix (id : Fin m → Fin m) κ) ρ (Function.Embedding.refl (Fin r))
    (by rw [hsub]; exact hU)

/-- **The exact rank bridge (per cell, general-`L`).** On the atlas cell of a CR-path (any level `j`,
right factor `Q` of FULL COLUMN RANK `q`), the composed rank `(prodAux j · Q).rank` is EXACTLY
`cellRank` — the deepest node's `r.1`. Per-`A` induction on the path length: the base (terminal) reads
the full-column-rank invariant; the step establishes the node rank `= r.1` (`isUnit_submatrix_le_rank`
+ the cell's `≤ r.1`), applies `prodAux_reduce_rank_of` (composed rank preserved through the reduction),
and recurses, the reduced factor being full column rank `r.1` (`reduced_factor_rank`). -/
theorem prodAux_rank_eq_cellRank (H : Fin (L + 1) → ℕ) (s : ℕ) (A : Params H) :
    ∀ (j : ℕ) (hj : j ≤ L) (q : ℕ)
      (Q : Params H → Matrix (Fin (H ⟨j, Nat.lt_succ_of_le hj⟩)) (Fin q) ℝ),
      (Q A).rank = q → ∀ (path : CRPath H j hj q),
        A ∈ deepCell H s j hj q path Q →
        (prodAux H A j (Nat.lt_succ_of_le hj) * Q A).rank = cellRank H j hj q path := by
  intro j
  induction j with
  | zero =>
      intro hj q Q hQrank path hA
      have hmul : prodAux H A 0 (Nat.lt_succ_of_le hj) * Q A = Q A := Matrix.one_mul (Q A)
      rw [hmul]; simpa only [cellRank] using hQrank
  | succ k ih =>
      intro hj q Q hQrank path hA
      obtain ⟨r, ρ, κ, tail⟩ := path
      have hk' : k + 1 < L + 1 := Nat.lt_succ_of_le hj
      have hkL : k ≤ L := Nat.le_of_succ_le hj
      simp only [deepCell, Set.mem_inter_iff, Set.mem_setOf_eq] at hA
      -- unfold the descent-node cell
      have hApiv : IsUnit ((effLayer H A k hk' * Q A).submatrix ρ κ)
          ∧ (effLayer H A k hk' * Q A).rank ≤ r.1 := hA.1
      have hAtail : A ∈ deepCell H s k hkL r.1 tail
          (fun A' => (effLayer H A' k hk' * Q A').submatrix id κ
            * ((effLayer H A' k hk' * Q A').submatrix ρ κ)⁻¹) := hA.2
      -- the effective-layer rank is EXACTLY `r.1` on the cell
      have hge : r.1 ≤ (effLayer H A k hk' * Q A).rank :=
        isUnit_submatrix_le_rank _ ρ κ hApiv.1
      have hr : (effLayer H A k hk' * Q A).rank = r.1 := le_antisymm hApiv.2 hge
      -- composed-rank preservation through the reduction
      have hrank := prodAux_reduce_rank_of H A k q hk' (Q A) r.1 hr ρ κ hApiv.1
      rw [Matrix.mul_assoc (prodAux H A k (Nat.lt_of_succ_lt hk'))
        ((effLayer H A k hk' * Q A).submatrix id κ)
        ((effLayer H A k hk' * Q A).submatrix ρ κ)⁻¹] at hrank
      -- the reduced factor is full column rank `r.1`
      have hRed : ((effLayer H A k hk' * Q A).submatrix id κ
          * ((effLayer H A k hk' * Q A).submatrix ρ κ)⁻¹).rank = r.1 :=
        reduced_factor_rank _ ρ κ hApiv.1
      -- recurse on the tail cell (reduced factor, full column rank)
      have hIH := ih hkL r.1
        (fun A' => (effLayer H A' k hk' * Q A').submatrix id κ
          * ((effLayer H A' k hk' * Q A').submatrix ρ κ)⁻¹)
        hRed tail hAtail
      rw [hrank, hIH]
      simp only [cellRank]

/-- **The exact rank bridge in top-level `CRIndex` form** (dbuild's consumed interface). On the atlas
cell of `i : CRIndex H` (full chain, right factor `1`), the deep-product rank is exactly `cellRankIndex i`. -/
theorem prod_rank_eq_cellRankIndex (H : Fin (L + 1) → ℕ) (s : ℕ) (A : Params H)
    (i : CRIndex H)
    (hA : A ∈ deepCell H s L le_rfl (H (Fin.last L)) i
      (fun _ => (1 : Matrix (Fin (H (Fin.last L))) (Fin (H (Fin.last L))) ℝ))) :
    (prod H A).rank = cellRankIndex H i := by
  have hone : ((1 : Matrix (Fin (H (Fin.last L))) (Fin (H (Fin.last L))) ℝ)).rank
      = H (Fin.last L) := by
    rw [Matrix.rank_one]; exact Fintype.card_fin _
  have h := prodAux_rank_eq_cellRank H s A L le_rfl (H (Fin.last L))
    (fun _ => (1 : Matrix (Fin (H (Fin.last L))) (Fin (H (Fin.last L))) ℝ)) hone i hA
  rw [cellRankIndex, ← h, prod]
  congr 1
  exact (Matrix.mul_one _).symm

end DeepAtlas

end DLNFibre.DLN.RLCT
