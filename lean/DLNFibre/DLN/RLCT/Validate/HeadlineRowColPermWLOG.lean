import DLNFibre.DLN.RLCT.Validate.HeadlineColPermWLOG
import DLNFibre.DLN.RLCT.Validate.FrontPivotRowWLOG

/-!
# `DLNFibre.DLN.RLCT.Validate.HeadlineRowColPermWLOG` — the COMPOSED row+column headline WLOG (#154)

The KC1 ⨅-level row-WLOG, composed with the KC2 column-WLOG (`HeadlineColPermWLOG`) into ONE bundle: the
headline learning-coefficient infimum for a GENERAL target `B` equals the infimum for a row-AND-column
permuted target `Bpr = B.submatrix R P` whose rank-`r` pivot COLUMNS are at the FRONT (the `hJfront`
precursor, KC2) AND whose top `r` ROWS have full rank (the `htop` datum, KC1). The gauge-chart producer
`deepest_gauge_chart_construct` needs BOTH (`hJfront` + `htop`), so the WLOG must supply both at once.

Assembly of banked facts, no new geometry:
- `front_pivot_perm_exists` (`FrontPivotWLOG`) — the column permutation `P` (front-pivot cols of `Bp`).
- `front_row_pivot_perm_exists` (`FrontPivotRowWLOG`) — the row permutation `R` (top-`r` rows of `Bpr`).
- `rlct_infimum_colPerm_eq` ∘ `rlct_infimum_rowPerm_eq` (`FrontPivot{,Row}WLOG`) — the two banked
  ⨅-over-`optimalSet` MP-transfers, CHAINED (`B → Bp → Bpr`). The heavy ⨅-cast (the MP homeomorphism +
  germ-invariance) is INSIDE those banked transfers; this module only composes them.

The columns and rows index DISTINCT sets (`Fin (H (Fin.last L))` vs `Fin (H 0)`), so the two permutations
commute and coexist: the row permutation `R` (chosen for `Bp`) preserves `Bp`'s front-`r`-columns rank
(rank is invariant under a row permutation — `Matrix.rank_submatrix` with an `Equiv` row factor), so
`Bpr` carries BOTH front-pivot-columns AND top-`r`-rows. The RHS of the headline (`ofReal (aoyagiLambda
H r)`, `B`-independent) is untouched.
-/

open MeasureTheory Matrix
open scoped ENNReal

namespace DLNFibre.DLN.RLCT

variable {L : ℕ}

/-- **The composed row+column headline ⨅-WLOG (#154).** For a rank-`r` target `B`, there is a column
permutation `P` and a row permutation `R` such that `Bpr = B.submatrix R P` has rank `r`, its first `r`
COLUMNS have rank `r` (front pivot, KC2 — the `hJfront` precursor), its top `r` ROWS have rank `r`
(KC1 — the `htop` datum), and the headline learning-coefficient infimum against `B` equals the one against
`Bpr`. Assembled from `front_pivot_perm_exists` + `front_row_pivot_perm_exists` + the chained
`rlct_infimum_colPerm_eq` ∘ `rlct_infimum_rowPerm_eq`. The `Bpr`-side infimum is the row-and-column
front-aligned target the gauge chart can run on (both `hJfront` and `htop` available). -/
theorem headline_frontRowColPivot_exists (H : Fin (L + 1) → ℕ) (r : ℕ)
    (B : Matrix (Fin (H 0)) (Fin (H (Fin.last L))) ℝ) (hB : B.rank = r) (hL : 1 ≤ L) :
    ∃ (P : Equiv.Perm (Fin (H (Fin.last L)))) (R : Equiv.Perm (Fin (H 0)))
      (hrn : r ≤ H (Fin.last L)) (hrH : r ≤ H 0),
      (B.submatrix (R : Fin (H 0) → Fin (H 0)) (P : Fin (H (Fin.last L)) → Fin (H (Fin.last L)))).rank = r ∧
      -- front-`r` COLUMNS full rank (KC2, the `hJfront` precursor):
      ((B.submatrix (R : Fin (H 0) → Fin (H 0)) (P : Fin (H (Fin.last L)) → Fin (H (Fin.last L)))).submatrix
        (id : Fin (H 0) → Fin (H 0)) (Fin.castLE hrn : Fin r → Fin (H (Fin.last L)))).rank = r ∧
      -- top-`r` ROWS full rank (KC1, the `htop` datum):
      ((B.submatrix (R : Fin (H 0) → Fin (H 0)) (P : Fin (H (Fin.last L)) → Fin (H (Fin.last L)))).submatrix
        (Fin.castLE hrH : Fin r → Fin (H 0)) (id : Fin (H (Fin.last L)) → Fin (H (Fin.last L)))).rank = r ∧
      -- the headline ⨅ is invariant:
      (⨅ w ∈ optimalSet H B, rlctAt H (dlnLoss H B) w)
        = ⨅ w ∈ optimalSet H
            (B.submatrix (R : Fin (H 0) → Fin (H 0)) (P : Fin (H (Fin.last L)) → Fin (H (Fin.last L)))),
            rlctAt H
              (dlnLoss H
                (B.submatrix (R : Fin (H 0) → Fin (H 0))
                  (P : Fin (H (Fin.last L)) → Fin (H (Fin.last L))))) w := by
  -- KC2 column permutation: `Bp = B.submatrix id P`, front-`r`-cols rank `r`.
  obtain ⟨P, hrn, hBp_rank, hBp_front⟩ := front_pivot_perm_exists B hB
  set Bp : Matrix (Fin (H 0)) (Fin (H (Fin.last L))) ℝ :=
    B.submatrix (id : Fin (H 0) → Fin (H 0)) (P : Fin (H (Fin.last L)) → Fin (H (Fin.last L)))
    with hBp
  -- KC1 row permutation applied to `Bp`: `Bpr = Bp.submatrix R id`, rank `r`, top-`r`-rows rank `r`.
  obtain ⟨R, hrH, hBpr_rank, hBpr_top⟩ := front_row_pivot_perm_exists Bp hBp_rank
  set Bpr : Matrix (Fin (H 0)) (Fin (H (Fin.last L))) ℝ :=
    Bp.submatrix (R : Fin (H 0) → Fin (H 0)) (id : Fin (H (Fin.last L)) → Fin (H (Fin.last L)))
    with hBpr
  -- `Bpr = B.submatrix R P` (the two submatrices compose).
  have hBpr_eq : Bpr = B.submatrix (R : Fin (H 0) → Fin (H 0))
      (P : Fin (H (Fin.last L)) → Fin (H (Fin.last L))) := by
    rw [hBpr, hBp, Matrix.submatrix_submatrix]; rfl
  refine ⟨P, R, hrn, hrH, ?_, ?_, ?_, ?_⟩
  · -- rank `Bpr = r` (from `front_row_pivot_perm_exists`, rewritten to the composed form).
    rw [← hBpr_eq]; exact hBpr_rank
  · -- front-`r`-COLUMNS of `Bpr` rank `r`: `Bp`'s front-`r`-cols (rank `r`, `hBp_front`) row-permuted by
    -- `R` — rank invariant under the row equiv (`Matrix.rank_submatrix`).
    rw [← hBpr_eq]
    -- The front-cols of `Bpr` = the front-cols of `Bp` row-permuted by the equiv `R` (col factor `refl`).
    have hcols : Bpr.submatrix (id : Fin (H 0) → Fin (H 0))
        (Fin.castLE hrn : Fin r → Fin (H (Fin.last L)))
      = (Bp.submatrix (id : Fin (H 0) → Fin (H 0))
          (Fin.castLE hrn : Fin r → Fin (H (Fin.last L)))).submatrix
          (R : Fin (H 0) → Fin (H 0)) ((Equiv.refl (Fin r)) : Fin r → Fin r) := by
      rw [hBpr, Matrix.submatrix_submatrix]; rfl
    rw [hcols, Matrix.rank_submatrix]
    exact hBp_front
  · -- top-`r`-ROWS of `Bpr` rank `r` (from `front_row_pivot_perm_exists`, rewritten).
    rw [← hBpr_eq]; exact hBpr_top
  · -- ⨅-equality: chain `rlct_infimum_colPerm_eq` (B → Bp) and `rlct_infimum_rowPerm_eq` (Bp → Bpr).
    rw [hBpr_eq.symm, ← rlct_infimum_rowPerm_eq H hL Bp R, ← rlct_infimum_colPerm_eq H hL B P]

end DLNFibre.DLN.RLCT
