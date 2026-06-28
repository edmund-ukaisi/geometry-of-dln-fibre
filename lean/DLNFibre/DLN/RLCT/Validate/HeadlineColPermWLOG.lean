import DLNFibre.DLN.RLCT.Validate.FrontPivotWLOG

/-!
# `DLNFibre.DLN.RLCT.Validate.HeadlineColPermWLOG` — the headline ⨅-level WLOG reduction

The KC2 ⨅-level wire: the headline learning-coefficient infimum for a GENERAL target `B` equals the
same infimum for a column-permuted target `Bp = B.submatrix id P` whose rank-`r` pivot columns are
at the FRONT. This is the column-permutation WLOG move at exactly the headline's `⨅`-form (the
`aoyagi_learning_coefficient` LHS), letting the gauge-chart producer be run only at a front-pivot
target (where the `hJfront` front-pivot hypothesis is available).

It is the assembly of two banked facts, no new geometry:
- `front_pivot_perm_exists` (`FrontPivotWLOG`) — a column permutation `P` bringing `B`'s rank-`r`
  pivot columns to the front (`Bp.rank = r`, front-`r` cols rank `r`);
- `rlct_infimum_colPerm_eq` (`FrontPivotWLOG`) — the ⨅-over-`optimalSet` RLCT is invariant under
  a column permutation of `B` (the global MP homeomorphism `τ_P` + banked germ-invariance).

The RHS of the headline (`ofReal (aoyagiLambda H r)`) is `B`-independent (`aoyagiLambda` reads only
`H, r`), so the column permutation leaves it untouched — the reduction is purely on the LHS. The
front-pivot rank facts are bundled (`headline_frontPivot_exists`) so a consumer gets `(P, Bp, hBp,
hfront, the ⨅-equality)` in one obtain. NO `hJfront` is discharged here — that is the deepest-point
front-alignment (KC1), kept separate.
-/

open MeasureTheory
open scoped ENNReal

namespace DLNFibre.DLN.RLCT

variable {L : ℕ}

/-- **The headline ⨅-level WLOG reduction (KC2, the ⨅-wire).** For a rank-`r` target `B`, there is a
column permutation `P` such that `Bp = B.submatrix id P` has rank `r`, its first `r` columns have
rank `r` (front pivot), and the headline learning-coefficient infimum against `B` equals the one
against `Bp`. Assembled from `front_pivot_perm_exists` (the permutation) + `rlct_infimum_colPerm_eq`
(the ⨅-transfer). The `Bp`-side infimum is the front-pivot target the gauge chart can run on. -/
theorem headline_frontPivot_exists (H : Fin (L + 1) → ℕ) (r : ℕ)
    (B : Matrix (Fin (H 0)) (Fin (H (Fin.last L))) ℝ) (hB : B.rank = r) (hL : 1 ≤ L) :
    ∃ (P : Equiv.Perm (Fin (H (Fin.last L)))) (hrn : r ≤ H (Fin.last L)),
      (B.submatrix id (P : Fin (H (Fin.last L)) → Fin (H (Fin.last L)))).rank = r ∧
      ((B.submatrix id (P : Fin (H (Fin.last L)) → Fin (H (Fin.last L)))).submatrix id
        (Fin.castLE hrn : Fin r → Fin (H (Fin.last L)))).rank = r ∧
      (⨅ w ∈ optimalSet H B, rlctAt H (dlnLoss H B) w)
        = ⨅ w ∈ optimalSet H
            (B.submatrix id (P : Fin (H (Fin.last L)) → Fin (H (Fin.last L)))),
            rlctAt H
              (dlnLoss H (B.submatrix id (P : Fin (H (Fin.last L)) → Fin (H (Fin.last L))))) w := by
  obtain ⟨P, hrn, hBpr, hfront⟩ := front_pivot_perm_exists B hB
  exact ⟨P, hrn, hBpr, hfront, rlct_infimum_colPerm_eq H hL B P⟩

end DLNFibre.DLN.RLCT
