import DLNFibre.DLN.RLCT.Validate.DeepestL2NormalFormFrontAligned
import DLNFibre.DLN.RLCT.Validate.HeadlineRowColPermWLOG

/-!
# `DLNFibre.DLN.RLCT.Validate.HeadlineL2InfimumWLOG` — the headline ⨅-WLOG at L=2 (ROUTE (a))

The headline learning-coefficient infimum `⨅ v ∈ optimalSet B, rlctAt (dlnLoss B) v =
ofReal (aoyagiLambda H r)` for an **arbitrary** rank-`r` target `B` at `L = 2`, assembled by
transporting the permutation-WLOG to the infimum level (NOT the pointwise per-`B` level — see the
genm-p44wire Finding 2: the per-point closure at an arbitrary `deepestPoint` is new math; the
infimum is permutation-invariant, so the `B → B·Π` WLOG belongs here, downstream).

**The chain (banked pieces + explicit-hypothesis gaps).** For arbitrary rank-`r` `B`:
1. `headline_frontRowColPivot_exists` (banked): a column perm `P` + row perm `R` give
   `Bpr = B.submatrix R P` that is front-COLUMN aligned and top-ROW aligned, with the headline
   infimum invariant `⨅(B) = ⨅(Bpr)` (banked `rlct_infimum_{row,col}Perm_eq` ∘
   `Set.BijOn.iInf_congr`).
2. The **aligned headline** `headline_infimum_eq_aoyagiLambda_aligned`: for the front+row-aligned
   `Bpr`, `⨅(Bpr) = ofReal(aoyagiLambda H r)`, GIVEN the residual gaps {D1, R1 value, front-pivot
   bridge}. Chains D1 (`deepest_point_reduction`) ▸ front-aligned #44
   (`deepest_regular_core_normal_form_frontAligned`) ▸ `reg_shift_add_core_eq_aoyagiLambda`
   (proven).
3. Transport: `⨅(B) = ⨅(Bpr) = ofReal(aoyagiLambda H r)`.

**The explicit remaining gaps (carried as hypotheses, named, NOT ground — per controller scoping):**
- `hD1` — D1 (`deepest_point_reduction`) for the aligned target (its `≥`-leg is genm-d1ladder's
  `hchart`).
- `hcore` — the R1 reduced-core value (R1's lane).
- `hJfront` — the front-pivot-frame identity (`deepestPoint_frame_pivot_exists(·).choose =
  frontEmbed`). The WLOG supplies the aligned target's front-COLUMN rank, but converting that to the
  deepest-point FRAME's pivot identity is NOT banked (the frame pivot is the deepest-point matrix's
  column pivot, an arbitrary `Classical.choice` witness's structure, not the target's columns
  directly) — a genm-p44wire verify-first finding. Carried as a hypothesis until that bridge is
  built/adjudicated.

So this pre-positions the WHOLE L2 headline to `{D1 ≥-leg, R1 value, front-pivot bridge}`-ready.
-/

open MeasureTheory Matrix
open scoped ENNReal BigOperators Topology

namespace DLNFibre.DLN.RLCT

variable {L : ℕ}

/-- **The aligned-target L2 headline value, modulo {D1, R1, front-pivot bridge}.** For a
front+row-aligned rank-`r` target `B'` at `L = 2` (front-pivot frame `hJfront`, top-row rank
`htop`), the headline infimum equals `ofReal (aoyagiLambda H r)` — GIVEN the D1 reduction `hD1` for
`B'` and the R1 core-value `hcore`. Chains D1 (`⨅ = rlctAt deepest`) ▸ the front-aligned #44
(`rlctAt deepest = nReg/2 + ofReal(lambdaCore)`) ▸ `reg_shift_add_core_eq_aoyagiLambda`
(`= ofReal(aoyagiLambda)`). The three named gaps are carried, not built. -/
theorem headline_infimum_eq_aoyagiLambda_aligned (H : Fin (L + 1) → ℕ) (r : ℕ)
    (B' : Matrix (Fin (H 0)) (Fin (H (Fin.last L))) ℝ) (hB' : B'.rank = r)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L) (hL2 : 2 ≤ L) (hLlt : L < 3)
    (hpos : ∀ s : Fin (L + 1), r < H s)
    (hJfront : ((deepestPoint_frame_pivot_exists H r B' hB' hr hL hL2).choose).trans
        (finCongr (H_lastLayer_succ H hL)).toEmbedding = frontEmbed H r hr)
    (htop : (B'.submatrix (Fin.castLE (hr 0) : Fin r → Fin (H 0))
        (id : Fin (H (Fin.last L)) → Fin (H (Fin.last L)))).rank = r)
    (hcore : rlctAtOn
        (fun A : Params (fun s => H s - r) =>
          dlnLoss (fun s => H s - r)
            (0 : Matrix (Fin ((fun s => H s - r) 0))
              (Fin ((fun s => H s - r) (Fin.last L))) ℝ) A)
        (fun _ => 0 : Params (fun s => H s - r))
      = ENNReal.ofReal (lambdaCore (fun s => H s - r) : ℝ))
    (hD1 : (⨅ v ∈ optimalSet H B', rlctAt H (dlnLoss H B') v)
        = rlctAt H (dlnLoss H B') (deepestPoint H r B' hB' hr hL)) :
    (⨅ v ∈ optimalSet H B', rlctAt H (dlnLoss H B') v) = ENNReal.ofReal (aoyagiLambda H r : ℝ) := by
  rw [hD1,
    deepest_regular_core_normal_form_frontAligned H r B' hB' hr hL hL2 hLlt hpos hJfront htop hcore,
    reg_shift_add_core_eq_aoyagiLambda H r hr hL]

/-- **The L2 headline ⨅-WLOG for arbitrary rank-`r` `B`, modulo {D1, R1, front-pivot bridge}.** The
headline infimum equals `ofReal (aoyagiLambda H r)` for ANY rank-`r` `B` at `L = 2`. The `B → B·Π`
permutation (front+row alignment) and the infimum invariance `⨅(B) = ⨅(Bpr)` are the banked
`headline_frontRowColPivot_exists`; the aligned-target value is
`headline_infimum_eq_aoyagiLambda_aligned`, which consumes the residual gaps. The gaps are taken as
a hypothesis `haligned` keyed to the EXACT WLOG-produced permuted target `B.submatrix R P` (the
column perm `P`, row perm `R` the WLOG returns), so the caller supplies {D1, R1, front-pivot bridge}
only for that target — not for an arbitrary matrix (which need not be front+row-aligned). -/
theorem headline_infimum_eq_aoyagiLambda (H : Fin (L + 1) → ℕ) (r : ℕ)
    (B : Matrix (Fin (H 0)) (Fin (H (Fin.last L))) ℝ) (hB : B.rank = r) (hL : 1 ≤ L)
    -- the aligned-target headline value, for the EXACT WLOG-produced target `B.submatrix R P`:
    (haligned : ∀ (P : Equiv.Perm (Fin (H (Fin.last L)))) (R : Equiv.Perm (Fin (H 0)))
        (_ : (B.submatrix (R : Fin (H 0) → Fin (H 0))
          (P : Fin (H (Fin.last L)) → Fin (H (Fin.last L)))).rank = r),
        (⨅ v ∈ optimalSet H (B.submatrix (R : Fin (H 0) → Fin (H 0))
            (P : Fin (H (Fin.last L)) → Fin (H (Fin.last L)))),
          rlctAt H (dlnLoss H (B.submatrix (R : Fin (H 0) → Fin (H 0))
            (P : Fin (H (Fin.last L)) → Fin (H (Fin.last L))))) v)
          = ENNReal.ofReal (aoyagiLambda H r : ℝ)) :
    (⨅ v ∈ optimalSet H B, rlctAt H (dlnLoss H B) v) = ENNReal.ofReal (aoyagiLambda H r : ℝ) := by
  obtain ⟨P, R, _hrn, _hrH, hBpr_rank, _hBpr_front, _hBpr_top, hinf⟩ :=
    headline_frontRowColPivot_exists H r B hB hL
  rw [hinf]
  exact haligned P R hBpr_rank

end DLNFibre.DLN.RLCT
