import DLNFibre.DLN.RLCT.Validate.DeepestFrontGaugeGen
import DLNFibre.DLN.RLCT.Validate.HeadlineRowColPermWLOG
import DLNFibre.DLN.RLCT.Validate.D1GeLegGenL
import DLNFibre.DLN.RLCT.Validate.D1GeHAtVClose

/-!
# `DLNFibre.DLN.RLCT.Validate.HeadlineGenAssembly` — the general-`L` headline (conditional on R1)

The FULLY-GENERAL (`L ≥ 3` included) Aoyagi learning-coefficient headline, assembled from the general-`L`
banked rungs, CONDITIONAL on the single R1 resolution value `hRValue` (the `#72` gate — the reduced-core
local RLCT). This is the direct mirror of `aoyagi_learning_coefficient_L2` (`HeadlineL2Assembly`), with:

  * the L=2 gauge/value rungs replaced by the general-`L` hJfront-free FRONT chain
    (`DeepestFrontGaugeGen`: `deepest_regular_core_reduces_frontPivot_front` /
    `aoyagi_learning_coefficient_frontPivot_front`);
  * the L=2 D1 `≥`-leg (`d1ge_L2_deepestPoint_via_explicit_core_genL`) replaced by the general-`L` wired
    core `d1ge_deepestPoint_via_explicit_core_genL_wired` (`D1GeLegGenL`) fed the general deepest value
    (the front reduces) + the general hAtV producer `d1ge_hAtV_explicit_close_gen` (`D1GeHAtVClose`);
  * the L2-banked R1 interface (`r1_resolution_interface_L2_generic`) replaced by the HYPOTHESIS
    `hRValue` — the general R1-LOWER resolution value at the reduced widths `H − r`, which is `#72`.

So the D1 `≥`-leg and the whole value side are WIRED sorry-free for general `L`; the SOLE open input is
`hRValue`. When `#72` lands, this headline is unconditional. NOT wired into `DLNFibre.lean` /
`Skeleton.lean` (single-writer) — the controller wires it.
-/

open MeasureTheory
open scoped ENNReal Topology

namespace DLNFibre.DLN.RLCT

variable {L : ℕ}

/-- **The fully-general Aoyagi learning-coefficient headline** (conditional on the R1 resolution value
`hRValue`, `#72`). For a nondegenerate width vector (`r < H s`), the global learning-coefficient infimum
`⨅ w ∈ optimalSet, rlctAt (dlnLoss B) w` equals Aoyagi's closed form `ofReal (aoyagiLambda H r)`. Proof:

1. `headline_frontRowColPivot_exists` (WLOG) transports the ⨅ to a front-pivoted `B'` and supplies
   `htop`/`hcolfront` for `B'`.
2. D1 `≥`-leg at `B'` (per-`v`): `d1ge_deepestPoint_via_explicit_core_genL_wired`, fed the general deepest
   value (`deepest_regular_core_reduces_frontPivot_front`, `hGne` from `hpos`) + the general hAtV bound
   (`d1ge_hAtV_explicit_close_gen`); `le_antisymm` closes the ⨅ to `rlctAt (deepestPoint)`.
3. Value side: `aoyagi_learning_coefficient_frontPivot_front` (front normal form fed `hRValue` ▸ the
   arithmetic recombination `reg_shift_add_core_eq_aoyagiLambda`).

`aoyagiLambda H r` is `B`-free, so the WLOG transport is value-free on the right. -/
theorem aoyagi_learning_coefficient_gen (H : Fin (L + 1) → ℕ) (r : ℕ)
    (B : Matrix (Fin (H 0)) (Fin (H (Fin.last L))) ℝ) (hB : B.rank = r)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L) (hL2 : 2 ≤ L)
    (hpos : ∀ s : Fin (L + 1), r < H s)
    (hRValue :
      rlctAtOn
          (fun A : Params (fun s => H s - r) =>
            dlnLoss (fun s => H s - r)
              (0 : Matrix (Fin ((fun s => H s - r) 0)) (Fin ((fun s => H s - r) (Fin.last L))) ℝ) A)
          (fun _ => 0 : Params (fun s => H s - r))
        = ENNReal.ofReal (lambdaCore (fun s => H s - r) : ℝ)) :
    (⨅ w ∈ optimalSet H B, rlctAt H (dlnLoss H B) w) = ENNReal.ofReal (aoyagiLambda H r) := by
  -- ===== STEP A: headline row/col-perm WLOG → front-pivot `B'` (+ `htop`/`hcolfront`). =====
  obtain ⟨P, R, hrn, hrH, hB'_rank, hB'_colfront, hB'_top, hinv⟩ :=
    headline_frontRowColPivot_exists H r B hB hL
  set B' : Matrix (Fin (H 0)) (Fin (H (Fin.last L))) ℝ :=
    B.submatrix (R : Fin (H 0) → Fin (H 0)) (P : Fin (H (Fin.last L)) → Fin (H (Fin.last L)))
    with hB'def
  rw [hinv]
  -- ===== LEAF (D1 ≥-leg at `B'`): the ∀-v per-point slot, wired sorry-free for general L. =====
  -- The general deepest value (front reduces, `hGne` discharged from `hpos`) + the general hAtV bound
  -- (`d1ge_hAtV_explicit_close_gen`) feed the wired core `d1ge_deepestPoint_via_explicit_core_genL_wired`
  -- (`m = nRegGen H r = r·(H 0 + H (last) − r)` matches both).
  have hGne := dlnLoss_deepest_core_ae_ne_zero (fun s => H s - r)
    (fun s => Nat.sub_pos_of_lt (hpos s))
  have hDeepest := deepest_regular_core_reduces_frontPivot_front H r B' hB'_rank hr hL hL2 hpos
    hB'_top hB'_colfront hGne
  have hD1ge : ∀ v ∈ optimalSet H B',
      rlctAt H (dlnLoss H B') (deepestPoint H r B' hB'_rank hr hL) ≤ rlctAt H (dlnLoss H B') v :=
    fun v hv => d1ge_deepestPoint_via_explicit_core_genL_wired H r B' hB'_rank hr hL v (nRegGen H r)
      hDeepest (d1ge_hAtV_explicit_close_gen H r B' v hv hB'_rank hpos hL)
  -- ===== STEP B: D1 reduction — ⨅ over `B'` = rlctAt at the deepest point. =====
  have hD1 : (⨅ w ∈ optimalSet H B', rlctAt H (dlnLoss H B') w)
      = rlctAt H (dlnLoss H B') (deepestPoint H r B' hB'_rank hr hL) :=
    le_antisymm
      (iInf₂_le (deepestPoint H r B' hB'_rank hr hL)
        (deepestPoint_isDeep H r B' hB'_rank hr hL).1)
      (le_iInf₂ (fun v hv => hD1ge v hv))
  -- ===== STEP C: the value side — front normal form (fed `hRValue`) ▸ arithmetic recombination. =====
  exact aoyagi_learning_coefficient_frontPivot_front H r B' hB'_rank hr hL hL2 hpos
    hB'_top hB'_colfront hRValue hD1

end DLNFibre.DLN.RLCT
