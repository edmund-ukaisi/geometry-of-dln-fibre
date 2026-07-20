import DLNFibre.DLN.RLCT.Validate.DeepestFrontGaugeGen
import DLNFibre.DLN.RLCT.Validate.HeadlineRowColPermWLOG
import DLNFibre.DLN.RLCT.Validate.D1GeLegGenL
import DLNFibre.DLN.RLCT.Validate.D1GeHAtVClose
import DLNFibre.DLN.RLCT.Validate.R1ResolutionGeneral

/-!
# `DLNFibre.DLN.RLCT.Validate.HeadlineGenAssembly` — the general-`L` headline (conditional on R1)

The FULLY-GENERAL (`L ≥ 3` included) Aoyagi learning-coefficient headline, assembled from the
general-`L` banked rungs, CONDITIONAL on the single R1 resolution value `hRValue` (the `#72` gate —
the reduced-core local RLCT). Mirror of `aoyagi_learning_coefficient_L2` (`HeadlineL2Assembly`):

  * the L=2 gauge/value rungs replaced by the general-`L` hJfront-free FRONT chain
    (`DeepestFrontGaugeGen`: `deepest_regular_core_reduces_frontPivot_front` /
    `aoyagi_learning_coefficient_frontPivot_front`);
  * the L=2 D1 `≥`-leg (`d1ge_L2_deepestPoint_via_explicit_core_genL`) replaced by the general-`L`
    wired core `d1ge_deepestPoint_via_explicit_core_genL_wired` (`D1GeLegGenL`) fed the deepest
    value (the front reduces) + the general hAtV producer `d1ge_hAtV_explicit_close_gen`
    (`D1GeHAtVClose`);
  * the L2-banked R1 interface (`r1_resolution_interface_L2_generic`) replaced by the HYPOTHESIS
    `(□)` = `RouteMBoxThresholdFinite (H − r)` — the box-FINITENESS half of the reduced-core RLCT
    (for every `c' < ½·minAdm` the layer-product box integral is finite). The proven-`∀L` `≤`-half
    (achiever divergence, `routeMCore_box_diverges_achiever_full'`) is folded in via
    `r1_resolution_general`, which turns `(□)` alone into the full reduced-core RLCT value.

So the D1 `≥`-leg, the whole value side, AND the `≤`-half are all WIRED sorry-free for general `L`;
the SOLE open input is the finiteness half `(□)`. Discharging `(□)` (the native `(S,J)`
box-finiteness build, DEFERRED) makes this headline unconditional.
-/

open MeasureTheory
open scoped ENNReal Topology

namespace DLNFibre.DLN.RLCT

variable {L : ℕ}

/-- **The fully-general Aoyagi learning-coefficient headline** (conditional on the box-finiteness
half `(□) = RouteMBoxThresholdFinite (H − r)`). For a nondegenerate width vector (`r < H s`), the
learning-coefficient infimum `⨅ w ∈ optimalSet, rlctAt (dlnLoss B) w` equals
`ofReal (aoyagiLambda H r)`. Proof:

0. `(□) → hRValue`: `r1_resolution_general` folds the proven-`∀L` `≤`-half (achiever divergence)
   with the box-finiteness `(□)` to recover the reduced-core RLCT value.
1. `headline_frontRowColPivot_exists` (WLOG) transports the ⨅ to a front-pivoted `B'` and supplies
   `htop`/`hcolfront` for `B'`.
2. D1 `≥`-leg at `B'` (per-`v`): `d1ge_deepestPoint_via_explicit_core_genL_wired`, fed the general
   deepest value (`deepest_regular_core_reduces_frontPivot_front`, `hGne` from `hpos`) + the general
   hAtV bound (`d1ge_hAtV_explicit_close_gen`); `le_antisymm` closes ⨅ to `rlctAt (deepestPoint)`.
3. Value side: `aoyagi_learning_coefficient_frontPivot_front` (front normal form fed the recovered
   value ▸ the arithmetic recombination `reg_shift_add_core_eq_aoyagiLambda`).

`aoyagiLambda H r` is `B`-free, so the WLOG transport is value-free on the right.

**This is THE honest generic engine for the value `C/2`** (`hbox = (□)` is the SINGLE open half).
It already composes `(□)` (the RLCT lower-bound half) with the BANKED divergence achiever
(`routeMCore_box_diverges_achiever_full'`, the upper-bound half, sorry-free) and `minAdm_eq_cCodim`, so
the value is `rlct = ½·minAdm = ½·cCodim = C/2`. `(□)`'s discharge is IDEAL-LEVEL (Aoyagi Lemma 1 over
the banked resolution), NOT a chart change-of-variables — the α-atlas chart-CoV route is
category-refuted for ALL charts (`cert-full-value-walk` §6), so no `ChartBridgeFaithful`-conditioned
restatement is non-vacuous; `(□)` itself is the satisfiable hypothesis (proven clean-three at `L = 2`
by `routeMBoxThresholdFinite_mnp`, the general-`L` case being the ideal-level follow-up). -/
theorem aoyagi_learning_coefficient_gen (H : Fin (L + 1) → ℕ) (r : ℕ)
    (B : Matrix (Fin (H 0)) (Fin (H (Fin.last L))) ℝ) (hB : B.rank = r)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L) (hL2 : 2 ≤ L)
    (hpos : ∀ s : Fin (L + 1), r < H s)
    (hbox : RouteMBoxThresholdFinite (fun s => H s - r)) :
    (⨅ w ∈ optimalSet H B, rlctAt H (dlnLoss H B) w) = ENNReal.ofReal (aoyagiLambda H r) := by
  -- ===== STEP 0: (□) → reduced-core value. Fold the proven-∀L ≤-half (achiever divergence,
  -- `routeMCore_box_diverges_achiever_full'`) with the box-finiteness `(□) = hbox` via
  -- `r1_resolution_general` — recovering the reduced-core RLCT value the value side consumes. =====
  have hRValue := r1_resolution_general (fun s => H s - r) hL
    (fun s => Nat.sub_pos_of_lt (hpos s)) hbox
  -- ===== STEP A: headline row/col-perm WLOG → front-pivot `B'` (+ `htop`/`hcolfront`). =====
  obtain ⟨P, R, hrn, hrH, hB'_rank, hB'_colfront, hB'_top, hinv⟩ :=
    headline_frontRowColPivot_exists H r B hB hL
  set B' : Matrix (Fin (H 0)) (Fin (H (Fin.last L))) ℝ :=
    B.submatrix (R : Fin (H 0) → Fin (H 0)) (P : Fin (H (Fin.last L)) → Fin (H (Fin.last L)))
    with hB'def
  rw [hinv]
  -- ===== LEAF (D1 ≥-leg at `B'`): the ∀-v per-point slot, wired sorry-free for general L. =====
  -- The general deepest value (front reduces, `hGne` from `hpos`) + the general hAtV bound
  -- (`d1ge_hAtV_explicit_close_gen`) feed the wired core
  -- `d1ge_deepestPoint_via_explicit_core_genL_wired` (`m = nRegGen H r = r·(H 0 + H (last) − r)`).
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
  -- ===== STEP C: value side — front normal form (fed `hRValue`) ▸ arithmetic recombination. =====
  exact aoyagi_learning_coefficient_frontPivot_front H r B' hB'_rank hr hL hL2 hpos
    hB'_top hB'_colfront hRValue hD1

end DLNFibre.DLN.RLCT
