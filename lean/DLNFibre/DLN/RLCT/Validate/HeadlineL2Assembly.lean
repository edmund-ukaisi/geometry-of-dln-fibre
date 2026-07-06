import DLNFibre.DLN.RLCT.Validate.DeepestFrontGauge
import DLNFibre.DLN.RLCT.Validate.HeadlineRowColPermWLOG
import DLNFibre.DLN.RLCT.Validate.R1ResolutionInterfaceL2
import DLNFibre.DLN.RLCT.Validate.D1L2ExplicitCoreProducer

/-!
# `DLNFibre.DLN.RLCT.Validate.HeadlineL2Assembly` — the L = 2 headline ENDGAME scaffold

This module SCAFFOLDS the `L = 2` instance of the headline
`aoyagi_learning_coefficient` (`Skeleton.lean:1725`) from the L = 2-banked rungs, so that the day
its remaining open leaf lands the headline closes in one step. It does NOT edit `Skeleton.lean`
(single-writer); it states the `L = 2` headline as its own theorem `aoyagi_learning_coefficient_L2`,
assembled from the banked pieces (now including the landed R1 interface) + exactly ONE clearly-named,
route-independent `sorry` leaf — the D1 wall.

## STEP-0 finding (the honest dependency graph — TWO open leaves, not one)

The de-risk brief framed the endgame as "three ready rungs + R1 as the SOLE open leg". Reading the
banked rungs (corroborated decorrelated by Codex xhigh, 2026-06-30) shows the dependency graph is:

  * **VALUE side (L2)** — CLOSED modulo the R1 value. `deepest_regular_core_normal_form_L2_front`
    (#44 at `L = 2`, `hJfront`-free) gives, conditional on the headline-WLOG facts `htop` (#154) +
    `hcolfront` (#100) + the R1 value `hRValue` at the full reduced widths `H − r`, the equality
    `rlctAt (deepestPoint) = nReg/2 + ofReal(lambdaCore (H − r))`; then the PROVEN arithmetic
    recombination `reg_shift_add_core_eq_aoyagiLambda` turns this into `ofReal(aoyagiLambda H r)`.
    `htop`/`hcolfront` are supplied at the headline ⨅ by `headline_frontRowColPivot_exists` (WLOG),
    which also transports the ⨅ from the general `B` to the front-pivoted `B'`. The closed form
    `aoyagiLambda H r` is `B`-free, so the WLOG transport is value-free on the right-hand side.

  * **INFIMUM side (D1)** — its `≥`-direction is a SECOND open obligation, NOT discharged by R1.
    `deepest_point_reduction` turns the ⨅ into `rlctAt (deepestPoint)`, but consumes the ∀-`v`
    per-point slot `rlctAt_deepest_le_of_optimal`
    (`∀ v ∈ optimalSet, rlctAt deepestPoint ≤ rlctAt v`).
    The banked L = 2 D1 thing (`rlctAt_deepest_le_of_optimal_L2`) is NOT that slot: it is per-`v`,
    scoped to a MIDDLE-STRATUM optimal `v` with SQUARE deepest reduced widths, and carries the
    second-peel `(m,a,b)` middle-stratum data + the rank bound `hrank₂` as hypotheses — analytic
    content BEYOND R1 (the per-`v` D1 producer). So the honest scaffold names this leg as its own
    leaf `hD1ge_L2`, distinct from the R1 leaf.

So the scaffold below wires everything mechanical and (as of the R1-interface landing) leaves
exactly ONE named leaf:

  1. **`hR1_L2`** — the route-independent R1 resolution interface (`R1ResolutionInterface`-shaped):
     for every nondegenerate reduced width vector `M`, the deepest DLN core has local RLCT
     `ofReal(lambdaCore M)`. This is the EXACT target the R1-LOWER interior leg must produce; it is
     route-independent (the same value statement regardless of the interior chart route), and it
     discharges the `hRValue` slot of #44 by instantiation at `M = H − r`. **LANDED** — via
     `r1_resolution_interface_L2_generic` (`R1ResolutionInterfaceL2.lean`): the sorry-free
     `IsRouteMCover` assembly (`L = 2` achiever box divergence + depth-2 box finiteness) ∘ the
     cover→rlct bridge ∘ the flat↔params transport ∘ the layer-atlas value lane.
  2. **`hD1ge_L2`** — the D1 `≥`-leg ∀-`v` per-point slot at the front-pivoted `B'` (the ONLY
     remaining open obligation: the per-`v` middle-stratum chart producer, which sequences on R1 but
     is not closed by R1 alone).

When `hD1ge_L2` lands, `aoyagi_learning_coefficient_L2` closes with no further work.
-/

open MeasureTheory
open scoped ENNReal Topology
namespace DLNFibre.DLN.RLCT

variable {L : ℕ}

/-- **The L = 2 headline ENDGAME scaffold.** The `L = 2` instance of `aoyagi_learning_coefficient`,
assembled from the banked rungs + two named-open leaves. The hypotheses `hL2 : 2 ≤ L`,
`hLlt : L < 3` pin `L = 2` (the front-gauge rung's scope); `hr`/`hpos` are the headline domain
(every width `≥ r`,
strict `r < H s` so the reduced widths `M = H − r` are nondegenerate).

The proof:
1. `headline_frontRowColPivot_exists` (WLOG) transports the ⨅ to a front-pivoted `B'` and supplies
   `htop`/`hcolfront` for `B'`.
2. On `B'`: `deepest_point_reduction` (D1, consuming `hD1ge_L2`) turns the ⨅ into
   `rlctAt deepestPoint`.
3. `deepest_regular_core_normal_form_L2_front` (#44, fed `hR1_L2 (H − r)`) + the PROVEN
   `reg_shift_add_core_eq_aoyagiLambda` give `ofReal(aoyagiLambda H r)`.

The two open leaves are stated as the named hypotheses `hR1_L2`, `hD1ge_L2`. -/
theorem aoyagi_learning_coefficient_L2 (H : Fin (L + 1) → ℕ) (r : ℕ)
    (B : Matrix (Fin (H 0)) (Fin (H (Fin.last L))) ℝ) (hB : B.rank = r)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L) (hL2 : 2 ≤ L) (hLlt : L < 3)
    (hpos : ∀ s : Fin (L + 1), r < H s) :
    (⨅ w ∈ optimalSet H B, rlctAt H (dlnLoss H B) w) = ENNReal.ofReal (aoyagiLambda H r) := by
  -- ===== STEP A: the headline-WLOG transport (front-pivot `B'`, supplying htop/hcolfront). =====
  obtain ⟨P, R, hrn, hrH, hB'_rank, hB'_colfront, hB'_top, hinv⟩ :=
    headline_frontRowColPivot_exists H r B hB hL
  set B' : Matrix (Fin (H 0)) (Fin (H (Fin.last L))) ℝ :=
    B.submatrix (R : Fin (H 0) → Fin (H 0)) (P : Fin (H (Fin.last L)) → Fin (H (Fin.last L)))
    with hB'def
  rw [hinv]
  -- ===== LEAF 1 (R1): the route-independent resolution interface — NOW LANDED. =====
  -- The R1-LOWER interior leg's EXACT target: for every nondegenerate reduced-width vector `M`, the
  -- deepest DLN core has local RLCT `ofReal(lambdaCore M)`. Discharged by the banked
  -- `r1_resolution_interface_L2_generic` (`R1ResolutionInterfaceL2.lean`) — the `IsRouteMCover`
  -- assembly (achiever divergence + depth-2 box finiteness) ∘ bridge ∘ transport ∘ value lane.
  have hR1_L2 : ∀ (M : Fin (L + 1) → ℕ), (∀ s, 0 < M s) →
      rlctAtOn
          (fun A : Params M =>
            dlnLoss M (0 : Matrix (Fin (M 0)) (Fin (M (Fin.last L))) ℝ) A)
          (fun _ => 0 : Params M)
        = ENNReal.ofReal (lambdaCore M : ℝ) :=
    fun M hMid => r1_resolution_interface_L2_generic hL2 hLlt M hMid
  -- ===== LEAF 2 (D1): the ∀-v per-point ≥-leg slot at `B'` — WIRED via the EXPLICIT core. =====
  -- The corrected route (genm-d1l2close2 card → genm-hAtV tide): the two-IFT-peel producer is
  -- retired (its second peel routes through the germ-discarding existence-only IFT inverse `Ψsymm`,
  -- so `rlctAtOn(slice-of-q₂) = lambdaCore(M')` is unprovable — only first-order data survives). The
  -- leg now routes through the EXPLICIT homogeneous core `dlnLoss (H−r) 0` (germ-preserving), assembled
  -- by `d1ge_L2_deepestPoint_via_explicit_core_genL` (`D1L2ExplicitCoreProducer`) from THREE pieces:
  --   * the deepest value (#44 `deepest_regular_core_normal_form_L2_front` + banked R1
  --     `r1_resolution_interface_L2_generic`, hbox-free at L = 2);
  --   * `core_zero_le_of_params` — Aoyagi Theorem 4 on the EXPLICIT core (Params-domain, discharged by
  --     the degree-`2L`-homogeneity comparison `deepest_le_of_homogeneous_core`, NOT the blocked
  --     residual-value identity) — the previously-blocked `hCore`;
  --   * `d1ge_L2_hAtV_explicit` — the SOLE remaining crux: the Aoyagi Step-1 explicit corner-elimination
  --     block reduction landing `rlctAt v` on `dlnLoss (H−r) 0` at an explicit reduced-core point.
  -- `hv : v ∈ optimalSet H B'` is `prod H v = B'` definitionally, fed as the producer's `hopt`.
  have hD1ge_L2 : ∀ v ∈ optimalSet H B',
      rlctAt H (dlnLoss H B') (deepestPoint H r B' hB'_rank hr hL)
        ≤ rlctAt H (dlnLoss H B') v :=
    fun v hv => d1ge_L2_deepestPoint_via_explicit_core_genL H r B' hB'_rank hr hL hL2 hpos
      hB'_top hB'_colfront hLlt v hv
  -- ===== STEP B: D1 reduction — ⨅ over `B'` = rlctAt at the constructed deepestPoint. =====
  rw [show (⨅ w ∈ optimalSet H B', rlctAt H (dlnLoss H B') w)
        = rlctAt H (dlnLoss H B') (deepestPoint H r B' hB'_rank hr hL) from
      le_antisymm
        (iInf₂_le (deepestPoint H r B' hB'_rank hr hL)
          (deepestPoint_isDeep H r B' hB'_rank hr hL).1)
        (le_iInf₂ (fun v hv => hD1ge_L2 v hv))]
  -- ===== STEP C: the L2 value side — #44 (fed R1 at M = H−r) ▸ the arithmetic recombination. =====
  rw [deepest_regular_core_normal_form_L2_front H r B' hB'_rank hr hL hL2 hpos
        hB'_top hB'_colfront hLlt
        (hR1_L2 (fun s => H s - r) (fun s => Nat.sub_pos_of_lt (hpos s))),
      reg_shift_add_core_eq_aoyagiLambda H r hr hL]

end DLNFibre.DLN.RLCT
