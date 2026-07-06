import DLNFibre.DLN.RLCT.Validate.DeepestFrontGauge
import DLNFibre.DLN.RLCT.Validate.HeadlineRowColPermWLOG
import DLNFibre.DLN.RLCT.Validate.R1ResolutionInterfaceL2

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
  -- ===== LEAF 2 (D1): the ∀-v per-point ≥-leg slot at `B'` (the second open obligation). =====
  -- The per-`v` D1 producer. Core-geometry (`hrank₂`, via b3) is DONE
  -- (`d1ge_L2_rect_two_peel_hrank_closed`, `D1RectTwoPeelClosed`); the residual is the two ANALYTIC
  -- gates `hRne` (slice non-vanishing) + `hInterface` (R1 degraded core).
  --
  -- FINDING (genm-gatesclose2 tide, 2026-07-06, Codex xhigh corroborated): these gates are NOT
  -- dischargeable through the ∀-`q` wire `hD1ge_L2_rect_of_gates` as literally stated:
  --   * `hRne` (∀ `C²` `q` with the chart equation ⟹ slice a.e.-nonzero) is FALSE without an extra
  --     `rlctAt v > nReg/2`: `q ≡ 0` satisfies the equation at a degenerate core, zero slice.
  --     With that bound it needs a NEW cap lemma `slice_zero_set_caps_rlct_half`
  --     (pos-measure slice zero-set ⟹ `rlctAtOn (∑s²+∑q²) ≤ nReg/2`).
  --   * `hInterface` (∀ `C²` `q₂` ⟹ slice-RLCT `= lambdaCore(MprimeRect …)`) is FALSE ∀-`q₂`:
  --     `R = x² + u⁴` peels to `q₂ = u²`, slice `u⁴`, `rlctAtOn = 1/4 ≠ lambdaCore M'` in general.
  --     It needs a DLN model-identification of the built residual (`R₂ = unit · (dlnLoss M' 0)∘φ`).
  -- gatesclose2 proposed the fix: bind `q`/`q₂` to the CONCRETE producer residual (where b3 gives
  -- `rank(jacResid) = extraCountRect`) and discharge the gates for THAT `q`.
  --
  -- FINDING (genm-d1l2close2 tide, 2026-07-06, Codex xhigh corroborated): binding to the concrete
  -- `q₂` is NOT sufficient — the `hInterface` value gate is blocked at a deeper level than "∀-`q`".
  -- The concrete `q₂` that `d1ge_L2_rect_two_peel_hrank_closed` constructs is the abstract IFT-peel
  -- residual: BOTH peels route through `rlctAtOn_eq_of_contDiff_chart_rinv`, which REPLACES the
  -- explicit DLN polynomial loss by `f ∘ Ψsymm` for an EXISTENCE-ONLY IFT inverse `Ψsymm` (no closed
  -- form, no retained algebraic tie to `dlnLoss`). After two peels `q₂` is defined purely through
  -- `Ψsymm`, `Ψsymm₂`, bump cutoffs. Only FIRST-ORDER data survives (`D1ResidualDerivExpose` exposes
  -- the slice derivative; b3 gives its rank) — enough for `hRne` (slice a.e.-nonzero) but NOT for the
  -- higher-order germ that PINS the RLCT value (`x² + u⁴` peels to slice `u⁴`, `rlctAtOn = 1/4`,
  -- unpinned by first-order data). So `rlctAtOn(slice-of-q₂) = lambdaCore(M')` is UNPROVABLE from
  -- what the producer retains — and the one-sided `lambdaCore(M') ≤ rlctAtOn(slice-of-q₂)` is equally
  -- blocked (any nonzero value handle is absent). Strengthening the chart lemma to return more
  -- derivatives does NOT fix it (finite-jet data do not pin the RLCT).
  --
  -- CORRECTED ROADMAP (Codex-recommended, matches the `genm-d1reduce-aoyagi` de-risk): retire the
  -- two-IFT-peel producer for this leg and route through the EXPLICIT homogeneous core. The banked
  -- `deepest_le_of_optimal_via_L2_ge` + banked `deepest_le_of_homogeneous_core` (DeepestMinRlct,
  -- hypothesis-free: measurable + degree-`D` homogeneous ⟹ `rlctAtOn F 0 ≤ rlctAtOn F v`) reduce the
  -- WHOLE leg to ONE new producer:
  --     `hAtV : (nRegL2 H r)/2 + rlctAtOn (dlnLoss (H−r) 0) corePoint_v ≤ rlctAt H (dlnLoss H B') v`
  -- — the Aoyagi Step-1 explicit iterated corner-elimination block reduction landing `rlctAt v` on
  -- the EXPLICIT DLN core `dlnLoss (H−r) 0` (whose RLCT/homogeneity IS known: R1 + `deepest_le_of_
  -- homogeneous_core`), at an explicit reduced-core point `corePoint_v`. Then `hCore` is the banked
  -- homogeneity comparison, `coreDeepest = rlctAtOn (dlnLoss (H−r) 0) 0`, and NO residual-value
  -- identity / R1-at-`M'` interface is needed. The new producer is a fresh ~600–1500-line tide
  -- (the de-risk's estimate), NOT a gate-discharge for the existing `q₂`. See the genm-d1l2close2
  -- statement card + `codex/crux-answer.md`.
  have hD1ge_L2 : ∀ v ∈ optimalSet H B',
      rlctAt H (dlnLoss H B') (deepestPoint H r B' hB'_rank hr hL)
        ≤ rlctAt H (dlnLoss H B') v := by
    sorry
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
