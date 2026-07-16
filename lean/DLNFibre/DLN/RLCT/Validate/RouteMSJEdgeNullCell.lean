import DLNFibre.DLN.RLCT.Validate.RouteMSJFrontChargeBox
import DLNFibre.DLN.RLCT.Validate.RouteMSJCellRank
import DLNFibre.DLN.RLCT.Validate.RouteMSJDeepRankGen

set_option linter.style.longLine false

/-!
# `RouteMSJEdgeNullCell` — (D) null-disposal: deficient deep-rank cells integrate to `0`

Thread `genm-tideD-joint`, the joint corank-one / rank-sector resolution (D). One of the two pieces the
coupled per-cell target (`coupledBox_lt_top_of_cells`'s `hcell ∀ i`) splits into: the **deficient** deep-rank
cells carry `∫coupledBox = 0`, so only the **generic** cell (`cellRank i = deepTailMin`) needs the real edge/
deep-corank bricks (corankrec's null-set insight, red-teamed and confirmed for Route B — the deficient cells
are genuinely null, the divergence lives on the positive-measure generic cell).

**Mechanism.** The deep-atlas cell `i` fixes the deep-factor rank at `cellRank i` exactly
(`prod_rank_eq_cellRankIndex`, corankrec's bridge `RouteMSJCellRank`). When `cellRank i < deepTailMin M`,
the cell lies inside `{p | rank (deeperFlagZdeep M u p.1) < deepTailMin M}`, which — since
`deepFactor_rank_ge_deepTailMin_ae` puts the deep rank `≥ deepTailMin` a.e. — is a null set (`N ×ˢ univ`,
`N` null in the `z`-marginal). Integrating ANY integrand over a null set gives `0` (`setLIntegral_measure_zero`);
in particular `∫coupledBox = 0 < ⊤`. Integrand-agnostic: no analysis of `coupledBoxIntegrand` is used.
-/

namespace DLNFibre.DLN.RLCT

open Matrix MeasureTheory DeepAtlas
open scoped ENNReal

variable {L : ℕ}

/-- **The deep factor as a `prod` of the projected deep params.** `deeperFlagZdeep M u p.1 =
prod (dropHead (redChain u M)) (projDeep M u p)` — both unfold to `prod (dropHead (redChain u M))
((paramsHeadSplit (redChain u M) p.1).2)`. The bridge between `deepFactor_rank_ge_deepTailMin_ae` (stated on
`deeperFlagZdeep`) and `prod_rank_eq_cellRankIndex` (stated on `prod H · `). -/
theorem deeperFlagZdeep_eq_prod_projDeep (M : Fin (L + 1 + 1 + 1) → ℕ) (u : ℕ)
    (p : Params (redChain u M) × (Fin (M 1 - u) → Fin (M 2) → ℝ)) :
    deeperFlagZdeep M u p.1 = prod (dropHead (redChain u M)) (projDeep M u p) := rfl

/-- **Null-disposal — a deficient deep-rank cell integrates `coupledBox` to `0`.** For a deep-atlas index
`i` with `cellRank i < deepTailMin M` (a rank-deficient cell), the coupled-box integral over the cell
`box ∩ projDeep⁻¹'(deepCell … i)` is `0`. The cell sits in the a.e.-null low-rank locus of the deep factor
(via corankrec's exact rank bridge + the generic-rank a.e. floor), so `setLIntegral_measure_zero` closes it —
independently of `c'` and of the integrand. This disposes ALL deficient cells; only the generic cell
(`cellRank i = deepTailMin`) is left for the edge / deep-corank / interior bricks. -/
theorem coupledBox_deficientCell_null (M : Fin (L + 1 + 1 + 1) → ℕ) (u : ℕ) (c' : ℝ)
    (i : CRIndex (dropHead (redChain u M)))
    (hdef : cellRankIndex (dropHead (redChain u M)) i < deepTailMin M) :
    ∫⁻ p in (paramsBoxM (redChain u M) 1 ×ˢ matBox (M 1 - u) (M 2) 1)
        ∩ projDeep M u ⁻¹' (deepCell (dropHead (redChain u M)) (dropHead (redChain u M) 0) L
            le_rfl (dropHead (redChain u M) (Fin.last L)) i
            (fun _ => (1 : Matrix (Fin (dropHead (redChain u M) (Fin.last L)))
              (Fin (dropHead (redChain u M) (Fin.last L))) ℝ))),
        coupledBoxIntegrand M u c' p = 0 := by
  classical
  -- the low-rank locus in the `z`-marginal is null (generic-rank a.e. floor)
  set Nz : Set (Params (redChain u M)) :=
    {z | (deeperFlagZdeep M u z).rank < deepTailMin M} with hNz
  have hNnull : volume Nz = 0 := by
    have hae := deepFactor_rank_ge_deepTailMin_ae M u
    rw [ae_iff] at hae
    have hset : Nz = {z | ¬ deepTailMin M ≤ (deeperFlagZdeep M u z).rank} := by
      ext z; simp only [hNz, Set.mem_setOf_eq, not_le]
    rw [hset]; exact hae
  -- the product low-rank locus is null (`Nz ×ˢ univ`)
  set Bad : Set (Params (redChain u M) × (Fin (M 1 - u) → Fin (M 2) → ℝ)) :=
    {p | (deeperFlagZdeep M u p.1).rank < deepTailMin M} with hBad
  have hBadnull : volume Bad = 0 := by
    have hprod : Bad = Nz ×ˢ (Set.univ : Set (Fin (M 1 - u) → Fin (M 2) → ℝ)) := by
      ext p; simp only [hBad, hNz, Set.mem_setOf_eq, Set.mem_prod, Set.mem_univ, and_true]
    rw [hprod, Measure.volume_eq_prod, Measure.prod_prod, hNnull, zero_mul]
  -- the cell lies inside the null low-rank locus (exact rank bridge)
  have hsub : ((paramsBoxM (redChain u M) 1 ×ˢ matBox (M 1 - u) (M 2) 1)
      ∩ projDeep M u ⁻¹' (deepCell (dropHead (redChain u M)) (dropHead (redChain u M) 0) L
        le_rfl (dropHead (redChain u M) (Fin.last L)) i
        (fun _ => (1 : Matrix (Fin (dropHead (redChain u M) (Fin.last L)))
          (Fin (dropHead (redChain u M) (Fin.last L))) ℝ)))) ⊆ Bad := by
    intro p hp
    have hmem : projDeep M u p ∈ deepCell (dropHead (redChain u M)) (dropHead (redChain u M) 0) L
        le_rfl (dropHead (redChain u M) (Fin.last L)) i
        (fun _ => (1 : Matrix (Fin (dropHead (redChain u M) (Fin.last L)))
          (Fin (dropHead (redChain u M) (Fin.last L))) ℝ)) := hp.2
    have hbridge := prod_rank_eq_cellRankIndex (dropHead (redChain u M)) (dropHead (redChain u M) 0)
      (projDeep M u p) i hmem
    change (deeperFlagZdeep M u p.1).rank < deepTailMin M
    rw [deeperFlagZdeep_eq_prod_projDeep M u p, hbridge]
    exact hdef
  -- integrate over a null set
  exact setLIntegral_measure_zero _ _ (measure_mono_null hsub hBadnull)

end DLNFibre.DLN.RLCT
