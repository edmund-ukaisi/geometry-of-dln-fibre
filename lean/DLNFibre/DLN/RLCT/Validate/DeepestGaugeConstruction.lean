import DLNFibre.DLN.RLCT.Validate.DeepestGaugeChart
import DLNFibre.DLN.RLCT.Validate.DeepestGaugeBlocks

/-!
# `DLNFibre.DLN.RLCT.Validate.DeepestGaugeConstruction` — the `DeepestGaugeChart` instance (#44c)

The producer for `deepest_gauge_squeeze_exists` (sub-3, the single piece gating #44): construct a
`DeepestGaugeChart H r B` instance at the deepest point. crux2's `DeepestGaugeChart.lean`
(single-writer) carries the `sorry`; this module builds the instance and crux2 wires
`exact deepest_gauge_chart_construct …`.

## The decomposition (design D structure; #155 Part-2 cert; sub-34 g152/g153/g154)

Producing the instance splits into four named obligations (skeleton-first, `sorry` each, then fill):
- **(i) gauge-slice MP reindex** (`deepestSplit_exists`): `nGauge` + `split : flat ≃ₜ DeepestSplit`
  measure-preserving + `split_basepoint`. The per-layer `block_elimination` units `P_s,Q_s` reindex
  the flat params into `(regular residuals) × (raw reduced blocks T_s) × (gauge spectators)`. Pure
  coordinate/measure infra (the `paramsEquivFlat` / S1 idiom).
- **(ii) gauge-absorption homeomorphism** (`coreAbsorb_exists`): `coreAbsorb` turning raw `T_s` into
  `T̃_s = T_s·(I−V_sY_s)⁻¹` (the Schur core), fixing reg+spec + origin. (`schur_P11_decomp`'s `R`.)
- **(iii) g-unit RLCT peel** (`coreAbsorb_rlct_holds`): absorbed and raw cores have the same RLCT at
  the origin, via `weightedThreshold_weight_unit_invariant` (the det-unit `det(I−VY)⁻ᴹ⁰ ≈ 1`).
- **(iv) loss-squeeze** (`deepest_loss_squeeze_holds`): the two-sided bound, via the banked
  `core_comparability_squeeze` + `frobenius_fromBlocks` (g153: leak ∈ ideal(reg) charged to `∑E²`).

## Status

ROUTE-FIRST skeleton: the four sub-lemma signatures + the assembly, all `sorry`. The matrix bedrock
(`DeepestGaugeBlocks`: `twofactor_block_product`, `schur_P11_decomp`, `frobenius_fromBlocks`,
`core_comparability_squeeze`) is GREEN and feeds (iii)+(iv). (i)+(ii) are the heavy geometric part.
-/

open MeasureTheory Matrix
open scoped ENNReal BigOperators Topology
namespace DLNFibre.DLN.RLCT

variable {L : ℕ}

/-- **(i) The gauge-slice MP reindex** (#44c sub-3 part i). At the deepest point, an MP
homeomorphism `split` reindexes the flat params into `DeepestSplit` (regular, raw-core, spectator),
carrying the deepest point to the origin. Per-layer `block_elimination` units + `paramsEquivFlat`;
`nGauge` = the gauge-orbit (spectator) dimension. -/
theorem deepestSplit_exists (H : Fin (L + 1) → ℕ) (r : ℕ)
    (B : Matrix (Fin (H 0)) (Fin (H (Fin.last L))) ℝ) (hB : B.rank = r)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L) :
    ∃ (nGauge : ℕ) (split : (Fin (flatDim H) → ℝ) ≃ₜ DeepestSplit H r nGauge),
      MeasurePreserving split volume volume ∧
        split ((paramsEquivFlat H) (deepestPoint H r B hB hr hL)) = 0 := by
  sorry

/-- **(ii) The gauge-absorption homeomorphism** (#44c sub-3 part ii). A self-homeomorphism of
`DeepestSplit` turning the raw core slot `T_s` into the gauge-normalized `T̃_s = T_s·(I−V_sY_s)⁻¹`
(the Schur core), fixing the regular and spectator slots and the origin. The g-absorption: NON-MP,
unit Jacobian `det(I−VY)⁻ᴹ⁰` (`=1` at the basepoint). -/
theorem coreAbsorb_exists (H : Fin (L + 1) → ℕ) (r nGauge : ℕ) :
    ∃ coreAbsorb : DeepestSplit H r nGauge ≃ₜ DeepestSplit H r nGauge,
      coreAbsorb 0 = 0 ∧
      (∀ q : DeepestSplit H r nGauge, (coreAbsorb q).1 = q.1) ∧
      (∀ q : DeepestSplit H r nGauge, (coreAbsorb q).2.2 = q.2.2) := by
  sorry

/-- **(iii) The g-unit RLCT peel** (#44c sub-3 part iii). The absorbed-core `Φ` and the
raw-disjoint-core `Φ` have the same RLCT at the origin — the bounded-unit Jacobian `det(I−VY)⁻ᴹ⁰` is
peeled via `weightedThreshold_weight_unit_invariant` + `weightedThreshold_transport`. -/
theorem coreAbsorb_rlct_holds (H : Fin (L + 1) → ℕ) (r nGauge : ℕ)
    (coreAbsorb : DeepestSplit H r nGauge ≃ₜ DeepestSplit H r nGauge)
    (hreg : ∀ q : DeepestSplit H r nGauge, (coreAbsorb q).1 = q.1) :
    rlctAtOn
        (fun q : DeepestSplit H r nGauge => (∑ i, q.1 i ^ 2) + deepestCoreF H r (coreAbsorb q).2.1)
        (0 : DeepestSplit H r nGauge)
      = rlctAtOn
          (fun q : DeepestSplit H r nGauge => (∑ i, q.1 i ^ 2) + deepestCoreF H r q.2.1)
          (0 : DeepestSplit H r nGauge) := by
  sorry

/-- **(iv) The loss-squeeze** (#44c sub-3 part iv). Near the deepest point, `dlnLoss H B` is
two-sidedly bounded by `Φ = ∑ regular² + deepestCoreF (absorbed core)`. The banked
`core_comparability_squeeze` (leak ∈ ideal(reg), `∑leak² ≤ t²∑E²`) + `frobenius_fromBlocks`
(`loss = ∑E² + ‖P11‖²`); the g153 raw-`∏T` refutation is dodged (core = the absorbed `T̃`). -/
theorem deepest_loss_squeeze_holds (H : Fin (L + 1) → ℕ) (r nGauge : ℕ)
    (B : Matrix (Fin (H 0)) (Fin (H (Fin.last L))) ℝ) (hB : B.rank = r)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L)
    (split : (Fin (flatDim H) → ℝ) ≃ₜ DeepestSplit H r nGauge)
    (coreAbsorb : DeepestSplit H r nGauge ≃ₜ DeepestSplit H r nGauge) :
    ∃ c₁ c₂ : ℝ, 0 < c₁ ∧ 0 < c₂ ∧
      ∃ U ∈ 𝓝 ((paramsEquivFlat H) (deepestPoint H r B hB hr hL)),
        ∀ w ∈ U,
          0 ≤ ((∑ i, (split w).1 i ^ 2) + deepestCoreF H r (coreAbsorb (split w)).2.1) ∧
          c₁ * ((∑ i, (split w).1 i ^ 2) + deepestCoreF H r (coreAbsorb (split w)).2.1)
            ≤ dlnLoss H B ((paramsEquivFlat H).symm w) ∧
          dlnLoss H B ((paramsEquivFlat H).symm w)
            ≤ c₂ * ((∑ i, (split w).1 i ^ 2) + deepestCoreF H r (coreAbsorb (split w)).2.1) := by
  sorry

/-- **The `DeepestGaugeChart` instance** (#44c sub-3, `deepest_gauge_squeeze_exists`). Assembles the
four obligations into the structure. crux2 wires `deepest_gauge_squeeze_exists := this …`. -/
theorem deepest_gauge_chart_construct (H : Fin (L + 1) → ℕ) (r : ℕ)
    (B : Matrix (Fin (H 0)) (Fin (H (Fin.last L))) ℝ) (hB : B.rank = r)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L) :
    Nonempty (DeepestGaugeChart H r B hB hr hL) := by
  obtain ⟨nGauge, split, hsplit_mp, hsplit_base⟩ := deepestSplit_exists H r B hB hr hL
  obtain ⟨coreAbsorb, hca_base, hca_reg, hca_spec⟩ := coreAbsorb_exists H r nGauge
  exact ⟨{
    nGauge := nGauge
    split := split
    split_mp := hsplit_mp
    split_basepoint := hsplit_base
    coreAbsorb := coreAbsorb
    coreAbsorb_basepoint := hca_base
    coreAbsorb_regular := hca_reg
    coreAbsorb_spectator := hca_spec
    coreAbsorb_rlct := coreAbsorb_rlct_holds H r nGauge coreAbsorb hca_reg
    loss_squeeze := deepest_loss_squeeze_holds H r nGauge B hB hr hL split coreAbsorb }⟩

end DLNFibre.DLN.RLCT
