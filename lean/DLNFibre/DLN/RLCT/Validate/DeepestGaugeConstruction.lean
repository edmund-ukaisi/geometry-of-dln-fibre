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
  the per-layer **Schur complement** `S_s = T_s − Z_s(I+X_s)⁻¹Y_s` (g156/#61: the honest core,
  NOT the unit `T_s·(I−V_sY_s)⁻¹` which is `0` at `T_s=0`); `∏S_s = R|{E=0}` (`schur_P11_decomp`'s
  full-product Schur `R`), fixing reg+spec + origin.
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

/-! ## The slot-grouping contract (controller precision pin, option (e))

The #64 confound (and its subtler "wrong grouping" form) recurs unless the `split` slot-semantics
are a STATED, durable contract — not a verbal agreement. The honest contract (controller): `split`
delivers semantically **role-grouped RAW slots** (a measure-preserving `det = ±1` reindex), and the
nonlinear gauge work lives in the absorptions (`regAbsorb` → `E`, `coreAbsorb` → the Schur `S_s`),
each a clean unit-Jacobian self-map of `DeepestSplit`. So the contract `split` must satisfy is: its
slots **decode** to the per-layer gauge blocks `(X_s, Y_s, Z_s, T_s)` — pinned here as the consuming
interface `PerLayerGaugeBlocks` + the `gaugeDecode` map, so the grouping survives as bedrock.
-/

/-- The per-layer gauge blocks of a rank-`r`-sliced point: for each layer `s : Fin L`, the
`(X_s, Y_s, Z_s, T_s)` decomposition of `C_s = [[I_r+X_s, Y_s],[Z_s, T_s]]` (`X_s : r×r`,
`Y_s : r×(H_{s+1}−r)`, `Z_s : (H_s−r)×r`, `T_s : (H_s−r)×(H_{s+1}−r)`). The decode target of the
split slots — `regAbsorb` reads `(X,Y,Z)` for `E`, `coreAbsorb` reads all four for `S_s`. -/
abbrev PerLayerGaugeBlocks (H : Fin (L + 1) → ℕ) (r : ℕ) : Type :=
  ∀ s : Fin L,
    (Matrix (Fin r) (Fin r) ℝ) × (Matrix (Fin r) (Fin (H s.succ - r)) ℝ)
      × (Matrix (Fin (H s.castSucc - r)) (Fin r) ℝ)
      × (Matrix (Fin (H s.castSucc - r)) (Fin (H s.succ - r)) ℝ)

/-- **The slot-grouping contract** (controller precision pin). A `split`'s `DeepestSplit` slots
decode — via a continuous, basepoint-preserving map — to the per-layer gauge blocks. The durable
the absorptions consume: it pins WHICH slot-entry is which `(X_s,Y_s,Z_s,T_s)` block, so the #64
"wrong grouping" confound cannot recur. `split` must provide a `gaugeDecode` satisfying this;
`regAbsorb`/`coreAbsorb` read it. (Reg slot = the `X/Y/Z` gauge entries `E` reads; core = `T_s`;
split is `det = ±1`, the absorptions carry the gauge nonlinearity.) -/
structure IsGaugeSliceDecode (H : Fin (L + 1) → ℕ) (r : ℕ) (nGauge : ℕ)
    (gaugeDecode : DeepestSplit H r nGauge → PerLayerGaugeBlocks H r) : Prop where
  /-- The decode is continuous (the slots are a coordinate regrouping). -/
  continuous : Continuous gaugeDecode
  /-- At the split origin (the deepest basepoint), every gauge block is `0` (the deepest point is
  the block-normal rank-`r` chain: `X_s=Y_s=Z_s=T_s=0`, i.e. `C_s = blockdiag[I_r, 0]`). -/
  basepoint : gaugeDecode 0 = fun _ => (0, 0, 0, 0)

/-- **The bundled gauge-slice construction** (#44c sub-3, the COUPLED obligation). The four fields
are properties of the SAME maps `(split, coreAbsorb)`, so they bundle into one existence statement
(the loss-squeeze + RLCT-peel are FALSE for arbitrary maps — they hold only for the specific gauge
maps). Producing this is the heavy geometric construction:
- `split`: the `block_elimination` MP reindex (flat ⟶ regular ⊕ raw-core ⊕ spectator),
  `split_basepoint` carries the deepest point to `0`;
- `coreAbsorb`: the g-absorption `T_s ↦ S_s = T_s − Z_s(I+X_s)⁻¹Y_s` (the per-layer **Schur
  complement**, g156/#61 — NOT the unit `T_s·(I−V_sY_s)⁻¹`), fixing reg+spec+origin;
- `coreAbsorb_rlct`: the bounded-unit Jacobian peel (`det(I−VY)⁻ᴹ⁰` via
  `weightedThreshold_weight_unit_invariant`);
- `loss_squeeze`: the two-sided bound (banked `core_comparability_squeeze` + `frobenius_fromBlocks`,
  g153: leak ∈ ideal(reg) charged to `∑E²`; core = Schur `∏S_s` = `R` on `{E=0}`, NOT raw `∏T`). -/
theorem deepest_gauge_construction (H : Fin (L + 1) → ℕ) (r : ℕ)
    (B : Matrix (Fin (H 0)) (Fin (H (Fin.last L))) ℝ) (hB : B.rank = r)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L) :
    ∃ (nGauge : ℕ) (split : (Fin (flatDim H) → ℝ) ≃ₜ DeepestSplit H r nGauge)
      (coreAbsorb regAbsorb : DeepestSplit H r nGauge ≃ₜ DeepestSplit H r nGauge),
      MeasurePreserving split volume volume ∧
      split ((paramsEquivFlat H) (deepestPoint H r B hB hr hL)) = 0 ∧
      coreAbsorb 0 = 0 ∧
      (∀ q : DeepestSplit H r nGauge, (coreAbsorb q).1 = q.1) ∧
      (∀ q : DeepestSplit H r nGauge, (coreAbsorb q).2.2 = q.2.2) ∧
      rlctAtOn
          (fun q : DeepestSplit H r nGauge => (∑ i, q.1 i ^ 2) + deepestCoreF H r (coreAbsorb q).2.1)
          (0 : DeepestSplit H r nGauge)
        = rlctAtOn
            (fun q : DeepestSplit H r nGauge => (∑ i, q.1 i ^ 2) + deepestCoreF H r q.2.1)
            (0 : DeepestSplit H r nGauge) ∧
      regAbsorb 0 = 0 ∧
      (∀ q : DeepestSplit H r nGauge, (regAbsorb q).2.1 = q.2.1) ∧
      (∀ q : DeepestSplit H r nGauge, (regAbsorb q).2.2 = q.2.2) ∧
      rlctAtOn
          (fun q : DeepestSplit H r nGauge =>
            (∑ i, (regAbsorb q).1 i ^ 2) + deepestCoreF H r (coreAbsorb q).2.1)
          (0 : DeepestSplit H r nGauge)
        = rlctAtOn
            (fun q : DeepestSplit H r nGauge =>
              (∑ i, q.1 i ^ 2) + deepestCoreF H r (coreAbsorb q).2.1)
            (0 : DeepestSplit H r nGauge) ∧
      ∃ c₁ c₂ : ℝ, 0 < c₁ ∧ 0 < c₂ ∧
        ∃ U ∈ 𝓝 ((paramsEquivFlat H) (deepestPoint H r B hB hr hL)),
          ∀ w ∈ U,
            0 ≤ ((∑ i, (regAbsorb (split w)).1 i ^ 2)
                + deepestCoreF H r (coreAbsorb (split w)).2.1) ∧
            c₁ * ((∑ i, (regAbsorb (split w)).1 i ^ 2)
                + deepestCoreF H r (coreAbsorb (split w)).2.1)
              ≤ dlnLoss H B ((paramsEquivFlat H).symm w) ∧
            dlnLoss H B ((paramsEquivFlat H).symm w)
              ≤ c₂ * ((∑ i, (regAbsorb (split w)).1 i ^ 2)
                + deepestCoreF H r (coreAbsorb (split w)).2.1) := by
  sorry

/-- **The `DeepestGaugeChart` instance** (#44c sub-3, `deepest_gauge_squeeze_exists`). Destructures
the bundled construction into the structure. crux2 wires `deepest_gauge_squeeze_exists := this`. -/
theorem deepest_gauge_chart_construct (H : Fin (L + 1) → ℕ) (r : ℕ)
    (B : Matrix (Fin (H 0)) (Fin (H (Fin.last L))) ℝ) (hB : B.rank = r)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L) :
    Nonempty (DeepestGaugeChart H r B hB hr hL) := by
  obtain ⟨nGauge, split, coreAbsorb, regAbsorb, hsplit_mp, hsplit_base, hca_base, hca_reg, hca_spec,
    hca_rlct, hra_base, hra_core, hra_spec, hra_rlct, hsq⟩ :=
    deepest_gauge_construction H r B hB hr hL
  exact ⟨{
    nGauge := nGauge
    split := split
    split_mp := hsplit_mp
    split_basepoint := hsplit_base
    coreAbsorb := coreAbsorb
    coreAbsorb_basepoint := hca_base
    coreAbsorb_regular := hca_reg
    coreAbsorb_spectator := hca_spec
    coreAbsorb_rlct := hca_rlct
    regAbsorb := regAbsorb
    regAbsorb_basepoint := hra_base
    regAbsorb_core := hra_core
    regAbsorb_spectator := hra_spec
    regAbsorb_rlct := hra_rlct
    loss_squeeze := hsq }⟩

end DLNFibre.DLN.RLCT
