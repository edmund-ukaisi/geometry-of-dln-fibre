import DLNFibre.DLN.RLCT.Skeleton
import DLNFibre.DLN.RLCT.Foundations.S1Spectator
import DLNFibre.DLN.RLCT.Foundations.S1NonMPTransport

/-!
# `DLNFibre.DLN.RLCT.Validate.DeepestGaugeChart` — the L2 deepest-point gauge-slice normal form (#44)

The heavy geometric obligation of L2 (`product_reduction`): at the deepest point (every layer rank
exactly `r`), the local RLCT of `dlnLoss H B` splits as the **regular gauge shift** `nReg/2`
(`nReg = r(H⁰+Hᴸ−r)` nondegenerate gauge-orbit-transversal directions, Fubini-additive `S1.5`) plus
the **reduced singular core** `rlctAtOn (dlnLoss M 0) 0` on the reduced widths `M = H−r`.

This is the **VALUE-FREE** L2 reduction (`deepest_regular_core_reduces`): it lands on
`rlctAtOn (dlnLoss M 0) 0`, the core RLCT at its deepest point — NOT on the closed form
`ofReal(lambdaCore M)`. Folding the core value `rlctAtOn (dlnLoss M 0) 0 = ofReal(lambdaCore M)` is
**R1** (`resolution_charts` + A1), kept separate (the gauge chart carries no `lambdaCore`).

## The mechanism (pp-hall cert g150, decorrelated Codex; g147 skeleton)

At a deepest point `w0` with `IsDeepLayers H r B w0` (every layer rank exactly `r`), gauge-slice each
layer. By `block_elimination` there are units `P_s,Q_s` with `P_s (w0 s) Q_s = blockdiag[I_r,0]`; in
the gauge coords each layer is `C_s = [[I_r+X_s, Y_s],[Z_s, T_s]]`, the reduced block `T_s` of width
`M_s = H_s − r`. The product residuals `E = (∏C − blockdiag[I_r,0])` on the `(0,0),(0,1),(1,0)` blocks
are the `nReg` regular coords (Jacobian rank `= nReg` at the chain endpoints). **The reduced core is
the GAUGE-NORMALIZED chain `‖T̃₁···T̃_L‖² = dlnLoss M 0` (the `core` coords), NOT the raw `‖∏T_s‖²`**
(g150-fix; Codex caught the raw-`T` error): on `{E=0}` the internal gauge unit `(I−V_sY_s)⁻¹` sits
between layers, so the honest reduced chain is `T̃_s = T_s` with that unit absorbed (the product Schur
complement). The raw-`∏T` form is FALSE for matrices (`‖T·g·S‖²/‖TS‖²→∞`). The `core` slot of `split`
carries the `T̃`-normalized chain — the structure is abstract over it; the gauge-normalization is the
chart's (cobuild-sub34's) obligation. The transport is the local SQUEEZE (`rlctAtOn_squeeze`), not the
over-reaching global chart (sub-34 g152: the gauge slice is a LOCAL diffeo).

## Route status

ROUTE-FIRST: structure pinned (g147) + 7 sub-lemma signatures + the value-free assembly, all `sorry`.
The reachable sub-lemmas (1,2,5,6,7) route through green primitives; the heavy chart-existence
(sub-3,4) is the g150-cert-backed block algebra (#44c). The Skeleton `deepest_regular_core_normal_form`
discharge = this reduction `▸` the R1 core value (controller wires, single-writer for Skeleton).
-/

open MeasureTheory Matrix
open scoped ENNReal BigOperators Topology
namespace DLNFibre.DLN.RLCT

variable {L : ℕ}

/-- The reduced widths `M = H − r` (the deepest-point reduced chain). -/
abbrev deepestM (H : Fin (L + 1) → ℕ) (r : ℕ) : Fin (L + 1) → ℕ := fun s => H s - r

/-- The regular gauge-orbit-transversal dimension `nReg = r(H⁰+Hᴸ−r)`. -/
abbrev deepestNReg (H : Fin (L + 1) → ℕ) (r : ℕ) : ℕ := r * (H 0 + H (Fin.last L) - r)

/-- The split codomain: `(regular nReg) × ((reduced core flatDim M) × (spectators nGauge))`. -/
abbrev DeepestSplit (H : Fin (L + 1) → ℕ) (r nGauge : ℕ) : Type :=
  (Fin (deepestNReg H r) → ℝ)
    × ((Fin (flatDim (deepestM H r)) → ℝ) × (Fin nGauge → ℝ))

/-- The RAW reduced-core loss in flat coordinates: `‖∏ T_s‖² = dlnLoss M 0` via the fixed flattening
`paramsEquivFlat M`. (The additive-block + spectator-peel run on this raw disjoint core; the
gauge-normalized `T̃` core reaches it through `coreAbsorb` + `coreAbsorb_rlct`.) -/
noncomputable abbrev deepestCoreF (H : Fin (L + 1) → ℕ) (r : ℕ)
    (y : Fin (flatDim (deepestM H r)) → ℝ) : ℝ :=
  dlnLoss (deepestM H r)
    (0 : Matrix (Fin (deepestM H r 0)) (Fin (deepestM H r (Fin.last L))) ℝ)
    ((paramsEquivFlat (deepestM H r)).symm y)

/-- The layer partial-product matrix is continuous in the parameters (induction on chain length:
base `prodAux 0 = 1` constant; step `prodAux (k+1) = prodAux k * (layer k)`, the cast-transported
`k`-th layer normalised by `simp only [e1, e2, eq_mpr_eq_cast, cast_eq]` to the plain projection,
then `Continuous.matrix_mul`). Local helper — `fun_prop` deep-recurses on `prodAux`; lift to a shared
`Foundations` home (downstream of the `Params` topology) at #28. -/
private theorem continuous_prodAux (H : Fin (L + 1) → ℕ) (k : ℕ) (hk : k < L + 1) :
    Continuous (fun A : Params H => prodAux H A k hk) := by
  revert hk
  induction k with
  | zero =>
      intro hk
      simpa [prodAux] using
        (continuous_const :
          Continuous (fun _ : Params H => (1 : Matrix (Fin (H 0)) (Fin (H 0)) ℝ)))
  | succ k ih =>
      intro hk
      have hk' : k < L + 1 := Nat.lt_of_succ_lt hk
      have hkL : k < L := Nat.lt_of_succ_lt_succ hk
      have e1 : (⟨k, hk'⟩ : Fin (L + 1)) = (⟨k, hkL⟩ : Fin L).castSucc := by
        apply Fin.ext; simp [Fin.castSucc]
      have e2 : (⟨k + 1, hk⟩ : Fin (L + 1)) = (⟨k, hkL⟩ : Fin L).succ := by
        apply Fin.ext; simp [Fin.succ]
      let layer : Params H → Matrix (Fin (H ⟨k, hk'⟩)) (Fin (H ⟨k + 1, hk⟩)) ℝ :=
        fun A => ((by rw [e1, e2]; exact A ⟨k, hkL⟩) :
          Matrix (Fin (H ⟨k, hk'⟩)) (Fin (H ⟨k + 1, hk⟩)) ℝ)
      have hLayer : Continuous layer := by
        dsimp [layer]
        simpa only [e1, e2, eq_mpr_eq_cast, cast_eq] using
          (continuous_apply (⟨k, hkL⟩ : Fin L) :
            Continuous (fun A : Params H => A ⟨k, hkL⟩))
      have hMul : Continuous (fun A : Params H => prodAux H A k hk' * layer A) :=
        (ih hk').matrix_mul hLayer
      exact hMul.congr fun A => by dsimp [layer]; rfl

/-- The multiplication map is continuous (`continuous_prodAux` at `k = L`). Local helper. -/
private theorem continuous_prod (H : Fin (L + 1) → ℕ) : Continuous (prod H) :=
  continuous_prodAux H L (Nat.lt_succ_self L)

/-- **`dlnLoss H B` is continuous** (hence measurable) — a finite sum of squares of entries of
`prod H A − B`. The integrand measurability `fun_prop` cannot get (deep-recurses on `prodAux`).
Local helper; lift to a shared `Foundations` home at #28. -/
theorem continuous_dlnLoss (H : Fin (L + 1) → ℕ)
    (B : Matrix (Fin (H 0)) (Fin (H (Fin.last L))) ℝ) :
    Continuous (dlnLoss H B) := by
  unfold dlnLoss
  apply continuous_finset_sum; intro i _
  apply continuous_finset_sum; intro j _
  have hc : Continuous (fun A : Params H => (prod H A - B) i j) := by
    simp only [Matrix.sub_apply]
    exact ((continuous_prod H).matrix_elem i j).sub continuous_const
  exact hc.pow 2

/-- **The deepest-point gauge-slice squeeze datum** (R-squeeze; g150 cert + the sub-34 g152 finding).
At a rank-`r`-exact deepest point, a measure-preserving coordinate reindex `split` of the flat
parameter space `Fin (flatDim H) → ℝ` into `nReg` regular gauge directions, the reduced core
`Fin (flatDim M) → ℝ`, and `nGauge` spectators, under which the loss `dlnLoss H B` (in flat coords) is
**two-sidedly squeezed** near the deepest point by `Φ = ∑ regular² + dlnLoss M 0 (core)`:
`c₁·Φ ≤ loss ≤ c₂·Φ` with `0 < c₁, c₂`.

**Why a SQUEEZE, not a chart equality (sub-34 g152, decorrelated):** the honest gauge slice is a LOCAL
diffeo (its inverse uses `(I_r+X)⁻¹`, `(I−VY)⁻¹` — blows up off the deepest point), so the global
`chart : Flat ≃ₜ Flat` + `∀x HasFDerivAt` of the chart-equality form over-reaches (possibly unsound).
`rlctAtOn` is local, so the squeeze (`rlctAtOn_squeeze`) is the right altitude — matching the blessed
per-node `schur_recursion_step_squeeze`. The squeeze's core is the GAUGE-NORMALIZED chain (the gauge
unit `(I−VY)⁻¹` between layers makes the raw-`∏T` squeeze FALSE for matrices; the `Φ`-core
`dlnLoss M 0 (core)` is the `T̃`-normalized chain in the `core` coords). -/
structure DeepestGaugeChart (H : Fin (L + 1) → ℕ) (r : ℕ)
    (B : Matrix (Fin (H 0)) (Fin (H (Fin.last L))) ℝ) (hB : B.rank = r)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L) where
  /-- The spectator-coordinate count (the remaining flat directions). -/
  nGauge : ℕ
  /-- The coordinate split: flat `H`-params ≃ₜ `(regular nReg) × ((reduced core flatDim M) × (spectators))`,
  a MEASURE-PRESERVING reindex (so the core slot holds the RAW layer blocks `T_s`). -/
  split : (Fin (flatDim H) → ℝ) ≃ₜ DeepestSplit H r nGauge
  /-- `split` is measure-preserving (a coordinate reindex). -/
  split_mp : MeasurePreserving split volume volume
  /-- `split` carries the flat image of the deepest point to the split origin (deviation coords `= 0`). -/
  split_basepoint : split ((paramsEquivFlat H) (deepestPoint H r B hB hr hL)) = 0
  /-- **The gauge-absorption** on split coords (sub-34 g153): a self-homeomorphism that turns the RAW
  core slot `T_s` into the GAUGE-NORMALIZED `T̃_s = T_s·(I−V_sY_s)⁻¹` (the product Schur complement),
  fixing the regular and spectator slots. NON-MP (unit Jacobian `det(I−VY)^{−M0}`, `=1` at the basepoint)
  — needed because the raw-`∏T` squeeze is FALSE for matrices, and a pure MP `split` cannot produce `T̃`. -/
  coreAbsorb : DeepestSplit H r nGauge ≃ₜ DeepestSplit H r nGauge
  /-- `coreAbsorb` fixes the origin. -/
  coreAbsorb_basepoint : coreAbsorb 0 = 0
  /-- `coreAbsorb` fixes the regular slot. -/
  coreAbsorb_regular : ∀ q : DeepestSplit H r nGauge, (coreAbsorb q).1 = q.1
  /-- `coreAbsorb` fixes the spectator slot. -/
  coreAbsorb_spectator : ∀ q : DeepestSplit H r nGauge, (coreAbsorb q).2.2 = q.2.2
  /-- **The producer's unit-Jacobian absorption identity** (the one hard g-unit-peel field, sub-34's
  obligation): the absorbed-core `Φ` and the raw-disjoint-core `Φ` have the SAME RLCT at the origin.
  Proof intent: `π := coreAbsorb`, `rawΦ ∘ π = absorbedΦ` (via `coreAbsorb_regular`),
  `weightedThreshold_transport` deposits `|det Dπ|` in the weight, `weightedThreshold_weight_unit_invariant`
  peels the bounded unit (`det(I−VY)^{−M0}`). -/
  coreAbsorb_rlct :
    rlctAtOn
        (fun q : DeepestSplit H r nGauge => (∑ i, q.1 i ^ 2) + deepestCoreF H r (coreAbsorb q).2.1)
        (0 : DeepestSplit H r nGauge)
      = rlctAtOn
          (fun q : DeepestSplit H r nGauge => (∑ i, q.1 i ^ 2) + deepestCoreF H r q.2.1)
          (0 : DeepestSplit H r nGauge)
  /-- **The regular-absorption** on split coords (g161, the (e)-fix). The split's regular slot is the
  RAW gauge pivots `(X,Y,Z)`, NOT the nonlinear regular residual `E = X₁+X₂+X₁X₂+…` the squeeze needs
  (`loss_squeeze` over `(split w).1` raw is FALSE, g161 counterexample). `regAbsorb` is a self-homeo
  turning the raw reg slot into `E`, fixing the core and spectator slots — symmetric to `coreAbsorb`
  (which turns the raw core into the Schur `S_s`, fixing reg+spec). NON-MP (bounded-unit Jacobian, `=1`
  at the basepoint via the IFT `dE(0)=id`); the MAP is the producer's (cobuild-sub34's IFT diffeo). -/
  regAbsorb : DeepestSplit H r nGauge ≃ₜ DeepestSplit H r nGauge
  /-- `regAbsorb` fixes the origin. -/
  regAbsorb_basepoint : regAbsorb 0 = 0
  /-- `regAbsorb` fixes the core slot. -/
  regAbsorb_core : ∀ q : DeepestSplit H r nGauge, (regAbsorb q).2.1 = q.2.1
  /-- `regAbsorb` fixes the spectator slot. -/
  regAbsorb_spectator : ∀ q : DeepestSplit H r nGauge, (regAbsorb q).2.2 = q.2.2
  /-- **The regular-unit RLCT peel** (the (e)-fix's reg-side, peeled FIRST so it composes with
  `coreAbsorb_rlct`): the reg-absorbed `Φ` (regular through `regAbsorb`, core already through `coreAbsorb`)
  and the reg-raw `Φ` have the SAME RLCT at the origin. Sequenced: `regAbsorb_rlct` peels the reg unit
  (core stays `coreAbsorb`'d), then `coreAbsorb_rlct` peels the core unit. Discharged via
  `rlctAtOn_boundedUnit_localHomeomorph` (crux2 #72): `regAbsorb` is a local diffeo, `|det| = 1` at `0`. -/
  regAbsorb_rlct :
    rlctAtOn
        (fun q : DeepestSplit H r nGauge =>
          (∑ i, (regAbsorb q).1 i ^ 2) + deepestCoreF H r (coreAbsorb q).2.1)
        (0 : DeepestSplit H r nGauge)
      = rlctAtOn
          (fun q : DeepestSplit H r nGauge =>
            (∑ i, q.1 i ^ 2) + deepestCoreF H r (coreAbsorb q).2.1)
          (0 : DeepestSplit H r nGauge)
  /-- **The loss-squeeze datum** (g161 (e)-form). Near the deepest point, `dlnLoss H B` is two-sidedly
  bounded by `Φ = ∑ (regAbsorb (split w)).1² + deepestCoreF (coreAbsorb (split w)).2.1` — the regular
  slot through `regAbsorb` (→ the nonlinear residual `E`), the core slot through `coreAbsorb` (→ the
  Schur core). Both gauge units; symmetric. The matrix comparability is cobuild-sub34's (the banked
  `core_comparability_squeeze`). -/
  loss_squeeze :
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
              + deepestCoreF H r (coreAbsorb (split w)).2.1)

/-- **Smart constructor from an EXACT germ** — a CONVENIENCE for the special case `c₁ = c₂ = 1`. If a
producer delivers `dlnLoss H B ∘ flatSymm =ᶠ[𝓝 wstar] Φ` (an EXACT germ equality), it discharges
`loss_squeeze` trivially. **NOTE (precision, "name results for what they are"):** the ACTUAL
gauge-normalized comparability is a genuine SQUEEZE, NOT exact — cobuild-sub34's `core_comparability_squeeze`
(#54) proves `(2(1+t²))⁻¹·Φ ≤ loss ≤ (2+2t²)·Φ` (`c₁ < c₂`, the regular×regular leak `≤ t²∑E²` charged
to the regular block, `t = ‖pivot‖ → 0` at `w0`). So `loss_squeeze` is kept GENERAL (`c₁, c₂` > 0, not
narrowed to exact), and cobuild-sub34 populates it DIRECTLY with those constants — NOT via `ofExactGerm`.
This helper is for any genuinely-exact consumer only. NO global chart / `jac_unit` / measure-Jacobian. -/
noncomputable def DeepestGaugeChart.ofExactGerm (H : Fin (L + 1) → ℕ) (r : ℕ)
    (B : Matrix (Fin (H 0)) (Fin (H (Fin.last L))) ℝ) (hB : B.rank = r)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L)
    (nGauge : ℕ)
    (split : (Fin (flatDim H) → ℝ) ≃ₜ DeepestSplit H r nGauge)
    (split_mp : MeasurePreserving split volume volume)
    (split_basepoint : split ((paramsEquivFlat H) (deepestPoint H r B hB hr hL)) = 0)
    (coreAbsorb : DeepestSplit H r nGauge ≃ₜ DeepestSplit H r nGauge)
    (coreAbsorb_basepoint : coreAbsorb 0 = 0)
    (coreAbsorb_regular : ∀ q : DeepestSplit H r nGauge, (coreAbsorb q).1 = q.1)
    (coreAbsorb_spectator : ∀ q : DeepestSplit H r nGauge, (coreAbsorb q).2.2 = q.2.2)
    (coreAbsorb_rlct :
      rlctAtOn
          (fun q : DeepestSplit H r nGauge => (∑ i, q.1 i ^ 2) + deepestCoreF H r (coreAbsorb q).2.1)
          (0 : DeepestSplit H r nGauge)
        = rlctAtOn
            (fun q : DeepestSplit H r nGauge => (∑ i, q.1 i ^ 2) + deepestCoreF H r q.2.1)
            (0 : DeepestSplit H r nGauge))
    (loss_germ :
      (fun w => dlnLoss H B ((paramsEquivFlat H).symm w))
          =ᶠ[𝓝 ((paramsEquivFlat H) (deepestPoint H r B hB hr hL))]
        fun w => (∑ i, (split w).1 i ^ 2) + deepestCoreF H r (coreAbsorb (split w)).2.1) :
    DeepestGaugeChart H r B hB hr hL where
  nGauge := nGauge
  split := split
  split_mp := split_mp
  split_basepoint := split_basepoint
  coreAbsorb := coreAbsorb
  coreAbsorb_basepoint := coreAbsorb_basepoint
  coreAbsorb_regular := coreAbsorb_regular
  coreAbsorb_spectator := coreAbsorb_spectator
  coreAbsorb_rlct := coreAbsorb_rlct
  -- For an EXACT germ the raw reg slot IS `E` (no nonlinear indirection), so `regAbsorb = id`.
  regAbsorb := Homeomorph.refl _
  regAbsorb_basepoint := rfl
  regAbsorb_core := fun _ => rfl
  regAbsorb_spectator := fun _ => rfl
  regAbsorb_rlct := rfl
  loss_squeeze := by
    obtain ⟨U, hU, hUeq⟩ := loss_germ.exists_mem
    refine ⟨1, 1, one_pos, one_pos, U, hU, fun w hw => ?_⟩
    have heq : dlnLoss H B ((paramsEquivFlat H).symm w)
        = (∑ i, (split w).1 i ^ 2) + deepestCoreF H r (coreAbsorb (split w)).2.1 := hUeq hw
    refine ⟨?_, ?_, ?_⟩
    · exact add_nonneg (Finset.sum_nonneg fun i _ => sq_nonneg _) (dlnLoss_nonneg _ _ _)
    · rw [one_mul]; exact le_of_eq heq.symm
    · rw [one_mul]; exact le_of_eq heq

/-- **Sub-lemma 2 (`deepestPoint_is_rank_exact`).** The constructed deepest point is rank-`r`-exact on
every interior layer — a restatement of the green `deepestPoint_isDeep` (`IsDeepLayers.2`), exposed in
the layer-rank form the gauge chart consumes. -/
theorem deepestPoint_is_rank_exact (H : Fin (L + 1) → ℕ) (r : ℕ)
    (B : Matrix (Fin (H 0)) (Fin (H (Fin.last L))) ℝ) (hB : B.rank = r)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L) :
    ∀ s : Fin L, ((deepestPoint H r B hB hr hL) s).rank = r :=
  (deepestPoint_isDeep H r B hB hr hL).2

/-- **Sub-lemma 3 (`deepest_gauge_squeeze_exists`, HEAVY #44c — the sub-34 obligation).** The
gauge-slice squeeze datum exists at the deepest point. The g150-cert block algebra (re-scoped to the
squeeze form, sub-34 g152): per-layer `block_elimination` units `P_s,Q_s`, the 2-factor block product
folded over `L`, the MP regular/core/spectator reindex `split` (`split_mp`/`split_basepoint`), and the
two-sided `loss_squeeze` (`c₁Φ ≤ loss ≤ c₂Φ`) whose load-bearing content is the matrix-core
comparability `‖T·(I−VY)⁻¹·S‖² ≍ dlnLoss M 0 (core)`. -/
theorem deepest_gauge_squeeze_exists (H : Fin (L + 1) → ℕ) (r : ℕ)
    (B : Matrix (Fin (H 0)) (Fin (H (Fin.last L))) ℝ) (hB : B.rank = r)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L) :
    Nonempty (DeepestGaugeChart H r B hB hr hL) := by
  sorry

/-- **Sub-lemma 5 (`deepest_squeeze_transport`).** The squeeze datum transports the local RLCT:
`rlctAt (dlnLoss H B) deepest = rlctAtOn Φ wstar`, where `Φ = ∑ regular² + dlnLoss M 0 (core)` and
`wstar = (paramsEquivFlat H) deepest`. Chain: `rlctAtOn_eq_rlctAt` (Params), Params→flat MP transport
(`rlctAtOn_comp_homeomorph` on `paramsEquivFlat H`), then `rlctAtOn_squeeze` consuming `loss_squeeze`
(the local two-sided bound — NO chart, NO measure Jacobian; matches `schur_recursion_step_squeeze`).
`Φ` and `wstar` feed sub-6 (the smooth-block split). -/
theorem deepest_squeeze_transport (H : Fin (L + 1) → ℕ) (r : ℕ)
    (B : Matrix (Fin (H 0)) (Fin (H (Fin.last L))) ℝ) (hB : B.rank = r)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L)
    (Γ : DeepestGaugeChart H r B hB hr hL) :
    rlctAt H (dlnLoss H B) (deepestPoint H r B hB hr hL)
      = rlctAtOn
          (fun x : Fin (flatDim H) → ℝ =>
            (∑ i, (Γ.regAbsorb (Γ.split x)).1 i ^ 2)
              + deepestCoreF H r (Γ.coreAbsorb (Γ.split x)).2.1)
          ((paramsEquivFlat H) (deepestPoint H r B hB hr hL)) := by
  set wstar := (paramsEquivFlat H) (deepestPoint H r B hB hr hL) with hwstar
  set Φ : (Fin (flatDim H) → ℝ) → ℝ := fun x =>
    (∑ i, (Γ.regAbsorb (Γ.split x)).1 i ^ 2)
      + deepestCoreF H r (Γ.coreAbsorb (Γ.split x)).2.1 with hΦ
  -- Step 1: `rlctAt` on `Params` is `rlctAtOn`; transport Params→flat (MP homeomorph).
  rw [← rlctAtOn_eq_rlctAt]
  set e : Params H ≃ₜ (Fin (flatDim H) → ℝ) :=
    ⟨(paramsEquivFlat H).toEquiv, continuous_paramsEquivFlat H, continuous_paramsEquivFlat_symm H⟩
    with he
  have hmp : MeasurePreserving e (volume : Measure (Params H)) volume :=
    measurePreserving_paramsEquivFlat H
  have hemb : MeasurableEmbedding e := (paramsEquivFlat H).measurableEmbedding
  have htrans := rlctAtOn_comp_homeomorph e hmp hemb
    (fun x : Fin (flatDim H) → ℝ => dlnLoss H B ((paramsEquivFlat H).symm x))
    (deepestPoint H r B hB hr hL)
  have hcomp : (fun A : Params H => dlnLoss H B ((paramsEquivFlat H).symm (e A)))
      = fun A : Params H => dlnLoss H B A := by
    funext A; congr 1; exact (paramsEquivFlat H).symm_apply_apply A
  rw [hcomp] at htrans
  have he_deepest : e (deepestPoint H r B hB hr hL) = wstar := rfl
  rw [he_deepest] at htrans
  rw [htrans]
  -- Step 2: `rlctAtOn_squeeze` consuming the `loss_squeeze` datum, landing on `Φ` at `wstar`.
  obtain ⟨c₁, c₂, hc₁, hc₂, U, hU, hsq⟩ := Γ.loss_squeeze
  refine rlctAtOn_squeeze (fun x => dlnLoss H B ((paramsEquivFlat H).symm x)) Φ wstar
    ((continuous_dlnLoss H B).comp (continuous_paramsEquivFlat_symm H)).measurable ?_
    c₁ c₂ hc₁ hc₂ ⟨U, hU, fun w hw => hsq w hw⟩
  -- `Φ` measurable: regular sum-of-squares + the core loss through the reindex + absorb + flattening.
  rw [hΦ]
  apply Measurable.add
  · exact (Finset.measurable_sum _ (fun i _ =>
      ((measurable_pi_apply i).comp
        (continuous_fst.comp (Γ.regAbsorb.continuous.comp Γ.split.continuous)).measurable).pow_const _))
  · exact ((continuous_dlnLoss (deepestM H r) _).comp
      (continuous_paramsEquivFlat_symm _)).measurable.comp
      ((continuous_fst.comp continuous_snd).comp
        (Γ.coreAbsorb.continuous.comp Γ.split.continuous)).measurable

/-- **Sub-lemma 7 (`deepest_reduced_core_identification`).** The reduced core loss in flat
coordinates has the same RLCT as on `Params M`: `rlctAtOn (dlnLoss M 0 ∘ (paramsEquivFlat M).symm) 0
= rlctAtOn (dlnLoss M 0) (fun _ => 0)`. Transport along the measure-preserving flattening
`paramsEquivFlat M` (its `.symm` is a measure-preserving homeomorph, `0 ↦ fun _ => 0`). -/
theorem deepest_reduced_core_identification (M : Fin (L + 1) → ℕ) :
    rlctAtOn
        (fun y : Fin (flatDim M) → ℝ =>
          dlnLoss M (0 : Matrix (Fin (M 0)) (Fin (M (Fin.last L))) ℝ) ((paramsEquivFlat M).symm y))
        (0 : Fin (flatDim M) → ℝ)
      = rlctAtOn (fun A : Params M => dlnLoss M (0 : Matrix (Fin (M 0)) (Fin (M (Fin.last L))) ℝ) A)
          (fun _ => 0 : Params M) := by
  set e : Params M ≃ₜ (Fin (flatDim M) → ℝ) :=
    ⟨(paramsEquivFlat M).toEquiv, continuous_paramsEquivFlat M, continuous_paramsEquivFlat_symm M⟩
    with he
  have hmp : MeasurePreserving e (volume : Measure (Params M)) volume :=
    measurePreserving_paramsEquivFlat M
  -- `e` shares the underlying map with the `MeasurableEquiv` `paramsEquivFlat M`, so its measurable
  -- embedding comes from the latter (no `BorelSpace (Params M)` needed).
  have hemb : MeasurableEmbedding e := (paramsEquivFlat M).measurableEmbedding
  have key := rlctAtOn_comp_homeomorph e hmp hemb
    (fun y : Fin (flatDim M) → ℝ =>
      dlnLoss M (0 : Matrix (Fin (M 0)) (Fin (M (Fin.last L))) ℝ) ((paramsEquivFlat M).symm y))
    (fun _ => 0 : Params M)
  have he0 : e (fun _ => 0 : Params M) = (0 : Fin (flatDim M) → ℝ) := by
    show (paramsEquivFlat M) (fun _ => 0) = 0
    funext i
    show (paramsEquivFlat M) (fun _ => 0) i = 0
    rfl
  rw [he0] at key
  have hcomp : (fun A : Params M =>
      dlnLoss M (0 : Matrix (Fin (M 0)) (Fin (M (Fin.last L))) ℝ) ((paramsEquivFlat M).symm (e A)))
      = fun A : Params M => dlnLoss M (0 : Matrix (Fin (M 0)) (Fin (M (Fin.last L))) ℝ) A := by
    funext A
    congr 1
    show (paramsEquivFlat M).symm ((paramsEquivFlat M) A) = A
    exact (paramsEquivFlat M).symm_apply_apply A
  rw [hcomp] at key
  exact key.symm

/-- **Sub-lemma 6 (`deepest_regular_smooth_split`).** The pulled-back loss `∑ regular² + (reduced
core)` has RLCT `nReg/2 + rlctAtOn (dlnLoss M 0) 0`: the `nReg` nondegenerate quadratic directions
split off additively (`rlct_additive_smooth_block`, with `G = √∘(dlnLoss M 0)`, `G² = dlnLoss M 0`
via `dlnLoss_nonneg`), the loss-independent gauge spectators peel off (`rlctAtOn_spectator_peel`),
and the reduced block's RLCT is `rlctAtOn (dlnLoss M 0) 0` (sub-7).

**Precondition `hGne` (the reduced-core germ-nonvanishing, found in the build — NOT in the g150/g147
cert).** `rlct_additive_smooth_block` is FALSE for a germ-vanishing block (13th-finding: `G ≡ 0` near
`0` ⟹ block RLCT `⊤`). So the split needs the reduced core `dlnLoss M 0` to be `≠ 0` a.e. on a nbhd
of the deepest core point (the flat origin). This holds when the reduced chain `M = H − r` is
non-degenerate (the zero-product locus `{prod_M = 0}` is then a proper subvariety, measure zero) — it
can FAIL if some interior `M_s = H_s − r = 0` (then `prod_M ≡ 0`). Carried as a hypothesis here,
discharged by the chart-existence/non-degeneracy (the same `hGne`-as-hypothesis discipline as
`GeneralR1Recursion`'s smooth-split). -/
theorem deepest_regular_smooth_split (H : Fin (L + 1) → ℕ) (r : ℕ)
    (B : Matrix (Fin (H 0)) (Fin (H (Fin.last L))) ℝ) (hB : B.rank = r)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L)
    (Γ : DeepestGaugeChart H r B hB hr hL)
    (hGne : ∃ U ∈ 𝓝 (0 : Fin (flatDim (fun s => H s - r)) → ℝ),
      ∀ᵐ z ∂(volume.restrict U),
        dlnLoss (fun s => H s - r)
          (0 : Matrix (Fin ((fun s => H s - r) 0)) (Fin ((fun s => H s - r) (Fin.last L))) ℝ)
          ((paramsEquivFlat (fun s => H s - r)).symm z) ≠ 0) :
    rlctAtOn
        (fun x : Fin (flatDim H) → ℝ =>
          (∑ i, (Γ.regAbsorb (Γ.split x)).1 i ^ 2)
            + deepestCoreF H r (Γ.coreAbsorb (Γ.split x)).2.1)
        ((paramsEquivFlat H) (deepestPoint H r B hB hr hL))
      = ((r * (H 0 + H (Fin.last L) - r) : ℕ) : ℝ≥0∞) / 2
        + rlctAtOn
            (fun A : Params (fun s => H s - r) =>
              dlnLoss (fun s => H s - r)
                (0 : Matrix (Fin ((fun s => H s - r) 0)) (Fin ((fun s => H s - r) (Fin.last L))) ℝ) A)
            (fun _ => 0 : Params (fun s => H s - r)) := by
  set M : Fin (L + 1) → ℕ := fun s => H s - r with hM
  set coreF : (Fin (flatDim M) → ℝ) → ℝ :=
    fun y => dlnLoss M (0 : Matrix (Fin (M 0)) (Fin (M (Fin.last L))) ℝ) ((paramsEquivFlat M).symm y)
    with hcoreF
  have hcoreF_meas : Measurable coreF :=
    ((continuous_dlnLoss M _).comp (continuous_paramsEquivFlat_symm M)).measurable
  have hcoreF_nonneg : ∀ y, 0 ≤ coreF y := fun y => dlnLoss_nonneg _ _ _
  -- Step 1: transport through the MP split homeomorphism (`split` carries the basepoint to `0`).
  have hstep1 := rlctAtOn_comp_homeomorph Γ.split Γ.split_mp Γ.split.measurableEmbedding
    (fun q : DeepestSplit H r Γ.nGauge => (∑ i, (Γ.regAbsorb q).1 i ^ 2) + coreF (Γ.coreAbsorb q).2.1)
    ((paramsEquivFlat H) (deepestPoint H r B hB hr hL))
  rw [Γ.split_basepoint] at hstep1
  have hgoalfun :
      (fun x : Fin (flatDim H) → ℝ =>
        (∑ i, (Γ.regAbsorb (Γ.split x)).1 i ^ 2) + deepestCoreF H r (Γ.coreAbsorb (Γ.split x)).2.1)
      = fun x => (fun q : DeepestSplit H r Γ.nGauge =>
          (∑ i, (Γ.regAbsorb q).1 i ^ 2) + coreF (Γ.coreAbsorb q).2.1) (Γ.split x) := by funext x; rfl
  rw [hgoalfun, hstep1]
  -- Step 2a: peel the regular-absorption (`regAbsorb_rlct`) — reg `E` ↦ raw reg (core stays absorbed).
  rw [Γ.regAbsorb_rlct]
  -- Step 2b: peel the gauge-absorption (`coreAbsorb_rlct`) — absorbed core ↦ raw disjoint core.
  rw [Γ.coreAbsorb_rlct]
  -- Step 2: additive smooth-block split on `Y = (core) × (spectator)`, `G = √∘(coreF ∘ fst)`.
  set G : (Fin (flatDim M) → ℝ) × (Fin Γ.nGauge → ℝ) → ℝ := fun p => Real.sqrt (coreF p.1) with hG
  have hGsq : ∀ p, G p ^ 2 = coreF p.1 := fun p => Real.sq_sqrt (hcoreF_nonneg p.1)
  have hfun2 :
      (fun q : (Fin (r * (H 0 + H (Fin.last L) - r)) → ℝ) ×
          ((Fin (flatDim M) → ℝ) × (Fin Γ.nGauge → ℝ)) => (∑ i, q.1 i ^ 2) + coreF q.2.1)
      = fun q => (∑ i, q.1 i ^ 2) + G q.2 ^ 2 := by funext q; rw [hGsq]
  rw [hfun2]
  have hGmeas : Measurable G := (Real.continuous_sqrt.measurable.comp hcoreF_meas).comp measurable_fst
  have hGne' : ∃ U ∈ 𝓝 (0 : (Fin (flatDim M) → ℝ) × (Fin Γ.nGauge → ℝ)),
      ∀ᵐ z ∂(volume.restrict U), G z ≠ 0 := by
    obtain ⟨Uc, hUc, hUcne⟩ := hGne
    refine ⟨Uc ×ˢ (Set.univ : Set (Fin Γ.nGauge → ℝ)), prod_mem_nhds hUc Filter.univ_mem, ?_⟩
    have hmono : ∀ᵐ z ∂(volume.restrict (Uc ×ˢ (Set.univ : Set (Fin Γ.nGauge → ℝ)))),
        coreF z.1 ≠ 0 := by
      rw [show (volume.restrict (Uc ×ˢ (Set.univ : Set (Fin Γ.nGauge → ℝ))))
          = (volume.restrict Uc).prod (volume.restrict Set.univ) by
        rw [Measure.prod_restrict, Measure.volume_eq_prod]]
      exact (Measure.quasiMeasurePreserving_fst (μ := volume.restrict Uc)
        (ν := volume.restrict (Set.univ : Set (Fin Γ.nGauge → ℝ)))).ae hUcne
    filter_upwards [hmono] with z hz
    rw [hG]; intro hsqrt
    exact hz (le_antisymm (Real.sqrt_eq_zero'.1 hsqrt) (hcoreF_nonneg z.1))
  have hadd := rlct_additive_smooth_block (n := r * (H 0 + H (Fin.last L) - r)) G
    (0 : (Fin (flatDim M) → ℝ) × (Fin Γ.nGauge → ℝ)) hGmeas hGne'
  rw [show (0 : (Fin (r * (H 0 + H (Fin.last L) - r)) → ℝ) ×
      ((Fin (flatDim M) → ℝ) × (Fin Γ.nGauge → ℝ)))
      = ((0 : Fin (r * (H 0 + H (Fin.last L) - r)) → ℝ),
         (0 : (Fin (flatDim M) → ℝ) × (Fin Γ.nGauge → ℝ))) from rfl, hadd]
  -- Step 3: spectator-peel `rlctAtOn (G²) (0,0) = rlctAtOn coreF 0` then sub-7.
  have hGsqfun : (fun p : (Fin (flatDim M) → ℝ) × (Fin Γ.nGauge → ℝ) => G p ^ 2)
      = fun p => coreF p.1 := by funext p; rw [hGsq]
  rw [hGsqfun,
    show (0 : (Fin (flatDim M) → ℝ) × (Fin Γ.nGauge → ℝ))
      = ((0 : Fin (flatDim M) → ℝ), (0 : Fin Γ.nGauge → ℝ)) from rfl,
    rlctAtOn_spectator_peel coreF (0 : Fin (flatDim M) → ℝ) (0 : Fin Γ.nGauge → ℝ)
      ⟨Metric.ball (0 : Fin Γ.nGauge → ℝ) 1, Metric.isOpen_ball,
        Metric.mem_ball_self (by norm_num), measure_ball_lt_top⟩,
    deepest_reduced_core_identification M]

/-- **The VALUE-FREE L2 reduction (`deepest_regular_core_reduces`).** The local RLCT of `dlnLoss H B`
at the deepest point splits as the regular gauge shift `nReg/2` (`nReg = r(H⁰+Hᴸ−r)`) plus the reduced
singular **core RLCT** `rlctAtOn (dlnLoss M 0) 0` on the reduced widths `M = H−r`. This is the gauge
chart's full content: it carries NO `lambdaCore` (R1's value `rlctAtOn (dlnLoss M 0) 0 =
ofReal(lambdaCore M)` is folded separately). Assembled from the chart-existence (#44c) + the transport
+ smooth-split sub-lemmas. The `hGne` (reduced-core germ-nonvanishing) precondition — found in the
build, NOT in the cert; see `deepest_regular_smooth_split` — is carried: it holds when the reduced
chain is non-degenerate (no interior `M_s = 0`), discharged at the spine wiring. -/
theorem deepest_regular_core_reduces (H : Fin (L + 1) → ℕ) (r : ℕ)
    (B : Matrix (Fin (H 0)) (Fin (H (Fin.last L))) ℝ) (hB : B.rank = r)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L)
    (hGne : ∃ U ∈ 𝓝 (0 : Fin (flatDim (fun s => H s - r)) → ℝ),
      ∀ᵐ z ∂(volume.restrict U),
        dlnLoss (fun s => H s - r)
          (0 : Matrix (Fin ((fun s => H s - r) 0)) (Fin ((fun s => H s - r) (Fin.last L))) ℝ)
          ((paramsEquivFlat (fun s => H s - r)).symm z) ≠ 0) :
    rlctAt H (dlnLoss H B) (deepestPoint H r B hB hr hL)
      = ((r * (H 0 + H (Fin.last L) - r) : ℕ) : ℝ≥0∞) / 2
        + rlctAtOn
            (fun A : Params (fun s => H s - r) =>
              dlnLoss (fun s => H s - r)
                (0 : Matrix (Fin ((fun s => H s - r) 0)) (Fin ((fun s => H s - r) (Fin.last L))) ℝ) A)
            (fun _ => 0 : Params (fun s => H s - r)) := by
  obtain ⟨Γ⟩ := deepest_gauge_squeeze_exists H r B hB hr hL
  rw [deepest_squeeze_transport H r B hB hr hL Γ,
    deepest_regular_smooth_split H r B hB hr hL Γ hGne]

end DLNFibre.DLN.RLCT
