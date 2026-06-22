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
are the `nReg` regular coords (Jacobian rank `= nReg` at the chain endpoints); the cross term
`Z₁Y₂` in the `(1,1)` block is `regular×regular ∈ ideal(reg)`, absorbed into `E`, so the reduced core
is the clean `‖∏T_s‖² = dlnLoss M 0`. The chart Jacobian is a **bounded UNIT** (`≠ 1`), so the
transport is **NON-MP**: `rlctAtOn_unit_invariant_aux` (peel the unit `|det Dπ|` weight) + germ-locality,
NOT `rlctAtOn_comp_homeomorph`.

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
  /-- The spectator-coordinate count (the remaining flat directions). The reduced widths
  `M = H − r` and the regular dimension `nReg = r(H⁰+Hᴸ−r)` are pinned in the field types below. -/
  nGauge : ℕ
  /-- The coordinate split: flat `H`-params ≃ₜ `(regular nReg) × ((reduced core flatDim M) × (spectators))`. -/
  split :
    (Fin (flatDim H) → ℝ) ≃ₜ
      ((Fin (r * (H 0 + H (Fin.last L) - r)) → ℝ)
        × ((Fin (flatDim (fun s => H s - r)) → ℝ) × (Fin nGauge → ℝ)))
  /-- `split` is measure-preserving (a coordinate reindex). -/
  split_mp : MeasurePreserving split volume volume
  /-- `split` carries the flat image of the deepest point to the split origin (deviation coords `= 0`). -/
  split_basepoint : split ((paramsEquivFlat H) (deepestPoint H r B hB hr hL)) = 0
  /-- **The loss-squeeze datum.** Near the deepest point (in flat coords), `dlnLoss H B` is two-sidedly
  bounded by `Φ = ∑ regular² + dlnLoss M 0 (core)` (the smooth regular block + the gauge-normalized
  reduced core). The matrix-core comparability is the sub-34 pp-hall obligation. -/
  loss_squeeze :
    ∃ c₁ c₂ : ℝ, 0 < c₁ ∧ 0 < c₂ ∧
      ∃ U ∈ 𝓝 ((paramsEquivFlat H) (deepestPoint H r B hB hr hL)),
        ∀ w ∈ U,
          0 ≤ (let q := split w
              (∑ i, q.1 i ^ 2) +
                dlnLoss (fun s => H s - r)
                  (0 : Matrix (Fin ((fun s => H s - r) 0)) (Fin ((fun s => H s - r) (Fin.last L))) ℝ)
                  ((paramsEquivFlat (fun s => H s - r)).symm q.2.1)) ∧
          c₁ * (let q := split w
              (∑ i, q.1 i ^ 2) +
                dlnLoss (fun s => H s - r)
                  (0 : Matrix (Fin ((fun s => H s - r) 0)) (Fin ((fun s => H s - r) (Fin.last L))) ℝ)
                  ((paramsEquivFlat (fun s => H s - r)).symm q.2.1))
            ≤ dlnLoss H B ((paramsEquivFlat H).symm w) ∧
          dlnLoss H B ((paramsEquivFlat H).symm w)
            ≤ c₂ * (let q := split w
              (∑ i, q.1 i ^ 2) +
                dlnLoss (fun s => H s - r)
                  (0 : Matrix (Fin ((fun s => H s - r) 0)) (Fin ((fun s => H s - r) (Fin.last L))) ℝ)
                  ((paramsEquivFlat (fun s => H s - r)).symm q.2.1))

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
            let q := Γ.split x
            (∑ i, q.1 i ^ 2) +
              dlnLoss (fun s => H s - r)
                (0 : Matrix (Fin ((fun s => H s - r) 0)) (Fin ((fun s => H s - r) (Fin.last L))) ℝ)
                ((paramsEquivFlat (fun s => H s - r)).symm q.2.1))
          ((paramsEquivFlat H) (deepestPoint H r B hB hr hL)) := by
  set wstar := (paramsEquivFlat H) (deepestPoint H r B hB hr hL) with hwstar
  set Φ : (Fin (flatDim H) → ℝ) → ℝ := fun x =>
    let q := Γ.split x
    (∑ i, q.1 i ^ 2) +
      dlnLoss (fun s => H s - r)
        (0 : Matrix (Fin ((fun s => H s - r) 0)) (Fin ((fun s => H s - r) (Fin.last L))) ℝ)
        ((paramsEquivFlat (fun s => H s - r)).symm q.2.1) with hΦ
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
  -- `Φ` measurable: regular sum-of-squares + the core loss through the reindex + flattening.
  rw [hΦ]
  apply Measurable.add
  · exact (Finset.measurable_sum _ (fun i _ =>
      ((measurable_pi_apply i).comp (continuous_fst.comp Γ.split.continuous).measurable).pow_const _))
  · exact ((continuous_dlnLoss (fun s => H s - r) _).comp
      (continuous_paramsEquivFlat_symm _)).measurable.comp
      ((continuous_fst.comp continuous_snd).comp Γ.split.continuous).measurable

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
          let q := Γ.split x
          (∑ i, q.1 i ^ 2) +
            dlnLoss (fun s => H s - r)
              (0 : Matrix (Fin ((fun s => H s - r) 0)) (Fin ((fun s => H s - r) (Fin.last L))) ℝ)
              ((paramsEquivFlat (fun s => H s - r)).symm q.2.1))
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
    (fun q : (Fin (r * (H 0 + H (Fin.last L) - r)) → ℝ) ×
        ((Fin (flatDim M) → ℝ) × (Fin Γ.nGauge → ℝ)) => (∑ i, q.1 i ^ 2) + coreF q.2.1)
    ((paramsEquivFlat H) (deepestPoint H r B hB hr hL))
  rw [Γ.split_basepoint] at hstep1
  have hgoalfun :
      (fun x : Fin (flatDim H) → ℝ =>
        let q := Γ.split x
        (∑ i, q.1 i ^ 2) +
          dlnLoss M (0 : Matrix (Fin (M 0)) (Fin (M (Fin.last L))) ℝ)
            ((paramsEquivFlat M).symm q.2.1))
      = fun x => (fun q : (Fin (r * (H 0 + H (Fin.last L) - r)) → ℝ) ×
          ((Fin (flatDim M) → ℝ) × (Fin Γ.nGauge → ℝ)) =>
          (∑ i, q.1 i ^ 2) + coreF q.2.1) (Γ.split x) := by funext x; rfl
  rw [hgoalfun, hstep1]
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
