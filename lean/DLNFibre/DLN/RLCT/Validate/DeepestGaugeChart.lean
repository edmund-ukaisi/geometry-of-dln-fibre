import DLNFibre.DLN.RLCT.Skeleton
import DLNFibre.DLN.RLCT.Foundations.S1Spectator

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

/-- **The deepest-point gauge-slice chart** (g147 pinned interface, g150 cert). At a rank-`r`-exact
deepest point, a coordinate change on the flat parameter space `Fin (flatDim H) → ℝ` splitting into
`nReg` regular gauge directions, the reduced core `Fin (flatDim M) → ℝ`, and `nGauge` spectator
directions, under which `dlnLoss H B` pulls back (as a germ at `0`) to `∑ regular² + dlnLoss M 0`.
The chart is a homeomorphism with a **bounded-unit** (not `±1`) Jacobian — the transport is NON-MP. -/
structure DeepestGaugeChart (H : Fin (L + 1) → ℕ) (r : ℕ)
    (B : Matrix (Fin (H 0)) (Fin (H (Fin.last L))) ℝ) (hB : B.rank = r)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L) where
  /-- The spectator-coordinate count (the remaining flat directions). The reduced widths
  `M = H − r` and the regular dimension `nReg = r(H⁰+Hᴸ−r)` are pinned in the field types below
  (not free fields — the construction always uses these). -/
  nGauge : ℕ
  /-- The coordinate split: flat `H`-params ≃ₜ `(regular nReg) × ((reduced core flatDim M) × (spectators))`. -/
  split :
    (Fin (flatDim H) → ℝ) ≃ₜ
      ((Fin (r * (H 0 + H (Fin.last L) - r)) → ℝ)
        × ((Fin (flatDim (fun s => H s - r)) → ℝ) × (Fin nGauge → ℝ)))
  /-- `split` is measure-preserving (a coordinate reindex) — needed to transport `rlctAtOn`
  through it via `rlctAtOn_comp_homeomorph`. -/
  split_mp : MeasurePreserving split volume volume
  /-- `split` fixes the origin (the deepest-point basepoint, all deviation coords `= 0`). -/
  split_zero : split 0 = 0
  /-- The gauge-slice + regular-residual change of variables (a self-homeomorphism of flat space). -/
  chart : (Fin (flatDim H) → ℝ) ≃ₜ (Fin (flatDim H) → ℝ)
  /-- The chart derivative (for the bounded-unit Jacobian fact). -/
  Dchart : (Fin (flatDim H) → ℝ) →
    ((Fin (flatDim H) → ℝ) →L[ℝ] (Fin (flatDim H) → ℝ))
  /-- `chart 0` maps back (via the flattening) to the deepest point — the singular zero of the loss. -/
  chart_zero :
    (paramsEquivFlat H).symm (chart 0) = deepestPoint H r B hB hr hL
  /-- `chart` has the stated Fréchet derivative everywhere. -/
  hasDeriv : ∀ x, HasFDerivAt chart (Dchart x) x
  /-- The chart Jacobian determinant is a **bounded unit** near `0` (the NON-MP key: `det ≠ ±1`). -/
  jac_unit :
    ∃ U ∈ 𝓝 (0 : Fin (flatDim H) → ℝ), ∃ a b : ℝ, 0 < a ∧
      ∀ x ∈ U, a ≤ |(Dchart x).det| ∧ |(Dchart x).det| ≤ b
  /-- The loss pulls back (as a germ at `0`) to `∑ regular² + reduced core`. -/
  loss_form :
    (fun x => dlnLoss H B ((paramsEquivFlat H).symm (chart x))) =ᶠ[𝓝 0]
      fun x =>
        let q := split x
        (∑ i, q.1 i ^ 2) +
          dlnLoss (fun s => H s - r)
            (0 : Matrix (Fin ((fun s => H s - r) 0)) (Fin ((fun s => H s - r) (Fin.last L))) ℝ)
            ((paramsEquivFlat (fun s => H s - r)).symm q.2.1)

/-- **Sub-lemma 2 (`deepestPoint_is_rank_exact`).** The constructed deepest point is rank-`r`-exact on
every interior layer — a restatement of the green `deepestPoint_isDeep` (`IsDeepLayers.2`), exposed in
the layer-rank form the gauge chart consumes. -/
theorem deepestPoint_is_rank_exact (H : Fin (L + 1) → ℕ) (r : ℕ)
    (B : Matrix (Fin (H 0)) (Fin (H (Fin.last L))) ℝ) (hB : B.rank = r)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L) :
    ∀ s : Fin L, ((deepestPoint H r B hB hr hL) s).rank = r :=
  (deepestPoint_isDeep H r B hB hr hL).2

/-- **Sub-lemma 3 (`deepest_gauge_chart_exists`, HEAVY #44c).** The gauge-slice chart exists at the
deepest point. The g150-cert block algebra: per-layer `block_elimination` units `P_s,Q_s`, the
2-factor block product folded over `L`, the regular-residual det-unit completion, `chart_zero`. -/
theorem deepest_gauge_chart_exists (H : Fin (L + 1) → ℕ) (r : ℕ)
    (B : Matrix (Fin (H 0)) (Fin (H (Fin.last L))) ℝ) (hB : B.rank = r)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L) :
    Nonempty (DeepestGaugeChart H r B hB hr hL) := by
  sorry

/-- **Sub-lemma 5 (`deepest_nonMP_chart_transport_unit`).** The chart transports the local RLCT:
`rlctAt (dlnLoss H B) deepest = rlctAtOn (pulled-back loss) 0`. NON-MP — the bounded-unit Jacobian
`jac_unit` is peeled by `rlctAtOn_unit_invariant_aux` (NOT `rlctAtOn_comp_homeomorph`); `chart_zero`
pins the basepoint, `loss_form` the germ. -/
theorem deepest_nonMP_chart_transport_unit (H : Fin (L + 1) → ℕ) (r : ℕ)
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
          (0 : Fin (flatDim H) → ℝ) := by
  sorry

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
        (0 : Fin (flatDim H) → ℝ)
      = ((r * (H 0 + H (Fin.last L) - r) : ℕ) : ℝ≥0∞) / 2
        + rlctAtOn
            (fun A : Params (fun s => H s - r) =>
              dlnLoss (fun s => H s - r)
                (0 : Matrix (Fin ((fun s => H s - r) 0)) (Fin ((fun s => H s - r) (Fin.last L))) ℝ) A)
            (fun _ => 0 : Params (fun s => H s - r)) := by
  -- ROUTE (mapped + partly built; full fill needs a `dlnLoss` measurability/continuity lemma,
  -- found missing — `fun_prop` deep-recurses on `prodAux`):
  --   (1) transport through the MP split homeomorph (`rlctAtOn_comp_homeomorph` + `split_mp` +
  --       `split_zero`) — drops to `rlctAtOn (fun q => ∑q.1² + coreF q.2.1) 0`;
  --   (2) `rlct_additive_smooth_block` with `G = √∘(coreF∘fst)` (`hGsq` via `dlnLoss_nonneg`,
  --       `hGmeas` needs `Measurable (dlnLoss M 0)`, `hGne'` lifts the given `hGne` to the product
  --       nbhd `Uc ×ˢ univ`) — peels `nReg/2`;
  --   (3) `rlctAtOn_spectator_peel` on `coreF∘fst` (the `nGauge` gauge spectators) then sub-7
  --       (`deepest_reduced_core_identification`) — lands on `rlctAtOn (dlnLoss M 0) 0`.
  sorry

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
  obtain ⟨Γ⟩ := deepest_gauge_chart_exists H r B hB hr hL
  rw [deepest_nonMP_chart_transport_unit H r B hB hr hL Γ,
    deepest_regular_smooth_split H r B hB hr hL Γ hGne]

end DLNFibre.DLN.RLCT
