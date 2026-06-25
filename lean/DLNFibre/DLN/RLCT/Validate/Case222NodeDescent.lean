import DLNFibre.DLN.RLCT.Validate.RouteMNodeDescentBuild
import DLNFibre.DLN.RLCT.Validate.RouteMNReg
import DLNFibre.DLN.RLCT.Foundations.ParamsFlat
import DLNFibre.DLN.RLCT.Foundations.LossContinuity

/-!
# `Case222NodeDescent` — the standalone `(2,2,2)` `RouteMNodeDescent` anchor (fm3 #147)

The `(B)`-lane anchor: a concrete `(2,2,2)` `RouteMNodeDescent` instance feeding
`RouteMNodeDescent.ofNodePresentation`, built by TRANSCRIBING the sympy-verified Schur certificate
(`expeditions/.../fm3-coord-bridge/case222-hnode-schur-cert.md`) — NOT re-deriving from rs-grind's
general producer. This decorrelates the per-node descent from the general G-a path.

## What the certificate gives (transcribed, not re-derived)
- `M222 = (2,2,2)`, `schurStateRed M222 = (1,1,2)` (`schurStateRed_M222`); the reduced node is `(1,1,2)`.
- The post-`A`-pivot blow-up core `core = ‖Â·B‖²` splits (sympy-verified `core − Schur = 0`) as
  `core = (∑ₖ Erowₖ²) + (∑ₖ (bcol·Erowₖ + SΓₖ)²)`, `nReg = 2` (the `Erow` block), the single lower
  row `Mblk = Unit` (`m − 1 = 1`).
- The reduced core `G² = ‖SΓ‖² = (y3−y2y1)²·(x6²+x7²) = dlnLoss (1,1,2) 0` (`α = y3−y2y1`, `[β0,β1] =
  [x6,x7]`).

## The construction here (working at the SOUND `flatCore` level — `ofNodePresentation`)
Per the soundness constraint (`RouteMO1Bridge` caveat): we build at the `flatCore` level, the SOUND
object the squeeze/`ofNodePresentation` consume (NOT the raw `dlnLoss` via the flagged MP-chart bridge).
The pieces:
- `Y = Fin (flatDim S.red) → ℝ` (the reduced flat ambient), `redEmbed = (paramsEquivFlat S.red).symm`
  upgraded to a `≃ₜ` — the proven measure-preserving flattening homeomorphism. This discharges the
  `ReducedTransport` contract (a det-1 MP `Y ≃ₜ Params S.red` closing the descent); it is NOT the cert's
  explicit Schur shear `(y3−y2y1) ↦ y3'` (that straightening is part of the squeeze/`hnode` PRODUCER, and
  is unnecessary here since `Y` is already the flattened reduced `Params (1,1,2)` with `α` a single coord).
- `G y = √(dlnLoss S.red 0 (redEmbed y))`, so `hredCore` is `Real.sq_sqrt ∘ dlnLoss_nonneg`.
- `flatCore w = (∑ⱼ w.1ⱼ²) + (∑ᵢⱼ (bcol·w.1ⱼ + SΓ)²)` — an object of the cert's Schur-normal-form SHAPE,
  DEFINED here (NOT proven equal to the genuine `(2,2,2)` post-blow-up `core`; that identification needs
  the blow-up-Jacobian bridge, deliberately not invoked). `SΓ w () = α·[β0,β1]` is the cert's reduced
  core `S·[x6,x7]` read off `redEmbed w.2` — so `‖SΓ‖² = dlnLoss (1,1,2) 0` faithfully (`dlnLoss_Sred_entry`).
  `bcol w () = w.1 0` is a contract-satisfying pivot-column placeholder (a regular coord vanishing at the
  deepest point, `∑ bcol² ≤ T²`), NOT the cert's independent column `y2`; `bcol` enters `descentStep` only
  through the squeeze (`schur_node_squeeze_unif`), whose RLCT conclusion is independent of `bcol`'s value.

`descentStep : rlctAtOn flatCore (0,0) = nReg/2 + rlctAtOn (dlnLoss (1,1,2) 0) 0 = 2/2 + rlctAtOn(child)`.
The `(2,2,2)` RLCT `3/2` is recovered (`routeMNodeDescent222_descentStep_eq_three_halves`) GIVEN the
reduced `(1,1,2)` child value `1/2` (the recursion's child, deferred — not re-derived). The `3/2`
NUMERICALLY equals the committed `case222_rlctAtOn_eq` (`Case222Rlct`); this is a value coincidence — the
file does NOT prove `rlctAtOn flatCore (0,0) = rlctAtOn (dlnLoss H222 0) deepest222` (that is exactly the
blow-up-Jacobian bridge). `nReg = 2` is hard-coded and numerically agrees with `nRegOf_M222 = 2`.

CRUX2's ι-ruling honored: this is an EXPLICIT standalone `(2,2,2)` leaf (no `routeMIota`); the index is
the concrete `Mblk = Unit`.
-/

open DLNFibre.DLN.RLCT MeasureTheory
open scoped BigOperators ENNReal

namespace DLNFibre.DLN.RLCT

/-- The `(2,2,2)` reduced-width chain `S.red = (1,1,2)` (the `schurState`-reduced node). -/
abbrev Sred222 : Fin 3 → ℕ := (schurState M222route M222_hlo).red

/-! ## The entrywise reduced loss `dlnLoss (1,1,2) 0` (the cert's `G²` shape) -/

/-- The `L = 2` product entry for the reduced chain `(1,1,2)`: `prod A i j = ∑ₖ A⁰ᵢₖ·A¹ₖⱼ` (inner
dim `Fin (Sred222 1) = Fin 1`). Mirrors `Case222Algebra.prod_two_layer` for the reduced widths. -/
theorem prod_two_layer_Sred (A : Params Sred222) (i : Fin (Sred222 0)) (j : Fin (Sred222 2)) :
    prod Sred222 A i j = ∑ k : Fin (Sred222 1), A 0 i k * A 1 k j := by
  unfold prod
  simp only [prodAux, Matrix.mul_apply, eq_mpr_eq_cast]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  congr 1
  convert congrFun (congrFun (Matrix.one_mul (cast (by rfl) (cast (by rfl) (A 0)))) i) k using 2

/-- **The reduced loss is the cert's `G²`.** `dlnLoss (1,1,2) 0 A = (α·β0)² + (α·β1)²` with the `1×1`
Schur scalar `α = A⁰₀₀` and the `B`-row `[β0,β1] = [A¹₀₀, A¹₀₁]` — exactly the certificate's reduced
core `G² = (y3−y2y1)²·(x6²+x7²)`. From `prod_two_layer_Sred` + the `Fin 1`/`Fin 2` sum expansion. -/
theorem dlnLoss_Sred_entry (A : Params Sred222) :
    dlnLoss Sred222 0 A
      = (A 0 ⟨0, by norm_num⟩ ⟨0, by norm_num⟩ * A 1 ⟨0, by norm_num⟩ ⟨0, by norm_num⟩) ^ 2
        + (A 0 ⟨0, by norm_num⟩ ⟨0, by norm_num⟩ * A 1 ⟨0, by norm_num⟩ ⟨1, by norm_num⟩) ^ 2 := by
  unfold dlnLoss
  simp only [sub_zero]
  simp_rw [prod_two_layer_Sred]
  change ∑ i : Fin 1, ∑ j : Fin 2, (∑ k : Fin 1, A 0 i k * A 1 k j) ^ 2 = _
  simp only [Fin.sum_univ_one, Fin.sum_univ_two]
  rfl

/-! ## The `ReducedTransport` (the det-1 MP reindex to `Params (1,1,2)`) -/

/-- The reduced flat ambient `Y = Fin (flatDim (1,1,2)) → ℝ` carries all the `ofNodePresentation`
instances (`ProperSpace`/Borel/finite-on-compacts `volume`/`Zero`) — the cert's post-peel coords. -/
abbrev YRed222 : Type := Fin (flatDim Sred222) → ℝ

/-- The reduced-coord reindex `Y ≃ₜ Params (1,1,2)`: the proven measure-preserving flattening
(`paramsEquivFlat`), as a homeomorphism (the cert's coordinate identification `(α, [β0,β1]) ↦
Params (1,1,2)`, here via the generic flat equivalence). -/
noncomputable def redEmbed222 : YRed222 ≃ₜ Params Sred222 where
  toFun := (paramsEquivFlat Sred222).symm
  invFun := (paramsEquivFlat Sred222)
  left_inv := (paramsEquivFlat Sred222).apply_symm_apply
  right_inv := (paramsEquivFlat Sred222).symm_apply_apply
  continuous_toFun := continuous_paramsEquivFlat_symm Sred222
  continuous_invFun := continuous_paramsEquivFlat Sred222

/-- The reduced core `G y = √(dlnLoss (1,1,2) 0 (redEmbed y))` — so `G² = dlnLoss (1,1,2) 0 ∘ redEmbed`
by `Real.sq_sqrt` (`dlnLoss` nonneg). -/
noncomputable def GRed222 : YRed222 → ℝ := fun y => Real.sqrt (dlnLoss Sred222 0 (redEmbed222 y))

/-- `redEmbed222` is measure-preserving (the `.symm` of the proven MP flattening). -/
theorem measurePreserving_redEmbed222 : MeasurePreserving redEmbed222 volume volume :=
  (measurePreserving_paramsEquivFlat Sred222).symm _

/-- `redEmbed222` is a measurable embedding. -/
theorem measurableEmbedding_redEmbed222 : MeasurableEmbedding redEmbed222 :=
  (paramsEquivFlat Sred222).symm.measurableEmbedding

/-- `redEmbed222` sends the reduced deepest point `0` to the layerwise-zero tuple `fun _ => 0`. -/
theorem redEmbed222_zero :
    redEmbed222 (0 : YRed222) = (fun _ => 0 : Params Sred222) := rfl

/-- `GRed222² = dlnLoss (1,1,2) 0 (redEmbed y)` (the `hredCore` obligation): `Real.sq_sqrt` on the
nonneg loss. -/
theorem GRed222_sq (y : YRed222) :
    GRed222 y ^ 2 = dlnLoss Sred222 0 (redEmbed222 y) :=
  Real.sq_sqrt (dlnLoss_nonneg Sred222 0 (redEmbed222 y))

/-- The `(2,2,2)`-node `ReducedTransport` (the det-1 MP descent closing `rlctAtOn (G²) 0 = rlctAtOn
(dlnLoss (1,1,2) 0) 0`). -/
noncomputable def transport222 : ReducedTransport (schurState M222route M222_hlo) YRed222 where
  G := GRed222
  redEmbed := redEmbed222
  hmp := measurePreserving_redEmbed222
  hemb := measurableEmbedding_redEmbed222
  hzero := redEmbed222_zero
  hredCore := GRed222_sq

/-! ## The `hnode` Schur presentation (the `(B)`-lane contract — Schur-SHAPED, from the cert)

`nReg = 2` (the `Erow` block), the single lower row `Mblk = Unit` (`m − 1 = 1`). The pieces:
- `SΓ222 w () = α·[β0,β1]` reads the cert's reduced core `SΓ = S·[x6,x7]` off `redEmbed w.2` (`α =
  S = y3−y2y1` the `1×1` Schur scalar, `[β0,β1] = [x6,x7]` the `B`-row) — so `‖SΓ‖² = dlnLoss (1,1,2) 0`
  FAITHFULLY (`dlnLoss_Sred_entry`, the reduced-core identity the cert pins);
- `bcol222 w () = w.1 0` is a contract-satisfying pivot-column PLACEHOLDER (a regular coord vanishing at
  the deepest point, giving `∑ bcol² = (w.1 0)² ≤ T²` near `(0,0)`) — NOT the cert's independent column
  `y2`. The RLCT conclusion of `descentStep` is independent of `bcol`'s value (the squeeze absorbs it);
- `flatCore222` is an object of the cert's Schur-normal-form SHAPE `(∑ⱼ Erowⱼ²) + (∑ᵢⱼ (bcol·Erowⱼ +
  SΓ)²)`, DEFINED here (the SOUND object `ofNodePresentation` consumes) — NOT proven equal to the genuine
  `(2,2,2)` post-blow-up `core` (that identification needs the blow-up-Jacobian bridge, not invoked). -/

/-- The cert's `1×1` Schur scalar `α = S = y3−y2y1`, read off `redEmbed w.2` (`= A⁰₀₀` of the reduced
tuple). -/
noncomputable def alpha222 (w : (Fin 2 → ℝ) × YRed222) : ℝ :=
  (redEmbed222 w.2) 0 ⟨0, by norm_num⟩ ⟨0, by norm_num⟩

/-- The cert's `B`-row `[β0,β1] = [x6,x7]`, read off `redEmbed w.2` (`= A¹₀ⱼ`). -/
noncomputable def beta222 (w : (Fin 2 → ℝ) × YRed222) (j : Fin 2) : ℝ :=
  (redEmbed222 w.2) 1 ⟨0, by norm_num⟩ j

/-- The reduced core `SΓ = S·[x6,x7] = α·[β0,β1]` (the single lower row `Mblk = Unit`, the `nReg = 2`
components `j`). -/
noncomputable def SΓ222 (w : (Fin 2 → ℝ) × YRed222) (_ : Unit) (j : Fin 2) : ℝ :=
  alpha222 w * beta222 w j

/-- The pivot-column generator: a contract-satisfying PLACEHOLDER `w.1 0` (a regular coord vanishing at
the deepest point), NOT the cert's independent column `y2`. The squeeze absorbs it, so `descentStep`'s
RLCT is `bcol`-value-independent. -/
noncomputable def bcol222 (w : (Fin 2 → ℝ) × YRed222) (_ : Unit) : ℝ := w.1 0

/-- An object of the cert's Schur-normal-form SHAPE `flatCore = (∑ⱼ Erowⱼ²) + (∑ᵢⱼ (bcol·Erowⱼ + SΓ)²)`,
DEFINED here as the SOUND object `ofNodePresentation` consumes — NOT proven equal to the genuine
`(2,2,2)` post-blow-up `core` (that needs the blow-up-Jacobian bridge, not invoked). -/
noncomputable def flatCore222 (w : (Fin 2 → ℝ) × YRed222) : ℝ :=
  (∑ j, (w.1 j) ^ 2) + (∑ i, ∑ j, (bcol222 w i * w.1 j + SΓ222 w i j) ^ 2)

/-- **The reduced-core identity** `G(w.2)² = ∑ᵢⱼ SΓ²` (the cert's `G² = ‖SΓ‖²`): `G² = dlnLoss (1,1,2)
0 (redEmbed w.2) = (α·β0)² + (α·β1)²` (`dlnLoss_Sred_entry`) `= ∑_{i:Unit} ∑_{j:Fin 2} (α·βⱼ)²`. -/
theorem GRed222_sq_eq_sum_SΓ (w : (Fin 2 → ℝ) × YRed222) :
    transport222.G w.2 ^ 2 = ∑ i, ∑ j, (SΓ222 w i j) ^ 2 := by
  show GRed222 w.2 ^ 2 = _
  rw [GRed222_sq, dlnLoss_Sred_entry]
  simp only [SΓ222, alpha222, beta222, Finset.univ_unique, Finset.sum_singleton, Fin.sum_univ_two]
  rfl

/-! ## Measurability of `flatCore222` and `GRed222` -/

/-- `GRed222 = √(dlnLoss (1,1,2) 0 ∘ redEmbed)` is measurable (a `Real.sqrt` of a continuous loss
composed with the continuous reindex). -/
theorem measurable_GRed222 : Measurable transport222.G := by
  show Measurable GRed222
  unfold GRed222
  have hloss : Measurable (fun y : YRed222 => dlnLoss Sred222 0 (redEmbed222 y)) :=
    (measurable_dlnLoss Sred222 0).comp (paramsEquivFlat Sred222).symm.measurable
  exact Real.continuous_sqrt.measurable.comp hloss

/-- `flatCore222` is measurable (a polynomial in `w.1` and the continuous entries of `redEmbed w.2`). -/
theorem measurable_flatCore222 : Measurable flatCore222 := by
  have hred : Continuous (fun w : (Fin 2 → ℝ) × YRed222 => redEmbed222 w.2) :=
    redEmbed222.continuous.comp continuous_snd
  have hcont : Continuous flatCore222 := by
    unfold flatCore222 SΓ222 bcol222 alpha222 beta222
    fun_prop
  exact hcont.measurable

/-! ## The full `hnode` Schur presentation -/

/-- **The `hnode` presentation near the deepest point** (the `(B)`-lane contract). On `U = {w | (w.1
0)² < 1}` (open, `∋ (0,0)`), with `T = 1`, `flatCore = (∑ⱼ Erowⱼ²) + (∑ᵢⱼ (bcol·Erowⱼ + SΓ)²)` (by
def), `G(w.2)² = ∑ᵢⱼ SΓ²` (`GRed222_sq_eq_sum_SΓ`), and `∑ᵢ bcol² = (w.1 0)² ≤ 1` (the pivot column
vanishing at the deepest point). -/
theorem hnode222 :
    ∃ U ∈ nhds ((0, 0) : (Fin 2 → ℝ) × YRed222), ∀ w ∈ U,
      flatCore222 w = (∑ j, (w.1 j) ^ 2) + (∑ i, ∑ j, (bcol222 w i * w.1 j + SΓ222 w i j) ^ 2)
      ∧ transport222.G w.2 ^ 2 = (∑ i, ∑ j, (SΓ222 w i j) ^ 2)
      ∧ (∑ i, (bcol222 w i) ^ 2) ≤ (1 : ℝ) ^ 2 := by
  refine ⟨{w | (w.1 0) ^ 2 < 1}, ?_, fun w hw => ⟨rfl, GRed222_sq_eq_sum_SΓ w, ?_⟩⟩
  · -- the set is open (preimage of `Iio 1` under `w ↦ (w.1 0)²`, continuous) and contains `(0,0)`.
    refine IsOpen.mem_nhds ?_ ?_
    · exact isOpen_lt (by fun_prop) continuous_const
    · simp
  · -- `∑_{i:Unit} (w.1 0)² = (w.1 0)² < 1 = 1²`
    simp only [bcol222, Finset.univ_unique, Finset.sum_singleton, one_pow]
    exact le_of_lt hw

/-! ## Germ-nonvanishing of `GRed222` (the S1.5 hygiene at the non-leaf node) -/

/-- **The reduced loss is nonzero a.e. on `Params (1,1,2)`.** Its zero set is `{α = 0} ∪ {β0 = 0 ∧
β1 = 0}` (from `dlnLoss_Sred_entry`, `dlnLoss = (αβ0)² + (αβ1)²`) — a union of two coordinate
subspaces of `Params (1,1,2) ≅ ℝ³`, hence null. The non-leaf node `(1,1,2)` is non-degenerate. -/
theorem dlnLoss_Sred_ne_ae :
    ∀ᵐ A ∂(volume : Measure (Params Sred222)), dlnLoss Sred222 0 A ≠ 0 := by
  -- Transport to the flat ambient `Fin (flatDim Sred222) → ℝ`: it suffices that the loss is
  -- nonzero a.e. after `(paramsEquivFlat).symm`, then pull back through the MP equiv.
  have hmp := measurePreserving_paramsEquivFlat Sred222
  suffices hflat :
      ∀ᵐ x ∂(volume : Measure (Fin (flatDim Sred222) → ℝ)),
        dlnLoss Sred222 0 ((paramsEquivFlat Sred222).symm x) ≠ 0 by
    have := hmp.quasiMeasurePreserving.ae hflat
    filter_upwards [this] with A hA
    rwa [(paramsEquivFlat Sred222).symm_apply_apply A] at hA
  -- On flat coords, `dlnLoss = (α·β0)² + (α·β1)²` with the two factors read as single flat
  -- coordinates `x iα`, `x iβ0` (the `rfl` entry-extraction). Its zero-set sits inside
  -- `{x | x iα = 0} ∪ {x | x iβ0 = 0}`, a union of two coordinate hyperplanes, each null.
  set iα : Fin (flatDim Sred222) :=
    (Fintype.equivFin (FlatIdx Sred222))
      (⟨⟨⟨0, by norm_num⟩, ⟨0, by norm_num⟩⟩, ⟨0, by norm_num⟩⟩ : FlatIdx Sred222) with hiα
  set iβ : Fin (flatDim Sred222) :=
    (Fintype.equivFin (FlatIdx Sred222))
      (⟨⟨⟨1, by norm_num⟩, ⟨0, by norm_num⟩⟩, ⟨0, by norm_num⟩⟩ : FlatIdx Sred222) with hiβ
  -- the two coordinate hyperplanes are null (single fixed coordinate in a `Measure.pi`)
  have hα : ∀ᵐ x ∂(volume : Measure (Fin (flatDim Sred222) → ℝ)), x iα ≠ 0 :=
    MeasureTheory.Measure.ae_eval_ne (fun _ => (volume : Measure ℝ)) iα 0
  have hβ : ∀ᵐ x ∂(volume : Measure (Fin (flatDim Sred222) → ℝ)), x iβ ≠ 0 :=
    MeasureTheory.Measure.ae_eval_ne (fun _ => (volume : Measure ℝ)) iβ 0
  filter_upwards [hα, hβ] with x hxα hxβ
  -- read the loss in flat coords; `(α·β0)² + (α·β1)² = 0 → α·β0 = 0 → α = 0 ∨ β0 = 0`
  rw [dlnLoss_Sred_entry]
  have eα : ((paramsEquivFlat Sred222).symm x) 0 ⟨0, by norm_num⟩ ⟨0, by norm_num⟩ = x iα := rfl
  have eβ : ((paramsEquivFlat Sred222).symm x) 1 ⟨0, by norm_num⟩ ⟨0, by norm_num⟩ = x iβ := rfl
  rw [eα, eβ]
  intro hzero
  -- `(x iα · x iβ)² + (x iα · …)² = 0` forces `(x iα · x iβ)² = 0`, i.e. `x iα = 0 ∨ x iβ = 0`
  set γ : ℝ := ((paramsEquivFlat Sred222).symm x) 1 ⟨0, by norm_num⟩ ⟨1, by norm_num⟩ with hγ
  have h1 : (x iα * x iβ) ^ 2 = 0 :=
    le_antisymm
      (by nlinarith [sq_nonneg (x iα * γ)])
      (sq_nonneg _)
  have h2 : x iα * x iβ = 0 := by
    have := (pow_eq_zero_iff (n := 2) (by norm_num)).1 h1; exact this
  rcases mul_eq_zero.1 h2 with h | h
  · exact hxα h
  · exact hxβ h

/-- **Germ-nonvanishing of `GRed222`** (`Gne`, the `schur_recursion_step` hygiene). `GRed222 z ≠ 0` for
a.e. `z` near `0`: `GRed222 z = √(dlnLoss (1,1,2) 0 (redEmbed z))`, nonzero iff the reduced loss is
(`Real.sqrt_eq_zero'`); the loss is nonzero a.e. (`dlnLoss_Sred_ne_ae`), transported through the
measure-preserving `redEmbed`. -/
theorem GRed222_ne :
    ∃ U ∈ nhds (0 : YRed222), ∀ᵐ z ∂(volume.restrict U), transport222.G z ≠ 0 := by
  refine ⟨Set.univ, Filter.univ_mem, ?_⟩
  rw [Measure.restrict_univ]
  -- pull `dlnLoss ∘ redEmbed ≠ 0` a.e. back through the MP equiv
  have hpull : ∀ᵐ z ∂(volume : Measure YRed222), dlnLoss Sred222 0 (redEmbed222 z) ≠ 0 :=
    (measurePreserving_redEmbed222.quasiMeasurePreserving).ae dlnLoss_Sred_ne_ae
  filter_upwards [hpull] with z hz
  show GRed222 z ≠ 0
  unfold GRed222
  -- `√(loss) = 0 ↔ loss ≤ 0`; with `loss ≥ 0` and `loss ≠ 0`, `loss > 0`, so `√ ≠ 0`.
  have hpos : 0 < dlnLoss Sred222 0 (redEmbed222 z) :=
    lt_of_le_of_ne (dlnLoss_nonneg Sred222 0 _) (Ne.symm hz)
  exact ne_of_gt (Real.sqrt_pos.mpr hpos)

/-- The width drops `∑ (1,1,2) < ∑ (2,2,2)` (the `ChainDimSplit` termination measure). -/
theorem hdrop222 : ∑ s, (schurState M222route M222_hlo).red s < ∑ s, M222route s :=
  (schurState M222route M222_hlo).redM_widthSum_lt

/-! ## The `(2,2,2)` `RouteMNodeDescent` anchor + the `3/2` endpoint cross-check -/

/-- **The standalone `(2,2,2)` `RouteMNodeDescent`** (the `(B)`-anchor). Built by
`RouteMNodeDescent.ofNodePresentation` from the transcribed Schur certificate: `transport222` (the det-1
MP reindex), `flatCore222` (a Schur-SHAPED core, not the identified `(2,2,2)` blow-up core), `T = 1`,
`SΓ222` (the cert's reduced core `S·[x6,x7]`, faithful), `bcol222` (a contract-satisfying pivot-column
placeholder, not the cert's `y2`), and the `hnode222` presentation. `nReg = 2` (the `Erow` block, the
hard-coded count numerically agreeing with `nRegOf_M222 = 2`). Decorrelated from rs-grind's general
producer. -/
noncomputable def routeMNodeDescent222 :
    RouteMNodeDescent M222route (schurState M222route M222_hlo) 2 YRed222 :=
  RouteMNodeDescent.ofNodePresentation transport222 flatCore222 1 bcol222 SΓ222
    measurable_flatCore222 measurable_GRed222 GRed222_ne hdrop222 hnode222

/-- **The per-node descent step** for the `(2,2,2)` anchor: `rlctAtOn flatCore (0,0) = 2/2 + rlctAtOn
(dlnLoss (1,1,2) 0) 0`. The standalone value-half (the `nReg/2 = 1` Morse share + the reduced `(1,1,2)`
RLCT). -/
theorem routeMNodeDescent222_descentStep :
    rlctAtOn routeMNodeDescent222.flatCore (0, 0)
      = (2 : ℝ≥0∞) / 2 + rlctAtOn (dlnLoss (schurState M222route M222_hlo).red 0)
          (fun _ => 0 : Params (schurState M222route M222_hlo).red) :=
  routeMNodeDescent222.descentStep

/-- **The `c' = 3/2` endpoint cross-check.** The `(2,2,2)`-node descent step composes to `3/2`:
`nReg/2 + lambdaCore(1,1,2) = 2/2 + 1/2 = 3/2`. The reduced `(1,1,2)` RLCT `= 1/2` (the cert's
`lambdaCore(1,1,2)`, the recursion's child value) enters as the hypothesis `hred` — deferred, not
re-derived here; combined with the node's `nReg/2 = 1` Morse share it lands on `3/2`. This value
NUMERICALLY equals the committed `(2,2,2)` RLCT `case222_rlctAtOn_eq = 3/2` — a coincidence, NOT an
identification: this proves `rlctAtOn flatCore222 (0,0) = 3/2`, not `rlctAtOn (dlnLoss H222 0)
deepest222 = 3/2` (the latter is the committed lemma; the bridge between the two objects is exactly the
deliberately-uninvoked blow-up-Jacobian content). The `nReg = 2` count numerically agrees with
`nRegOf_M222 = 2` (cert: three independent confirmations). -/
theorem routeMNodeDescent222_descentStep_eq_three_halves
    (hred : rlctAtOn (dlnLoss (schurState M222route M222_hlo).red 0)
        (fun _ => 0 : Params (schurState M222route M222_hlo).red) = 1 / 2) :
    rlctAtOn routeMNodeDescent222.flatCore (0, 0) = 3 / 2 := by
  rw [routeMNodeDescent222_descentStep, hred, ENNReal.div_add_div_same]
  norm_num

end DLNFibre.DLN.RLCT
