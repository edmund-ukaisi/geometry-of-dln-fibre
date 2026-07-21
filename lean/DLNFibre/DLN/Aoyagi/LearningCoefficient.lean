import DLNFibre.Core.Aoyagi.Engine
import DLNFibre.DLN.Aoyagi.RecursionAdapter
import DLNFibre.DLN.RlctPayoff
import DLNFibre.DLN.RLCT.Foundations.GlobalHomog
import DLNFibre.DLN.RLCT.Foundations.ParamsFlat
import Meta.Cordon

/-!
# `DLN.Aoyagi.LearningCoefficient` — the corollary/test: `rlct(K^DLN_0) = C/2` VIA THE ENGINE

**BLUEPRINT (v3/v4).** The learning-coefficient theorem as a **corollary and test** of Objects A–D
(charter §0: the objects are the goal). It routes the value entirely through the engine, so its axiom
cone has `sorryAx` (the frontier leaves) but **NOT** `cited_aoyagi_lower_ax`/`cited_watanabe_upper_ax`.

## Soundness fixes carried (v2 defects 3 & 5, and the v4 un-bundling)

* **Concrete `F` (no adversarial existential).** The resolved family is the CONCRETE flattened
  product-map entry family `coreGen d e` (`(∏C)ᵢⱼ` in flat coordinates), not an `∃ F` an adversary
  could pick to trivially satisfy the conjuncts.
* **The reduction is a SEPARATE named leaf.** `coreReduction` (the deepest-point Thm 4 + the
  regular-block/flatten R0 + the ℝ≥0∞→ℝ carrier bridge) is un-bundled from the resolution existence;
  it rides banked machinery (`deepest_le_of_homogeneous_core`, the measure-preserving flatten). The
  genuinely-new content it names is the carrier bridge.
* **Defect 5.** The resolution is OBTAINED from `exists_coreResolution` (B's existence on the cone);
  no analytic side condition is user-facing.
* **Defect 3.** `exists_coreResolution` guarded by `0 < N` + positive widths.
* **Scope (named future leaf).** The `Monotone d` hypothesis is the QIP-side scope; the non-monotone
  extension rides the banked permutation-invariance of `(C, θ)` — a future leaf, not a hidden gap.
-/

open MeasureTheory Filter Topology
open Meta.Cordon
open DLNFibre.Core DLNFibre.Core.Aoyagi
open DLNFibre.DLN.RLCT (rlctGlobal_comp_homeomorph globalRlctAt_comp_homeomorph
  rlctGlobal_eq_rlctAt_zero_of_homogeneous measurePreserving_piCurry continuous_sigmaCurry
  continuous_sigmaUncurry)

namespace DLNFibre.DLN.Aoyagi

variable {N : ℕ}

/-- The **flattened parameter dimension** `∑ᵢ d(i+1)·d(i)` — the number of real coordinates of
`Rep_d` (a matrix tuple), the source dimension of the resolution charts. -/
def flatDim (d : Fin (N + 1) → ℕ) : ℕ := ∑ i : Fin N, d i.succ * d i.castSucc

/-- The **concrete flattened core-generator family**: `coreGen d e k u = (∏ C)ᵢⱼ` where `(i,j)` is the
`k`-th entry of the product `mult d` evaluated at the tuple `e u` (the flatten `e` of the exceptional
coordinates `u`). The entries of the multiplication map — Aoyagi's core `∏ C`, worked.tex:120–128.
Definable and concrete (no existential family). -/
noncomputable def coreGen (d : Fin (N + 1) → ℕ)
    (e : (Fin (flatDim d) → ℝ) ≃ₜ Tuple (k := ℝ) d) :
    Fin (d (Fin.last N) * d 0) → (Fin (flatDim d) → ℝ) → ℝ :=
  fun k u ↦ (mult d (e u)) (finProdFinEquiv.symm k).1 (finProdFinEquiv.symm k).2

/-- **STRIKE-ABLE leaf (Frobenius) — the flat core loss IS the zero-product DLN loss pulled back
along the flatten.** `∑ (coreGen d e)ᵢ² = lossDLN d 0 ∘ e`: the sum of squares of the flattened
product entries equals the square-Frobenius loss `‖mult‖²_F = Tr(MᵀM) = ∑ᵢⱼ Mᵢⱼ²` at `B = 0`,
evaluated at `e u`. Reindexing the flat `Fin (d_N·d_0)` sum to the matrix `(i,j)` sum via
`finProdFinEquiv` and expanding the Frobenius trace. Holds for ANY homeomorphism `e` (it unfolds
`coreGen`'s definition; no measure/linearity hypothesis). -/
theorem lossDLN_zero_eq_coreLoss (d : Fin (N + 1) → ℕ)
    (e : (Fin (flatDim d) → ℝ) ≃ₜ Tuple (k := ℝ) d) :
    sumSqFam (coreGen d e) = fun u ↦ lossDLN d 0 (e u) := by
  funext u
  show (∑ k, (coreGen d e k u) ^ 2) = lossDLN d 0 (e u)
  -- reindex the flat sum `∑ k : Fin (d_N·d_0)` to the matrix sum `∑ (i,j)` via `finProdFinEquiv`.
  have h1 : (∑ k, (coreGen d e k u) ^ 2)
      = ∑ p : Fin (d (Fin.last N)) × Fin (d 0), ((mult d (e u)) p.1 p.2) ^ 2 :=
    Equiv.sum_comp finProdFinEquiv.symm (fun p => ((mult d (e u)) p.1 p.2) ^ 2)
  rw [h1, Fintype.sum_prod_type]
  -- expand `lossDLN d 0 (e u) = Tr((mult)ᵀ (mult)) = ∑ⱼ ∑ᵢ (mult)ᵢⱼ²`, then swap the sum order.
  rw [lossDLN, sub_zero, Matrix.trace]
  simp only [Matrix.diag_apply, Matrix.mul_apply, Matrix.transpose_apply]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
  rw [sq]

/-! ## Homogeneity of the zero-product loss (degree `2N`)

The multiplication map scales as `mult (c • A) = c^N • mult A` (each of the `N` layers picks up one
factor of `c`), so the square-Frobenius zero-product loss `‖mult‖²_F` is homogeneous of degree `2N`.
The deepest-point argument (the origin has the minimal local RLCT) rides this homogeneity. -/

/-- **Prefix-product scaling.** `multPrefix d (c • A) j = c^j • multPrefix d A j` (the first `j`
layers each contribute one factor `c`). By `Fin.induction` on `j`. -/
theorem multPrefix_smul (d : Fin (N + 1) → ℕ) (c : ℝ) (A : Tuple (k := ℝ) d) (j : Fin (N + 1)) :
    multPrefix d (c • A) j = c ^ (j : ℕ) • multPrefix d A j := by
  induction j using Fin.induction with
  | zero => simp
  | succ i ih =>
    rw [multPrefix_succ, multPrefix_succ, ih, Pi.smul_apply, Matrix.smul_mul, Matrix.mul_smul,
      smul_smul, Fin.val_succ, Fin.coe_castSucc, pow_succ']

/-- **Scalar homogeneity of `mult`** (degree `N`): `mult d (c • A) = c^N • mult d A`. -/
theorem mult_smul_scalar (d : Fin (N + 1) → ℕ) (c : ℝ) (A : Tuple (k := ℝ) d) :
    mult d (c • A) = c ^ N • mult d A := by
  rw [mult, mult, multPrefix_smul, Fin.val_last]

/-- **The zero-product loss is homogeneous of degree `2N`:** `lossDLN d 0 (c • A) = c^(2N)·lossDLN d
0 A`. From `mult (c • A) = c^N • mult A` and `Tr((c^N M)ᵀ (c^N M)) = c^(2N)·Tr(MᵀM)`. -/
theorem lossDLN_zero_homogeneous (d : Fin (N + 1) → ℕ) (c : ℝ) (A : Tuple (k := ℝ) d) :
    lossDLN d 0 (c • A) = c ^ (2 * N) * lossDLN d 0 A := by
  simp only [lossDLN, sub_zero, mult_smul_scalar, Matrix.transpose_smul, Matrix.smul_mul,
    Matrix.mul_smul, smul_smul, Matrix.trace_smul, smul_eq_mul, ← pow_add, two_mul]

/-- **The prefix product is continuous** (`Fin.induction` on `j`, `Continuous.matrix_mul`). -/
theorem continuous_multPrefix (d : Fin (N + 1) → ℕ) (j : Fin (N + 1)) :
    Continuous (fun A : Tuple (k := ℝ) d => multPrefix d A j) := by
  induction j using Fin.induction with
  | zero => simpa only [multPrefix_zero] using continuous_const
  | succ i ih =>
    simp only [multPrefix_succ]
    exact (continuous_apply i).matrix_mul ih

/-- **The multiplication map is continuous.** -/
theorem continuous_mult (d : Fin (N + 1) → ℕ) :
    Continuous (fun A : Tuple (k := ℝ) d => mult d A) :=
  continuous_multPrefix d (Fin.last N)

/-- **The zero-product square-Frobenius loss is continuous** (trace of `(mult)ᵀ (mult)`). -/
theorem continuous_lossDLN_zero (d : Fin (N + 1) → ℕ) :
    Continuous (fun A : Tuple (k := ℝ) d => lossDLN d 0 A) := by
  simp only [lossDLN, sub_zero]
  exact ((continuous_mult d).matrix_transpose.matrix_mul (continuous_mult d)).matrix_trace

/-- The **flat index** for `Tuple d`: one coordinate per matrix entry `(layer i, row, col)` with
`row : Fin d_{i+1}`, `col : Fin d_i`. Its cardinality is `flatDim d`. -/
abbrev tupIdx (d : Fin (N + 1) → ℕ) : Type :=
  Σ q : (Σ i : Fin N, Fin (d i.succ)), Fin (d q.1.castSucc)

/-- `#tupIdx d = flatDim d = ∑ᵢ d_{i+1}·d_i` (the `Σ`-card collapse). -/
theorem card_tupIdx (d : Fin (N + 1) → ℕ) : Fintype.card (tupIdx d) = flatDim d := by
  unfold tupIdx flatDim
  rw [Fintype.card_sigma, Fintype.sum_sigma]
  simp only [Fintype.card_fin, Finset.sum_const, Finset.card_univ, smul_eq_mul]

/-- The re-indexing `tupIdx d ≃ Fin (flatDim d)`. -/
noncomputable def tupIdxEquiv (d : Fin (N + 1) → ℕ) : tupIdx d ≃ Fin (flatDim d) :=
  (Fintype.equivFin (tupIdx d)).trans (finCongr (card_tupIdx d))

/-- The **measure-preserving flatten** `Tuple d ≃ᵐ (Fin (flatDim d) → ℝ)`: two `piCurry` collapses
of the nested `Pi`, then the `arrowCongr'` re-index by `tupIdxEquiv` (mirrors `paramsEquivFlat`, with
`Tuple`'s row/col orientation `Matrix (Fin d_{i+1}) (Fin d_i)`). -/
noncomputable def tupleFlat (d : Fin (N + 1) → ℕ) :
    Tuple (k := ℝ) d ≃ᵐ (Fin (flatDim d) → ℝ) :=
  (MeasurableEquiv.piCurry
      (fun (i : Fin N) (_ : Fin (d i.succ)) => Fin (d i.castSucc) → ℝ)).symm.trans
    ((MeasurableEquiv.piCurry
        (fun (q : Σ i : Fin N, Fin (d i.succ)) (_ : Fin (d q.1.castSucc)) => ℝ)).symm.trans
      (MeasurableEquiv.arrowCongr' (tupIdxEquiv d) (MeasurableEquiv.refl ℝ)))

/-- `tupleFlat` is measure-preserving (two `measurePreserving_piCurry` + `volume_preserving_arrowCongr'`). -/
theorem measurePreserving_tupleFlat (d : Fin (N + 1) → ℕ) :
    MeasurePreserving (tupleFlat d) (volume : Measure (Tuple (k := ℝ) d))
      (volume : Measure (Fin (flatDim d) → ℝ)) := by
  unfold tupleFlat
  have h1 := measurePreserving_piCurry
    (fun (i : Fin N) (_ : Fin (d i.succ)) => Fin (d i.castSucc) → ℝ)
    (fun i _ => (volume : Measure (Fin (d i.castSucc) → ℝ)))
  have h2 := measurePreserving_piCurry
    (fun (q : Σ i : Fin N, Fin (d i.succ)) (_ : Fin (d q.1.castSucc)) => ℝ)
    (fun _ _ => (volume : Measure ℝ))
  have ha := volume_preserving_arrowCongr' (tupIdxEquiv d) (MeasurableEquiv.refl ℝ)
    (MeasurePreserving.id (volume : Measure ℝ))
  exact (h1.symm _).trans ((h2.symm _).trans ha)

/-- `tupleFlat` is continuous (two `Sigma.uncurry` + an evaluation re-index). -/
theorem continuous_tupleFlat (d : Fin (N + 1) → ℕ) : Continuous (tupleFlat d) := by
  unfold tupleFlat
  have e1 : Continuous (⇑(MeasurableEquiv.piCurry
      (fun (i : Fin N) (_ : Fin (d i.succ)) => Fin (d i.castSucc) → ℝ)).symm) := by
    rw [MeasurableEquiv.coe_piCurry_symm]; exact continuous_sigmaUncurry _
  have e2 : Continuous (⇑(MeasurableEquiv.piCurry
      (fun (q : Σ i : Fin N, Fin (d i.succ)) (_ : Fin (d q.1.castSucc)) => ℝ)).symm) := by
    rw [MeasurableEquiv.coe_piCurry_symm]; exact continuous_sigmaUncurry _
  have e3 : Continuous (⇑(MeasurableEquiv.arrowCongr' (tupIdxEquiv d) (MeasurableEquiv.refl ℝ))) := by
    apply continuous_pi; intro i; exact continuous_apply ((tupIdxEquiv d).symm i)
  exact e3.comp (e2.comp e1)

/-- `tupleFlat.symm` is continuous (two `Sigma.curry` + an evaluation re-index). -/
theorem continuous_tupleFlat_symm (d : Fin (N + 1) → ℕ) : Continuous (tupleFlat d).symm := by
  unfold tupleFlat
  have e1 : Continuous (⇑(MeasurableEquiv.piCurry
      (fun (i : Fin N) (_ : Fin (d i.succ)) => Fin (d i.castSucc) → ℝ))) := by
    rw [MeasurableEquiv.coe_piCurry]; exact continuous_sigmaCurry _
  have e2 : Continuous (⇑(MeasurableEquiv.piCurry
      (fun (q : Σ i : Fin N, Fin (d i.succ)) (_ : Fin (d q.1.castSucc)) => ℝ))) := by
    rw [MeasurableEquiv.coe_piCurry]; exact continuous_sigmaCurry _
  have e3 : Continuous (⇑(MeasurableEquiv.arrowCongr'
      (tupIdxEquiv d) (MeasurableEquiv.refl ℝ)).symm) := by
    apply continuous_pi; intro i; exact continuous_apply (tupIdxEquiv d i)
  exact e1.comp (e2.comp e3)

/-- **FRONTIER leaf (bookkeeping) — the measure-preserving flatten exists.** A **homeomorphism**
`Rep_d ≃ₜ ℝ^flatDim` (continuous both ways — REQUIRED for rlct locality), LINEAR (a coordinate
reindexing), sending the deepest tuple `0` to `0`, volume-preserving. Built from `tupleFlat`
(measure-preserving `MeasurableEquiv`, both continuities), inverted to `flat → Tuple`; linearity is
pointwise (each output coordinate is one input coordinate), so `IsLinearMap` closes by `rfl`. -/
theorem exists_flatten (d : Fin (N + 1) → ℕ) :
    ∃ e : (Fin (flatDim d) → ℝ) ≃ₜ Tuple (k := ℝ) d,
      IsLinearMap ℝ (⇑e) ∧ MeasurePreserving e ∧ e 0 = 0 := by
  refine ⟨{ (tupleFlat d).symm.toEquiv with
      continuous_toFun := continuous_tupleFlat_symm d
      continuous_invFun := continuous_tupleFlat d }, ?_, ?_, ?_⟩
  · exact ⟨fun x y => by funext i row col; rfl, fun c x => by funext i row col; rfl⟩
  · exact (measurePreserving_tupleFlat d).symm _
  · funext i row col; rfl

/-- **The deepest-point + flatten reduction.** `rlctGlobal (lossDLN d 0) = rlctAt (∑ (coreGen d e)ᵢ²)
0`: the global RLCT of the zero-product loss equals the local RLCT of the flattened core
`∑ (∏C)ᵢⱼ²` at the origin. Route (`GlobalHomog`): pick a CANONICAL **linear** measure-preserving
flatten `f` (`exists_flatten`); then `lossDLN d 0 ∘ f` is homogeneous of degree `2N`
(`f` linear + `lossDLN_zero_homogeneous`), so the origin is its deepest point and `rlctGlobal =
rlctAt·0` there (`rlctGlobal_eq_rlctAt_zero_of_homogeneous`, via the banked
`deepest_le_of_homogeneous_core`). The GLOBAL RLCT transports across the measure-preserving
homeomorphism `f` (`rlctGlobal_comp_homeomorph`), and the LOCAL RLCT at `0` is invariant under BOTH
`f` and the given `e` (`globalRlctAt_comp_homeomorph`, any measure-preserving homeomorphism fixing
`0` — no linearity needed on `e`), so the value transports through `e` to the concrete flat core
`∑(coreGen d e)ᵢ² = lossDLN d 0 ∘ e` (`lossDLN_zero_eq_coreLoss`). The last step
(`RLCT.Global.rlctAt = RLCT.rlctAt` on `ℝ^flatDim`) is the definitional bridge `global_rlctAt_eq`. -/
theorem coreReduction (d : Fin (N + 1) → ℕ) (hN : 0 < N)
    (e : (Fin (flatDim d) → ℝ) ≃ₜ Tuple (k := ℝ) d) (hemp : MeasurePreserving e) (he0 : e 0 = 0) :
    RLCT.Global.rlctGlobal (lossDLN d 0) = _root_.RLCT.rlctAt (sumSqFam (coreGen d e)) 0 := by
  -- a CANONICAL linear measure-preserving flatten `f` (its homogeneity drives the deepest-point step).
  obtain ⟨f, hf_lin, hf_mp, hf0⟩ := exists_flatten d
  haveI : BorelSpace (Tuple (k := ℝ) d) :=
    inferInstanceAs (BorelSpace (∀ i : Fin N, Fin (d i.succ) → Fin (d i.castSucc) → ℝ))
  have hembf : MeasurableEmbedding f := f.measurableEmbedding
  have hembe : MeasurableEmbedding e := e.measurableEmbedding
  -- `G_f = lossDLN d 0 ∘ f` : continuous, nonnegative, homogeneous of degree `2N` (`f` linear).
  have hcontGf : Continuous (fun u => lossDLN d 0 (f u)) :=
    (continuous_lossDLN_zero d).comp f.continuous
  have hnnGf : ∀ u, 0 ≤ lossDLN d 0 (f u) := fun u => lossDLN_nonneg d 0 (f u)
  have hhomGf : ∀ (c : ℝ) (u : Fin (flatDim d) → ℝ),
      lossDLN d 0 (f (c • u)) = c ^ (2 * N) * lossDLN d 0 (f u) := by
    intro c u
    rw [hf_lin.map_smul, lossDLN_zero_homogeneous]
  calc RLCT.Global.rlctGlobal (lossDLN d 0)
      = RLCT.Global.rlctGlobal (fun u => lossDLN d 0 (f u)) :=
        (rlctGlobal_comp_homeomorph f hf_mp hembf (lossDLN d 0)).symm
    _ = RLCT.Global.rlctAt (fun u => lossDLN d 0 (f u)) 0 :=
        rlctGlobal_eq_rlctAt_zero_of_homogeneous _ (2 * N) hcontGf hnnGf hhomGf
    _ = RLCT.Global.rlctAt (lossDLN d 0) (f 0) :=
        globalRlctAt_comp_homeomorph f hf_mp hembf (lossDLN d 0) 0
    _ = RLCT.Global.rlctAt (lossDLN d 0) (e 0) := by rw [hf0, he0]
    _ = RLCT.Global.rlctAt (fun u => lossDLN d 0 (e u)) 0 :=
        (globalRlctAt_comp_homeomorph e hemp hembe (lossDLN d 0) 0).symm
    _ = RLCT.Global.rlctAt (sumSqFam (coreGen d e)) 0 := by
        rw [← lossDLN_zero_eq_coreLoss d e]
    _ = _root_.RLCT.rlctAt (sumSqFam (coreGen d e)) 0 := RLCT.global_rlctAt_eq _ _

/-- **FRONTIER leaf (the geometric MONUMENT) — the core resolution exists.** For a genuine deep
network (`0 < N`) with positive widths (`hpos`), the flattened zero-product core `∑ (coreGen d e)ᵢ²`
admits a certified resolution **atlas** (Object B) at the deepest point `0`, whose binding divisors —
across all charts — realise the QIP spectrum with **min-attainment** (Object D, defect-4 form:
`hlb` no undershoot + `hattain` some chart's divisor attains `qipMin`). The atlas's existence is
Aoyagi's Hironaka construction with the explicit coupled `diag(b)` recursion for corank ≥ 2
(worked.tex:475–520; the genuine frontier this expedition must build, charter §1.B); the
min-attainment is Aoyagi's Lemma 3 minimisation (worked.tex:529–542). `F = coreGen d e` is concrete.
Two guards are REQUIRED, each rejecting a verified counterexample: (i) `he0 : e 0 = 0` — else a
translated flatten (`e u = u + 1`) makes `coreGen` not vanish at `0`, so no resolution at `0` exists;
(ii) `he_lin : IsLinearMap ℝ ⇑e` — the flatten is a LINEAR reindexing (the banked `paramsEquivFlat` is
linear), else a non-analytic origin-fixing homeomorphism (`e u = u·|u|` at `d=(1,1)`: `coreGen u = u|u|`)
makes `coreGen` non-analytic, and no analytic-`g` `Chart` can resolve it (the dom-wide `hideal_bwd` +
analyticity of `g` force `1 ≤ A·L²·|u| → 0`). This is the single genuine-mathematics frontier leaf of
the blueprint (the reduction is bookkeeping). -/
@[blueprint]
theorem exists_coreResolution (d : Fin (N + 1) → ℕ) (hd : Monotone d) (hN : 0 < N)
    (hpos : ∀ k, 0 < d k) (hne : (qipFeasible d).Nonempty)
    (e : (Fin (flatDim d) → ℝ) ≃ₜ Tuple (k := ℝ) d) (he0 : e 0 = 0)
    (he_lin : IsLinearMap ℝ (⇑e)) :
    ∃ res : Resolution (coreGen d e) 0,
      (∀ (c : Fin res.numCharts) (a : Fin (flatDim d)),
        a ∈ bindingAxes ((res.charts c).bexp (res.charts c).k₀) →
        qipMin d hne ≤ ((res.charts c).jac a + 1 : ℤ)) ∧
      (∃ (c : Fin res.numCharts) (a : Fin (flatDim d)),
        a ∈ bindingAxes ((res.charts c).bexp (res.charts c).k₀) ∧
        ((res.charts c).jac a + 1 : ℤ) = qipMin d hne) := by
  -- The COMBINATORIAL conjuncts (hlb/hattain) are discharged by the salvage adapter
  -- (`RecursionAdapter.exists_hlb_hattain_of_exists_atlasRealizesExponents`, riding the axiom-clean
  -- Engine combinatorics `minAdm_le_terminalExponents` + `o5_core_realized` + the
  -- `minAdm = cCodim = qipMin` bridge). The sole RESIDUAL is now the GEOMETRIC obligation: an atlas
  -- realizing the built tree's exponents exists.
  refine exists_hlb_hattain_of_exists_atlasRealizesExponents d hd hN hpos hne ?_
  -- map: DLN-existence-GEOMETRIC (the coupled ideal-route atlas `res : Resolution (coreGen d e) 0`
  -- with `AtlasRealizesExponents d res`; charter §1.B, the coupled monument + `hcover` BUILD)
  sorry

/-- **The learning coefficient `rlct(K^DLN_0) = C/2`, VIA THE ENGINE (the corollary/test).** For a
genuine deep network with positive widths, the global RLCT of the zero-product square-Frobenius DLN
loss equals half the combinatorial codimension `C = cCodim d 0` — DLNs are mildly singular. Wired:
the flatten (`exists_flatten`) + the reduction (`coreReduction`: `rlctGlobal = rlctAt (∑coreGenᵢ²) 0`),
then the engine value `2·rlctAt (∑coreGenᵢ²) 0 = cCodim d 0`
(`Resolution.two_mul_rlctAt_eq_cCodim` = Object B's atlas-min CoV/monomial rule ∘ Object D's QIP
bridge), obtaining the resolution from `exists_coreResolution`. The axiom cone is
`{propext, sorryAx, Classical.choice, Quot.sound}` — the DLN cites are NOT invoked (the value is
derived, not cited); the kill-path (charter §3). -/
@[blueprint]
theorem aoyagi_learning_coefficient_via_engine (d : Fin (N + 1) → ℕ) (hd : Monotone d) (hN : 0 < N)
    (hpos : ∀ k, 0 < d k) (h : (kostantPartitions d 0).Nonempty) (hne : (qipFeasible d).Nonempty) :
    RLCT.Global.rlctGlobal (lossDLN d 0) = ((cCodim d 0 h).toNat : ℝ) / 2 := by
  obtain ⟨e, he_lin, hemp, he0⟩ := exists_flatten d
  obtain ⟨res, hlb, hattain⟩ := exists_coreResolution d hd hN hpos hne e he0 he_lin
  have hred : RLCT.Global.rlctGlobal (lossDLN d 0) = _root_.RLCT.rlctAt (sumSqFam (coreGen d e)) 0 :=
    coreReduction d hN e hemp he0
  have heng : 2 * _root_.RLCT.rlctAt (sumSqFam (coreGen d e)) 0 = ((cCodim d 0 h).toNat : ℝ) :=
    res.two_mul_rlctAt_eq_cCodim d hd h hne hlb hattain
  rw [hred]; linarith [heng]

end DLNFibre.DLN.Aoyagi
