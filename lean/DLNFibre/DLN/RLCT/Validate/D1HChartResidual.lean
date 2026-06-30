import DLNFibre.DLN.RLCT.Validate.D1HChartWire
import DLNFibre.DLN.RLCT.Validate.D1HChartInverse
import DLNFibre.DLN.RLCT.Validate.D1HChartConstruction
import DLNFibre.DLN.RLCT.Validate.D1HChartFlatten
import DLNFibre.DLN.RLCT.Foundations.S1IFTProducer
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Logic.Equiv.Fin.Basic

/-!
# `DLNFibre.DLN.RLCT.Validate.D1HChartResidual` — the #231 `hchart` assembly (sub-build 5)

The capstone of the D1 `hchart` slot: turn the banked germ/chart/inverse blocks into the EXACT
`hchart` shape the §SEL engine consumer (`deepest_le_of_optimal_of_iftResidual`) demands:

    rlctAt H (dlnLoss H B) v
      = rlctAtOn (fun p : (Fin nReg → ℝ) × Y => (∑ i, p.1 i ^ 2) + (∑ i, q p i ^ 2)) (0, t0),

with `Y = Fin (flatDim H − nReg) → ℝ`, `q` a GLOBAL `C¹` residual, and `t0` the reindex of the flat
origin. STATUS: SCAFFOLD — sub-builds being filled one at a time.
-/

open Matrix Module MeasureTheory Set Filter
open scoped ENNReal Topology
namespace DLNFibre.DLN.RLCT

variable {H : Fin (2 + 1) → ℕ} {m : ℕ} {ec : Fin m → Fin (flatDim H)}

/-! ## Sub-build 1 — the measure-preserving split homeomorph `ℝ^N ≃ₜ ℝ^m × ℝ^(N−m)` -/

/-- The selected-membership predicate on flat coordinates: `c` is one of the `ec`-columns. -/
def selPred (ec : Fin m → Fin (flatDim H)) : Fin (flatDim H) → Prop := fun c => ∃ k, ec k = c

/-- `ec` injective reindexes the SELECTED subtype `{c // ∃ k, ec k = c}` onto `Fin m`. -/
noncomputable def selEquiv (hec : Function.Injective ec) :
    Fin m ≃ {c : Fin (flatDim H) // selPred ec c} where
  toFun k := ⟨ec k, ⟨k, rfl⟩⟩
  invFun c := c.2.choose
  left_inv k := hec (Exists.choose_spec (⟨k, rfl⟩ : selPred ec (ec k)))
  right_inv c := Subtype.ext c.2.choose_spec

instance instDecidableSelPred (ec : Fin m → Fin (flatDim H)) : DecidablePred (selPred ec) :=
  fun c => Fintype.decidableExistsFintype

/-- The COMPLEMENT subtype `{c // ¬ selPred ec c}` has cardinality `flatDim H − m`. -/
theorem card_complSub (hec : Function.Injective ec) :
    Fintype.card {c : Fin (flatDim H) // ¬ selPred ec c} = flatDim H - m := by
  classical
  rw [Fintype.card_subtype_compl]
  have hsel : Fintype.card {c : Fin (flatDim H) // selPred ec c} = m := by
    rw [← Fintype.card_congr (selEquiv hec), Fintype.card_fin]
  rw [hsel, Fintype.card_fin]

/-- Reindex the COMPLEMENT subtype to `Fin (flatDim H − m)` (card bridge). -/
noncomputable def complEquiv (hec : Function.Injective ec) :
    Fin (flatDim H - m) ≃ {c : Fin (flatDim H) // ¬ selPred ec c} :=
  (finCongr (card_complSub hec).symm).trans (Fintype.equivFin _).symm

/-- **The split homeomorph** `ℝ^N ≃ₜ ℝ^m × ℝ^(N−m)`: separate the selected `ec`-columns from the
complement, then reindex each subtype factor to a `Fin`. The selected slot `k` reads coordinate
`ec k` (`splitHomeo_fst_apply`). -/
noncomputable def splitHomeo (hec : Function.Injective ec) :
    (Fin (flatDim H) → ℝ) ≃ₜ ((Fin m → ℝ) × (Fin (flatDim H - m) → ℝ)) :=
  (Homeomorph.piEquivPiSubtypeProd (selPred ec) (fun _ => ℝ)).trans
    ((Homeomorph.piCongrLeft (Y := fun _ : {c // selPred ec c} => ℝ) (selEquiv hec)).symm.prodCongr
      (Homeomorph.piCongrLeft (Y := fun _ : {c // ¬ selPred ec c} => ℝ) (complEquiv hec)).symm)

/-- The selected slot `k` of `splitHomeo` reads the `ec k` flat coordinate. -/
theorem splitHomeo_fst_apply (hec : Function.Injective ec) (w : Fin (flatDim H) → ℝ) (k : Fin m) :
    (splitHomeo hec w).1 k = w (ec k) := by
  simp only [splitHomeo, Homeomorph.trans_apply, Homeomorph.coe_prodCongr, Prod.map_apply,
    Homeomorph.piCongrLeft_symm_apply]
  rfl

/-- `splitHomeo` is measure-preserving (volume on the flat space ↔ product volume). -/
theorem splitHomeo_mp (hec : Function.Injective ec) :
    MeasurePreserving (splitHomeo hec)
      (volume : Measure (Fin (flatDim H) → ℝ)) volume := by
  have hA : MeasurePreserving
      ⇑(MeasurableEquiv.piCongrLeft (fun _ : {c // selPred ec c} => ℝ) (selEquiv hec)).symm
      volume volume :=
    MeasurePreserving.symm _
      (volume_measurePreserving_piCongrLeft (fun _ : {c // selPred ec c} => ℝ) (selEquiv hec))
  have hB : MeasurePreserving
      ⇑(MeasurableEquiv.piCongrLeft (fun _ : {c // ¬ selPred ec c} => ℝ) (complEquiv hec)).symm
      volume volume :=
    MeasurePreserving.symm _
      (volume_measurePreserving_piCongrLeft (fun _ : {c // ¬ selPred ec c} => ℝ) (complEquiv hec))
  have hpiv := volume_preserving_piEquivPiSubtypeProd (fun _ : Fin (flatDim H) => ℝ) (selPred ec)
  have hprod := hA.prod hB
  exact hprod.comp hpiv

/-- `splitHomeo` is a measurable embedding (it is a homeomorphism). -/
theorem splitHomeo_emb (hec : Function.Injective ec) :
    MeasurableEmbedding (splitHomeo hec) :=
  (splitHomeo hec).measurableEmbedding

/-- `splitHomeo.symm` reads coordinate `c`: the selected branch from `s`, the complement from `t`. -/
theorem splitHomeo_symm_apply (hec : Function.Injective ec)
    (p : (Fin m → ℝ) × (Fin (flatDim H - m) → ℝ)) (c : Fin (flatDim H)) :
    (splitHomeo hec).symm p c
      = if hc : selPred ec c then p.1 ((selEquiv hec).symm ⟨c, hc⟩)
        else p.2 ((complEquiv hec).symm ⟨c, hc⟩) := by
  classical
  simp only [splitHomeo, Homeomorph.symm_trans_apply, Homeomorph.prodCongr_symm,
    Homeomorph.symm_symm, Homeomorph.coe_prodCongr,
    Homeomorph.piEquivPiSubtypeProd_symm_apply, Prod.map_fst, Prod.map_snd,
    Homeomorph.piCongrLeft_apply, Equiv.piCongrLeft, Equiv.piCongrLeft'_symm,
    Equiv.symm_symm, Equiv.piCongrLeft'_apply]

/-- `splitHomeo.symm` is `C^∞` (each coordinate is a `contDiff_apply` of `s` or `t`). -/
theorem contDiff_splitHomeo_symm (hec : Function.Injective ec) :
    ContDiff ℝ (⊤ : ℕ∞) (splitHomeo hec).symm := by
  classical
  rw [contDiff_pi]
  intro c
  have hfun : (fun p : (Fin m → ℝ) × (Fin (flatDim H - m) → ℝ) => (splitHomeo hec).symm p c)
      = fun p => if hc : selPred ec c then p.1 ((selEquiv hec).symm ⟨c, hc⟩)
          else p.2 ((complEquiv hec).symm ⟨c, hc⟩) := by
    funext p; exact splitHomeo_symm_apply hec p c
  rw [hfun]
  by_cases hc : selPred ec c
  · simp only [dif_pos hc]
    exact (contDiff_apply ℝ _ ((selEquiv hec).symm ⟨c, hc⟩)).comp contDiff_fst
  · simp only [dif_neg hc]
    exact (contDiff_apply ℝ _ ((complEquiv hec).symm ⟨c, hc⟩)).comp contDiff_snd

/-! ## Sub-build 3 — the raw residual and the flat-space loss germ -/

variable {B : Matrix (Fin (H 0)) (Fin (H (Fin.last 2))) ℝ} {v : Params H}
  {er : Fin m → Fin (H 0) × Fin (H 2)}

/-- The selected-entry predicate on loss-entry pairs: `(i,j)` is one of the `er`-rows. -/
def selRow (er : Fin m → Fin (H 0) × Fin (H 2)) : Fin (H 0) × Fin (H 2) → Prop :=
  fun ij => ∃ k, er k = ij

instance instDecidableSelRow (er : Fin m → Fin (H 0) × Fin (H 2)) : DecidablePred (selRow er) :=
  fun _ => Fintype.decidableExistsFintype

/-- The RAW residual loss-entry vector `g₀ ∘ Ψsymm`: the `(i,j)` loss entry of
`prod (gmapAt H v (Ψsymm w)) − B`, ZEROED on the selected `er`-rows (those become the `∑ s²` block).
A function of the flat point `w` (pre-reindex), keyed by the loss-entry pair. -/
noncomputable def rawResid (B : Matrix (Fin (H 0)) (Fin (H (Fin.last 2))) ℝ) (v : Params H)
    {m : ℕ} (er : Fin m → Fin (H 0) × Fin (H 2))
    (Ψsymm : (Fin (flatDim H) → ℝ) → (Fin (flatDim H) → ℝ))
    (w : Fin (flatDim H) → ℝ) (ij : Fin (H 0) × Fin (H 2)) : ℝ :=
  if selRow er ij then 0 else (prod H (gmapAt H v (Ψsymm w)) - B) ij.1 ij.2

/-- **The selected/residual sum split** (network-free, `er` injective). For any `f`, the full
double sum splits as the selected `er`-rows (reindexed by `k`) plus the zeroed-selected residual:

    ∑_{(i,j)} f (i,j) = ∑_{k} f (er k) + ∑_{(i,j)} (if selRow er (i,j) then 0 else f (i,j)). -/
theorem sum_split_selected (her : Function.Injective er) (f : Fin (H 0) × Fin (H 2) → ℝ) :
    ∑ ij : Fin (H 0) × Fin (H 2), f ij
      = (∑ k : Fin m, f (er k))
        + ∑ ij : Fin (H 0) × Fin (H 2), (if selRow er ij then 0 else f ij) := by
  classical
  -- the selected finset = image of `er`
  set S : Finset (Fin (H 0) × Fin (H 2)) := Finset.image er Finset.univ with hS
  have hsel_mem : ∀ ij, ij ∈ S ↔ selRow er ij := by
    intro ij; rw [hS, Finset.mem_image]
    constructor
    · rintro ⟨k, _, rfl⟩; exact ⟨k, rfl⟩
    · rintro ⟨k, rfl⟩; exact ⟨k, Finset.mem_univ k, rfl⟩
  -- selected sum reindexes to `∑ k`
  have hsumS : ∑ ij ∈ S, f ij = ∑ k : Fin m, f (er k) := by
    rw [hS, Finset.sum_image (fun a _ b _ h => her h)]
  -- the residual sum drops the selected
  have hresid : ∑ ij : Fin (H 0) × Fin (H 2), (if selRow er ij then 0 else f ij)
      = ∑ ij ∈ Sᶜ, f ij := by
    rw [← Finset.sum_compl_add_sum S (fun ij => if selRow er ij then 0 else f ij)]
    have hSpart : ∑ ij ∈ S, (if selRow er ij then 0 else f ij) = 0 := by
      apply Finset.sum_eq_zero; intro ij hij; rw [if_pos ((hsel_mem ij).mp hij)]
    rw [hSpart, add_zero]
    apply Finset.sum_congr rfl; intro ij hij
    have hnot : ¬ selRow er ij := fun h => (Finset.mem_compl.mp hij) ((hsel_mem ij).mpr h)
    rw [if_neg hnot]
  rw [hresid, ← hsumS]
  rw [add_comm (∑ ij ∈ S, f ij) (∑ ij ∈ Sᶜ, f ij)]
  exact (Finset.sum_compl_add_sum S f).symm

/-- **Germ A — the flat-space loss decomposition.** Near the flat origin, the chart-pulled loss
`lossFlatShift ∘ Ψsymm` splits as the `m` selected squared coordinates `(w (ec k))²` plus the
squared residual `∑_{(i,j)} (rawResid w (i,j))²` (the selected entries become coordinates via
`selected_lossEntry_germ`; the rest are the residual, with `0²` collapsing the selected slots). -/
theorem germA (hopt : prod H v = B) (her : Function.Injective er) (hec : Function.Injective ec)
    (Ψsymm : (Fin (flatDim H) → ℝ) → (Fin (flatDim H) → ℝ))
    (hrinv : ∀ᶠ w in 𝓝 (0 : Fin (flatDim H) → ℝ), chartΦ H B v er ec (Ψsymm w) = w) :
    (fun w => lossFlatShift H B v (Ψsymm w)) =ᶠ[𝓝 (0 : Fin (flatDim H) → ℝ)]
      fun w => (∑ k : Fin m, (w (ec k)) ^ 2)
        + ∑ ij : Fin (H 0) × Fin (H 2), (rawResid B v er Ψsymm w ij) ^ 2 := by
  classical
  -- the selected-entry germ for each `k`
  have hsel : ∀ k : Fin m, ∀ᶠ w in 𝓝 (0 : Fin (flatDim H) → ℝ),
      (prod H (gmapAt H v (Ψsymm w)) - B) (er k).1 (er k).2 = w (ec k) :=
    fun k => selected_lossEntry_germ hopt hec Ψsymm hrinv k
  filter_upwards [Filter.eventually_all.2 hsel] with w hw
  -- expand the loss as the double sum of squared entries
  rw [lossFlatShift_eq_sum_sq]
  -- fold the `Fin (H 0) × Fin (H 2)` double sum to a product index (`H (Fin.last 2) = H 2` defeq)
  have hfold : (∑ i, ∑ j, ((prod H (gmapAt H v (Ψsymm w)) - B) i j) ^ 2)
      = ∑ ij : Fin (H 0) × Fin (H 2), ((prod H (gmapAt H v (Ψsymm w)) - B) ij.1 ij.2) ^ 2 :=
    (Fintype.sum_prod_type (f := fun ij : Fin (H 0) × Fin (H 2) =>
      ((prod H (gmapAt H v (Ψsymm w)) - B) ij.1 ij.2) ^ 2)).symm
  rw [hfold]
  -- split selected/residual
  rw [sum_split_selected (er := er) her
    (fun ij => ((prod H (gmapAt H v (Ψsymm w)) - B) ij.1 ij.2) ^ 2)]
  congr 1
  · -- selected: each squared entry becomes `(w (ec k))²`
    apply Finset.sum_congr rfl; intro k _; rw [hw k]
  · -- residual: `if sel then 0 else (entry)² = (rawResid)²`
    apply Finset.sum_congr rfl; intro ij _
    rw [rawResid]
    by_cases hsr : selRow er ij
    · rw [if_pos hsr, if_pos hsr]; norm_num
    · rw [if_neg hsr, if_neg hsr]

/-! ## Sub-build 4 — globalize a locally-`C^n` map by a bump cutoff -/

/-- **Bump-globalization.** A map `g : E → F` (`E` finite-dim real normed) that is `ContDiffOn ℝ n`
on an open `U ∋ x₀` can be replaced by a GLOBAL `ContDiff ℝ n` map agreeing with `g` on a
neighbourhood of `x₀`: multiply by a `C^∞` bump `χ` with `tsupport χ ⊆ U` and `χ =ᶠ 1` near `x₀`,
extending by `0` off `tsupport χ`. The product is `C^n` everywhere — on the open `U` both factors
are, and off the open `(tsupport χ)ᶜ` it vanishes; these cover `E`. -/
theorem exists_contDiff_eventuallyEq_of_contDiffOn {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [HasContDiffBump E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {n : ℕ∞} {g : E → F} {U : Set E} {x₀ : E} (hUopen : IsOpen U) (hx₀ : x₀ ∈ U)
    (hg : ContDiffOn ℝ n g U) :
    ∃ G : E → F, ContDiff ℝ n G ∧ G =ᶠ[𝓝 x₀] g := by
  classical
  -- a metric ball `ball x₀ r ⊆ U`.
  obtain ⟨r, hrpos, hrU⟩ := Metric.isOpen_iff.1 hUopen x₀ hx₀
  -- a `C^∞` bump centred at `x₀` with `rOut = r/2 < r`, `≡ 1` near `x₀`, `tsupport ⊆ ball x₀ r`.
  set χ : ContDiffBump x₀ :=
    { rIn := r / 4, rOut := r / 2, rIn_pos := by positivity, rIn_lt_rOut := by linarith } with hχ
  have hχsupp : tsupport (χ : E → ℝ) ⊆ U := by
    rw [χ.tsupport_eq]
    refine subset_trans (fun y hy => ?_) hrU
    rw [Metric.mem_ball]; rw [Metric.mem_closedBall] at hy
    have hrout : χ.rOut = r / 2 := rfl
    rw [hrout] at hy; linarith
  refine ⟨fun x => χ x • g x, ?_, ?_⟩
  · -- global `C^n`: pointwise `ContDiffAt`.
    rw [contDiff_iff_contDiffAt]
    intro x
    by_cases hx : x ∈ tsupport (χ : E → ℝ)
    · -- inside `tsupport χ ⊆ U`: both `χ` and `g` are `C^n` on the open `U`.
      have hxU : x ∈ U := hχsupp hx
      exact ((χ.contDiff (n := n)).contDiffAt).smul (hg.contDiffAt (hUopen.mem_nhds hxU))
    · -- outside `tsupport χ` (open): `χ • g ≡ 0`.
      have hopen : IsOpen (tsupport (χ : E → ℝ))ᶜ := (isClosed_tsupport _).isOpen_compl
      have hzero : (fun x => χ x • g x) =ᶠ[𝓝 x] fun _ => (0 : F) := by
        filter_upwards [hopen.mem_nhds hx] with y hy
        rw [image_eq_zero_of_notMem_tsupport hy, zero_smul]
      exact (contDiff_const.contDiffAt).congr_of_eventuallyEq hzero
  · -- `χ • g =ᶠ g` near `x₀` (where `χ ≡ 1`).
    filter_upwards [χ.eventuallyEq_one] with x hx
    rw [hx, Pi.one_apply, one_smul]

/-- **Each flat loss entry is globally `C^∞`** (the reconstruction is entry-wise a flat coordinate,
`prod` is entry-polynomial). Mirrors `contDiff_chartΦ`'s internal `hprodSmooth`. -/
theorem contDiff_prod_gmapAt_entry (H : Fin (2 + 1) → ℕ) (v : Params H)
    (i : Fin (H 0)) (j : Fin (H (Fin.last 2))) :
    ContDiff ℝ (⊤ : ℕ∞) (fun w => prod H (gmapAt H v w) i j) := by
  have hgmap : ∀ (s : Fin 2) (a : Fin (H s.castSucc)) (b : Fin (H s.succ)),
      ContDiff ℝ (⊤ : ℕ∞) (fun w => gmapAt H v w s a b) := by
    intro s a b
    have hcoord : (fun w => gmapAt H v w s a b)
        = fun w : Fin (flatDim H) → ℝ =>
          (w + (paramsEquivFlat H) v) ((Fintype.equivFin (FlatIdx H)) ⟨⟨s, a⟩, b⟩) := by
      funext w; rw [gmapAt]; exact paramsEquivFlat_symm_entry H _ s a b
    rw [hcoord]
    exact (contDiff_apply ℝ _ _).comp (contDiff_id.add contDiff_const)
  exact contDiff_prod_entry H (gmapAt H v) hgmap i j

/-- The product index `Fin (H 0) × Fin (H 2) ≃ Fin (H 0 * H 2)` (loss-entry coordinate labelling). -/
noncomputable def entryIdx (H : Fin (2 + 1) → ℕ) : Fin (H 0) × Fin (H 2) ≃ Fin (H 0 * H 2) :=
  finProdFinEquiv

/-- The RAW residual as a `EuclideanSpace`-valued vector on the FLAT space (selected slots zeroed),
coordinatised by `entryIdx`. -/
noncomputable def rawResidVec (B : Matrix (Fin (H 0)) (Fin (H (Fin.last 2))) ℝ) (v : Params H)
    {m : ℕ} (er : Fin m → Fin (H 0) × Fin (H 2))
    (Ψsymm : (Fin (flatDim H) → ℝ) → (Fin (flatDim H) → ℝ))
    (w : Fin (flatDim H) → ℝ) : EuclideanSpace ℝ (Fin (H 0 * H 2)) :=
  WithLp.toLp 2 (fun i => rawResid B v er Ψsymm w ((entryIdx H).symm i))

/-- The `i`-th coordinate of `rawResidVec` is the raw residual at the `entryIdx`-decoded pair. -/
theorem rawResidVec_apply (B : Matrix (Fin (H 0)) (Fin (H (Fin.last 2))) ℝ) (v : Params H)
    {m : ℕ} (er : Fin m → Fin (H 0) × Fin (H 2))
    (Ψsymm : (Fin (flatDim H) → ℝ) → (Fin (flatDim H) → ℝ))
    (w : Fin (flatDim H) → ℝ) (i : Fin (H 0 * H 2)) :
    rawResidVec B v er Ψsymm w i = rawResid B v er Ψsymm w ((entryIdx H).symm i) := rfl

/-- On the open set `V` where `Ψsymm` is `C²`, the raw residual vector is `C²`. -/
theorem contDiffOn_rawResidVec (hopt : prod H v = B)
    (Ψsymm : (Fin (flatDim H) → ℝ) → (Fin (flatDim H) → ℝ)) {V : Set (Fin (flatDim H) → ℝ)}
    (hsymmCD : ContDiffOn ℝ 2 Ψsymm V) :
    ContDiffOn ℝ 2 (rawResidVec B v er Ψsymm) V := by
  classical
  -- coordinate-wise via `contDiffOn_euclidean`
  rw [contDiffOn_euclidean]
  intro i
  set ij := (entryIdx H).symm i with hij
  have hcoord : (fun w => rawResidVec B v er Ψsymm w i)
      = fun w => if selRow er ij then 0 else (prod H (gmapAt H v (Ψsymm w)) - B) ij.1 ij.2 := by
    funext w; rw [rawResidVec_apply, rawResid]
  rw [hcoord]
  by_cases hsr : selRow er ij
  · simp only [if_pos hsr]; exact contDiffOn_const
  · simp only [if_neg hsr]
    have hsub : (fun w => (prod H (gmapAt H v (Ψsymm w)) - B) ij.1 ij.2)
        = fun w => prod H (gmapAt H v (Ψsymm w)) ij.1 ij.2 - B ij.1 ij.2 := by
      funext w; rw [Matrix.sub_apply]
    rw [hsub]
    refine ContDiffOn.sub ?_ contDiffOn_const
    -- `(prod (gmapAt v ·) ij) ∘ Ψsymm`: outer `C^∞` (global), inner `Ψsymm` `C²` on `V`.
    have houter : ContDiff ℝ 2 (fun w' => prod H (gmapAt H v w') ij.1 ij.2) := by
      refine (contDiff_prod_gmapAt_entry H v ij.1 ij.2).of_le ?_
      rw [show (2 : WithTop ℕ∞) = ((2 : ℕ∞) : WithTop ℕ∞) from rfl]
      exact WithTop.coe_le_coe.mpr le_top
    exact houter.comp_contDiffOn hsymmCD

end DLNFibre.DLN.RLCT
