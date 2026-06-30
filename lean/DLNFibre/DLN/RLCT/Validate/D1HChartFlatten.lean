import DLNFibre.DLN.RLCT.Foundations.S1IFTChart
import DLNFibre.DLN.RLCT.Foundations.ParamsFlat
import DLNFibre.DLN.RLCT.Foundations.LossContinuity
import DLNFibre.DLN.RLCT.Validate.DeepestFramedProduct
import Mathlib.MeasureTheory.Group.Measure

/-!
# `DLNFibre.DLN.RLCT.Validate.D1HChartFlatten` — the flatten + translate bridge for the D1 `hchart`

The measure-preserving plumbing that moves the D1 loss off `Params H` onto the flat space
`Fin N → ℝ` with the basepoint translated to the origin — the prerequisite for instantiating the
banked abstract `hchart` (`rlctAtOn_eq_of_contDiff_chart`, `S1IFTChart`) with the concrete DLN
selected-minor chart.

Two MP steps, both `rlctAtOn_comp_homeomorph`:
  * **flatten** `paramsEquivFlat H : Params H ≃ᵐ (Fin (flatDim H) → ℝ)` (banked, MP):
    `rlctAt H (dlnLoss H B) v = rlctAtOn (dlnLoss H B ∘ flatSymm) (flat v)`;
  * **translate** `Homeomorph.addRight (flat v)` (Haar-invariant on `Fin N → ℝ`):
    `rlctAtOn (dlnLoss∘flatSymm) (flat v) = rlctAtOn (dlnLoss∘flatSymm ∘ (· + flat v)) 0`.

Composed: `rlctAt H (dlnLoss H B) v = rlctAtOn (lossFlatShift H B v) 0`, basepoint at the flat
origin (where the IFT chart `Φ` fixes `0`). STATUS: built sorry-free, axiom-clean.
-/

open MeasureTheory
open scoped ENNReal Topology
namespace DLNFibre.DLN.RLCT

variable {L : ℕ}

/-- The D1 loss in FLAT, ORIGIN-CENTRED coordinates: `dlnLoss H B` precomposed with the flat-inverse
and the translation by the flat image of `v`. Its local RLCT at the flat origin `0` equals
`rlctAt H (dlnLoss H B) v` (`rlctAt_eq_rlctAtOn_lossFlatShift`). -/
noncomputable def lossFlatShift (H : Fin (L + 1) → ℕ)
    (B : Matrix (Fin (H 0)) (Fin (H (Fin.last L))) ℝ) (v : Params H) :
    (Fin (flatDim H) → ℝ) → ℝ :=
  fun w => dlnLoss H B ((paramsEquivFlat H).symm (w + (paramsEquivFlat H) v))

/-- **The flatten + translate bridge.** The local RLCT of the D1 loss `dlnLoss H B` at the optimal
point `v` equals that of the flat, origin-centred `lossFlatShift H B v` at `0`:

    rlctAt H (dlnLoss H B) v = rlctAtOn (lossFlatShift H B v) 0.

Two measure-preserving changes of variable (`rlctAtOn_comp_homeomorph`): the flatten
`paramsEquivFlat H` (banked MP) then the translation `(· + flat v)` (Haar-invariant). The basepoint
lands at the flat origin, where the IFT chart fixes `0`. -/
theorem rlctAt_eq_rlctAtOn_lossFlatShift (H : Fin (L + 1) → ℕ)
    (B : Matrix (Fin (H 0)) (Fin (H (Fin.last L))) ℝ) (v : Params H) :
    rlctAt H (dlnLoss H B) v = rlctAtOn (lossFlatShift H B v) (0 : Fin (flatDim H) → ℝ) := by
  -- Step 1: flatten via `paramsEquivFlat H` (MP homeomorph), basepoint `v ↦ flat v`.
  set e : Params H ≃ₜ (Fin (flatDim H) → ℝ) :=
    ⟨(paramsEquivFlat H).toEquiv, continuous_paramsEquivFlat H, continuous_paramsEquivFlat_symm H⟩
    with he
  have hmp : MeasurePreserving e (volume : Measure (Params H)) volume :=
    measurePreserving_paramsEquivFlat H
  have hemb : MeasurableEmbedding e := (paramsEquivFlat H).measurableEmbedding
  have hstep1 := rlctAtOn_comp_homeomorph e hmp hemb
    (fun w : Fin (flatDim H) → ℝ => dlnLoss H B ((paramsEquivFlat H).symm w)) v
  have hcomp1 : (fun A : Params H => dlnLoss H B ((paramsEquivFlat H).symm (e A)))
      = fun A : Params H => dlnLoss H B A := by
    funext A; congr 1; exact (paramsEquivFlat H).symm_apply_apply A
  rw [hcomp1] at hstep1
  have he_v : e v = (paramsEquivFlat H) v := rfl
  rw [he_v] at hstep1
  -- now `hstep1 : rlctAtOn (dlnLoss H B) v = rlctAtOn (loss∘flatSymm) (flat v)` … but actually
  -- `rlctAtOn` on `Params` = `rlctAt`. Convert.
  rw [← rlctAtOn_eq_rlctAt H (dlnLoss H B) v, hstep1]
  -- Step 2: translate by `flat v` (MP, Haar), basepoint `0 ↦ flat v` via `addRight`.
  set τ : (Fin (flatDim H) → ℝ) ≃ₜ (Fin (flatDim H) → ℝ) :=
    Homeomorph.addRight ((paramsEquivFlat H) v) with hτ
  have hτmp : MeasurePreserving τ (volume : Measure (Fin (flatDim H) → ℝ)) volume := by
    rw [hτ]; exact measurePreserving_add_right volume ((paramsEquivFlat H) v)
  have hτemb : MeasurableEmbedding τ := τ.measurableEmbedding
  have hstep2 := rlctAtOn_comp_homeomorph τ hτmp hτemb
    (fun w : Fin (flatDim H) → ℝ => dlnLoss H B ((paramsEquivFlat H).symm w))
    (0 : Fin (flatDim H) → ℝ)
  have hτ0 : τ (0 : Fin (flatDim H) → ℝ) = (paramsEquivFlat H) v := by
    rw [hτ]; simp [Homeomorph.addRight]
  rw [hτ0] at hstep2
  rw [← hstep2]
  rfl

/-- **The flat-space D1 `hchart`** — flatten bridge + abstract chart-transfer, composed. For a
`ContDiff ℝ 2` self-map `Φ` of the flat space fixing the origin with invertible derivative `f'` at
`0`, if the flat origin-centred loss `lossFlatShift H B v` equals the post-chart `F ∘ Φ` near `0`
(`hgerm`), then `rlctAt H (dlnLoss H B) v = rlctAtOn F 0`. Chains
`rlctAt_eq_rlctAtOn_lossFlatShift` (the MP flatten+translate) with the banked
`rlctAtOn_eq_of_contDiff_chart` (the IFT chart-transfer, `det ≠ 0` proven from `f'`). `F` is the
post-chart loss `∑s² + ∑q²` (read on the flat space; the `(Fin nReg → ℝ) × Y` product split is a
separate MP reindex at the engine use-site). -/
theorem dln_hchart_flat (H : Fin (L + 1) → ℕ)
    (B : Matrix (Fin (H 0)) (Fin (H (Fin.last L))) ℝ) (v : Params H)
    (F : (Fin (flatDim H) → ℝ) → ℝ) (Φ : (Fin (flatDim H) → ℝ) → (Fin (flatDim H) → ℝ))
    (f' : (Fin (flatDim H) → ℝ) ≃L[ℝ] (Fin (flatDim H) → ℝ))
    (hΦ : ContDiff ℝ 2 Φ)
    (hΦ' : HasFDerivAt Φ (f' : (Fin (flatDim H) → ℝ) →L[ℝ] (Fin (flatDim H) → ℝ))
      (0 : Fin (flatDim H) → ℝ))
    (hfix : Φ (0 : Fin (flatDim H) → ℝ) = 0)
    (hgerm : lossFlatShift H B v =ᶠ[𝓝 (0 : Fin (flatDim H) → ℝ)] fun w => F (Φ w)) :
    rlctAt H (dlnLoss H B) v = rlctAtOn F (0 : Fin (flatDim H) → ℝ) := by
  rw [rlctAt_eq_rlctAtOn_lossFlatShift H B v]
  exact rlctAtOn_eq_of_contDiff_chart (lossFlatShift H B v) F Φ
    (0 : Fin (flatDim H) → ℝ) f' hΦ hΦ' hfix hgerm

/-- **The flatten-inverse entry is a single flat coordinate** (the entry-wise unblocker). The
flattening `paramsEquivFlat H` is a coordinate REINDEX, so each `Params`-entry of its inverse reads
one flat coordinate: `((paramsEquivFlat H).symm x) s i j = x (equivFin (FlatIdx H) ⟨⟨s,i⟩,j⟩)`. This
is what makes the flat-coord loss `C^∞` ENTRY-WISE into `ℝ` — necessary because `Params H` is NOT a
normed space, so no `ContDiff` map routes through it. -/
theorem paramsEquivFlat_symm_entry (H : Fin (L + 1) → ℕ) (x : Fin (flatDim H) → ℝ)
    (s : Fin L) (i : Fin (H s.castSucc)) (j : Fin (H s.succ)) :
    ((paramsEquivFlat H).symm x) s i j
      = x ((Fintype.equivFin (FlatIdx H)) ⟨⟨s, i⟩, j⟩) := rfl

/-- **`lossFlatShift` is `C^∞`** — the smoothness the IFT chart (and the `ContDiff ℝ 2` premise of
`dln_hchart_flat`) needs, built ENTRY-WISE into `ℝ` (never through the un-normed `Params H`).
`lossFlatShift w = ∑_ij ((prod H (flatSymm(w+flat v)) − B) i j)²`; each layer entry
`(flatSymm(w+flat v)) s i j = (w + flat v)(idx s i j)` is `C^∞` in `w` (a flat coordinate + const,
`paramsEquivFlat_symm_entry`), so each product entry is `C^∞` (`contDiff_prod_entry`); the loss is
then a finite sum of squares. -/
theorem contDiff_lossFlatShift (H : Fin (L + 1) → ℕ)
    (B : Matrix (Fin (H 0)) (Fin (H (Fin.last L))) ℝ) (v : Params H) :
    ContDiff ℝ (⊤ : ℕ∞) (lossFlatShift H B v) := by
  -- the reconstruction `gmap w = flatSymm (w + flat v)`, accessed entry-wise.
  set gmap : (Fin (flatDim H) → ℝ) → Params H :=
    fun w => (paramsEquivFlat H).symm (w + (paramsEquivFlat H) v) with hgmap
  -- each layer entry is `C^∞`: it's a single flat coordinate of `w + flat v`.
  have hentry : ∀ (s : Fin L) (i : Fin (H s.castSucc)) (j : Fin (H s.succ)),
      ContDiff ℝ (⊤ : ℕ∞) (fun w => gmap w s i j) := by
    intro s i j
    have hcoord : (fun w => gmap w s i j)
        = fun w : Fin (flatDim H) → ℝ =>
          (w + (paramsEquivFlat H) v) ((Fintype.equivFin (FlatIdx H)) ⟨⟨s, i⟩, j⟩) := by
      funext w; rw [hgmap]; exact paramsEquivFlat_symm_entry H _ s i j
    rw [hcoord]
    exact (contDiff_apply ℝ _ _).comp (contDiff_id.add contDiff_const)
  -- each product entry is `C^∞`.
  have hprod : ∀ (i : Fin (H 0)) (j : Fin (H (Fin.last L))),
      ContDiff ℝ (⊤ : ℕ∞) (fun w => prod H (gmap w) i j) :=
    fun i j => contDiff_prod_entry H gmap hentry i j
  -- the loss as a finite double sum of squares.
  have heq : lossFlatShift H B v = fun w => ∑ i, ∑ j, ((prod H (gmap w) - B) i j) ^ 2 := by
    funext w; rw [lossFlatShift, dlnLoss]
  rw [heq]
  apply ContDiff.sum; intro i _
  apply ContDiff.sum; intro j _
  have hsub : ContDiff ℝ (⊤ : ℕ∞) (fun w => (prod H (gmap w) - B) i j) := by
    have hrw : (fun w => (prod H (gmap w) - B) i j)
        = fun w => prod H (gmap w) i j - B i j := by funext w; simp [Matrix.sub_apply]
    rw [hrw]; exact (hprod i j).sub contDiff_const
  exact hsub.pow 2

end DLNFibre.DLN.RLCT
