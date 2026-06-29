import DLNFibre.DLN.RLCT.Validate.RouteMSmearedHeadlineL2
import DLNFibre.DLN.RLCT.Validate.RouteM231Smeared

/-!
# `RouteMSmearedHeadlineL2Inst` — non-vacuity of the conditioned-box L=2 headline (the `(2,3,1)` witness)

The bedrock companion to `RouteMSmearedHeadlineL2`: it WITNESSES that the conditioned-box assembly
`routeMCore_box_diverges_smearedL2`'s hypothesis bundle is jointly SATISFIABLE — by instantiating it on
the worked `(2,3,1)` chart (`RouteM231Smeared`: `psi231`/`R231`/`D231`, the conditioned `subBox231`
shape). This rules out the conceptual-slop trap the smeared headline could otherwise hide: an assembly
whose conditioned hypotheses (the peeled rate + `U`-positivity ON the conditioned box, the field-A
containment, the radial det) cannot all hold at once would be vacuous. They all hold for `(2,3,1)`, and
the assembly fires end-to-end to reproduce `routeM231sm_box_diverges` (the validate-small headline).

The instance's `box i = if i = 0 ∨ i = 4 then Icc (δ/2) δ else Icc (−(δ/8)) (δ/8)` is the conditioned
rank-block diagonal (`u0,u4 ∈ [δ/2,δ]` keeps `det P₁ ≥ δ²/8 > 0`, so `U = ‖P₁H̄‖² > 0` and the off-pole
rate holds) — exactly `subBox231`'s shape (`subBox231_eq_pi`). The peeled rate and `U`-positivity ride on
the banked `subBox231_det_ne`/`subBox231_U_pos` via the membership bridge `insertNth 6 z y ∈ subBox231 δ`.
-/

open MeasureTheory
open scoped ENNReal BigOperators Matrix

namespace DLNFibre.DLN.RLCT

/-- The `(2,3,1)` conditioned per-axis box: coords `0,4` (the rank-block diagonal) in `[δ/2,δ]`, the rest
in `[−δ/8,δ/8]`. The non-pivot intervals of `subBox231`. -/
noncomputable def box231 (δ : ℝ) : Fin 9 → Set ℝ :=
  fun i => if i = 0 ∨ i = 4 then Set.Icc (δ/2) δ else Set.Icc (-(δ/8)) (δ/8)

/-- `box231 δ k` is measurable for every `k`. -/
theorem measurableSet_box231 (δ : ℝ) (k : Fin 9) : MeasurableSet (box231 δ k) := by
  unfold box231; split <;> exact measurableSet_Icc

/-- **The membership bridge** `insertNth ⟨6,_⟩ z y ∈ subBox231 δ` for `z ∈ Ioo 0 δ` and `y` in the
conditioned rest box. The peeled point reconstructs a `subBox231` element (pivot `= z`, coords `0,4` in
`[δ/2,δ]`, rest in `[−δ/8,δ/8]`), so the banked `subBox231_*` bounds apply. -/
theorem insertNth6_mem_subBox231 {δ : ℝ} {z : ℝ} (hz : z ∈ Set.Ioo (0:ℝ) δ) {y : Fin 8 → ℝ}
    (hy : y ∈ Set.univ.pi (fun k : Fin 8 => box231 δ ((⟨6, by decide⟩ : Fin 9).succAbove k))) :
    Fin.insertNth (⟨6, by decide⟩ : Fin 9) z y ∈ subBox231 δ := by
  simp only [Set.mem_pi, Set.mem_univ, true_implies] at hy
  -- helper: each non-pivot slot `succAbove k` reads `y k`, in `box231 δ (succAbove k)`
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [show (0:Fin 9) = (⟨6, by decide⟩ : Fin 9).succAbove ⟨0, by decide⟩ from by decide,
      Fin.insertNth_apply_succAbove]
    have := hy ⟨0, by decide⟩
    rwa [show box231 δ ((⟨6, by decide⟩ : Fin 9).succAbove ⟨0, by decide⟩) = Set.Icc (δ/2) δ from by
      simp only [box231]; rw [if_pos (Or.inl (by decide))]] at this
  · rw [show (1:Fin 9) = (⟨6, by decide⟩ : Fin 9).succAbove ⟨1, by decide⟩ from by decide,
      Fin.insertNth_apply_succAbove]
    have := hy ⟨1, by decide⟩
    rwa [show box231 δ ((⟨6, by decide⟩ : Fin 9).succAbove ⟨1, by decide⟩)
      = Set.Icc (-(δ/8)) (δ/8) from by simp only [box231]; rw [if_neg (by decide)]] at this
  · rw [show (2:Fin 9) = (⟨6, by decide⟩ : Fin 9).succAbove ⟨2, by decide⟩ from by decide,
      Fin.insertNth_apply_succAbove]
    have := hy ⟨2, by decide⟩
    rwa [show box231 δ ((⟨6, by decide⟩ : Fin 9).succAbove ⟨2, by decide⟩)
      = Set.Icc (-(δ/8)) (δ/8) from by simp only [box231]; rw [if_neg (by decide)]] at this
  · rw [show (3:Fin 9) = (⟨6, by decide⟩ : Fin 9).succAbove ⟨3, by decide⟩ from by decide,
      Fin.insertNth_apply_succAbove]
    have := hy ⟨3, by decide⟩
    rwa [show box231 δ ((⟨6, by decide⟩ : Fin 9).succAbove ⟨3, by decide⟩)
      = Set.Icc (-(δ/8)) (δ/8) from by simp only [box231]; rw [if_neg (by decide)]] at this
  · rw [show (4:Fin 9) = (⟨6, by decide⟩ : Fin 9).succAbove ⟨4, by decide⟩ from by decide,
      Fin.insertNth_apply_succAbove]
    have := hy ⟨4, by decide⟩
    rwa [show box231 δ ((⟨6, by decide⟩ : Fin 9).succAbove ⟨4, by decide⟩) = Set.Icc (δ/2) δ from by
      simp only [box231]; rw [if_pos (Or.inr (by decide))]] at this
  · rw [show (5:Fin 9) = (⟨6, by decide⟩ : Fin 9).succAbove ⟨5, by decide⟩ from by decide,
      Fin.insertNth_apply_succAbove]
    have := hy ⟨5, by decide⟩
    rwa [show box231 δ ((⟨6, by decide⟩ : Fin 9).succAbove ⟨5, by decide⟩)
      = Set.Icc (-(δ/8)) (δ/8) from by simp only [box231]; rw [if_neg (by decide)]] at this
  · rw [show (6:Fin 9) = (⟨6, by decide⟩ : Fin 9) from rfl, Fin.insertNth_apply_same]; exact hz
  · rw [show (7:Fin 9) = (⟨6, by decide⟩ : Fin 9).succAbove ⟨6, by decide⟩ from by decide,
      Fin.insertNth_apply_succAbove]
    have := hy ⟨6, by decide⟩
    rwa [show box231 δ ((⟨6, by decide⟩ : Fin 9).succAbove ⟨6, by decide⟩)
      = Set.Icc (-(δ/8)) (δ/8) from by simp only [box231]; rw [if_neg (by decide)]] at this
  · rw [show (8:Fin 9) = (⟨6, by decide⟩ : Fin 9).succAbove ⟨7, by decide⟩ from by decide,
      Fin.insertNth_apply_succAbove]
    have := hy ⟨7, by decide⟩
    rwa [show box231 δ ((⟨6, by decide⟩ : Fin 9).succAbove ⟨7, by decide⟩)
      = Set.Icc (-(δ/8)) (δ/8) from by simp only [box231]; rw [if_neg (by decide)]] at this

/-- **`condBox ⟨6,_⟩ (box231 δ) δ ⊆ subBox231 δ`** (`Fin 9`): the conditioned box for `(2,3,1)` sits
inside `subBox231`. Lets the containment/injectivity reuse the banked `subBox231_*` facts directly (only
the forward inclusion is needed: field A composes via `subBox231_subset_preimage`, injectivity via
`R231_injOn`'s `.mono`). -/
theorem condBox231_subset_subBox231 (δ : ℝ) :
    condBox (⟨6, by decide⟩ : Fin 9) (box231 δ) δ ⊆ subBox231 δ := by
  rintro u ⟨hpiv, hrest⟩
  simp only [box231] at hrest
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, hpiv, ?_, ?_⟩
  · have := hrest 0 (by decide); rwa [if_pos (Or.inl rfl)] at this
  · have := hrest 1 (by decide); rwa [if_neg (by decide)] at this
  · have := hrest 2 (by decide); rwa [if_neg (by decide)] at this
  · have := hrest 3 (by decide); rwa [if_neg (by decide)] at this
  · have := hrest 4 (by decide); rwa [if_pos (Or.inr rfl)] at this
  · have := hrest 5 (by decide); rwa [if_neg (by decide)] at this
  · have := hrest 7 (by decide); rwa [if_neg (by decide)] at this
  · have := hrest 8 (by decide); rwa [if_neg (by decide)] at this

/-- The `(2,3,1)` peeled unit `Uy y = Uval231 (insertNth ⟨6,_⟩ 0 y)` (the `z`-free polynomial). -/
noncomputable def Uy231 (y : Fin 8 → ℝ) : ℝ := Uval231 (Fin.insertNth (⟨6, by decide⟩ : Fin 9) (0:ℝ) y)

/-- `Uy231` is measurable. -/
theorem Uy231_measurable : Measurable Uy231 := by
  have : Uy231 = (fun y : Fin 8 → ℝ => Uval231 (Fin.insertNth (6 : Fin 9) (0:ℝ) y)) := by
    funext y; rw [Uy231, show ((⟨6, by decide⟩ : Fin 9)) = (6 : Fin 9) from rfl]
  rw [this]; exact Uval231_insertNth_6_measurable

/-- **The `(2,3,1)` conditioned-box L=2 headline (non-vacuity witness).** The conditioned-box assembly
`routeMCore_box_diverges_smearedL2` FIRES on the worked `(2,3,1)` chart: feeding `box231`/`psi231`/`R231`/
`D231` + the `subBox231`-conditioned facts reproduces the achiever box-divergence
`∫⁻_{cubeBox 9 ε} |routeMCore M231|^{−c'} = ⊤` for `c' ≥ ½·minAdm M231 = 1`. This witnesses the
conditioned hypothesis bundle is jointly satisfiable (NOT vacuous). -/
theorem routeM231sm_box_diverges_via_condBox (c' : NNReal)
    (hc' : (minAdm M231 : ℝ≥0∞) / 2 ≤ (c' : ℝ≥0∞)) (ε : ℝ) (hε : 0 < ε) :
    ∫⁻ x in cubeBox (routeMAmbient M231) ε,
      ENNReal.ofReal (|routeMCore M231 x| ^ (-(c' : ℝ))) = ⊤ := by
  -- `1 ≤ c'` from `minAdm M231 = 2` (mirrors `routeM231sm_box_diverges`)
  have hc'1 : (1:ℝ) ≤ (c' : ℝ) := by
    have hh : (minAdm M231 : ℝ≥0∞) / 2 = 1 := by
      rw [minAdm_M231, show ((2:ℕ):ℝ≥0∞) = 2 from by norm_num,
        ENNReal.div_self (by norm_num) (by norm_num)]
    rw [hh] at hc'
    rwa [show (1:ℝ≥0∞) = ((1:NNReal):ℝ≥0∞) by norm_num, ENNReal.coe_le_coe, ← NNReal.coe_le_coe,
      NNReal.coe_one] at hc'
  set δ : ℝ := min (ε/2) 1 with hδdef
  have hδ : 0 < δ := lt_min (by linarith) (by norm_num)
  have hδ1 : δ ≤ 1 := min_le_right _ _
  have h2δε : 2 * δ ≤ ε := by have : δ ≤ ε/2 := min_le_left _ _; linarith
  have hN : routeMAmbient M231 = 8 + 1 := rfl
  refine routeMCore_box_diverges_smearedL2 (M := M231) (n := 8) hN psi231 R231 D231
    (⟨6, by decide⟩ : Fin 9) (box231 δ) 1 (c' : ℝ) ε δ Uy231 hδ
    measurePreserving_psi231 measurableEmbedding_psi231 ?_ ?_ ?_ ?_ ?_ ?_ ?_ Uy231_measurable
    ?_ ?_ ?_
  · -- containment (field A): `condBox ⊆ subBox231`, then the banked containment
    show condBox (⟨6, by decide⟩ : Fin 9) (box231 δ) δ
      ⊆ (fun u => psi231 (R231 u)) ⁻¹' (cubeBox (routeMAmbient M231) ε)
    intro u hu
    rw [Set.mem_preimage, ← phi231sm_eq_psi_R]
    exact cubeBox_mono h2δε (subBox231_subset_preimage hδ hδ1 (condBox231_subset_subBox231 δ hu))
  · -- `R231` fderiv on the box
    exact fun u _ => R231_hasFDerivWithinAt _ u
  · -- `R231` injective on the box (`u 6 ∈ Ioo 0 δ`)
    show Set.InjOn R231 (condBox (⟨6, by decide⟩ : Fin 9) (box231 δ) δ)
    have hsub : condBox (⟨6, by decide⟩ : Fin 9) (box231 δ) δ ⊆ subBox231 δ \ {x | x 6 = 0} := by
      intro u hu
      refine ⟨condBox231_subset_subBox231 δ hu, ?_⟩
      obtain ⟨hpiv, _⟩ := hu
      simp only [Set.mem_setOf_eq]
      exact ne_of_gt (Set.mem_Ioo.mp hpiv).1
    exact (R231_injOn _).mono hsub
  · -- `|det (D231 u)| = |u 6|¹`
    exact fun u _ => D231_abs_det u
  · -- `box231 δ (succAbove k)` measurable
    exact fun k => measurableSet_box231 δ _
  · -- box231 δ (hN ▸ k) measurable (all coords)
    exact fun k => measurableSet_box231 δ _
  · -- the conditioned rest box has positive measure
    rw [volume_pi_pi]
    refine CanonicallyOrderedAdd.prod_pos.mpr (fun k _ => ?_)
    simp only [box231]
    split <;> · rw [Real.volume_Icc, ENNReal.ofReal_pos]; linarith
  · -- the exponent: `(1:ℝ) − 2c' ≤ −1` from `1 ≤ c'`
    push_cast; linarith
  · -- the PEELED RATE on the conditioned box: `routeMCore M231 (psi231 (R231 (insertNth 6 z y))) = z²·Uy y`
    intro z hz y hy
    have hmem := insertNth6_mem_subBox231 hz hy
    have hdet := subBox231_det_ne hδ hmem
    have h6eq : (⟨6, by decide⟩ : Fin 9) = (6 : Fin 9) := rfl
    -- collapse the `hN ▸` cast (`hN` is `rfl`), then the off-pole rate
    show routeMCore M231 (psi231 (R231 (Fin.insertNth (6 : Fin 9) z y))) = z ^ 2 * Uy231 y
    rw [← phi231sm_eq_psi_R, routeMCore_phi231sm_offpole _ (by rwa [h6eq] at hdet)]
    -- `u 6 = z`, `Uval231 u = Uy231 y` (z-free)
    rw [Uy231, h6eq, Uval231_insertNth_6 z y, Uval231_insertNth_6 0 y]
    simp only [Fin.insertNth_apply_same]
  · -- `U`-positivity on the conditioned box
    intro y hy
    rw [Uy231]
    -- `Uval231 (insertNth ⟨6,_⟩ 0 y) = Uval231 (insertNth ⟨6,_⟩ (δ/2) y)` (z-free), positive by membership
    have hmem : Fin.insertNth (⟨6, by decide⟩ : Fin 9) (δ/2) y ∈ subBox231 δ :=
      insertNth6_mem_subBox231 (Set.mem_Ioo.mpr ⟨by linarith, by linarith⟩) hy
    rw [show Uval231 (Fin.insertNth (⟨6, by decide⟩ : Fin 9) (0:ℝ) y)
        = Uval231 (Fin.insertNth (⟨6, by decide⟩ : Fin 9) (δ/2) y) from
      (Uval231_insertNth_6 0 y).trans (Uval231_insertNth_6 (δ/2) y).symm]
    exact subBox231_U_pos hδ hδ1 hmem

end DLNFibre.DLN.RLCT
