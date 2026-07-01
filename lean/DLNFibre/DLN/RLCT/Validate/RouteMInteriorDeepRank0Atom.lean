import DLNFibre.DLN.RLCT.Validate.RouteMInteriorDeepRank0
import DLNFibre.DLN.RLCT.Validate.RouteMInteriorDeepRank0AePos
import DLNFibre.DLN.RLCT.Validate.RouteMAchieverDispatch
import DLNFibre.DLN.RLCT.Validate.RouteMSmearedHSmearedL2

/-!
# `RouteMInteriorDeepRank0Atom` — the `deepRank = 0` box-divergence atom + the L=2 achiever wire

The DOWNSTREAM assembly of the `deepRank = 0` interior handler: the change-of-variables (cov), the
`NodeAchieverChart` bundle, the box-divergence atom `routeMCore_box_diverges_eDeepRank0`, and the L=2
achiever wire `routeMCore_box_diverges_achiever_L2`.

* The cov consumes the UNCONDITIONAL chart-Jacobian monomial `eDeepRank0_abs_det` (the pure single-axis
  `|u_p|^{minAdm−1}`, `|det DB| = 1` at `deepRank = 0`).
* The bundle wires `Ubound` from `eDeepRank0Unit_ae_pos` (`RouteMInteriorDeepRank0AePos`, item 6) +
  the compact-box bound (continuity), `Umeas` from measurability, `leaf_integrand` from the rate.
* The atom fires `routeMCore_box_diverges_of_nodeChart` at the threshold `½·minAdm`.
* The wire `routeMCore_box_diverges_achiever_L2` combines the `0 < deepRank` interior atom
  (`routeMCore_box_diverges_interiorLive`) + THIS `deepRank = 0` atom → `hInterior` on ALL
  `InteriorDrop M`, and feeds the spine (`routeMCore_box_diverges_achiever_spine`) with the banked
  smeared/clean side-conditions.

Axiom profile target: `routeMCore_box_diverges_achiever_L2` = `[propext, Classical.choice, Quot.sound,
monomial_rlct]` (the clean-three + the single S2 cited axiom).
-/

open MeasureTheory
open scoped ENNReal BigOperators

namespace DLNFibre.DLN.RLCT

variable {M : Fin (2 + 1) → ℕ}

/-! ## The deepRank = 0 change-of-variables + bundle + atom -/

/-- **The change-of-variables** — the cov engine `ldu_cov_of_differentiable_injOn` with `hdiff`
(`eDeepRank0_diff`), `habsdet` (`eDeepRank0_abs_det`, unconditional), `hinj` (`eDeepRank0_injOn`). -/
theorem eDeepRank0_cov (ha : StructAdm M (tach M)) (hdr0 : Text M (tach M) 2 = 0)
    (hr : 0 < Text M (tach M) 1 - Text M (tach M) 2) (hc : 0 < Wext M 1 - Text M (tach M) 2)
    (hp1 : Text M (tach M) (1 + 1) ≤ Text M (tach M) 1) (hp2 : Text M (tach M) (1 + 1) ≤ Wext M 1)
    (V : Set (Fin (routeMAmbient M) → ℝ)) (hV : MeasurableSet V)
    (g : (Fin (routeMAmbient M) → ℝ) → ℝ≥0∞) :
    ∫⁻ x in eDeepRank0Phi ha hr hc hp1 hp2 ''
        (V \ {x | x (eBlockPivot ha hr hc) = 0}), g x
      = ∫⁻ u in V \ {x | x (eBlockPivot ha hr hc) = 0},
          ENNReal.ofReal (∏ j, |u j| ^ (eDeepRank0_leafH ha hr hc j))
            * g (eDeepRank0Phi ha hr hc hp1 hp2 u) :=
  ldu_cov_of_differentiable_injOn (eDeepRank0Phi ha hr hc hp1 hp2)
    (eBlockPivot ha hr hc) (eDeepRank0_leafH ha hr hc)
    (Finset.univ : Finset (Fin (routeMAmbient M))) (eDeepRank0_diff ha hr hc hp1 hp2)
    (fun u => eDeepRank0_abs_det ha hdr0 hr hc hp1 hp2 u) (eDeepRank0_injOn ha hdr0 hr hc hp1 hp2)
    V hV g

/-- **The compact-box bound for `eDeepRank0Unit`** — continuity on `[0,δ]^N`. -/
theorem eDeepRank0Unit_le_on_box (ha : StructAdm M (tach M))
    (hr : 0 < Text M (tach M) 1 - Text M (tach M) 2) (hc : 0 < Wext M 1 - Text M (tach M) 2)
    (hp1 : Text M (tach M) (1 + 1) ≤ Text M (tach M) 1) (hp2 : Text M (tach M) (1 + 1) ≤ Wext M 1)
    (δ : ℝ) :
    ∃ B, 0 < B ∧ ∀ u ∈ Set.univ.pi (fun _ : Fin (routeMAmbient M) => Set.Icc (0 : ℝ) δ),
      eDeepRank0Unit ha hr hc hp1 hp2 u ≤ B := by
  have hcont : Continuous (eDeepRank0Unit ha hr hc hp1 hp2) := continuous_eDeepRank0Unit ha hr hc hp1 hp2
  have hcpt : IsCompact (Set.univ.pi (fun _ : Fin (routeMAmbient M) => Set.Icc (0 : ℝ) δ)) :=
    isCompact_univ_pi (fun _ => isCompact_Icc)
  rcases (Set.univ.pi (fun _ : Fin (routeMAmbient M) => Set.Icc (0 : ℝ) δ)).eq_empty_or_nonempty
    with he | hne
  · exact ⟨1, one_pos, fun u hu => absurd (he ▸ hu) (Set.mem_empty_iff_false u).mp⟩
  · obtain ⟨u0, _, hu0⟩ := hcpt.exists_isMaxOn hne hcont.continuousOn
    exact ⟨max 1 (eDeepRank0Unit ha hr hc hp1 hp2 u0), lt_of_lt_of_le one_pos (le_max_left _ _),
      fun u hu => le_trans (hu0 hu) (le_max_right _ _)⟩

/-- **The `NodeAchieverChart.Ubound` field** for the deepRank=0 chart — the box bound + the a.e.-pos
atom (`eDeepRank0Unit_ae_pos`). -/
theorem eDeepRank0_Ubound (ha : StructAdm M (tach M)) (hdr0 : Text M (tach M) 2 = 0)
    (hr : 0 < Text M (tach M) 1 - Text M (tach M) 2) (hc : 0 < Wext M 1 - Text M (tach M) 2)
    (hp1 : Text M (tach M) (1 + 1) ≤ Text M (tach M) 1) (hp2 : Text M (tach M) (1 + 1) ≤ Wext M 1)
    (hM2 : 0 < Wext M 2) :
    ∀ δ : ℝ, ∃ B : ℝ, 0 < B ∧
      (∀ u ∈ Set.univ.pi (fun _ : Fin (routeMAmbient M) => Set.Icc (0 : ℝ) δ),
        eDeepRank0Unit ha hr hc hp1 hp2 u ≤ B) ∧
      ∀ᵐ u ∂(volume.restrict
          (Set.univ.pi (fun _ : Fin (routeMAmbient M) => Set.Icc (0 : ℝ) δ))),
        0 < eDeepRank0Unit ha hr hc hp1 hp2 u := by
  intro δ
  obtain ⟨B, hB0, hBle⟩ := eDeepRank0Unit_le_on_box ha hr hc hp1 hp2 δ
  exact ⟨B, hB0, hBle, ae_restrict_of_ae (eDeepRank0Unit_ae_pos ha hdr0 hr hc hp1 hp2 hM2)⟩

/-- **The deepRank = 0 achiever chart bundle** — `eDeepRank0Phi` with binding pivot `eBlockPivot`, the
single-axis `eDeepRank0_leafH`, unit `eDeepRank0Unit`, and the analytic fields. -/
noncomputable def eDeepRank0NodeChart (ha : StructAdm M (tach M)) (hdr0 : Text M (tach M) 2 = 0)
    (hr : 0 < Text M (tach M) 1 - Text M (tach M) 2) (hc : 0 < Wext M 1 - Text M (tach M) 2)
    (hp1 : Text M (tach M) (1 + 1) ≤ Text M (tach M) 1) (hp2 : Text M (tach M) (1 + 1) ≤ Wext M 1)
    (hM2 : 0 < Wext M 2) (hpos : 1 ≤ minAdm M) :
    NodeAchieverChart M where
  hpos := hpos
  phi := eDeepRank0Phi ha hr hc hp1 hp2
  p := eBlockPivot ha hr hc
  leafH := eDeepRank0_leafH ha hr hc
  leafH_pivot := eDeepRank0_leafH_pivot ha hr hc
  Ufun := eDeepRank0Unit ha hr hc hp1 hp2
  Ubound := eDeepRank0_Ubound ha hdr0 hr hc hp1 hp2 hM2
  Umeas := measurable_eDeepRank0Unit ha hr hc hp1 hp2
  leaf_integrand := fun c =>
    Filter.Eventually.of_forall (fun x =>
      leaf_integrand_of_rate (eBlockPivot ha hr hc) (eDeepRank0_leafH ha hr hc)
        (fun y => routeMCore M (eDeepRank0Phi ha hr hc hp1 hp2 y)) (eDeepRank0Unit ha hr hc hp1 hp2)
        (fun y => routeMCore_eDeepRank0Phi ha hr hc hp1 hp2 y)
        (fun y => eDeepRank0Unit_nonneg ha hr hc hp1 hp2 y) c x)
  cov := eDeepRank0_cov ha hdr0 hr hc hp1 hp2
  image_subset := eDeepRank0_image ha hr hc hp1 hp2

/-- **The deepRank = 0 INTERIOR box-divergence atom** — `∫⁻_{cubeBox N ε} |routeMCore M|^{−c'} = ⊤`
for `c'` at-or-above `½·minAdm M`, every `ε > 0`, on the `deepRank = 0` interior stratum. Via the
M-agnostic `routeMCore_box_diverges_of_nodeChart`. -/
theorem routeMCore_box_diverges_eDeepRank0 (ha : StructAdm M (tach M)) (hdr0 : Text M (tach M) 2 = 0)
    (hr : 0 < Text M (tach M) 1 - Text M (tach M) 2) (hc : 0 < Wext M 1 - Text M (tach M) 2)
    (hp1 : Text M (tach M) (1 + 1) ≤ Text M (tach M) 1) (hp2 : Text M (tach M) (1 + 1) ≤ Wext M 1)
    (hM2 : 0 < Wext M 2) (hpos : 1 ≤ minAdm M)
    (c' : NNReal) (hc' : (minAdm M : ℝ≥0∞) / 2 ≤ (c' : ℝ≥0∞)) (ε : ℝ) (hε : 0 < ε) :
    ∫⁻ x in cubeBox (routeMAmbient M) ε,
      ENNReal.ofReal (|routeMCore M x| ^ (-(c' : ℝ))) = ⊤ :=
  routeMCore_box_diverges_of_nodeChart M
    (eDeepRank0NodeChart ha hdr0 hr hc hp1 hp2 hM2 hpos) c' hc' ε hε

/-! ## Item 9 — the L=2 achiever wire (`hInterior` on ALL `InteriorDrop`, then the spine) -/

/-- **The INTERIOR branch on ALL `InteriorDrop M` at L=2** — combines the `0 < deepRank` atom
(`routeMCore_box_diverges_interiorLive`) with the `deepRank = 0` atom
(`routeMCore_box_diverges_eDeepRank0`) by casing on `deepRank M = Text M (tach M) 2`. Both binding
axes carry `minAdm − 1`; the interior characterization (`interiorDrop_L2_iff`) supplies the widths. -/
theorem routeMCore_box_diverges_interior_L2 (M : Fin 3 → ℕ) (hpos : 1 ≤ minAdm M)
    (hInt : InteriorDrop M) (c' : NNReal) (hc' : (minAdm M : ℝ≥0∞) / 2 ≤ (c' : ℝ≥0∞))
    (ε : ℝ) (hε : 0 < ε) :
    ∫⁻ x in cubeBox (routeMAmbient M) ε,
      ENNReal.ofReal (|routeMCore M x| ^ (-(c' : ℝ))) = ⊤ := by
  have ha : StructAdm M (tach M) := structAdm_tach M (by norm_num)
  obtain ⟨hM2, hlt0, hlt1⟩ := (interiorDrop_L2_iff M).mp hInt
  -- `deepRank M = Text M (tach M) 2`; `Text 1 = M0`, `Wext 1 = M1`, `Wext 2 = M2`
  have hdeep : Text M (tach M) 2 = deepRank M := rfl
  have hText1 : Text M (tach M) 1 = M 0 := by
    rw [show (1 : ℕ) = 0 + 1 from rfl, Text_succ M (tach M) 0 (by omega)]
    exact tach_mk_zero M (by omega)
  have hWext1 : Wext M 1 = M 1 := Wext_apply M 1 (by omega)
  have hWext2 : Wext M 2 = M 2 := Wext_apply M 2 (by omega)
  by_cases hdr : Text M (tach M) 2 = 0
  · -- deepRank = 0: the E-radial atom
    have hr : 0 < Text M (tach M) 1 - Text M (tach M) 2 := by
      rw [hText1, hdr]; omega
    have hc : 0 < Wext M 1 - Text M (tach M) 2 := by
      rw [hWext1, hdr]; omega
    have hp1 : Text M (tach M) (1 + 1) ≤ Text M (tach M) 1 := by
      rw [show (1 : ℕ) + 1 = 2 from rfl, hdr]; exact Nat.zero_le _
    have hp2 : Text M (tach M) (1 + 1) ≤ Wext M 1 := by
      rw [show (1 : ℕ) + 1 = 2 from rfl, hdr]; exact Nat.zero_le _
    have hM2' : 0 < Wext M 2 := by rw [hWext2]; exact hM2
    exact routeMCore_box_diverges_eDeepRank0 ha hdr hr hc hp1 hp2 hM2' hpos c' hc' ε hε
  · -- 0 < deepRank: the LIVE-leaf ∘ kLDU interior atom
    have h0r : 0 < Text M (tach M) 2 := Nat.pos_of_ne_zero hdr
    have h0c : 0 < Wext M 2 := by rw [hWext2]; exact hM2
    exact routeMCore_box_diverges_interiorLive ha h0r h0c hpos hInt c' hc' ε hε

/-- **The L=2 achiever box-divergence** `routeMCore_box_diverges_achiever_L2` — the `M : Fin 3 → ℕ`
specialization of the achiever headline, discharged sorry-free by the `2 ≤ L` trichotomy
(`achiever_trichotomy_total`) done DIRECTLY at `L = 2` (not through the spine's flat `hNo`, which is
false on the interior/smeared branches): INTERIOR → `routeMCore_box_diverges_interior_L2` (combining the
`0<deepRank` + `deepRank=0` atoms); CLEAN → the banked `routeMCore_box_diverges_clean` with `hNo`
DERIVED in-branch from `hclean` (`boundaryClean_noInteriorBothDrop_L2`); SMEARED → the banked
`hSmeared_L2`. The clean side-conditions (`hMpos`, `hne`) come from `widths_pos_of_minAdm`. -/
theorem routeMCore_box_diverges_achiever_L2 (M : Fin 3 → ℕ) (hpos : 1 ≤ minAdm M)
    (c' : NNReal) (hc' : (minAdm M : ℝ≥0∞) / 2 ≤ (c' : ℝ≥0∞)) (ε : ℝ) (hε : 0 < ε) :
    ∫⁻ x in cubeBox (routeMAmbient M) ε,
      ENNReal.ofReal (|routeMCore M x| ^ (-(c' : ℝ))) = ⊤ := by
  obtain ⟨hM0, hM1, hM2⟩ := widths_pos_of_minAdm M hpos
  have hMpos : ∀ s, 0 < M s := fun s => by fin_cases s <;> assumption
  -- the deepest block is nonempty: `card = M1·M2 > 0`
  have hne : (deepestCoords M (by norm_num)).Nonempty := by
    rw [← Finset.card_pos, deepestCoords_card M (by norm_num),
      M_deepLayer_castSucc M (by norm_num), M_deepLayer_succ M (by norm_num)]
    have hrows : deepRows M = M 1 := by
      rw [deepRows]; exact (Wext_apply M (2 - 1) (by omega)).trans (by norm_num)
    have hlast : M (Fin.last 2) = M 2 := by congr 1
    rw [hrows, hlast]; exact Nat.mul_pos hM1 hM2
  rcases achiever_trichotomy_total (L := 2) M (le_refl 2) with hInt | hClean | hSmear
  · exact routeMCore_box_diverges_interior_L2 M hpos hInt c' hc' ε hε
  · -- CLEAN: `hNo` derived from `hClean.2` (`deepRank = deepRows`)
    exact routeMCore_box_diverges_clean (L := 2) M (by norm_num) hne
      (boundaryClean_noInteriorBothDrop_L2 M hClean.2) hClean.2 hpos hMpos c' hc' ε hε
  · exact hSmeared_L2_apply M hpos c' hc' ε hε hSmear

end DLNFibre.DLN.RLCT
