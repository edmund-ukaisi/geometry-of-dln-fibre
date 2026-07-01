import DLNFibre.DLN.RLCT.Validate.RouteMInteriorLiveGenHmap
import DLNFibre.DLN.RLCT.Validate.RouteMInteriorLiveAnalytic
import DLNFibre.DLN.RLCT.Validate.RouteMUPolyLive

/-!
# `RouteMInteriorLiveGenAnalytic` — the general-`L` ANALYTIC LEAF facts for the LIVE-leaf ∘ kLDU chart

The general-`L` lift (`genm-glift`, task (b)) of the `Fin (2 + 1)`-pinned analytic atoms in
`RouteMInteriorLiveAnalytic` (`ldu_image`/`ldu_Umeas`/`ldu_Ubound`/`ldu_Uval_le_on_box`) +
`RouteMUPolyLive` (`interiorLiveUnit_ae_pos` via `UPolyLive`), stated at arbitrary depth `L` for the
`NodeAchieverChart` bundle's analytic fields.

Consumes (banked, sorry-free): the ∀L chart layer `RouteMInteriorLiveGenChart` (`interiorLivePhiGen`,
`interiorLiveUnitGen`, `interiorLiveUnitGen_nonneg`, `kLDU_leafPivotGen`), the ∀L differentiability
`interiorLive_diffGen` + `differentiable_kLDUGen` (`RouteMInteriorLiveGenHmap`), the ∀L continuity infra
`GenBlkContinuous`/`continuous_Cgen`/`continuous_Agen`/`continuous_toChain_A/B/E`/`continuous_bmatStack`/
`continuous_rmatPad` + the ∀L `chartParamsGen_live_zero` (`RouteMInteriorLiveAnalytic`), and the ∀L
LDU-lens poly engine `kLDUGen`/`kLDUGen_eval`/`genBlkFlatLiveGen`/`rfinFixedPivotGen`/`sqSumHmat0_map`/
`genBlkFlatLiveGen_genBlkMap_of`/`kLens_one` + the ∀L witness machinery `wInt`/`InteriorDrop`/
`Hmat_pivot`/`Hmat_row_thread`/`suffix_carrier`/`genBlk_*`/`readK_wInt` (`RouteMUPolyLive` +
`RouteMAchieverWitnessInterior`). `cubeBox`/`cubeBox_subset_of_isOpen` are generic.

The co-import of the ∀L chart side (`…GenHmap → …GenChart → …GenPbo`) and the `Fin (2 + 1)`-side
(`…Analytic`/`…UPolyLive → …Contract`) is clash-free after the `readK_pbo_all → readK_pbo_allGen`
rename on the ∀L side (`RouteMInteriorLiveGenPbo`, base `45124eda`); the `Fin (2 + 1)`-side keeps the
incumbent `readK_pbo_all`, and no other name is shared.

Deliverables (the four (b) analytic facts):
* `continuous_Hmat0_gen` — the ∀L continuity of the chain's telescoped quotient `Hmat 0` in `x` (the
  depth-generic lift of the depth-2-hardcoded `continuous_Hmat0_L2`, by downward induction on `L − s`).
  The one genuinely-new engine piece here.
* `genBlkContinuous_liveGen` / `continuous_interiorLiveUnitGen` — the ∀L unit is continuous.
* `ldu_imageGen` (1) — small-box image containment.
* `ldu_UmeasGen` (2) — `interiorLiveUnitGen` is measurable.
* `ldu_UboundGen` (3) — box bound + a.e.-positivity, given `hpos`.
* `interiorLiveUnit_ae_posGen` (4) — a.e.-positivity of the unit, given `InteriorDrop M` (the VERIFY-FIRST
  nonvanishing: `UPolyLiveGen ≠ 0`, the surviving `Hmat 0 = 1` entry at the interior-drop witness — the
  ∀L witness machinery, `Rfin`/scalar-`u`-blind, so nonzero for any interior-drop config at any depth).

Axiom-clean `[propext, Classical.choice, Quot.sound]` (continuity + the banked matrix/poly engine + the
elementary polynomial-nullity `MvPolynomial.ae_eval_ne_zero`).
-/

open MeasureTheory
open scoped ENNReal BigOperators
open MvPolynomial Matrix

namespace DLNFibre.DLN.RLCT

variable {L : ℕ}

/-! ## General-`L` continuity of the chain's telescoped quotient `Hmat 0`

The depth-generic lift of the depth-2-hardcoded `continuous_Hmat0_L2`, by downward induction on the
remaining length `d = L − s`, reusing the banked ∀L `continuous_toChain_A/B/E` + `suffix_last`/
`suffix_succ`/`Hmat_last`/`Hmat_succ`. The `Chain` widths `Wwid = Wext M'`, `Twid = Text M' t` are
`x`-INDEPENDENT (`chainOfMt_Wwid` is `rfl`), so the codomain types of `suffix s`/`Hmat s` are fixed
constants and the induction runs without cast friction. -/

section ContHmat

variable {X : Type*} [TopologicalSpace X]

/-- **`suffix s` is continuous in `x`** at general `L`. -/
theorem continuous_suffix_gen {M' t : Fin (L + 1) → ℕ} {B : X → GenBlk M' t}
    (hB : GenBlkContinuous M' t B) {g : X → ℝ} (hg : Continuous g)
    (hle : ∀ k, k < L → Text M' t (k + 1) ≤ Wext M' k) (d : ℕ) :
    ∀ (s : ℕ) (hsd : s + d = L),
      Continuous (fun x => (show Matrix (Fin (Wext M' s)) (Fin (Wext M' L)) ℝ
        from (chainOfMt (g x) M' t (B x) hle).toChain.suffix s (by omega))) := by
  induction d with
  | zero =>
    intro s hsd
    have hsL : s = L := by omega
    subst hsL
    refine Continuous.congr (continuous_const
      (y := (1 : Matrix (Fin (Wext M' s)) (Fin (Wext M' s)) ℝ))) (fun x => ?_)
    exact ((chainOfMt (g x) M' t (B x) hle).toChain.suffix_last).symm
  | succ e ih =>
    intro s hsd
    have hslt : s < L := by omega
    have hstep := ih (s + 1) (by omega)
    refine Continuous.congr (Continuous.matrix_mul (n := Fin (Wext M' (s + 1)))
      (continuous_toChain_A hB hg hle s) hstep) (fun x => ?_)
    exact ((chainOfMt (g x) M' t (B x) hle).toChain.suffix_succ s hslt).symm

/-- **`Hmat s` is continuous in `x`** at general `L`. -/
theorem continuous_Hmat_gen {M' t : Fin (L + 1) → ℕ} {B : X → GenBlk M' t}
    (hB : GenBlkContinuous M' t B) {g : X → ℝ} (hg : Continuous g)
    (hle : ∀ k, k < L → Text M' t (k + 1) ≤ Wext M' k) (d : ℕ) :
    ∀ (s : ℕ) (hsd : s + d = L),
      Continuous (fun x => (show Matrix (Fin (Text M' t s)) (Fin (Wext M' L)) ℝ
        from (chainOfMt (g x) M' t (B x) hle).toChain.Hmat s (by omega))) := by
  induction d with
  | zero =>
    intro s hsd
    have hsL : s = L := by omega
    subst hsL
    refine Continuous.congr (hB.hRfin s) (fun x => ?_)
    exact ((chainOfMt (g x) M' t (B x) hle).toChain.Hmat_last).symm
  | succ e ih =>
    intro s hsd
    have hslt : s < L := by omega
    have hstep := ih (s + 1) (by omega)
    have hsuf := continuous_suffix_gen hB hg hle e (s + 1) (by omega)
    refine Continuous.congr (Continuous.add
      (Continuous.matrix_mul (n := Fin (Text M' t (s + 1)))
        (continuous_toChain_B hB hle s) hstep)
      (Continuous.matrix_mul (n := Fin (Wext M' (s + 1)))
        (continuous_toChain_E hB hg hle s) hsuf)) (fun x => ?_)
    exact ((chainOfMt (g x) M' t (B x) hle).toChain.Hmat_succ s hslt).symm

/-- **`Hmat 0` of the ∀L chain is continuous in `x`** — the `s = 0` instance of `continuous_Hmat_gen`. -/
theorem continuous_Hmat0_gen {M' t : Fin (L + 1) → ℕ} {B : X → GenBlk M' t}
    (hB : GenBlkContinuous M' t B) {g : X → ℝ} (hg : Continuous g)
    (hle : ∀ k, k < L → Text M' t (k + 1) ≤ Wext M' k) :
    Continuous (fun x => (show Matrix (Fin (Text M' t 0)) (Fin (Wext M' L)) ℝ
      from (chainOfMt (g x) M' t (B x) hle).toChain.Hmat 0 (Nat.zero_le L))) :=
  continuous_Hmat_gen hB hg hle L 0 (by omega)

end ContHmat

/-! ## `interiorLivePhiGen 0 = 0` (the deepest point) -/

/-- **`kLDU` fixes `0`** at general `L` (the ∀L lift of `kLDU_zero`). `kLens 0 = 0` (the diagonal pivots
vanish), the pass-through arms send `0` to `0`. -/
theorem kLDU_zeroGen (M : Fin (L + 1) → ℕ) (ha : StructAdm M (tach M)) :
    kLDU M (tach M) ha 0 = 0 := by
  funext q
  unfold kLDU
  split
  · rename_i k s heq
    split
    · rename_i qK hfeq
      show kLens (Matrix.of (readK M (tach M) ha 0 k)) _ _ = (0 : Fin (routeMAmbient M) → ℝ) q
      have h0 : Matrix.of (readK M (tach M) ha (0 : Fin (routeMAmbient M) → ℝ) k) = 0 := by
        funext i j; simp only [Matrix.of_apply, readK, Pi.zero_apply, Matrix.zero_apply]
      rw [h0]
      have hk0 : kLens (0 : Matrix (Fin (Text M (tach M) (k.val + 2)))
          (Fin (Text M (tach M) (k.val + 2))) ℝ) = 0 := by
        rw [kLens_eq]; simp
      rw [hk0]; simp
    · rfl
  · rfl

/-- **`interiorLivePhiGen` maps `0` to `0`** at general `L` — `kLDU 0 = 0`, the radial scalar `0` is
`0`, and `chartParamsGen 0 (zero-reader live decoder) = 0` (banked `chartParamsGen_live_zero`). -/
theorem interiorLivePhiGen_zero (M : Fin (L + 1) → ℕ) (ha : StructAdm M (tach M)) (hL : 0 < L)
    (h0r : 0 < Text M (tach M) L) (h0c : 0 < Wext M L) :
    interiorLivePhiGen M ha hL h0r h0c 0 = 0 := by
  rw [interiorLivePhiGen, kLDU_zeroGen M ha, phiFlatLiveAt]
  simp only [Pi.zero_apply]
  rw [phiGen]
  rw [chartParamsGen_live_zero M (tach M) ha (rfinFixedPivot M ha hL 0)]
  exact paramsEquivFlat_deepest M

/-! ## (1) `ldu_imageGen` — image containment (`NodeAchieverChart.image_subset`) -/

/-- **`ldu_imageGen`** (1) — a small source box `[0,δ]^N` maps into `cubeBox N ε` (continuity of
`interiorLivePhiGen` via `interiorLive_diffGen` + `interiorLivePhiGen 0 = 0`). -/
theorem ldu_imageGen (M : Fin (L + 1) → ℕ) (ha : StructAdm M (tach M)) (hL : 0 < L)
    (h0r : 0 < Text M (tach M) L) (h0c : 0 < Wext M L) :
    ∀ ε : ℝ, 0 < ε →
      ∃ δ > 0, interiorLivePhiGen M ha hL h0r h0c ''
        (Set.univ.pi (fun _ : Fin (routeMAmbient M) => Set.Icc (0 : ℝ) δ))
        ⊆ cubeBox (routeMAmbient M) ε := by
  intro ε hε
  have hcont : Continuous (interiorLivePhiGen M ha hL h0r h0c) :=
    (interiorLive_diffGen M ha hL h0r h0c).continuous
  have hopen : IsOpen (Set.univ.pi (fun _ : Fin (routeMAmbient M) => Set.Ioo (-ε) ε)) :=
    isOpen_set_pi Set.finite_univ (fun _ _ => isOpen_Ioo)
  have hmem : (0 : Fin (routeMAmbient M) → ℝ)
      ∈ interiorLivePhiGen M ha hL h0r h0c ⁻¹'
        (Set.univ.pi (fun _ : Fin (routeMAmbient M) => Set.Ioo (-ε) ε)) := by
    simp only [Set.mem_preimage, interiorLivePhiGen_zero M ha hL h0r h0c, Set.mem_pi, Set.mem_univ,
      true_implies, Set.mem_Ioo, Pi.zero_apply]
    exact fun i => ⟨by linarith, hε⟩
  obtain ⟨δ, hδ, hsub⟩ := cubeBox_subset_of_isOpen (hopen.preimage hcont) hmem
  refine ⟨δ, hδ, ?_⟩
  rintro y ⟨x, hx, rfl⟩
  have hxcube : x ∈ cubeBox (routeMAmbient M) δ := by
    simp only [cubeBox, Set.mem_pi, Set.mem_univ, true_implies, Set.mem_Icc] at hx ⊢
    intro i; exact ⟨le_trans (by linarith [hδ]) (hx i).1, (hx i).2⟩
  have hxmem : interiorLivePhiGen M ha hL h0r h0c x
      ∈ Set.univ.pi (fun _ : Fin (routeMAmbient M) => Set.Ioo (-ε) ε) :=
    Set.mem_preimage.mp (hsub hxcube)
  simp only [cubeBox, Set.mem_pi, Set.mem_univ, true_implies, Set.mem_Icc]
  intro i
  have hi := (Set.mem_pi.mp hxmem) i (Set.mem_univ i)
  rw [Set.mem_Ioo] at hi
  exact ⟨hi.1.le, hi.2.le⟩

/-! ## Continuity of `interiorLiveUnitGen` (the ∀L chain threaded through `x`) -/

/-- **The ∀L live decoder** `genBlkFlatLive … (rfinFixedPivot (kLDU x)) (kLDU x)` is block-continuous
in `x` (the ∀L lift of `genBlkContinuous_live`). -/
theorem genBlkContinuous_liveGen (M : Fin (L + 1) → ℕ) (ha : StructAdm M (tach M)) (hL : 0 < L)
    (h0r : 0 < Text M (tach M) L) (h0c : 0 < Wext M L) :
    GenBlkContinuous M (tach M)
      (fun x => genBlkFlatLive M (tach M) ha
        (rfinFixedPivot M ha hL (kLDU M (tach M) ha x)) (kLDU M (tach M) ha x)) := by
  have hkcont : Continuous (kLDU M (tach M) ha) := (differentiable_kLDUGen M (tach M) ha).continuous
  have hkapp : ∀ q, Continuous (fun x : Fin (routeMAmbient M) → ℝ => kLDU M (tach M) ha x q) :=
    fun q => (continuous_apply q).comp hkcont
  have hreadK : ∀ k : Fin L, Continuous (fun x => readK M (tach M) ha (kLDU M (tach M) ha x) k) :=
    fun k => continuous_matrix (fun i j => hkapp _)
  have hreadX : ∀ k : Fin L, Continuous (fun x => readX M (tach M) ha (kLDU M (tach M) ha x) k) :=
    fun k => continuous_matrix (fun i j => hkapp _)
  have hreadN : ∀ k : Fin L, Continuous (fun x => readN M (tach M) ha (kLDU M (tach M) ha x) k) :=
    fun k => continuous_matrix (fun i j => hkapp _)
  have hreadE : ∀ k : Fin L, Continuous (fun x => readE M (tach M) ha (kLDU M (tach M) ha x) k) :=
    fun k => continuous_matrix (fun i j => hkapp _)
  have hreadW : ∀ (k : Fin L) (hk : k.val + 1 < L),
      Continuous (fun x => readW M (tach M) ha (kLDU M (tach M) ha x) k hk) :=
    fun k hk => continuous_matrix (fun i j => hkapp _)
  refine ⟨fun k => ?_, fun k => ?_, fun k => ?_, fun k => ?_, fun k => ?_⟩
  · -- Bmat
    show Continuous (fun x => (genBlkFlatStruct M (tach M) ha (kLDU M (tach M) ha x)).Bmat k)
    match k with
    | 0 => exact continuous_const
    | (j + 1) =>
      simp only [genBlkFlatStruct]
      by_cases hj : j < L
      · simp only [dif_pos hj]
        exact continuous_bmatStack (j + 1) (ha.hdesc j hj) (hreadK ⟨j, hj⟩) (hreadX ⟨j, hj⟩)
      · simp only [dif_neg hj]; exact continuous_const
  · -- Nblk
    show Continuous (fun x => (genBlkFlatStruct M (tach M) ha (kLDU M (tach M) ha x)).Nblk k)
    match k with
    | 0 => exact continuous_const
    | (j + 1) =>
      simp only [genBlkFlatStruct]
      by_cases hj : j < L
      · simp only [dif_pos hj]; exact hreadN ⟨j, hj⟩
      · simp only [dif_neg hj]; exact continuous_const
  · -- Wblk
    show Continuous (fun x => (genBlkFlatStruct M (tach M) ha (kLDU M (tach M) ha x)).Wblk k)
    match k with
    | 0 => exact continuous_const
    | (j + 1) =>
      simp only [genBlkFlatStruct]
      by_cases hj : j < L
      · simp only [dif_pos hj]
        by_cases hj2 : j + 1 < L
        · simp only [dif_pos hj2]; exact hreadW ⟨j, hj⟩ hj2
        · simp only [dif_neg hj2]; exact continuous_const
      · simp only [dif_neg hj]; exact continuous_const
  · -- Rmat
    show Continuous (fun x => (genBlkFlatStruct M (tach M) ha (kLDU M (tach M) ha x)).Rmat k)
    match k with
    | 0 => exact continuous_const
    | (j + 1) =>
      simp only [genBlkFlatStruct]
      by_cases hj : j < L
      · simp only [dif_pos hj]
        exact continuous_rmatPad (j + 1) (ha.hdesc j hj) (ha.hub j) (hreadE ⟨j, hj⟩)
      · simp only [dif_neg hj]; exact continuous_const
  · -- Rfin = rfinFixedPivot ∘ kLDU
    by_cases hk : k = L
    · subst hk
      have hrw : (fun x => (genBlkFlatLive M (tach M) ha
            (rfinFixedPivot M ha hL (kLDU M (tach M) ha x)) (kLDU M (tach M) ha x)).Rfin k)
          = fun x => rfinFixedPivot M ha hL (kLDU M (tach M) ha x) := by
        funext x; simp only [genBlkFlatLive, dif_pos]
      rw [hrw]
      refine continuous_matrix (fun i j => ?_)
      show Continuous (fun x => if i.val = 0 ∧ j.val = 0 then (1 : ℝ)
        else kLDU M (tach M) ha x (leafSlot M (tach M) ha hL i j))
      by_cases hij : i.val = 0 ∧ j.val = 0
      · simp only [if_pos hij]; exact continuous_const
      · simp only [if_neg hij]; exact hkapp _
    · have hrw : (fun x => (genBlkFlatLive M (tach M) ha
            (rfinFixedPivot M ha hL (kLDU M (tach M) ha x)) (kLDU M (tach M) ha x)).Rfin k)
          = fun _ => 0 := by
        funext x; simp only [genBlkFlatLive, dif_neg hk]
      rw [hrw]; exact continuous_const

/-- **`interiorLiveUnitGen` is continuous** at general `L` — `= sqSumHmat0` of the chain
(`VvalGen_eq_sqSumHmat0`), continuous via `continuous_Hmat0_gen` + `genBlkContinuous_liveGen`. -/
theorem continuous_interiorLiveUnitGen (M : Fin (L + 1) → ℕ) (ha : StructAdm M (tach M)) (hL : 0 < L)
    (h0r : 0 < Text M (tach M) L) (h0c : 0 < Wext M L) :
    Continuous (interiorLiveUnitGen M ha hL h0r h0c) := by
  have hg : Continuous (fun x : Fin (routeMAmbient M) → ℝ => x (leafPivot M ha hL h0r h0c)) :=
    continuous_apply _
  have hHmat0 := continuous_Hmat0_gen (genBlkContinuous_liveGen M ha hL h0r h0c) hg
    (hleStruct M (tach M) ha)
  have hsq : Continuous (fun x => ∑ i, ∑ j,
      ((show Matrix (Fin (Text M (tach M) 0)) (Fin (Wext M L)) ℝ
          from (chainOfMt (x (leafPivot M ha hL h0r h0c)) M (tach M)
            (genBlkFlatLive M (tach M) ha (rfinFixedPivot M ha hL (kLDU M (tach M) ha x))
              (kLDU M (tach M) ha x)) (hleStruct M (tach M) ha)).toChain.Hmat 0 (Nat.zero_le L))
        i j) ^ 2) :=
    continuous_finset_sum _ (fun i _ => continuous_finset_sum _ (fun j _ =>
      (hHmat0.matrix_elem i j).pow 2))
  refine hsq.congr (fun x => ?_)
  rw [interiorLiveUnitGen, VvalGen_eq_sqSumHmat0, sqSumHmat0]
  rfl

/-! ## (2) `ldu_UmeasGen` — measurability of the lensed unit -/

/-- **`ldu_UmeasGen`** (2) — the ∀L lensed unit is measurable (continuity ⟹ measurable). -/
theorem ldu_UmeasGen (M : Fin (L + 1) → ℕ) (ha : StructAdm M (tach M)) (hL : 0 < L)
    (h0r : 0 < Text M (tach M) L) (h0c : 0 < Wext M L) :
    Measurable (interiorLiveUnitGen M ha hL h0r h0c) :=
  (continuous_interiorLiveUnitGen M ha hL h0r h0c).measurable

/-! ## (3) `ldu_UboundGen` — box bound + a.e.-positivity -/

/-- **The box bound** `interiorLiveUnitGen ≤ B` on `[0,δ]^N` (continuity on a compact box). -/
theorem ldu_Uval_le_on_boxGen (M : Fin (L + 1) → ℕ) (ha : StructAdm M (tach M)) (hL : 0 < L)
    (h0r : 0 < Text M (tach M) L) (h0c : 0 < Wext M L) (δ : ℝ) :
    ∃ B, 0 < B ∧ ∀ u ∈ Set.univ.pi (fun _ : Fin (routeMAmbient M) => Set.Icc (0 : ℝ) δ),
      interiorLiveUnitGen M ha hL h0r h0c u ≤ B := by
  have hcont : Continuous (interiorLiveUnitGen M ha hL h0r h0c) :=
    continuous_interiorLiveUnitGen M ha hL h0r h0c
  have hcpt : IsCompact (Set.univ.pi (fun _ : Fin (routeMAmbient M) => Set.Icc (0 : ℝ) δ)) :=
    isCompact_univ_pi (fun _ => isCompact_Icc)
  rcases (Set.univ.pi (fun _ : Fin (routeMAmbient M) => Set.Icc (0 : ℝ) δ)).eq_empty_or_nonempty
    with he | hne
  · exact ⟨1, one_pos, fun u hu => absurd (he ▸ hu) (Set.mem_empty_iff_false u).mp⟩
  · obtain ⟨u0, _, hu0⟩ := hcpt.exists_isMaxOn hne hcont.continuousOn
    exact ⟨max 1 (interiorLiveUnitGen M ha hL h0r h0c u0),
      lt_of_lt_of_le one_pos (le_max_left _ _),
      fun u hu => le_trans (hu0 hu) (le_max_right _ _)⟩

/-- **`ldu_UboundGen`** (3) — the full `NodeAchieverChart.Ubound` field, CONSUMING the a.e.-positivity
hypothesis `hpos`. The box bound is proven here (`ldu_Uval_le_on_boxGen`); the positivity conjunct is
restricted to the box (`ae_restrict_of_ae hpos`). -/
theorem ldu_UboundGen (M : Fin (L + 1) → ℕ) (ha : StructAdm M (tach M)) (hL : 0 < L)
    (h0r : 0 < Text M (tach M) L) (h0c : 0 < Wext M L)
    (hpos : ∀ᵐ u, 0 < interiorLiveUnitGen M ha hL h0r h0c u) :
    ∀ δ : ℝ, ∃ B : ℝ, 0 < B ∧
      (∀ u ∈ Set.univ.pi (fun _ : Fin (routeMAmbient M) => Set.Icc (0 : ℝ) δ),
        interiorLiveUnitGen M ha hL h0r h0c u ≤ B) ∧
      ∀ᵐ u ∂(volume.restrict
          (Set.univ.pi (fun _ : Fin (routeMAmbient M) => Set.Icc (0 : ℝ) δ))),
        0 < interiorLiveUnitGen M ha hL h0r h0c u := by
  intro δ
  obtain ⟨B, hB0, hBle⟩ := ldu_Uval_le_on_boxGen M ha hL h0r h0c δ
  exact ⟨B, hB0, hBle, ae_restrict_of_ae hpos⟩

/-! ## (4) `interiorLiveUnit_ae_posGen` — a.e.-positivity via the ∀L nonzero polynomial `UPolyLiveGen`

The VERIFY-FIRST risky one. The unit is `sqSumHmat0` of the ℝ live decoder chain; the POLYNOMIAL
`UPolyLiveGen` is `sqSumHmat0` of the poly live decoder chain (over `kLDUGen (Xvec)`). `eval u` pushes
through (`chainOfMt_map` + `genBlkFlatLiveGen_genBlkMap_of` glued from `kLDUGen_eval` +
`rfinFixedPivotGen_map` + `sqSumHmat0_map`). NONVANISHING: at the interior-drop witness `wInt p` the
K-blocks read the identity (`kLDU` fixes `wInt`, via `readK_wInt` + `kLens_one`), and the surviving
`Hmat 0 = 1` entry is built by the ∀L witness machinery (`Hmat_pivot`/`Hmat_row_thread`/`suffix_carrier`
+ the `genBlk_*` lemmas) — all ALREADY at general `L`. -/

/-- The ∀L poly pivot scalar `Xvec (kLDUGen-read) leafPivot` reduces (via `kLDUGen_eval` +
`kLDU_leafPivotGen`) to `eval u ↦ u leafPivot`. -/
theorem eval_kLDUGen_leafPivotGen (M : Fin (L + 1) → ℕ) (ha : StructAdm M (tach M)) (hL : 0 < L)
    (h0r : 0 < Text M (tach M) L) (h0c : 0 < Wext M L) (u : Fin (routeMAmbient M) → ℝ) :
    MvPolynomial.eval u (kLDUGen M (tach M) ha (Xvec (routeMAmbient M))
        (leafPivot M ha hL h0r h0c))
      = u (leafPivot M ha hL h0r h0c) := by
  rw [kLDUGen_eval M (tach M) ha u (leafPivot M ha hL h0r h0c),
    kLDU_leafPivotGen M ha hL h0r h0c u]

/-- **The named nonzero polynomial `UPolyLiveGen`** at general `L` — `sqSumHmat0` of the POLYNOMIAL live
decoder chain (decoder over `kLDUGen (Xvec)`, leaf `rfinFixedPivotGen (kLDUGen (Xvec))`, pivot
`Xvec (kLDUGen) leafPivot`). `eval u UPolyLiveGen = interiorLiveUnitGen u`. -/
noncomputable def UPolyLiveGen (M : Fin (L + 1) → ℕ) (ha : StructAdm M (tach M)) (hL : 0 < L)
    (h0r : 0 < Text M (tach M) L) (h0c : 0 < Wext M L) :
    MvPolynomial (Fin (routeMAmbient M)) ℝ :=
  sqSumHmat0 (chainOfMt
    (kLDUGen M (tach M) ha (Xvec (routeMAmbient M)) (leafPivot M ha hL h0r h0c))
    M (tach M)
    (genBlkFlatLiveGen M (tach M) ha
      (rfinFixedPivotGen M ha hL
        (kLDUGen M (tach M) ha (Xvec (routeMAmbient M))))
      (kLDUGen M (tach M) ha (Xvec (routeMAmbient M))))
    (hleStruct M (tach M) ha)).toChain

/-- **`eval u UPolyLiveGen = interiorLiveUnitGen u`** at general `L`. `eval u` pushes through `∑∑·²`, and
the chain naturality (`chainOfMt_map` + the live `GenBlkMap` glued from `kLDUGen_eval` +
`rfinFixedPivotGen_map`) identifies the evaluated poly chain's `Hmat 0` with the ℝ live decoder chain's;
the ℝ side is `interiorLiveUnitGen` by `VvalGen_eq_sqSumHmat0`. -/
theorem eval_UPolyLiveGen (M : Fin (L + 1) → ℕ) (ha : StructAdm M (tach M)) (hL : 0 < L)
    (h0r : 0 < Text M (tach M) L) (h0c : 0 < Wext M L) (u : Fin (routeMAmbient M) → ℝ) :
    MvPolynomial.eval u (UPolyLiveGen M ha hL h0r h0c) = interiorLiveUnitGen M ha hL h0r h0c u := by
  have hmap : GenBlkMap M (tach M)
      (genBlkFlatLiveGen M (tach M) ha
        (rfinFixedPivotGen M ha hL (kLDUGen M (tach M) ha (Xvec (routeMAmbient M))))
        (kLDUGen M (tach M) ha (Xvec (routeMAmbient M))))
      (genBlkFlatLive M (tach M) ha
        (rfinFixedPivot M ha hL (kLDU M (tach M) ha u))
        (kLDU M (tach M) ha u))
      (MvPolynomial.eval u) := by
    have h := genBlkFlatLiveGen_genBlkMap_of M (tach M) ha
      (kLDUGen M (tach M) ha (Xvec (routeMAmbient M))) (kLDU M (tach M) ha u)
      (MvPolynomial.eval u) (kLDUGen_eval M (tach M) ha u)
      (rfinFixedPivotGen M ha hL (kLDUGen M (tach M) ha (Xvec (routeMAmbient M))))
      (rfinFixedPivot M ha hL (kLDU M (tach M) ha u))
      (by
        rw [← rfinFixedPivotGen_eq M ha hL (kLDU M (tach M) ha u)]
        exact rfinFixedPivotGen_map M ha hL
          (kLDUGen M (tach M) ha (Xvec (routeMAmbient M))) (kLDU M (tach M) ha u)
          (MvPolynomial.eval u) (kLDUGen_eval M (tach M) ha u))
    rw [← genBlkFlatLiveGen_eq_live]; exact h
  have hchain := chainOfMt_map hmap
    (kLDUGen M (tach M) ha (Xvec (routeMAmbient M)) (leafPivot M ha hL h0r h0c))
    (hleStruct M (tach M) ha)
  rw [interiorLiveUnitGen, VvalGen_eq_sqSumHmat0, UPolyLiveGen,
    sqSumHmat0_map _ (MvPolynomial.eval u),
    hchain, eval_kLDUGen_leafPivotGen M ha hL h0r h0c u]

/-- **`kLDU` fixes the interior-drop witness** `kLDU (wInt p) = wInt p` at general `L`. On K-slots
`kLDU` reads `kLens (readK (wInt) k)`; `readK (wInt) k = I` (`readK_wInt`) and `kLens 1 = 1`
(`kLens_one`), so the K-slot is unchanged; off K, `kLDU` is identity. -/
theorem kLDU_wIntGen (M : Fin (L + 1) → ℕ) (ha : StructAdm M (tach M)) (p : ℕ) :
    kLDU M (tach M) ha (wInt M ha p) = wInt M ha p := by
  funext q
  rcases hq : chartIdxEquiv M (tDesc M (tach M)) ha.h0 ha.hc ha.hL q with ⟨k, s⟩
  cases s with
  | inl sfr =>
    rcases hframe : frameSplitEquiv M (tach M) (k.val + 1) (ha.hdesc k.val k.isLt) (ha.hub k.val) sfr
      with (((qK | qX) | qN) | qE)
    · have hK1 : Matrix.of (readK M (tach M) ha (wInt M ha p) k)
          = (1 : Matrix (Fin (Text M (tach M) (k.val + 2))) (Fin (Text M (tach M) (k.val + 2))) ℝ) := by
        ext a b; rw [Matrix.of_apply, readK_wInt, Matrix.one_apply]
      have hkl : kLens (readK M (tach M) ha (wInt M ha p) k)
          = (1 : Matrix (Fin (Text M (tach M) (k.val + 2))) (Fin (Text M (tach M) (k.val + 2))) ℝ) := by
        rw [show readK M (tach M) ha (wInt M ha p) k
              = Matrix.of (readK M (tach M) ha (wInt M ha p) k) from rfl, hK1, kLens_one]
      simp only [kLDU, hq, hframe]
      rw [hkl]
      have hone : (1 : Matrix (Fin (Text M (tach M) (k.val + 2))) (Fin (Text M (tach M) (k.val + 2))) ℝ)
          (finProdFinEquiv.symm qK).1 (finProdFinEquiv.symm qK).2
          = readK M (tach M) ha (wInt M ha p) k (finProdFinEquiv.symm qK).1 (finProdFinEquiv.symm qK).2 :=
        congrFun (congrFun hK1.symm _) _
      rw [hone, readK, wInt]
      simp only [Function.comp_apply, Equiv.apply_symm_apply, hq]
      congr 2
      rw [Prod.mk.eta, Equiv.apply_symm_apply, ← hframe, Equiv.symm_apply_apply]
    · simp only [kLDU, hq, hframe]
    · simp only [kLDU, hq, hframe]
    · simp only [kLDU, hq, hframe]
  | inr sl => simp only [kLDU, hq]

/-- **The ∀L LIVE interior unit is nonzero at the interior-drop witness** `interiorLiveUnitGen (wInt p) ≠ 0`.
Via `kLDU_wIntGen` (`kLDU` fixes `wInt`), the live unit is `sqSumHmat0` of the live decoder chain at pivot
`wInt leafPivot`. The surviving entry `Hmat 0 (ρ, 0) = 1` is built by the ∀L survival machinery
(`Hmat_pivot`/`Hmat_row_thread`/`suffix_carrier` + the `genBlk_*` lemmas), all general-`L`; the surviving
entry reads only `Bmat/Nblk/Wblk/Rmat` (shared with `genBlkFlatStruct ha (wInt)`), so it is `Rfin L`-blind
and scalar-`u`-blind. This is the VERIFY-FIRST nonvanishing verdict: the polynomial `UPolyLiveGen` is NOT
identically zero at general `L` (residual loss off the singular locus). -/
theorem interiorLiveUnitGen_wInt_ne_zero (M : Fin (L + 1) → ℕ) (ha : StructAdm M (tach M)) (hL : 0 < L)
    (h0r : 0 < Text M (tach M) L) (h0c : 0 < Wext M L)
    (p : ℕ) (hp1 : 1 ≤ p) (hpL : p < L)
    (hr : Text M (tach M) (p + 1) < Text M (tach M) p)
    (hcd : ∀ b, p ≤ b → b < L → Text M (tach M) (b + 1) < Wext M b) :
    interiorLiveUnitGen M ha hL h0r h0c (wInt M ha p) ≠ 0 := by
  have hML : 0 < Wext M L := h0c
  rw [interiorLiveUnitGen, kLDU_wIntGen M ha p, VvalGen_eq_sqSumHmat0]
  set hle := hleStruct M (tach M) ha with hledef
  set u := wInt M ha p (leafPivot M ha hL h0r h0c) with hudef
  set B := genBlkFlatLive M (tach M) ha (rfinFixedPivot M ha hL (wInt M ha p)) (wInt M ha p)
    with hBdef
  set c := (chainOfMt u M (tach M) B hle).toChain with hcdef
  have hTdesc : ∀ s, s < p → Text M (tach M) (s + 1) ≤ Text M (tach M) s := by
    intro s hsp
    match s with
    | 0 => exact le_of_eq (Text0_eq_Text1_struct M (tach M) ha.h0).symm
    | (k + 1) => exact ha.hdesc k (by omega)
  have hTle : ∀ d a, a + d ≤ p → Text M (tach M) (a + d) ≤ Text M (tach M) a := by
    intro d
    induction d with
    | zero => intro a _; rw [Nat.add_zero]
    | succ e ih =>
      intro a ha'
      calc Text M (tach M) (a + (e + 1)) = Text M (tach M) ((a + e) + 1) := by ring_nf
        _ ≤ Text M (tach M) (a + e) := hTdesc (a + e) (by omega)
        _ ≤ Text M (tach M) a := ih a (by omega)
  have hρlt : ∀ s, s < p → Text M (tach M) (p + 1) < Text M (tach M) (s + 1) := by
    intro s hsp
    have : Text M (tach M) ((s + 1) + (p - (s + 1))) ≤ Text M (tach M) (s + 1) :=
      hTle (p - (s + 1)) (s + 1) (by omega)
    rw [show (s + 1) + (p - (s + 1)) = p by omega] at this
    exact lt_of_lt_of_le hr this
  have hsurvW : ∀ s, p ≤ s → s ≤ L → survRowVal M (tach M) s < Wext M s := by
    intro s hps hsL
    by_cases hsl : s = L
    · subst hsl; simpa [survRowVal] using hML
    · simp only [survRowVal, if_neg hsl]; exact hcd s hps (by omega)
  have hWblk : ∀ k, B.Wblk k = (genBlkFlatStruct M (tach M) ha (wInt M ha p)).Wblk k := fun _ => rfl
  have hsuffix : ∀ s, p ≤ s → ∀ (r : Fin (Wext M s)), r.val = survRowVal M (tach M) s →
      ∀ (hsL : s ≤ L), c.suffix s hsL r ⟨0, hML⟩ = 1 := by
    intro s hps r hr' hsL
    refine suffix_carrier hML (fun s' hps' hs' r' hr'' c' => ?_) hsurvW (L - s) s (by omega) hps r hr'
    have hcds' : 0 < Wext M s' - Text M (tach M) (s' + 1) := by
      have := hcd s' hps' (by omega)
      simp only [survRowVal, if_neg (by omega : s' ≠ L)] at hr''; omega
    have hrlift : r' = liftRow M (tach M) hle s' hs' ⟨0, hcds'⟩ := by
      apply Fin.ext
      simp only [liftRow, Fin.val_cast, Fin.val_natAdd, hr'']
      simp only [survRowVal, if_neg (by omega : s' ≠ L), Nat.add_zero]
    rw [hrlift, chain_A_liftRow s' hs' _ c']
    obtain ⟨k, rfl⟩ : ∃ k, s' = k + 1 := ⟨s' - 1, by omega⟩
    show B.Wblk (k + 1) _ c' = _
    rw [hWblk, show (genBlkFlatStruct M (tach M) ha (wInt M ha p)).Wblk (k + 1)
          = (if hk : k < L then (if hk2 : k + 1 < L then
              readW M (tach M) ha (wInt M ha p) ⟨k, hk⟩ hk2 else 0) else 0) from rfl,
      dif_pos (by omega), dif_pos hs', readW_wInt]
    simp only [survCol, survRowVal, true_and]
    rfl
  obtain ⟨kp, rfl⟩ : ∃ kp, p = kp + 1 := ⟨p - 1, by omega⟩
  have hkpL : kp < L := by omega
  have hr2 : Text M (tach M) (kp + 2) < Text M (tach M) (kp + 1) := hr
  have hcd2 : Text M (tach M) (kp + 2) < Wext M (kp + 1) := hcd (kp + 1) (le_refl _) hpL
  set ρcast : Fin (Text M (tach M) (kp + 1)) :=
    Fin.cast (show Text M (tach M) (kp + 2) + (Text M (tach M) (kp + 1) - Text M (tach M) (kp + 2))
        = Text M (tach M) (kp + 1) by omega) (Fin.natAdd _ ⟨0, by omega⟩) with hρcastdef
  set colP : Fin (Wext M (kp + 1)) :=
    Fin.cast (show Text M (tach M) (kp + 2) + (Wext M (kp + 1) - Text M (tach M) (kp + 2))
        = Wext M (kp + 1) by omega) (Fin.natAdd _ ⟨0, by omega⟩) with hcolPdef
  have hcolPval : colP.val = survRowVal M (tach M) (kp + 1) := by
    simp only [hcolPdef, Fin.val_cast, Fin.val_natAdd, Nat.add_zero, survRowVal,
      if_neg (by omega : kp + 1 ≠ L)]
  have hpivot : c.Hmat (kp + 1) (le_of_lt hpL) ρcast ⟨0, hML⟩ = 1 := by
    refine Hmat_pivot hpL hML colP ρcast ?_ ?_ ?_
    · intro j
      exact genBlk_Bmat_succ_bot ha (kp + 1) kp hkpL ⟨0, by omega⟩ j
    · intro cc
      exact genBlk_Rmat_pivot ha kp hkpL hr2 hcd2 cc
    · exact hsuffix (kp + 1) (le_refl _) colP hcolPval (le_of_lt hpL)
  have hρT : ∀ s, s ≤ kp + 1 → Text M (tach M) (kp + 1 + 1) < Text M (tach M) s := by
    intro s hs
    have hle' : Text M (tach M) (kp + 1) ≤ Text M (tach M) s := by
      have := hTle (kp + 1 - s) s (by omega)
      rwa [show s + (kp + 1 - s) = kp + 1 by omega] at this
    exact lt_of_lt_of_le hr2 hle'
  have hEzero : ∀ s, s < kp + 1 → c.E s = 0 := by
    intro s hs
    show B.Rmat s * Agen u M (tach M) B hle s = 0
    have hRz : B.Rmat s = 0 := by
      show (genBlkFlatStruct M (tach M) ha (wInt M ha (kp + 1))).Rmat s = 0
      match s with
      | 0 => rfl
      | (k + 1) => exact genBlk_Rmat_succ_zero ha (kp + 1) k (by omega) (by omega)
    rw [hRz, Matrix.zero_mul]
  have hHmat0 : c.Hmat 0 (Nat.zero_le L) (rhoAt M (tach M) (kp + 1) 0 (hρT 0 (by omega)))
      ⟨0, hML⟩ = 1 := by
    refine Hmat_row_thread (B := B) hpL hML hρT (fun s hs => hTdesc s (by omega))
      ?_ (fun s hs => hEzero s hs) (fun s hs => hρlt s (by omega)) ?_ (kp + 1) 0 (by omega)
    · convert hpivot using 2
    · intro s hsp a j
      match s with
      | 0 => exact genBlk_Bmat_zero_top ha (kp + 1) a j _
      | (kk + 1) => exact genBlk_Bmat_succ_top ha (kp + 1) kk (by omega) a j
  exact sqSumHmat0_ne_zero_of_entry c (rhoAt M (tach M) (kp + 1) 0 (hρT 0 (by omega)))
    ⟨0, hML⟩ hHmat0

/-- **The nonzero witness `UPolyLiveGen ≠ 0`** at general `L` — from `interiorLiveUnitGen (wInt p) ≠ 0`
via `eval (wInt p) UPolyLiveGen = interiorLiveUnitGen (wInt p)`. The pivot `p` (`1 ≤ p < L`, the strict
row-drop, the tail column-drops, the leaf width) comes from `InteriorDrop M`. -/
theorem UPolyLiveGen_ne_zero (M : Fin (L + 1) → ℕ) (ha : StructAdm M (tach M)) (hL : 0 < L)
    (h0r : 0 < Text M (tach M) L) (h0c : 0 < Wext M L)
    (hInt : InteriorDrop M) :
    UPolyLiveGen M ha hL h0r h0c ≠ 0 := by
  obtain ⟨_hML, p, hp1, hpL, hrdrop, hcd⟩ := hInt
  intro h0
  refine interiorLiveUnitGen_wInt_ne_zero M ha hL h0r h0c p hp1 hpL hrdrop hcd ?_
  rw [← eval_UPolyLiveGen M ha hL h0r h0c (wInt M ha p), h0, map_zero]

/-- **(4) The LEAF-1 atom: a.e.-positivity of the ∀L LIVE interior unit** —
`∀ᵐ u, 0 < interiorLiveUnitGen ha hL h0r h0c u`, given `InteriorDrop M`. Via `eval_UPolyLiveGen`
(`interiorLiveUnitGen = eval · UPolyLiveGen`) + `MvPolynomial.ae_eval_ne_zero` (`UPolyLiveGen ≠ 0` ⟹ the
zero set is null) + `interiorLiveUnitGen_nonneg` (`≠ 0 ⟹ > 0`). -/
theorem interiorLiveUnit_ae_posGen (M : Fin (L + 1) → ℕ) (ha : StructAdm M (tach M)) (hL : 0 < L)
    (h0r : 0 < Text M (tach M) L) (h0c : 0 < Wext M L)
    (hInt : InteriorDrop M) :
    ∀ᵐ u, 0 < interiorLiveUnitGen M ha hL h0r h0c u := by
  have hae := MvPolynomial.ae_eval_ne_zero _ (UPolyLiveGen_ne_zero M ha hL h0r h0c hInt)
  filter_upwards [hae] with u hu
  rw [← eval_UPolyLiveGen M ha hL h0r h0c u] at *
  refine lt_of_le_of_ne ?_ (Ne.symm hu)
  rw [eval_UPolyLiveGen M ha hL h0r h0c u]; exact interiorLiveUnitGen_nonneg M ha hL h0r h0c u

end DLNFibre.DLN.RLCT
