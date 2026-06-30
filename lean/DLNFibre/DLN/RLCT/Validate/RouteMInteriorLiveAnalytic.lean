import DLNFibre.DLN.RLCT.Validate.RouteMInteriorLiveContract

/-!
# `RouteMInteriorLiveAnalytic` — the analytic chart atoms for the LIVE-leaf ∘ kLDU interior chart

The three analytic atoms the LIVE-leaf interior achiever contract (`RouteMInteriorLiveContract`)
consumes in its `NodeAchieverChart` `Umeas`/`Ubound`/`image_subset` slots. Built as named atoms in
this own module (genm-r1lower wires them into the contract's frozen `interiorLive_Umeas`/`_Ubound`/
`_image` `sorry`s).

* `ldu_image` — image containment (continuity of `interiorLivePhi` + `interiorLivePhi 0 = 0`).
* `ldu_Umeas` — `interiorLiveUnit` is measurable.
* `ldu_Ubound` — box bound + a.e.-positivity (the `NodeAchieverChart.Ubound` field).
-/

open MeasureTheory
open scoped ENNReal BigOperators

namespace DLNFibre.DLN.RLCT

open Matrix

variable {M : Fin (2 + 1) → ℕ}

/-! ## `interiorLivePhi 0 = 0` (the deepest point) -/

/-- **`kLDU` fixes `0`** — `kLens 0 = 0` (the diagonal pivots vanish), and the pass-through arms send
`0` to `0`. -/
theorem kLDU_zero (ha : StructAdm M (tach M)) :
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

/-- `chainA` of all-zero inputs is `0`. -/
theorem chainA_zero {M' t c m' : ℕ} (h : t + c = M') :
    chainA h (0 : Matrix (Fin t) (Fin c) ℝ) (0 : Matrix (Fin c) (Fin m') ℝ)
        (0 : Matrix (Fin t) (Fin m') ℝ) = 0 := by
  unfold chainA
  ext i j
  rw [Matrix.reindex_apply, Matrix.submatrix_apply, Matrix.of_apply, Matrix.zero_apply]
  rcases (finSplit (M := M') (t := t) (show t ≤ M' by omega)).symm.symm i with a | b
  · rw [Sum.elim_inl, Matrix.zero_mul, sub_zero, Matrix.zero_apply]
  · rw [Sum.elim_inr, Matrix.reindex_apply, Matrix.submatrix_zero]; rfl

/-! ## `chartParamsGen 0 (zero-reader live decoder) = 0` (the deepest-point telescope) -/

variable {L : ℕ}

/-- At the zero flat point, every interior `Cgen 0 … (k+1)` vanishes: the leaf carries scalar `0`
(`Cgen 0 … L = 0•Rfin = 0`) and the interior `Bmat (k+1)` is `bmatStack` of zero readers (`= 0`), so
`Cgen 0 … (k+1) = Bmat(k+1)·chainQ(0) + 0 = 0`. -/
theorem bmatStack_zero (M' t : Fin (L + 1) → ℕ) (k : ℕ) (hdesc : Text M' t (k + 1) ≤ Text M' t k) :
    bmatStack M' t k hdesc (0 : Matrix (Fin (Text M' t (k + 1))) (Fin (Text M' t (k + 1))) ℝ)
        (0 : Matrix (Fin (Text M' t k - Text M' t (k + 1))) (Fin (Text M' t (k + 1))) ℝ) = 0 := by
  funext i j
  rw [bmatStack, Matrix.reindex_apply, Matrix.submatrix_apply, Matrix.of_apply, Matrix.zero_apply]
  rcases finSumFinEquiv.symm _ with a | b
  · rw [Sum.elim_inl, Matrix.zero_apply]
  · rw [Sum.elim_inr, Matrix.zero_mul, Matrix.zero_apply]

theorem Cgen_zero_succ (M' t : Fin (L + 1) → ℕ) (ha : StructAdm M' t)
    (rfin : Matrix (Fin (Text M' t L)) (Fin (Wext M' L)) ℝ) (k : ℕ) :
    Cgen (0 : ℝ) M' t (genBlkFlatLive M' t ha rfin 0) (hleStruct M' t ha) (k + 1) = 0 := by
  unfold Cgen
  by_cases hk : k + 1 < L
  · rw [dif_pos hk, zero_smul, add_zero]
    have hB : (genBlkFlatLive M' t ha rfin 0).Bmat (k + 1) = 0 := by
      show (genBlkFlatStruct M' t ha 0).Bmat (k + 1) = 0
      simp only [genBlkFlatStruct]
      rw [dif_pos (by omega : k < L)]
      have hK : readK M' t ha (0 : Fin (routeMAmbient M') → ℝ) ⟨k, by omega⟩ = 0 := by
        funext i j; simp only [readK, Pi.zero_apply, Matrix.zero_apply]
      have hX : readX M' t ha (0 : Fin (routeMAmbient M') → ℝ) ⟨k, by omega⟩ = 0 := by
        funext i j; simp only [readX, Pi.zero_apply, Matrix.zero_apply]
      rw [hK, hX]
      exact bmatStack_zero M' t (k + 1) _
    rw [hB, Matrix.zero_mul]
  · rw [dif_neg hk, zero_smul]

/-- At the zero flat point, every layer `Agen 0 … k` vanishes: `Nblk k = Wblk k = 0` (zero readers)
and `Cgen 0 … (k+1) = 0` (`Cgen_zero_succ`), so `Agen 0 … k = chainA 0 0 0 = 0` (`chainA_zero`). -/
theorem Agen_zero (M' t : Fin (L + 1) → ℕ) (ha : StructAdm M' t)
    (rfin : Matrix (Fin (Text M' t L)) (Fin (Wext M' L)) ℝ) (k : ℕ) :
    Agen (0 : ℝ) M' t (genBlkFlatLive M' t ha rfin 0) (hleStruct M' t ha) k = 0 := by
  unfold Agen
  by_cases hk : k < L
  · rw [dif_pos hk]
    have hN : (genBlkFlatLive M' t ha rfin 0).Nblk k = 0 := by
      show (genBlkFlatStruct M' t ha 0).Nblk k = 0
      match k with
      | 0 => rfl
      | (j + 1) =>
        simp only [genBlkFlatStruct]; rw [dif_pos (by omega : j < L)]
        funext a b; simp only [readN, Pi.zero_apply, Matrix.zero_apply]
    have hW : (genBlkFlatLive M' t ha rfin 0).Wblk k = 0 := by
      show (genBlkFlatStruct M' t ha 0).Wblk k = 0
      match k with
      | 0 => rfl
      | (j + 1) =>
        simp only [genBlkFlatStruct]
        by_cases hj : j < L
        · rw [dif_pos hj]
          by_cases hj2 : j + 1 < L
          · rw [dif_pos hj2]; funext a b; simp only [readW, Pi.zero_apply, Matrix.zero_apply]
          · rw [dif_neg hj2]
        · rw [dif_neg hj]
    rw [hN, hW, Cgen_zero_succ M' t ha rfin k, chainA_zero]
  · rw [dif_neg hk]

/-- **`chartParamsGen 0 (zero-reader live decoder) = 0`** — every reindexed layer vanishes
(`Agen_zero`). -/
theorem chartParamsGen_live_zero (M' t : Fin (L + 1) → ℕ) (ha : StructAdm M' t)
    (rfin : Matrix (Fin (Text M' t L)) (Fin (Wext M' L)) ℝ) :
    chartParamsGen (0 : ℝ) M' t (genBlkFlatLive M' t ha rfin 0) (hleStruct M' t ha)
      = (fun _ => 0 : Params M') := by
  funext s
  rw [chartParamsGen]
  rw [show (chainOfMt (0 : ℝ) M' t (genBlkFlatLive M' t ha rfin 0) (hleStruct M' t ha)).toChain.A s.val
        = Agen (0 : ℝ) M' t (genBlkFlatLive M' t ha rfin 0) (hleStruct M' t ha) s.val from rfl,
    Agen_zero M' t ha rfin s.val]
  simp

/-! ## `interiorLivePhi 0 = 0` -/

/-- **`interiorLivePhi` maps `0` to `0`** (the deepest point) — `kLDU 0 = 0`, the scalar `0 leafPivot`
is `0`, and `chartParamsGen 0 (the zero-reader live decoder) = 0` (`chartParamsGen_live_zero`), so
`phiGen 0 … = paramsEquivFlat 0 = 0` (`paramsEquivFlat_deepest`). -/
theorem interiorLivePhi_zero (ha : StructAdm M (tach M))
    (h0r : 0 < Text M (tach M) 2) (h0c : 0 < Wext M 2) :
    interiorLivePhi ha h0r h0c 0 = 0 := by
  rw [interiorLivePhi, kLDU_zero ha, phiFlatLiveAt]
  simp only [Pi.zero_apply]
  rw [phiGen]
  rw [chartParamsGen_live_zero M (tach M) ha (rfinFixedPivot M ha (by norm_num) 0)]
  exact paramsEquivFlat_deepest M

/-! ## `ldu_image` — image containment (`NodeAchieverChart.image_subset`) -/

/-- **`ldu_image`** — a small source box `[0,δ]^N` maps into `cubeBox N ε` (continuity of
`interiorLivePhi` via `interiorLive_diff` + `interiorLivePhi 0 = 0`). Matches the contract's frozen
`interiorLive_image` signature. Mirrors `phi3333_image_subset_cubeBox`. -/
theorem ldu_image (ha : StructAdm M (tach M))
    (h0r : 0 < Text M (tach M) 2) (h0c : 0 < Wext M 2) :
    ∀ ε : ℝ, 0 < ε →
      ∃ δ > 0, interiorLivePhi ha h0r h0c ''
        (Set.univ.pi (fun _ : Fin (routeMAmbient M) => Set.Icc (0 : ℝ) δ))
        ⊆ cubeBox (routeMAmbient M) ε := by
  intro ε hε
  have hcont : Continuous (interiorLivePhi ha h0r h0c) := (interiorLive_diff ha h0r h0c).continuous
  have hopen : IsOpen (Set.univ.pi (fun _ : Fin (routeMAmbient M) => Set.Ioo (-ε) ε)) :=
    isOpen_set_pi Set.finite_univ (fun _ _ => isOpen_Ioo)
  have hmem : (0 : Fin (routeMAmbient M) → ℝ)
      ∈ interiorLivePhi ha h0r h0c ⁻¹' (Set.univ.pi (fun _ : Fin (routeMAmbient M) => Set.Ioo (-ε) ε)) := by
    simp only [Set.mem_preimage, interiorLivePhi_zero ha h0r h0c, Set.mem_pi, Set.mem_univ,
      true_implies, Set.mem_Ioo, Pi.zero_apply]
    exact fun i => ⟨by linarith, hε⟩
  obtain ⟨δ, hδ, hsub⟩ := cubeBox_subset_of_isOpen (hopen.preimage hcont) hmem
  refine ⟨δ, hδ, ?_⟩
  rintro y ⟨x, hx, rfl⟩
  have hxcube : x ∈ cubeBox (routeMAmbient M) δ := by
    simp only [cubeBox, Set.mem_pi, Set.mem_univ, true_implies, Set.mem_Icc] at hx ⊢
    intro i; exact ⟨le_trans (by linarith [hδ]) (hx i).1, (hx i).2⟩
  have hxmem : interiorLivePhi ha h0r h0c x
      ∈ Set.univ.pi (fun _ : Fin (routeMAmbient M) => Set.Ioo (-ε) ε) :=
    Set.mem_preimage.mp (hsub hxcube)
  simp only [cubeBox, Set.mem_pi, Set.mem_univ, true_implies, Set.mem_Icc]
  intro i
  have hi := (Set.mem_pi.mp hxmem) i (Set.mem_univ i)
  rw [Set.mem_Ioo] at hi
  exact ⟨hi.1.le, hi.2.le⟩

/-! ## Continuity of `interiorLiveUnit` (the chain threaded through `x`) -/

section Cont

variable {X : Type*} [TopologicalSpace X]

/-- `chainQ N` is continuous in `N`. -/
theorem continuous_chainQ {M' t c : ℕ} (h : t + c = M') {N : X → Matrix (Fin t) (Fin c) ℝ}
    (hN : Continuous N) : Continuous (fun x => chainQ h (N x)) := by
  unfold chainQ
  refine Continuous.matrix_reindex (continuous_matrix (fun i j => ?_)) _ _
  simp only [Matrix.of_apply]
  rcases j with a | b
  · simp only [Sum.elim_inl]; exact continuous_const
  · simp only [Sum.elim_inr]; exact (hN.matrix_reindex _ _).matrix_elem i b

/-- `chainA N W C` is continuous in `(N, W, C)`. -/
theorem continuous_chainA {M' t c m' : ℕ} (h : t + c = M')
    {N : X → Matrix (Fin t) (Fin c) ℝ} {W : X → Matrix (Fin c) (Fin m') ℝ}
    {C : X → Matrix (Fin t) (Fin m') ℝ}
    (hN : Continuous N) (hW : Continuous W) (hC : Continuous C) :
    Continuous (fun x => chainA h (N x) (W x) (C x)) := by
  unfold chainA
  refine Continuous.matrix_reindex (continuous_matrix (fun i j => ?_)) _ _
  simp only [Matrix.of_apply]
  rcases i with a | b
  · simp only [Sum.elim_inl]; exact (hC.sub (hN.matrix_mul hW)).matrix_elem a j
  · simp only [Sum.elim_inr]; exact (hW.matrix_reindex _ _).matrix_elem b j

variable {L : ℕ}

/-- Continuity bundle for a parametrized `GenBlk M' t`: every block family is continuous in `x`. -/
structure GenBlkContinuous (M' t : Fin (L + 1) → ℕ) (B : X → GenBlk M' t) : Prop where
  hBmat : ∀ k, Continuous (fun x => (B x).Bmat k)
  hNblk : ∀ k, Continuous (fun x => (B x).Nblk k)
  hWblk : ∀ k, Continuous (fun x => (B x).Wblk k)
  hRmat : ∀ k, Continuous (fun x => (B x).Rmat k)
  hRfin : ∀ k, Continuous (fun x => (B x).Rfin k)

/-- `Cgen (g x) (B x) k` is continuous in `x`. -/
theorem continuous_Cgen {M' t : Fin (L + 1) → ℕ} {B : X → GenBlk M' t}
    (hB : GenBlkContinuous M' t B) {g : X → ℝ} (hg : Continuous g)
    (hle : ∀ k, k < L → Text M' t (k + 1) ≤ Wext M' k) (k : ℕ) :
    Continuous (fun x => Cgen (g x) M' t (B x) hle k) := by
  unfold Cgen
  by_cases hk : k < L
  · simp only [dif_pos hk]
    exact ((hB.hBmat k).matrix_mul (continuous_chainQ _ (hB.hNblk k))).add
      (hg.smul (hB.hRmat k))
  · simp only [dif_neg hk]
    exact hg.smul (hB.hRfin k)

/-- `Agen (g x) (B x) k` is continuous in `x` (uses `continuous_Cgen` at `k+1`). -/
theorem continuous_Agen {M' t : Fin (L + 1) → ℕ} {B : X → GenBlk M' t}
    (hB : GenBlkContinuous M' t B) {g : X → ℝ} (hg : Continuous g)
    (hle : ∀ k, k < L → Text M' t (k + 1) ≤ Wext M' k) (k : ℕ) :
    Continuous (fun x => Agen (g x) M' t (B x) hle k) := by
  unfold Agen
  by_cases hk : k < L
  · simp only [dif_pos hk]
    exact continuous_chainA _ (hB.hNblk k) (hB.hWblk k) (continuous_Cgen hB hg hle (k + 1))
  · simp only [dif_neg hk]; exact continuous_const

/-- `.toChain.A s` continuity (= `Agen s`), in pinned `Wext M'` widths. -/
theorem continuous_toChain_A {M' t : Fin (L + 1) → ℕ} {B : X → GenBlk M' t}
    (hB : GenBlkContinuous M' t B) {g : X → ℝ} (hg : Continuous g)
    (hle : ∀ k, k < L → Text M' t (k + 1) ≤ Wext M' k) (s : ℕ) :
    Continuous (fun x => (Agen (g x) M' t (B x) hle s :
      Matrix (Fin (Wext M' s)) (Fin (Wext M' (s + 1))) ℝ)) :=
  continuous_Agen hB hg hle s

/-- `.toChain.B s` continuity (= `Bmat s`), in pinned `Text M' t` widths. -/
theorem continuous_toChain_B {M' t : Fin (L + 1) → ℕ} {B : X → GenBlk M' t}
    (hB : GenBlkContinuous M' t B)
    (hle : ∀ k, k < L → Text M' t (k + 1) ≤ Wext M' k) (s : ℕ) :
    Continuous (fun x => ((B x).Bmat s :
      Matrix (Fin (Text M' t s)) (Fin (Text M' t (s + 1))) ℝ)) :=
  hB.hBmat s

/-- `.toChain.E s` continuity (= `Rmat s · Agen s`), in pinned widths. -/
theorem continuous_toChain_E {M' t : Fin (L + 1) → ℕ} {B : X → GenBlk M' t}
    (hB : GenBlkContinuous M' t B) {g : X → ℝ} (hg : Continuous g)
    (hle : ∀ k, k < L → Text M' t (k + 1) ≤ Wext M' k) (s : ℕ) :
    Continuous (fun x => ((B x).Rmat s * Agen (g x) M' t (B x) hle s :
      Matrix (Fin (Text M' t s)) (Fin (Wext M' (s + 1))) ℝ)) :=
  (hB.hRmat s).matrix_mul (continuous_Agen hB hg hle s)

end Cont

end DLNFibre.DLN.RLCT
