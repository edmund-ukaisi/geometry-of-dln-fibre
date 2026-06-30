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

/-- **`Hmat 0` of the L=2 chain is continuous in `x`** — the depth-2 telescope, each chain-projection
wrapped with `show … from` so the codomain is the fixed `Text/Wext` type (`continuous_matrix` /
`matrix_mul` reject the syntactically-`x`-dependent `.Twid`/`.Wwid` projection codomain otherwise). -/
theorem continuous_Hmat0_L2 {M' t : Fin (2 + 1) → ℕ} {B : X → GenBlk M' t}
    (hB : GenBlkContinuous M' t B) {g : X → ℝ} (hg : Continuous g)
    (hle : ∀ k, k < 2 → Text M' t (k + 1) ≤ Wext M' k) :
    Continuous (fun x => (show Matrix (Fin (Text M' t 0)) (Fin (Wext M' 2)) ℝ
      from (chainOfMt (g x) M' t (B x) hle).toChain.Hmat 0 (by omega))) := by
  have hsuf2 : Continuous (fun x => (show Matrix (Fin (Wext M' 2)) (Fin (Wext M' 2)) ℝ
      from (chainOfMt (g x) M' t (B x) hle).toChain.suffix 2 (le_refl 2))) := by
    refine Continuous.congr (continuous_const
      (y := (1 : Matrix (Fin (Wext M' 2)) (Fin (Wext M' 2)) ℝ))) (fun x => ?_)
    exact ((chainOfMt (g x) M' t (B x) hle).toChain.suffix_last).symm
  have hsuf1 : Continuous (fun x => (show Matrix (Fin (Wext M' 1)) (Fin (Wext M' 2)) ℝ
      from (chainOfMt (g x) M' t (B x) hle).toChain.suffix 1 (by omega))) := by
    refine Continuous.congr (Continuous.matrix_mul (n := Fin (Wext M' 2))
      (continuous_toChain_A hB hg hle 1) hsuf2) (fun x => ?_)
    exact ((chainOfMt (g x) M' t (B x) hle).toChain.suffix_succ 1 (by omega)).symm
  have hH2 : Continuous (fun x => (show Matrix (Fin (Text M' t 2)) (Fin (Wext M' 2)) ℝ
      from (chainOfMt (g x) M' t (B x) hle).toChain.Hmat 2 (le_refl 2))) := by
    refine Continuous.congr (hB.hRfin 2) (fun x => ?_)
    exact ((chainOfMt (g x) M' t (B x) hle).toChain.Hmat_last).symm
  have hH1 : Continuous (fun x => (show Matrix (Fin (Text M' t 1)) (Fin (Wext M' 2)) ℝ
      from (chainOfMt (g x) M' t (B x) hle).toChain.Hmat 1 (by omega))) := by
    refine Continuous.congr (Continuous.add
      (Continuous.matrix_mul (n := Fin (Text M' t 2)) (continuous_toChain_B hB hle 1) hH2)
      (Continuous.matrix_mul (n := Fin (Wext M' 2)) (continuous_toChain_E hB hg hle 1) hsuf2))
      (fun x => ?_)
    exact ((chainOfMt (g x) M' t (B x) hle).toChain.Hmat_succ 1 (by omega)).symm
  refine Continuous.congr (Continuous.add
    (Continuous.matrix_mul (n := Fin (Text M' t 1)) (continuous_toChain_B hB hle 0) hH1)
    (Continuous.matrix_mul (n := Fin (Wext M' 1)) (continuous_toChain_E hB hg hle 0) hsuf1))
    (fun x => ?_)
  exact ((chainOfMt (g x) M' t (B x) hle).toChain.Hmat_succ 0 (by omega)).symm

/-! ### Continuity of the block constructors + readers (toward the live decoder) -/

/-- `bmatStack K X` is continuous in `(K, X)`. -/
theorem continuous_bmatStack {M' t : Fin (L + 1) → ℕ} (k : ℕ)
    (hdesc : Text M' t (k + 1) ≤ Text M' t k)
    {K : X → Matrix (Fin (Text M' t (k + 1))) (Fin (Text M' t (k + 1))) ℝ}
    {Xb : X → Matrix (Fin (Text M' t k - Text M' t (k + 1))) (Fin (Text M' t (k + 1))) ℝ}
    (hK : Continuous K) (hX : Continuous Xb) :
    Continuous (fun x => bmatStack M' t k hdesc (K x) (Xb x)) := by
  unfold bmatStack
  refine Continuous.matrix_reindex (continuous_matrix (fun i j => ?_)) _ _
  simp only [Matrix.of_apply]
  rcases finSumFinEquiv.symm i with a | b
  · simp only [Sum.elim_inl]; exact hK.matrix_elem a j
  · simp only [Sum.elim_inr]; exact (hX.matrix_mul hK).matrix_elem b j

/-- `rmatPad E` is continuous in `E`. -/
theorem continuous_rmatPad {M' t : Fin (L + 1) → ℕ} (s : ℕ)
    (h1 : Text M' t (s + 1) ≤ Text M' t s) (h2 : Text M' t (s + 1) ≤ Wext M' s)
    {E : X → Matrix (Fin (Text M' t s - Text M' t (s + 1))) (Fin (Wext M' s - Text M' t (s + 1))) ℝ}
    (hE : Continuous E) :
    Continuous (fun x => rmatPad M' t s h1 h2 (E x)) := by
  unfold rmatPad
  exact Continuous.matrix_reindex
    (Continuous.matrix_fromBlocks continuous_const continuous_const continuous_const hE) _ _

end Cont

/-! ## `ldu_Umeas` — measurability of the lensed unit (via continuity) -/

/-- **`kLDU` is continuous** (from the banked `differentiable_kLDU`). -/
theorem continuous_kLDU (ha : StructAdm M (tach M)) :
    Continuous (kLDU M (tach M) ha) := (differentiable_kLDU M (tach M) ha).continuous

/-- The live decoder `genBlkFlatLive … (rfinFixedPivot (kLDU x)) (kLDU x)` is block-continuous in `x`.
Each block is `bmatStack`/`rmatPad` of single-coordinate readers of `kLDU x`; the leaf `rfinFixedPivot`
reads single coordinates / constant `1`. (`L = 2` here.) -/
theorem genBlkContinuous_live (ha : StructAdm M (tach M))
    (h0r : 0 < Text M (tach M) 2) (h0c : 0 < Wext M 2) :
    GenBlkContinuous M (tach M)
      (fun x => genBlkFlatLive M (tach M) ha
        (rfinFixedPivot M ha (by norm_num) (kLDU M (tach M) ha x)) (kLDU M (tach M) ha x)) := by
  have hkapp : ∀ q, Continuous (fun x : Fin (routeMAmbient M) → ℝ => kLDU M (tach M) ha x q) :=
    fun q => (continuous_apply q).comp (continuous_kLDU ha)
  -- reader-block continuity: each reader entry is `(kLDU x)` at a fixed slot
  have hreadK : ∀ k : Fin 2, Continuous (fun x => readK M (tach M) ha (kLDU M (tach M) ha x) k) :=
    fun k => continuous_matrix (fun i j => hkapp _)
  have hreadX : ∀ k : Fin 2, Continuous (fun x => readX M (tach M) ha (kLDU M (tach M) ha x) k) :=
    fun k => continuous_matrix (fun i j => hkapp _)
  have hreadN : ∀ k : Fin 2, Continuous (fun x => readN M (tach M) ha (kLDU M (tach M) ha x) k) :=
    fun k => continuous_matrix (fun i j => hkapp _)
  have hreadE : ∀ k : Fin 2, Continuous (fun x => readE M (tach M) ha (kLDU M (tach M) ha x) k) :=
    fun k => continuous_matrix (fun i j => hkapp _)
  have hreadW : ∀ (k : Fin 2) (hk : k.val + 1 < 2),
      Continuous (fun x => readW M (tach M) ha (kLDU M (tach M) ha x) k hk) :=
    fun k hk => continuous_matrix (fun i j => hkapp _)
  refine ⟨fun k => ?_, fun k => ?_, fun k => ?_, fun k => ?_, fun k => ?_⟩
  · -- Bmat
    show Continuous (fun x => (genBlkFlatStruct M (tach M) ha (kLDU M (tach M) ha x)).Bmat k)
    match k with
    | 0 => exact continuous_const
    | (j + 1) =>
      simp only [genBlkFlatStruct]
      by_cases hj : j < 2
      · simp only [dif_pos hj]
        exact continuous_bmatStack (j + 1) (ha.hdesc j hj) (hreadK ⟨j, hj⟩) (hreadX ⟨j, hj⟩)
      · simp only [dif_neg hj]; exact continuous_const
  · -- Nblk
    show Continuous (fun x => (genBlkFlatStruct M (tach M) ha (kLDU M (tach M) ha x)).Nblk k)
    match k with
    | 0 => exact continuous_const
    | (j + 1) =>
      simp only [genBlkFlatStruct]
      by_cases hj : j < 2
      · simp only [dif_pos hj]; exact hreadN ⟨j, hj⟩
      · simp only [dif_neg hj]; exact continuous_const
  · -- Wblk
    show Continuous (fun x => (genBlkFlatStruct M (tach M) ha (kLDU M (tach M) ha x)).Wblk k)
    match k with
    | 0 => exact continuous_const
    | (j + 1) =>
      simp only [genBlkFlatStruct]
      by_cases hj : j < 2
      · simp only [dif_pos hj]
        by_cases hj2 : j + 1 < 2
        · simp only [dif_pos hj2]; exact hreadW ⟨j, hj⟩ hj2
        · simp only [dif_neg hj2]; exact continuous_const
      · simp only [dif_neg hj]; exact continuous_const
  · -- Rmat
    show Continuous (fun x => (genBlkFlatStruct M (tach M) ha (kLDU M (tach M) ha x)).Rmat k)
    match k with
    | 0 => exact continuous_const
    | (j + 1) =>
      simp only [genBlkFlatStruct]
      by_cases hj : j < 2
      · simp only [dif_pos hj]
        exact continuous_rmatPad (j + 1) (ha.hdesc j hj) (ha.hub j) (hreadE ⟨j, hj⟩)
      · simp only [dif_neg hj]; exact continuous_const
  · -- Rfin = rfinFixedPivot ∘ kLDU
    by_cases hk : k = 2
    · subst hk
      have hrw : (fun x => (genBlkFlatLive M (tach M) ha
            (rfinFixedPivot M ha (by norm_num) (kLDU M (tach M) ha x)) (kLDU M (tach M) ha x)).Rfin 2)
          = fun x => rfinFixedPivot M ha (by norm_num) (kLDU M (tach M) ha x) := by
        funext x; simp only [genBlkFlatLive, dif_pos]
      rw [hrw]
      refine continuous_matrix (fun i j => ?_)
      show Continuous (fun x => if i.val = 0 ∧ j.val = 0 then (1 : ℝ)
        else kLDU M (tach M) ha x (leafSlot M (tach M) ha (by norm_num) i j))
      by_cases hij : i.val = 0 ∧ j.val = 0
      · simp only [if_pos hij]; exact continuous_const
      · simp only [if_neg hij]; exact hkapp _
    · have hrw : (fun x => (genBlkFlatLive M (tach M) ha
            (rfinFixedPivot M ha (by norm_num) (kLDU M (tach M) ha x)) (kLDU M (tach M) ha x)).Rfin k)
          = fun _ => 0 := by
        funext x; simp only [genBlkFlatLive, dif_neg hk]
      rw [hrw]; exact continuous_const

/-- **`interiorLiveUnit` is continuous** — `= sqSumHmat0` of the chain (`VvalGen_eq_sqSumHmat0`),
which is `∑∑ (Hmat 0)²`; `Hmat 0` is continuous (`continuous_Hmat0_L2` with the live decoder
`genBlkContinuous_live` + the radial scalar `x ↦ x leafPivot`). -/
theorem continuous_interiorLiveUnit (ha : StructAdm M (tach M))
    (h0r : 0 < Text M (tach M) 2) (h0c : 0 < Wext M 2) :
    Continuous (interiorLiveUnit ha h0r h0c) := by
  have hg : Continuous (fun x : Fin (routeMAmbient M) → ℝ => x (leafPivot M ha (by norm_num) h0r h0c)) :=
    continuous_apply _
  have hHmat0 := continuous_Hmat0_L2 (genBlkContinuous_live ha h0r h0c) hg
    (hleStruct M (tach M) ha)
  -- ∑∑ (Hmat 0)² is continuous (each entry continuous via hHmat0, finite sum of squares)
  have hsq : Continuous (fun x => ∑ i, ∑ j,
      ((show Matrix (Fin (Text M (tach M) 0)) (Fin (Wext M 2)) ℝ
          from (chainOfMt (x (leafPivot M ha (by norm_num) h0r h0c)) M (tach M)
            (genBlkFlatLive M (tach M) ha (rfinFixedPivot M ha (by norm_num) (kLDU M (tach M) ha x))
              (kLDU M (tach M) ha x)) (hleStruct M (tach M) ha)).toChain.Hmat 0 (Nat.zero_le 2))
        i j) ^ 2) :=
    continuous_finset_sum _ (fun i _ => continuous_finset_sum _ (fun j _ =>
      (hHmat0.matrix_elem i j).pow 2))
  refine hsq.congr (fun x => ?_)
  rw [interiorLiveUnit, VvalGen_eq_sqSumHmat0, sqSumHmat0]
  rfl

/-- **`ldu_Umeas`** — the lensed unit is measurable (continuity ⟹ measurable). Matches the contract's
frozen `interiorLive_Umeas` signature. -/
theorem ldu_Umeas (ha : StructAdm M (tach M))
    (h0r : 0 < Text M (tach M) 2) (h0c : 0 < Wext M 2) :
    Measurable (interiorLiveUnit ha h0r h0c) :=
  (continuous_interiorLiveUnit ha h0r h0c).measurable

/-! ## `ldu_Ubound` — box bound + a.e.-positivity (consuming the positivity atom) -/

/-- **The box bound** `interiorLiveUnit ≤ B` on `[0,δ]^N` — continuity on a compact box
(`continuous_interiorLiveUnit` + `IsCompact.exists_isMaxOn`). Mirrors `achieverUfun_le_on_box`. -/
theorem ldu_Uval_le_on_box (ha : StructAdm M (tach M))
    (h0r : 0 < Text M (tach M) 2) (h0c : 0 < Wext M 2) (δ : ℝ) :
    ∃ B, 0 < B ∧ ∀ u ∈ Set.univ.pi (fun _ : Fin (routeMAmbient M) => Set.Icc (0 : ℝ) δ),
      interiorLiveUnit ha h0r h0c u ≤ B := by
  have hcont : Continuous (interiorLiveUnit ha h0r h0c) := continuous_interiorLiveUnit ha h0r h0c
  have hcpt : IsCompact (Set.univ.pi (fun _ : Fin (routeMAmbient M) => Set.Icc (0 : ℝ) δ)) :=
    isCompact_univ_pi (fun _ => isCompact_Icc)
  rcases (Set.univ.pi (fun _ : Fin (routeMAmbient M) => Set.Icc (0 : ℝ) δ)).eq_empty_or_nonempty
    with he | hne
  · exact ⟨1, one_pos, fun u hu => absurd (he ▸ hu) (Set.mem_empty_iff_false u).mp⟩
  · obtain ⟨u0, _, hu0⟩ := hcpt.exists_isMaxOn hne hcont.continuousOn
    exact ⟨max 1 (interiorLiveUnit ha h0r h0c u0), lt_of_lt_of_le one_pos (le_max_left _ _),
      fun u hu => le_trans (hu0 hu) (le_max_right _ _)⟩

/-- **`ldu_Ubound`** — the full `NodeAchieverChart.Ubound` field, CONSUMING the a.e.-positivity atom
`hpos` (the genm-upolylive deliverable: `∀ᵐ u, 0 < interiorLiveUnit …`). The box bound is proven here
(`ldu_Uval_le_on_box`); the positivity conjunct is restricted to the box (`ae_restrict_of_ae hpos`).
Matches the contract's frozen `interiorLive_Ubound` shape (modulo the extra `hpos` input genm-r1lower
threads from genm-upolylive). -/
theorem ldu_Ubound (ha : StructAdm M (tach M))
    (h0r : 0 < Text M (tach M) 2) (h0c : 0 < Wext M 2)
    (hpos : ∀ᵐ u, 0 < interiorLiveUnit ha h0r h0c u) :
    ∀ δ : ℝ, ∃ B : ℝ, 0 < B ∧
      (∀ u ∈ Set.univ.pi (fun _ : Fin (routeMAmbient M) => Set.Icc (0 : ℝ) δ),
        interiorLiveUnit ha h0r h0c u ≤ B) ∧
      ∀ᵐ u ∂(volume.restrict
          (Set.univ.pi (fun _ : Fin (routeMAmbient M) => Set.Icc (0 : ℝ) δ))),
        0 < interiorLiveUnit ha h0r h0c u := by
  intro δ
  obtain ⟨B, hB0, hBle⟩ := ldu_Uval_le_on_box ha h0r h0c δ
  exact ⟨B, hB0, hBle, ae_restrict_of_ae hpos⟩

end DLNFibre.DLN.RLCT
