import DLNFibre.DLN.RLCT.Validate.RouteMInteriorDeepRank0Gen
import DLNFibre.DLN.RLCT.Validate.RouteMInteriorLiveGenAtom
import DLNFibre.DLN.RLCT.Validate.RouteMInteriorLiveGenAnalytic
import DLNFibre.DLN.RLCT.Validate.RouteMInteriorLiveGenWire
import DLNFibre.DLN.RLCT.Validate.RouteMUPolyLive
import DLNFibre.DLN.RLCT.Validate.RouteMAchieverWitnessInterior
import DLNFibre.DLN.RLCT.Validate.RouteMGenLeafIntegrand

/-!
# `RouteMInteriorDeepRank0GenAtom` — the ASSEMBLED general-`L` `deepRank = 0` box-divergence ATOM

The DOWNSTREAM join for the general-`L` `deepRank = 0` interior handler (the general-`L` lift of
`RouteMInteriorDeepRank0Atom`, `Fin (2 + 1)`-pinned). The re-pivot CHART machinery is DONE
sorry-free upstream in `RouteMInteriorDeepRank0Gen` (`eDeepRank0PhiGen`, `eDeepRank0_abs_detGen`,
`eDeepRank0_diffGen`, `routeMCore_eDeepRank0PhiGen`, `eDeepRank0PhiGen_factor`). This module closes
the remaining gate — injectivity + the analytic leaf fields — and assembles the `NodeAchieverChart`
bundle, the box-divergence atom, and the `deepRank = 0` consumer form.

## The pivot alignment (the honest scope)

The chart binds an interior E-active slot `p₀ = eBlockPivotGen k` at a boundary `k`, `k.val ≠ L-1`.
The a.e.-positivity of the unit is witnessed at the interior-drop witness `wInt M ha (k+1)`, at
which the E-fixed decoder COLLAPSES to the plain live decoder
(`readE (wInt (k+1)) ⟨k⟩ = EfixedReaderKGen k`,
both the `(0,0)`-pivot indicator). The surviving `Hmat 0 = 1` entry threads from pivot `k+1` to the
leaf, so the witness needs the FULL suffix survival data at `k+1` (`Text (k+2) < Text (k+1)` +
`∀ b, k+1 ≤ b → b < L → Text (b+1) < Wext b`). These are exactly the `InteriorDrop`-pivot data. So
the consumer must ALIGN the chart boundary `k = p* - 1` with the `InteriorDrop` pivot `p*`
(decorrelated Codex-xhigh flagged the trap: forcing `p = k+1` for an arbitrary chart `k` is UNSOUND
— a `deepRank = 0` interior config need not drop tail columns from an arbitrary interior boundary).

Axiom profile target: `routeMCore_box_diverges_eDeepRank0Gen` = `[propext, Classical.choice,
Quot.sound, monomial_rlct]` (clean-three + the single S2 cited axiom).
-/

open MeasureTheory
open scoped ENNReal BigOperators
open MvPolynomial Matrix

namespace DLNFibre.DLN.RLCT

variable {L : ℕ}

/-! ## Step (b) — the E-pivot injectivity gate `det (readK (kLDU (pbo p₀ u)) k) ≠ 0` -/

/-- **The recovered K-block is nonsingular at EVERY boundary** for `y = kLDU (pbo p₀ u)` with `u`
all-nonzero and `p₀ ∈ activeMGen` (the pivot-generic lift of `detK_ne_zero_gen`). Via the K-monomial
det (`readK_kLDU_det`), each diagonal factor `= readK (pbo p₀ u) k i i = readK u k i i` (nonzero on
the all-nonzero domain, `readK_pbo_allGen_at` + `u_diagAxisGen`). -/
theorem detK_ne_zero_gen_at (M : Fin (L + 1) → ℕ) (ha : StructAdm M (tach M))
    (p₀ : Fin (routeMAmbient M)) (hp₀ : p₀ ∈ activeMGen M ha)
    (u : Fin (routeMAmbient M) → ℝ) (hu : ∀ j, u j ≠ 0) (k : Fin L) :
    (Matrix.of (readK M (tach M) ha
        (kLDU M (tach M) ha (pivotBlowupOn (activeMGen M ha) p₀ u)) k)).det ≠ 0 := by
  rw [readK_kLDU_det M (tach M) ha _ k, Finset.prod_ne_zero_iff]
  intro i _
  show (matrixSplit (Matrix.of (readK M (tach M) ha
    (pivotBlowupOn (activeMGen M ha) p₀ u) k))).2.1 i ≠ 0
  show (Matrix.of (readK M (tach M) ha
    (pivotBlowupOn (activeMGen M ha) p₀ u) k)) i i ≠ 0
  rw [Matrix.of_apply, readK_pbo_allGen_at M ha p₀ hp₀ u k i i]
  exact hu (readKslot M ha k i i)

/-- **`pbo p₀ u` is all-nonzero** for `u` all-nonzero and any pivot `p₀ ∈ activeMGen` —
`pivotBlowupOn`
scales by the pivot coord (nonzero) or fixes a coord, so every output coord is a product of nonzero
coords. Pivot-generic lift of `pbo_all_nonzero_of_mem`. -/
theorem pbo_all_nonzero_at (M : Fin (L + 1) → ℕ) (ha : StructAdm M (tach M))
    (p₀ : Fin (routeMAmbient M)) (u : Fin (routeMAmbient M) → ℝ) (hu : ∀ j, u j ≠ 0)
    (q : Fin (routeMAmbient M)) :
    pivotBlowupOn (activeMGen M ha) p₀ u q ≠ 0 := by
  rw [pivotBlowupOn]
  split
  · exact hu _
  · split
    · exact mul_ne_zero (hu _) (hu _)
    · exact hu _

/-! ## Step (b) — the E-pivot chart injectivity

`InjOn (eDeepRank0PhiGen k p₀ …) {u | u p₀ ≠ 0 ∧ ∀ j, u j ≠ 0}` via the factorization
`eDeepRank0PhiGen = (fun y => BchartLeafGen (kLDU y)) ∘ pbo p₀` (`eDeepRank0PhiGen_factor`):
`pbo p₀` injective off `{u p₀ = 0}` (`pivotBlowupOn_injOn`); `kLDU` injective on the all-nonzero
blowup image (`kLDU_inj_of_nonzeroGen`); `BchartLeafGen` injective via `BchartLeafGen_inj_of_detK`
with the per-boundary det gate `detK_ne_zero_gen_at`. -/

/-- **The E-pivot chart is injective** on `{u | u p₀ ≠ 0 ∧ ∀ j, u j ≠ 0}`, `p₀ = eBlockPivotGen k`.
The general-`L` lift of `eDeepRank0_injOn`. -/
theorem eDeepRank0_injOnGen (M : Fin (L + 1) → ℕ) (ha : StructAdm M (tach M)) (k : Fin L)
    (hk : k.val ≠ L - 1) (hdr0 : Text M (tach M) L = 0)
    (hr : 0 < Text M (tach M) (k.val + 1) - Text M (tach M) (k.val + 2))
    (hc : 0 < Wext M (k.val + 1) - Text M (tach M) (k.val + 2))
    (hp1 : Text M (tach M) (k.val + 1 + 1) ≤ Text M (tach M) (k.val + 1))
    (hp2 : Text M (tach M) (k.val + 1 + 1) ≤ Wext M (k.val + 1)) :
    Set.InjOn (eDeepRank0PhiGen M ha k (eBlockPivotGen M ha k hr hc) hp1 hp2)
      {u : Fin (routeMAmbient M) → ℝ | u (eBlockPivotGen M ha k hr hc) ≠ 0 ∧ ∀ j, u j ≠ 0} := by
  set p₀ := eBlockPivotGen M ha k hr hc with hp₀
  have hp₀mem : p₀ ∈ activeMGen M ha := eBlockPivotGen_mem_activeMGen M ha k hk hr hc
  have hL : 0 < L := lt_of_le_of_lt (Nat.zero_le k.val) k.isLt
  -- work on the domain set
  intro u hu u' hu' heq
  set pbo := pivotBlowupOn (activeMGen M ha) p₀ with hpbo
  -- the factorization
  have hfact := eDeepRank0PhiGen_factor M ha k hk hdr0 hr hc hp1 hp2
  rw [hfact] at heq
  simp only [Function.comp_apply] at heq
  -- `BchartLeafGen` injective on `kLDU (pbo u)`: use the per-boundary det gate + the weakened core
  have hdetK : ∀ kk : Fin L,
      (Matrix.of (readK M (tach M) ha (kLDU M (tach M) ha (pbo u)) kk)).det ≠ 0 :=
    fun kk => detK_ne_zero_gen_at M ha p₀ hp₀mem u hu.2 kk
  have hB : kLDU M (tach M) ha (pbo u) = kLDU M (tach M) ha (pbo u') :=
    BchartLeafGen_inj_of_detK M ha hL _ _ hdetK heq
  -- `kLDU` injective off the zero locus (`pbo u` all-nonzero)
  have hpboeq : pbo u = pbo u' :=
    kLDU_inj_of_nonzeroGen M ha _ _ (pbo_all_nonzero_at M ha p₀ u hu.2) hB
  -- `pbo` injective off `{u p₀ = 0}`
  refine (pivotBlowupOn_injOn (activeMGen M ha) p₀ Set.univ) ⟨Set.mem_univ _, ?_⟩
    ⟨Set.mem_univ _, ?_⟩ hpboeq
  · exact hu.1
  · exact hu'.1

/-! ## Step (c) analytics — continuity of `eDeepRank0UnitGen`

`eDeepRank0UnitGen x = VvalGen (x p₀) M tach (genBlkFlatEfpKGen k (kLDU x)) hle = sqSumHmat0` of the
chain (`VvalGen_eq_sqSumHmat0`); `Hmat 0` continuous via `continuous_Hmat0_gen` + the
block-continuity of the E-fixed decoder over `kLDU x`. The block-continuity mirrors
`genBlkContinuous_liveGen`, the pivot boundary `k+1`'s `Rmat` override via `Function.update`. -/

/-- **The E-fixed decoder over `kLDU x` is block-continuous in `x`.** `Bmat/Nblk/Wblk` are the
struct
decoder's readers of `kLDU x` (continuous); `Rmat` is the `Function.update` at `k+1` (off `k+1` the
struct `Rmat`, at `k+1` `rmatPad (EfixedReaderKGen k (kLDU x))`); `Rfin = 0`. -/
theorem genBlkContinuous_efpGen (M : Fin (L + 1) → ℕ) (ha : StructAdm M (tach M)) (k : Fin L)
    (hp1 : Text M (tach M) (k.val + 1 + 1) ≤ Text M (tach M) (k.val + 1))
    (hp2 : Text M (tach M) (k.val + 1 + 1) ≤ Wext M (k.val + 1)) :
    GenBlkContinuous M (tach M)
      (fun x => genBlkFlatEfpKGen M ha k hp1 hp2 (kLDU M (tach M) ha x)) := by
  have hkcont : Continuous (kLDU M (tach M) ha) := (differentiable_kLDUGen M (tach M) ha).continuous
  have hkapp : ∀ q, Continuous (fun x : Fin (routeMAmbient M) → ℝ => kLDU M (tach M) ha x q) :=
    fun q => (continuous_apply q).comp hkcont
  have hreadK : ∀ k' : Fin L, Continuous (fun x => readK M (tach M) ha (kLDU M (tach M) ha x) k') :=
    fun k' => continuous_matrix (fun i j => hkapp _)
  have hreadX : ∀ k' : Fin L, Continuous (fun x => readX M (tach M) ha (kLDU M (tach M) ha x) k') :=
    fun k' => continuous_matrix (fun i j => hkapp _)
  have hreadN : ∀ k' : Fin L, Continuous (fun x => readN M (tach M) ha (kLDU M (tach M) ha x) k') :=
    fun k' => continuous_matrix (fun i j => hkapp _)
  have hreadE : ∀ k' : Fin L, Continuous (fun x => readE M (tach M) ha (kLDU M (tach M) ha x) k') :=
    fun k' => continuous_matrix (fun i j => hkapp _)
  have hreadW : ∀ (k' : Fin L) (hk : k'.val + 1 < L),
      Continuous (fun x => readW M (tach M) ha (kLDU M (tach M) ha x) k' hk) :=
    fun k' hk => continuous_matrix (fun i j => hkapp _)
  refine ⟨fun j => ?_, fun j => ?_, fun j => ?_, fun j => ?_, fun j => ?_⟩
  · -- Bmat = genBlkFlatLive's = genBlkFlatStruct's
    show Continuous (fun x => (genBlkFlatStruct M (tach M) ha (kLDU M (tach M) ha x)).Bmat j)
    match j with
    | 0 => exact continuous_const
    | (jj + 1) =>
      simp only [genBlkFlatStruct]
      by_cases hjj : jj < L
      · simp only [dif_pos hjj]
        exact continuous_bmatStack (jj + 1) (ha.hdesc jj hjj) (hreadK ⟨jj, hjj⟩) (hreadX ⟨jj, hjj⟩)
      · simp only [dif_neg hjj]; exact continuous_const
  · -- Nblk
    show Continuous (fun x => (genBlkFlatStruct M (tach M) ha (kLDU M (tach M) ha x)).Nblk j)
    match j with
    | 0 => exact continuous_const
    | (jj + 1) =>
      simp only [genBlkFlatStruct]
      by_cases hjj : jj < L
      · simp only [dif_pos hjj]; exact hreadN ⟨jj, hjj⟩
      · simp only [dif_neg hjj]; exact continuous_const
  · -- Wblk
    show Continuous (fun x => (genBlkFlatStruct M (tach M) ha (kLDU M (tach M) ha x)).Wblk j)
    match j with
    | 0 => exact continuous_const
    | (jj + 1) =>
      simp only [genBlkFlatStruct]
      by_cases hjj : jj < L
      · simp only [dif_pos hjj]
        by_cases hjj2 : jj + 1 < L
        · simp only [dif_pos hjj2]; exact hreadW ⟨jj, hjj⟩ hjj2
        · simp only [dif_neg hjj2]; exact continuous_const
      · simp only [dif_neg hjj]; exact continuous_const
  · -- Rmat = Function.update (genBlkFlatLive 0 (kLDU x)).Rmat (k+1) (rmatPad (EfixedReaderKGen k))
    show Continuous (fun x => (genBlkFlatEfpKGen M ha k hp1 hp2 (kLDU M (tach M) ha x)).Rmat j)
    show Continuous (fun x => Function.update
      (genBlkFlatLive M (tach M) ha 0 (kLDU M (tach M) ha x)).Rmat (k.val + 1)
      (rmatPad M (tach M) (k.val + 1) hp1 hp2 (EfixedReaderKGen M ha k (kLDU M (tach M) ha x))) j)
    by_cases hj : j = k.val + 1
    · subst hj
      have hrw : (fun x => Function.update
            (genBlkFlatLive M (tach M) ha 0 (kLDU M (tach M) ha x)).Rmat (k.val + 1)
            (rmatPad M (tach M) (k.val + 1) hp1 hp2 (EfixedReaderKGen M ha k (kLDU M (tach M) ha x)))
            (k.val + 1))
          = fun x => rmatPad M (tach M) (k.val + 1) hp1 hp2
              (EfixedReaderKGen M ha k (kLDU M (tach M) ha x)) := by
        funext x; rw [Function.update_self]
      rw [hrw]
      apply continuous_rmatPad (k.val + 1) hp1 hp2
      exact continuous_matrix (fun i j => by
        by_cases hij : i.val = 0 ∧ j.val = 0
        · simp only [EfixedReaderKGen, Matrix.of_apply, if_pos hij]; exact continuous_const
        · simp only [EfixedReaderKGen, Matrix.of_apply, if_neg hij]
          exact (hreadE k).matrix_elem i j)
    · have hrw : (fun x => Function.update
            (genBlkFlatLive M (tach M) ha 0 (kLDU M (tach M) ha x)).Rmat (k.val + 1)
            (rmatPad M (tach M) (k.val + 1) hp1 hp2
              (EfixedReaderKGen M ha k (kLDU M (tach M) ha x))) j)
          = fun x => (genBlkFlatStruct M (tach M) ha (kLDU M (tach M) ha x)).Rmat j := by
        funext x; rw [Function.update_of_ne hj]; rfl
      rw [hrw]
      match j with
      | 0 => exact continuous_const
      | (jj + 1) =>
        simp only [genBlkFlatStruct]
        by_cases hjj : jj < L
        · simp only [dif_pos hjj]
          exact continuous_rmatPad (jj + 1) (ha.hdesc jj hjj) (ha.hub jj) (hreadE ⟨jj, hjj⟩)
        · simp only [dif_neg hjj]; exact continuous_const
  · -- Rfin = (genBlkFlatLive 0 (kLDU x)).Rfin = 0 (rfin = 0, so BOTH `dite` branches are `0`)
    change Continuous (fun x => (genBlkFlatLive M (tach M) ha 0 (kLDU M (tach M) ha x)).Rfin j)
    have hrw : (fun x => (genBlkFlatLive M (tach M) ha 0 (kLDU M (tach M) ha x)).Rfin j)
        = fun _ => 0 := by
      funext x
      simp only [genBlkFlatLive]
      split
      · rename_i h; subst h; simp
      · rfl
    rw [hrw]; exact continuous_const

/-- **`eDeepRank0UnitGen` is continuous** at general `L` — `= sqSumHmat0` of the chain
(`VvalGen_eq_sqSumHmat0`), continuous via `continuous_Hmat0_gen` + `genBlkContinuous_efpGen` + the
radial scalar `x ↦ x p₀`. -/
theorem continuous_eDeepRank0UnitGen (M : Fin (L + 1) → ℕ) (ha : StructAdm M (tach M)) (k : Fin L)
    (p₀ : Fin (routeMAmbient M))
    (hp1 : Text M (tach M) (k.val + 1 + 1) ≤ Text M (tach M) (k.val + 1))
    (hp2 : Text M (tach M) (k.val + 1 + 1) ≤ Wext M (k.val + 1)) :
    Continuous (eDeepRank0UnitGen M ha k p₀ hp1 hp2) := by
  have hg : Continuous (fun x : Fin (routeMAmbient M) → ℝ => x p₀) := continuous_apply _
  have hHmat0 := continuous_Hmat0_gen (genBlkContinuous_efpGen M ha k hp1 hp2) hg
    (hleStruct M (tach M) ha)
  have hsq : Continuous (fun x => ∑ i, ∑ j,
      ((show Matrix (Fin (Text M (tach M) 0)) (Fin (Wext M L)) ℝ
          from (chainOfMt (x p₀) M (tach M)
            (genBlkFlatEfpKGen M ha k hp1 hp2 (kLDU M (tach M) ha x))
              (hleStruct M (tach M) ha)).toChain.Hmat 0 (Nat.zero_le L))
        i j) ^ 2) :=
    continuous_finset_sum _ (fun i _ => continuous_finset_sum _ (fun j _ =>
      (hHmat0.matrix_elem i j).pow 2))
  refine hsq.congr (fun x => ?_)
  rw [eDeepRank0UnitGen, VvalGen_eq_sqSumHmat0, sqSumHmat0]
  rfl

/-- **`eDeepRank0UnitGen` is measurable** (continuity). -/
theorem measurable_eDeepRank0UnitGen (M : Fin (L + 1) → ℕ) (ha : StructAdm M (tach M)) (k : Fin L)
    (p₀ : Fin (routeMAmbient M))
    (hp1 : Text M (tach M) (k.val + 1 + 1) ≤ Text M (tach M) (k.val + 1))
    (hp2 : Text M (tach M) (k.val + 1 + 1) ≤ Wext M (k.val + 1)) :
    Measurable (eDeepRank0UnitGen M ha k p₀ hp1 hp2) :=
  (continuous_eDeepRank0UnitGen M ha k p₀ hp1 hp2).measurable

/-! ## Step (c) analytics — `eDeepRank0PhiGen 0 = 0` + image containment -/

/-- **The E-fixed chart-params at radial `0`** — `chartParamsGen 0 (genBlkFlatEfpKGen k 0) = 0`.
`Agen 0` reads `Nblk/Wblk/Cgen(·+1)`; the Efp and live decoders share `Bmat/Nblk/Wblk`, and the
`0 • Rmat` term of `Cgen 0` kills the only (Rmat-override) difference. General-`L` lift of
`chartParamsGen_Efp_zero`. -/
theorem chartParamsGen_EfpGen_zero (M : Fin (L + 1) → ℕ) (ha : StructAdm M (tach M)) (k : Fin L)
    (hp1 : Text M (tach M) (k.val + 1 + 1) ≤ Text M (tach M) (k.val + 1))
    (hp2 : Text M (tach M) (k.val + 1 + 1) ≤ Wext M (k.val + 1)) :
    chartParamsGen (0 : ℝ) M (tach M) (genBlkFlatEfpKGen M ha k hp1 hp2 0) (hleStruct M (tach M) ha)
      = (fun _ => 0 : Params M) := by
  rw [← chartParamsGen_live_zero M (tach M) ha 0]
  funext s
  change Matrix.reindex _ _ (Agen 0 M (tach M) (genBlkFlatEfpKGen M ha k hp1 hp2 0) _ s.val)
    = Matrix.reindex _ _ (Agen 0 M (tach M) (genBlkFlatLive M (tach M) ha 0 0) _ s.val)
  congr 1
  refine Agen_congr M (tach M) (hleStruct M (tach M) ha) 0 0 _ _ s.val rfl rfl ?_
  by_cases hs : s.val + 1 < L
  · -- `Cgen 0 (s+1) = Bmat(s+1)·chainQ(Nblk(s+1))` (the `0 • Rmat` term dies); Efp and live share
    -- `Bmat/Nblk` (both `genBlkFlatLive 0`'s), matched explicitly.
    rw [Cgen, Cgen, dif_pos hs, dif_pos hs, zero_smul, zero_smul, add_zero, add_zero,
      genBlkFlatEfpKGen_Bmat_succ M ha k hp1 hp2 0 s.val (by omega),
      genBlkFlatEfpKGen_Nblk_succ M ha k hp1 hp2 0 s.val (by omega),
      genBlkFlatLive_Bmat_succ M (tach M) ha 0 0 s.val (by omega),
      genBlkFlatLive_Nblk_succ M (tach M) ha 0 0 s.val (by omega)]
  · rw [Cgen, Cgen, dif_neg hs, dif_neg hs, zero_smul, zero_smul]

/-- **`eDeepRank0PhiGen 0 = 0`** (the deepest point) — `kLDU 0 = 0`, the radial scalar `0 p₀ = 0`,
and `chartParamsGen 0 (genBlkFlatEfpKGen k 0) = 0`. -/
theorem eDeepRank0PhiGen_zero (M : Fin (L + 1) → ℕ) (ha : StructAdm M (tach M)) (k : Fin L)
    (p₀ : Fin (routeMAmbient M))
    (hp1 : Text M (tach M) (k.val + 1 + 1) ≤ Text M (tach M) (k.val + 1))
    (hp2 : Text M (tach M) (k.val + 1 + 1) ≤ Wext M (k.val + 1)) :
    eDeepRank0PhiGen M ha k p₀ hp1 hp2 0 = 0 := by
  change phiEfpAt M ha k p₀ hp1 hp2 (kLDU M (tach M) ha 0) = 0
  rw [kLDU_zeroGen M ha]
  change phiGen ((0 : Fin (routeMAmbient M) → ℝ) p₀) M (tach M)
    (genBlkFlatEfpKGen M ha k hp1 hp2 0) (hleStruct M (tach M) ha) = 0
  rw [Pi.zero_apply, phiGen, chartParamsGen_EfpGen_zero M ha k hp1 hp2]
  exact paramsEquivFlat_deepest M

/-- **Image containment** — a small source box `[0,δ]^N` maps into `cubeBox N ε` (continuity of
`eDeepRank0PhiGen` via `eDeepRank0_diffGen` + `eDeepRank0PhiGen 0 = 0`). General-`L` lift of
`eDeepRank0_image`, structure mirrored from `ldu_imageGen`. -/
theorem eDeepRank0_imageGen (M : Fin (L + 1) → ℕ) (ha : StructAdm M (tach M)) (k : Fin L)
    (hk : k.val ≠ L - 1) (hdr0 : Text M (tach M) L = 0)
    (hr : 0 < Text M (tach M) (k.val + 1) - Text M (tach M) (k.val + 2))
    (hc : 0 < Wext M (k.val + 1) - Text M (tach M) (k.val + 2))
    (hp1 : Text M (tach M) (k.val + 1 + 1) ≤ Text M (tach M) (k.val + 1))
    (hp2 : Text M (tach M) (k.val + 1 + 1) ≤ Wext M (k.val + 1)) :
    ∀ ε : ℝ, 0 < ε →
      ∃ δ > 0, eDeepRank0PhiGen M ha k (eBlockPivotGen M ha k hr hc) hp1 hp2 ''
        (Set.univ.pi (fun _ : Fin (routeMAmbient M) => Set.Icc (0 : ℝ) δ))
        ⊆ cubeBox (routeMAmbient M) ε := by
  intro ε hε
  have hcont : Continuous (eDeepRank0PhiGen M ha k (eBlockPivotGen M ha k hr hc) hp1 hp2) :=
    (eDeepRank0_diffGen M ha k hk hdr0 hr hc hp1 hp2).continuous
  have hopen : IsOpen (Set.univ.pi (fun _ : Fin (routeMAmbient M) => Set.Ioo (-ε) ε)) :=
    isOpen_set_pi Set.finite_univ (fun _ _ => isOpen_Ioo)
  have hmem : (0 : Fin (routeMAmbient M) → ℝ)
      ∈ eDeepRank0PhiGen M ha k (eBlockPivotGen M ha k hr hc) hp1 hp2 ⁻¹'
        (Set.univ.pi (fun _ : Fin (routeMAmbient M) => Set.Ioo (-ε) ε)) := by
    simp only [Set.mem_preimage, eDeepRank0PhiGen_zero M ha k (eBlockPivotGen M ha k hr hc) hp1 hp2,
      Set.mem_pi, Set.mem_univ, true_implies, Set.mem_Ioo, Pi.zero_apply]
    exact fun i => ⟨by linarith, hε⟩
  obtain ⟨δ, hδ, hsub⟩ := cubeBox_subset_of_isOpen (hopen.preimage hcont) hmem
  refine ⟨δ, hδ, ?_⟩
  rintro y ⟨x, hx, rfl⟩
  have hxcube : x ∈ cubeBox (routeMAmbient M) δ := by
    simp only [cubeBox, Set.mem_pi, Set.mem_univ, true_implies, Set.mem_Icc] at hx ⊢
    intro i; exact ⟨le_trans (by linarith [hδ]) (hx i).1, (hx i).2⟩
  have hxmem : eDeepRank0PhiGen M ha k (eBlockPivotGen M ha k hr hc) hp1 hp2 x
      ∈ Set.univ.pi (fun _ : Fin (routeMAmbient M) => Set.Ioo (-ε) ε) :=
    Set.mem_preimage.mp (hsub hxcube)
  simp only [cubeBox, Set.mem_pi, Set.mem_univ, true_implies, Set.mem_Icc, Set.mem_Ioo] at hxmem ⊢
  exact fun i => ⟨le_of_lt (hxmem i).1, le_of_lt (hxmem i).2⟩

/-- **The box bound** `eDeepRank0UnitGen ≤ B` on `[0,δ]^N` (continuity on a compact box). -/
theorem eDeepRank0Unit_le_on_boxGen (M : Fin (L + 1) → ℕ) (ha : StructAdm M (tach M)) (k : Fin L)
    (p₀ : Fin (routeMAmbient M))
    (hp1 : Text M (tach M) (k.val + 1 + 1) ≤ Text M (tach M) (k.val + 1))
    (hp2 : Text M (tach M) (k.val + 1 + 1) ≤ Wext M (k.val + 1)) (δ : ℝ) :
    ∃ B, 0 < B ∧ ∀ u ∈ Set.univ.pi (fun _ : Fin (routeMAmbient M) => Set.Icc (0 : ℝ) δ),
      eDeepRank0UnitGen M ha k p₀ hp1 hp2 u ≤ B := by
  have hcont : Continuous (eDeepRank0UnitGen M ha k p₀ hp1 hp2) :=
    continuous_eDeepRank0UnitGen M ha k p₀ hp1 hp2
  have hcpt : IsCompact (Set.univ.pi (fun _ : Fin (routeMAmbient M) => Set.Icc (0 : ℝ) δ)) :=
    isCompact_univ_pi (fun _ => isCompact_Icc)
  rcases (Set.univ.pi (fun _ : Fin (routeMAmbient M) => Set.Icc (0 : ℝ) δ)).eq_empty_or_nonempty
    with he | hne
  · exact ⟨1, one_pos, fun u hu => absurd (he ▸ hu) (Set.mem_empty_iff_false u).mp⟩
  · obtain ⟨u0, _, hu0⟩ := hcpt.exists_isMaxOn hne hcont.continuousOn
    exact ⟨max 1 (eDeepRank0UnitGen M ha k p₀ hp1 hp2 u0),
      lt_of_lt_of_le one_pos (le_max_left _ _),
      fun u hu => le_trans (hu0 hu) (le_max_right _ _)⟩

/-! ## Step (c) analytics — a.e.-positivity of `eDeepRank0UnitGen` via a named nonzero polynomial

Mirror `interiorLiveUnit_ae_posGen`: encode `eDeepRank0UnitGen` as `eval u` of a NAMED nonzero
polynomial `UPolyEfpGen`, then `MvPolynomial.ae_eval_ne_zero` gives the zero set is null, and
`VvalGen_nonneg` upgrades `≠ 0` to `0 <`. The nonzero witness is the interior-drop witness
`wInt (k+1)` where the Efp decoder COLLAPSES to the plain live decoder
(`readE (wInt (k+1)) ⟨k⟩ = EfixedReaderKGen k`); the surviving `Hmat 0 = 1` entry threads from pivot
`k+1` (the survival machinery, `Rfin`-blind). -/

/-- **The generic (poly) E-fixed-pivot reader** at boundary `k` — `CommRing`-generic
`EfixedReaderKGen`:
the pivot `(0,0)` entry is the constant `1`, off `(0,0)` the coordinate `readE x ⟨k⟩`. -/
noncomputable def EfixedReaderKGenP (M : Fin (L + 1) → ℕ) (ha : StructAdm M (tach M)) (k : Fin L)
    {𝕜 : Type} [CommRing 𝕜] (x : Fin (routeMAmbient M) → 𝕜) :
    Matrix (Fin (Text M (tach M) (k.val + 1) - Text M (tach M) (k.val + 2)))
      (Fin (Wext M (k.val + 1) - Text M (tach M) (k.val + 2))) 𝕜 :=
  Matrix.of fun i j =>
    if i.val = 0 ∧ j.val = 0 then 1 else readE M (tach M) ha x k i j

/-- **The generic Efp reader maps to the target one** under a ring hom `f` when `f (vp q) = vr q`.
-/
theorem EfixedReaderKGenP_map (M : Fin (L + 1) → ℕ) (ha : StructAdm M (tach M)) (k : Fin L)
    {𝕜 𝕜' : Type} [CommRing 𝕜] [CommRing 𝕜']
    (vp : Fin (routeMAmbient M) → 𝕜) (vr : Fin (routeMAmbient M) → 𝕜') (f : 𝕜 →+* 𝕜')
    (hv : ∀ q, f (vp q) = vr q) :
    Matrix.map (EfixedReaderKGenP M ha k vp) f = EfixedReaderKGenP M ha k vr := by
  ext i j
  simp only [Matrix.map_apply, EfixedReaderKGenP, Matrix.of_apply]
  split
  · exact map_one f
  · exact hv _

/-- **The generic Efp reader over ℝ is dr0build's `EfixedReaderKGen`** (same formula). -/
theorem EfixedReaderKGenP_eq (M : Fin (L + 1) → ℕ) (ha : StructAdm M (tach M)) (k : Fin L)
    (x : Fin (routeMAmbient M) → ℝ) :
    EfixedReaderKGenP M ha k x = EfixedReaderKGen M ha k x := by
  ext i j; simp only [EfixedReaderKGenP, EfixedReaderKGen, Matrix.of_apply]

/-- **The generic (poly) E-fixed-pivot decoder** `genBlkFlatEfpKGenP k x : GenBlk M (tach M) 𝕜` — the
generic live decoder `genBlkFlatLiveGen ha 0 x` with boundary `k+1`'s `Rmat` overridden to
`rmatPad (EfixedReaderKGenP k x)`. -/
noncomputable def genBlkFlatEfpKGenP (M : Fin (L + 1) → ℕ) (ha : StructAdm M (tach M)) (k : Fin L)
    (hp1 : Text M (tach M) (k.val + 1 + 1) ≤ Text M (tach M) (k.val + 1))
    (hp2 : Text M (tach M) (k.val + 1 + 1) ≤ Wext M (k.val + 1))
    {𝕜 : Type} [CommRing 𝕜] (x : Fin (routeMAmbient M) → 𝕜) : GenBlk M (tach M) 𝕜 where
  Bmat := (genBlkFlatLiveGen M (tach M) ha 0 x).Bmat
  Nblk := (genBlkFlatLiveGen M (tach M) ha 0 x).Nblk
  Wblk := (genBlkFlatLiveGen M (tach M) ha 0 x).Wblk
  Rmat := Function.update (genBlkFlatLiveGen M (tach M) ha 0 x).Rmat (k.val + 1)
    (rmatPad M (tach M) (k.val + 1) hp1 hp2 (EfixedReaderKGenP M ha k x)
      : Matrix (Fin (Text M (tach M) (k.val + 1))) (Fin (Wext M (k.val + 1))) 𝕜)
  Rfin := (genBlkFlatLiveGen M (tach M) ha 0 x).Rfin

/-- **The generic Efp decoder over ℝ is dr0build's `genBlkFlatEfpKGen`** (definitional — same
fields). -/
theorem genBlkFlatEfpKGenP_eq_efp (M : Fin (L + 1) → ℕ) (ha : StructAdm M (tach M)) (k : Fin L)
    (hp1 : Text M (tach M) (k.val + 1 + 1) ≤ Text M (tach M) (k.val + 1))
    (hp2 : Text M (tach M) (k.val + 1 + 1) ≤ Wext M (k.val + 1))
    (x : Fin (routeMAmbient M) → ℝ) :
    genBlkFlatEfpKGenP M ha k hp1 hp2 x = genBlkFlatEfpKGen M ha k hp1 hp2 x := by
  unfold genBlkFlatEfpKGenP genBlkFlatEfpKGen
  rw [genBlkFlatLiveGen_eq_live, EfixedReaderKGenP_eq]

/-- **The Efp decoder's `GenBlkMap`** (poly → target under `f`) — the four `Bmat/Nblk/Wblk/Rfin`
fields
via `genBlkFlatLiveGen_genBlkMap_of` (`rfin = 0`); the `Rmat` override splits at `k+1` (natural via
`rmatPad_map` + `EfixedReaderKGenP_map`). -/
theorem genBlkFlatEfpKGenP_genBlkMap_of (M : Fin (L + 1) → ℕ) (ha : StructAdm M (tach M)) (k : Fin L)
    (hp1 : Text M (tach M) (k.val + 1 + 1) ≤ Text M (tach M) (k.val + 1))
    (hp2 : Text M (tach M) (k.val + 1 + 1) ≤ Wext M (k.val + 1))
    {𝕜 𝕜' : Type} [CommRing 𝕜] [CommRing 𝕜']
    (vp : Fin (routeMAmbient M) → 𝕜) (vr : Fin (routeMAmbient M) → 𝕜') (f : 𝕜 →+* 𝕜')
    (hv : ∀ q, f (vp q) = vr q) :
    GenBlkMap M (tach M) (genBlkFlatEfpKGenP M ha k hp1 hp2 vp)
      (genBlkFlatEfpKGenP M ha k hp1 hp2 vr) f := by
  have hbase : GenBlkMap M (tach M)
      (genBlkFlatLiveGen M (tach M) ha 0 vp) (genBlkFlatLiveGen M (tach M) ha 0 vr) f :=
    genBlkFlatLiveGen_genBlkMap_of M (tach M) ha vp vr f hv 0 0
      (by rw [Matrix.map_zero _ (map_zero _)])
  refine ⟨hbase.hBmat, hbase.hNblk, hbase.hWblk, ?_, hbase.hRfin⟩
  intro s
  change ((Function.update (genBlkFlatLiveGen M (tach M) ha 0 vp).Rmat (k.val + 1)
      (rmatPad M (tach M) (k.val + 1) hp1 hp2 (EfixedReaderKGenP M ha k vp))) s).map f
    = (Function.update (genBlkFlatLiveGen M (tach M) ha 0 vr).Rmat (k.val + 1)
      (rmatPad M (tach M) (k.val + 1) hp1 hp2 (EfixedReaderKGenP M ha k vr))) s
  by_cases hs : s = k.val + 1
  · subst hs
    rw [Function.update_self, Function.update_self, rmatPad_map,
      EfixedReaderKGenP_map M ha k vp vr f hv]
  · rw [Function.update_of_ne hs, Function.update_of_ne hs]
    exact hbase.hRmat s

/-- **The named nonzero polynomial `UPolyEfpGen`** — `sqSumHmat0` of the POLYNOMIAL Efp decoder
chain
(over `kLDUGen (Xvec)`, radial pivot `Xvec p₀`). `eval u UPolyEfpGen = eDeepRank0UnitGen u`. -/
noncomputable def UPolyEfpGen (M : Fin (L + 1) → ℕ) (ha : StructAdm M (tach M)) (k : Fin L)
    (p₀ : Fin (routeMAmbient M))
    (hp1 : Text M (tach M) (k.val + 1 + 1) ≤ Text M (tach M) (k.val + 1))
    (hp2 : Text M (tach M) (k.val + 1 + 1) ≤ Wext M (k.val + 1)) :
    MvPolynomial (Fin (routeMAmbient M)) ℝ :=
  sqSumHmat0 (chainOfMt
    (Xvec (routeMAmbient M) p₀) M (tach M)
    (genBlkFlatEfpKGenP M ha k hp1 hp2 (kLDUGen M (tach M) ha (Xvec (routeMAmbient M))))
    (hleStruct M (tach M) ha)).toChain

/-- **`eval u UPolyEfpGen = eDeepRank0UnitGen u`** at general `L`. `eval u` pushes through `∑∑·²`
and the
chain naturality identifies the poly Efp decoder chain (over `kLDUGen (Xvec)`) with the ℝ one (over
`kLDU u`); the ℝ side is `eDeepRank0UnitGen` by `VvalGen_eq_sqSumHmat0`. The poly pivot `Xvec p₀`
evals to `u p₀`. -/
theorem eval_UPolyEfpGen (M : Fin (L + 1) → ℕ) (ha : StructAdm M (tach M)) (k : Fin L)
    (p₀ : Fin (routeMAmbient M))
    (hp1 : Text M (tach M) (k.val + 1 + 1) ≤ Text M (tach M) (k.val + 1))
    (hp2 : Text M (tach M) (k.val + 1 + 1) ≤ Wext M (k.val + 1))
    (u : Fin (routeMAmbient M) → ℝ) :
    MvPolynomial.eval u (UPolyEfpGen M ha k p₀ hp1 hp2)
      = eDeepRank0UnitGen M ha k p₀ hp1 hp2 u := by
  have hmap : GenBlkMap M (tach M)
      (genBlkFlatEfpKGenP M ha k hp1 hp2 (kLDUGen M (tach M) ha (Xvec (routeMAmbient M))))
      (genBlkFlatEfpKGenP M ha k hp1 hp2 (kLDU M (tach M) ha u)) (MvPolynomial.eval u) :=
    genBlkFlatEfpKGenP_genBlkMap_of M ha k hp1 hp2
      (kLDUGen M (tach M) ha (Xvec (routeMAmbient M))) (kLDU M (tach M) ha u)
      (MvPolynomial.eval u) (kLDUGen_eval M (tach M) ha u)
  have hchain := chainOfMt_map hmap (Xvec (routeMAmbient M) p₀) (hleStruct M (tach M) ha)
  rw [eDeepRank0UnitGen, VvalGen_eq_sqSumHmat0,
    ← genBlkFlatEfpKGenP_eq_efp M ha k hp1 hp2 (kLDU M (tach M) ha u), UPolyEfpGen,
    sqSumHmat0_map _ (MvPolynomial.eval u), hchain, eval_Xvec u]

/-- **At the witness `wInt (k+1)` the E-fixed reader IS `readE (wInt (k+1)) ⟨k⟩`** — both are the
`(0,0)`-pivot indicator at boundary `k` (`EfixedReaderKGen` pins `(0,0) ↦ 1`, reads `readE`
elsewhere; `readE (wInt (k+1)) ⟨k⟩` is the pivot indicator at `p = k+1`). General-`L` lift of
`EfixedReader_wInt1`. -/
theorem EfixedReaderKGen_wInt (M : Fin (L + 1) → ℕ) (ha : StructAdm M (tach M)) (k : Fin L) :
    EfixedReaderKGen M ha k (wInt M ha (k.val + 1))
      = fun i j => readE M (tach M) ha (wInt M ha (k.val + 1)) k i j := by
  ext i j
  rw [EfixedReaderKGen, Matrix.of_apply, readE_wInt]
  by_cases hij : i.val = 0 ∧ j.val = 0
  · rw [if_pos hij, if_pos ⟨rfl, hij.1, hij.2⟩]
  · rw [if_neg hij, if_neg (fun h => hij ⟨h.2.1, h.2.2⟩)]

/-- **At the witness `wInt (k+1)` the Efp decoder IS the plain `genBlkFlatLive ha 0 (wInt (k+1))`**
— the
pivot `Rmat`-override collapses (the `Function.update` value equals the underlying `Rmat (k+1)`,
since
`EfixedReaderKGen k (wInt (k+1)) = readE (wInt (k+1)) ⟨k⟩`). General-`L` lift of
`genBlkFlatEfp_wInt1`. -/
theorem genBlkFlatEfpKGen_wInt (M : Fin (L + 1) → ℕ) (ha : StructAdm M (tach M)) (k : Fin L)
    (hp1 : Text M (tach M) (k.val + 1 + 1) ≤ Text M (tach M) (k.val + 1))
    (hp2 : Text M (tach M) (k.val + 1 + 1) ≤ Wext M (k.val + 1)) :
    genBlkFlatEfpKGen M ha k hp1 hp2 (wInt M ha (k.val + 1))
      = genBlkFlatLive M (tach M) ha 0 (wInt M ha (k.val + 1)) := by
  have hRmat : rmatPad M (tach M) (k.val + 1) hp1 hp2
        (EfixedReaderKGen M ha k (wInt M ha (k.val + 1)))
      = (genBlkFlatLive M (tach M) ha 0 (wInt M ha (k.val + 1))).Rmat (k.val + 1) := by
    rw [EfixedReaderKGen_wInt M ha k]
    rw [genBlkFlatLive_Rmat_succ M (tach M) ha 0 (wInt M ha (k.val + 1)) k.val k.isLt]
  unfold genBlkFlatEfpKGen
  rw [hRmat, Function.update_eq_self]

/-- **The Efp unit is nonzero at the interior-drop witness `wInt (k+1)`** (`p = k+1` the interior
pivot). At the witness the Efp decoder collapses to `genBlkFlatLive ha 0 (wInt (k+1))`
(`genBlkFlatEfpKGen_wInt`), `kLDU` fixes `wInt` (`kLDU_wIntGen`), and the surviving
`Hmat 0 (ρ,0) = 1` entry is built by the general-`L` survival machinery
(`Hmat_pivot`/`Hmat_row_thread`/`suffix_carrier`) on the `rfin = 0` decoder — verbatim from
`interiorLiveUnitGen_wInt_ne_zero`, specialised to the collapsed decoder + radial scalar. -/
theorem eDeepRank0UnitGen_wInt_ne_zero (M : Fin (L + 1) → ℕ) (ha : StructAdm M (tach M)) (k : Fin L)
    (hk : k.val ≠ L - 1) (p₀ : Fin (routeMAmbient M))
    (hp1 : Text M (tach M) (k.val + 1 + 1) ≤ Text M (tach M) (k.val + 1))
    (hp2 : Text M (tach M) (k.val + 1 + 1) ≤ Wext M (k.val + 1))
    (hML : 0 < Wext M L)
    (hr : Text M (tach M) (k.val + 2) < Text M (tach M) (k.val + 1))
    (hcd : ∀ b, k.val + 1 ≤ b → b < L → Text M (tach M) (b + 1) < Wext M b) :
    eDeepRank0UnitGen M ha k p₀ hp1 hp2 (wInt M ha (k.val + 1)) ≠ 0 := by
  rw [eDeepRank0UnitGen, kLDU_wIntGen M ha (k.val + 1), genBlkFlatEfpKGen_wInt M ha k hp1 hp2,
    VvalGen_eq_sqSumHmat0]
  set hle := hleStruct M (tach M) ha with hledef
  set u := wInt M ha (k.val + 1) p₀ with hudef
  set B := genBlkFlatLive M (tach M) ha 0 (wInt M ha (k.val + 1)) with hBdef
  set c := (chainOfMt u M (tach M) B hle).toChain with hcdef
  -- pivot `p = k+1` interior data (`k+1 < L` from `k ≠ L-1` + `k < L`)
  have hpL : k.val + 1 < L := by have := k.isLt; omega
  have hTdesc : ∀ s, s < k.val + 1 → Text M (tach M) (s + 1) ≤ Text M (tach M) s := by
    intro s hsp
    match s with
    | 0 => exact le_of_eq (Text0_eq_Text1_struct M (tach M) ha.h0).symm
    | (j + 1) => exact ha.hdesc j (by omega)
  have hTle : ∀ d a, a + d ≤ k.val + 1 → Text M (tach M) (a + d) ≤ Text M (tach M) a := by
    intro d
    induction d with
    | zero => intro a _; rw [Nat.add_zero]
    | succ e ih =>
      intro a ha'
      calc Text M (tach M) (a + (e + 1)) = Text M (tach M) ((a + e) + 1) := by ring_nf
        _ ≤ Text M (tach M) (a + e) := hTdesc (a + e) (by omega)
        _ ≤ Text M (tach M) a := ih a (by omega)
  have hρlt : ∀ s, s < k.val + 1 → Text M (tach M) (k.val + 2) < Text M (tach M) (s + 1) := by
    intro s hsp
    have : Text M (tach M) ((s + 1) + (k.val + 1 - (s + 1))) ≤ Text M (tach M) (s + 1) :=
      hTle (k.val + 1 - (s + 1)) (s + 1) (by omega)
    rw [show (s + 1) + (k.val + 1 - (s + 1)) = k.val + 1 by omega] at this
    exact lt_of_lt_of_le hr this
  have hsurvW : ∀ s, k.val + 1 ≤ s → s ≤ L → survRowVal M (tach M) s < Wext M s := by
    intro s hps hsL
    by_cases hsl : s = L
    · subst hsl; simpa [survRowVal] using hML
    · simp only [survRowVal, if_neg hsl]; exact hcd s hps (by omega)
  have hWblk : ∀ s, B.Wblk s = (genBlkFlatStruct M (tach M) ha (wInt M ha (k.val + 1))).Wblk s :=
    fun _ => rfl
  have hsuffix : ∀ s, k.val + 1 ≤ s → ∀ (r : Fin (Wext M s)), r.val = survRowVal M (tach M) s →
      ∀ (hsL : s ≤ L), c.suffix s hsL r ⟨0, hML⟩ = 1 := by
    intro s hps r hr' hsL
    refine suffix_carrier hML (fun s' hps' hs' r' hr'' c' => ?_) hsurvW (L - s) s (by omega)
      hps r hr'
    have hcds' : 0 < Wext M s' - Text M (tach M) (s' + 1) := by
      have := hcd s' hps' (by omega)
      simp only [survRowVal, if_neg (by omega : s' ≠ L)] at hr''; omega
    have hrlift : r' = liftRow M (tach M) hle s' hs' ⟨0, hcds'⟩ := by
      apply Fin.ext
      simp only [liftRow, Fin.val_cast, Fin.val_natAdd, hr'']
      simp only [survRowVal, if_neg (by omega : s' ≠ L), Nat.add_zero]
    rw [hrlift, chain_A_liftRow s' hs' _ c']
    obtain ⟨kk, rfl⟩ : ∃ kk, s' = kk + 1 := ⟨s' - 1, by omega⟩
    change B.Wblk (kk + 1) _ c' = _
    rw [hWblk, show (genBlkFlatStruct M (tach M) ha (wInt M ha (k.val + 1))).Wblk (kk + 1)
          = (if hk : kk < L then (if hk2 : kk + 1 < L then
              readW M (tach M) ha (wInt M ha (k.val + 1)) ⟨kk, hk⟩ hk2 else 0) else 0) from rfl,
      dif_pos (by omega), dif_pos hs', readW_wInt]
    simp only [survCol, survRowVal, true_and]
    rfl
  have hr2 : Text M (tach M) (k.val + 2) < Text M (tach M) (k.val + 1) := hr
  have hcd2 : Text M (tach M) (k.val + 2) < Wext M (k.val + 1) := hcd (k.val + 1) (le_refl _) hpL
  set ρcast : Fin (Text M (tach M) (k.val + 1)) :=
    Fin.cast (show Text M (tach M) (k.val + 2)
          + (Text M (tach M) (k.val + 1) - Text M (tach M) (k.val + 2))
        = Text M (tach M) (k.val + 1) by omega) (Fin.natAdd _ ⟨0, by omega⟩) with hρcastdef
  set colP : Fin (Wext M (k.val + 1)) :=
    Fin.cast (show Text M (tach M) (k.val + 2) + (Wext M (k.val + 1) - Text M (tach M) (k.val + 2))
        = Wext M (k.val + 1) by omega) (Fin.natAdd _ ⟨0, by omega⟩) with hcolPdef
  have hcolPval : colP.val = survRowVal M (tach M) (k.val + 1) := by
    simp only [hcolPdef, Fin.val_cast, Fin.val_natAdd, Nat.add_zero, survRowVal,
      if_neg (by omega : k.val + 1 ≠ L)]
  have hpivot : c.Hmat (k.val + 1) (le_of_lt hpL) ρcast ⟨0, hML⟩ = 1 := by
    refine Hmat_pivot hpL hML colP ρcast ?_ ?_ ?_
    · intro j
      exact genBlk_Bmat_succ_bot ha (k.val + 1) k.val (by omega) ⟨0, by omega⟩ j
    · intro cc
      exact genBlk_Rmat_pivot ha k.val (by omega) hr2 hcd2 cc
    · exact hsuffix (k.val + 1) (le_refl _) colP hcolPval (le_of_lt hpL)
  have hρT : ∀ s, s ≤ k.val + 1 → Text M (tach M) (k.val + 1 + 1) < Text M (tach M) s := by
    intro s hs
    have hle' : Text M (tach M) (k.val + 1) ≤ Text M (tach M) s := by
      have := hTle (k.val + 1 - s) s (by omega)
      rwa [show s + (k.val + 1 - s) = k.val + 1 by omega] at this
    exact lt_of_lt_of_le hr2 hle'
  have hEzero : ∀ s, s < k.val + 1 → c.E s = 0 := by
    intro s hs
    change B.Rmat s * Agen u M (tach M) B hle s = 0
    have hRz : B.Rmat s = 0 := by
      change (genBlkFlatStruct M (tach M) ha (wInt M ha (k.val + 1))).Rmat s = 0
      match s with
      | 0 => rfl
      | (j + 1) => exact genBlk_Rmat_succ_zero ha (k.val + 1) j (by omega) (by omega)
    rw [hRz, Matrix.zero_mul]
  have hHmat0 : c.Hmat 0 (Nat.zero_le L) (rhoAt M (tach M) (k.val + 1) 0 (hρT 0 (by omega)))
      ⟨0, hML⟩ = 1 := by
    refine Hmat_row_thread (B := B) hpL hML hρT (fun s hs => hTdesc s (by omega))
      ?_ (fun s hs => hEzero s hs) (fun s hs => hρlt s (by omega)) ?_ (k.val + 1) 0 (by omega)
    · convert hpivot using 2
    · intro s hsp a j
      match s with
      | 0 => exact genBlk_Bmat_zero_top ha (k.val + 1) a j _
      | (kk + 1) => exact genBlk_Bmat_succ_top ha (k.val + 1) kk (by omega) a j
  exact sqSumHmat0_ne_zero_of_entry c (rhoAt M (tach M) (k.val + 1) 0 (hρT 0 (by omega)))
    ⟨0, hML⟩ hHmat0

/-- **`UPolyEfpGen ≠ 0`** — from the witness (`eDeepRank0UnitGen_wInt_ne_zero`,
`eval_UPolyEfpGen`). -/
theorem UPolyEfpGen_ne_zero (M : Fin (L + 1) → ℕ) (ha : StructAdm M (tach M)) (k : Fin L)
    (hk : k.val ≠ L - 1) (p₀ : Fin (routeMAmbient M))
    (hp1 : Text M (tach M) (k.val + 1 + 1) ≤ Text M (tach M) (k.val + 1))
    (hp2 : Text M (tach M) (k.val + 1 + 1) ≤ Wext M (k.val + 1))
    (hML : 0 < Wext M L)
    (hr : Text M (tach M) (k.val + 2) < Text M (tach M) (k.val + 1))
    (hcd : ∀ b, k.val + 1 ≤ b → b < L → Text M (tach M) (b + 1) < Wext M b) :
    UPolyEfpGen M ha k p₀ hp1 hp2 ≠ 0 := by
  intro h0
  refine eDeepRank0UnitGen_wInt_ne_zero M ha k hk p₀ hp1 hp2 hML hr hcd ?_
  rw [← eval_UPolyEfpGen M ha k p₀ hp1 hp2 (wInt M ha (k.val + 1)), h0, map_zero]

/-- **a.e.-positivity of the `deepRank = 0` unit factor** — `∀ᵐ u, 0 < eDeepRank0UnitGen k p₀ u`,
given the interior-drop witness data at pivot `k+1`. Via `eval_UPolyEfpGen` +
`MvPolynomial.ae_eval_ne_zero` + `eDeepRank0UnitGen_nonneg`. -/
theorem eDeepRank0Unit_ae_posGen (M : Fin (L + 1) → ℕ) (ha : StructAdm M (tach M)) (k : Fin L)
    (hk : k.val ≠ L - 1) (p₀ : Fin (routeMAmbient M))
    (hp1 : Text M (tach M) (k.val + 1 + 1) ≤ Text M (tach M) (k.val + 1))
    (hp2 : Text M (tach M) (k.val + 1 + 1) ≤ Wext M (k.val + 1))
    (hML : 0 < Wext M L)
    (hr : Text M (tach M) (k.val + 2) < Text M (tach M) (k.val + 1))
    (hcd : ∀ b, k.val + 1 ≤ b → b < L → Text M (tach M) (b + 1) < Wext M b) :
    ∀ᵐ u, 0 < eDeepRank0UnitGen M ha k p₀ hp1 hp2 u := by
  have hae := MvPolynomial.ae_eval_ne_zero _ (UPolyEfpGen_ne_zero M ha k hk p₀ hp1 hp2 hML hr hcd)
  filter_upwards [hae] with u hu
  rw [← eval_UPolyEfpGen M ha k p₀ hp1 hp2 u] at *
  refine lt_of_le_of_ne ?_ (Ne.symm hu)
  rw [eval_UPolyEfpGen M ha k p₀ hp1 hp2 u]
  exact eDeepRank0UnitGen_nonneg M ha k p₀ hp1 hp2 u

/-! ## Step (c) — the change-of-variables, the bundle, the atom, the consumer -/

/-- **The general-`L` `deepRank = 0` change-of-variables** — the cov engine
`ldu_cov_of_differentiable_injOn` with `hdiff` (`eDeepRank0_diffGen`), `habsdet`
(`eDeepRank0_abs_detGen`, unconditional), `hinj` (`eDeepRank0_injOnGen`, massaged to `E = univ`). -/
theorem eDeepRank0_covGen (M : Fin (L + 1) → ℕ) (ha : StructAdm M (tach M)) (k : Fin L)
    (hk : k.val ≠ L - 1) (hdr0 : Text M (tach M) L = 0)
    (hr : 0 < Text M (tach M) (k.val + 1) - Text M (tach M) (k.val + 2))
    (hc : 0 < Wext M (k.val + 1) - Text M (tach M) (k.val + 2))
    (hp1 : Text M (tach M) (k.val + 1 + 1) ≤ Text M (tach M) (k.val + 1))
    (hp2 : Text M (tach M) (k.val + 1 + 1) ≤ Wext M (k.val + 1))
    (V : Set (Fin (routeMAmbient M) → ℝ)) (hV : MeasurableSet V)
    (g : (Fin (routeMAmbient M) → ℝ) → ℝ≥0∞) :
    ∫⁻ x in eDeepRank0PhiGen M ha k (eBlockPivotGen M ha k hr hc) hp1 hp2 ''
        (V \ {x | x (eBlockPivotGen M ha k hr hc) = 0}), g x
      = ∫⁻ u in V \ {x | x (eBlockPivotGen M ha k hr hc) = 0},
          ENNReal.ofReal (∏ j, |u j| ^ (eDeepRank0_leafHGen M ha (eBlockPivotGen M ha k hr hc) j))
            * g (eDeepRank0PhiGen M ha k (eBlockPivotGen M ha k hr hc) hp1 hp2 u) := by
  have hsub : {u : Fin (routeMAmbient M) → ℝ | u (eBlockPivotGen M ha k hr hc) ≠ 0
        ∧ ∀ j ∈ (Finset.univ : Finset (Fin (routeMAmbient M))), u j ≠ 0}
      ⊆ {u | u (eBlockPivotGen M ha k hr hc) ≠ 0 ∧ ∀ j, u j ≠ 0} := by
    rintro u ⟨hup, hall⟩
    exact ⟨hup, fun j => hall j (Finset.mem_univ j)⟩
  have hinj : Set.InjOn (eDeepRank0PhiGen M ha k (eBlockPivotGen M ha k hr hc) hp1 hp2)
      {u : Fin (routeMAmbient M) → ℝ | u (eBlockPivotGen M ha k hr hc) ≠ 0
        ∧ ∀ j ∈ (Finset.univ : Finset (Fin (routeMAmbient M))), u j ≠ 0} :=
    Set.InjOn.mono hsub (eDeepRank0_injOnGen M ha k hk hdr0 hr hc hp1 hp2)
  exact ldu_cov_of_differentiable_injOn
    (eDeepRank0PhiGen M ha k (eBlockPivotGen M ha k hr hc) hp1 hp2)
    (eBlockPivotGen M ha k hr hc) (eDeepRank0_leafHGen M ha (eBlockPivotGen M ha k hr hc))
    (Finset.univ : Finset (Fin (routeMAmbient M)))
    (eDeepRank0_diffGen M ha k hk hdr0 hr hc hp1 hp2)
    (fun u => eDeepRank0_abs_detGen M ha k hk hdr0 hr hc hp1 hp2 u) hinj V hV g

/-- **The `NodeAchieverChart.Ubound` field** for the general-`L` `deepRank = 0` chart — the box
bound (`eDeepRank0Unit_le_on_boxGen`) + the a.e.-positivity restricted to the box. -/
theorem eDeepRank0_UboundGen (M : Fin (L + 1) → ℕ) (ha : StructAdm M (tach M)) (k : Fin L)
    (hk : k.val ≠ L - 1) (p₀ : Fin (routeMAmbient M))
    (hp1 : Text M (tach M) (k.val + 1 + 1) ≤ Text M (tach M) (k.val + 1))
    (hp2 : Text M (tach M) (k.val + 1 + 1) ≤ Wext M (k.val + 1))
    (hML : 0 < Wext M L)
    (hrdrop : Text M (tach M) (k.val + 2) < Text M (tach M) (k.val + 1))
    (hcd : ∀ b, k.val + 1 ≤ b → b < L → Text M (tach M) (b + 1) < Wext M b) :
    ∀ δ : ℝ, ∃ B : ℝ, 0 < B ∧
      (∀ u ∈ Set.univ.pi (fun _ : Fin (routeMAmbient M) => Set.Icc (0 : ℝ) δ),
        eDeepRank0UnitGen M ha k p₀ hp1 hp2 u ≤ B) ∧
      ∀ᵐ u ∂(volume.restrict
          (Set.univ.pi (fun _ : Fin (routeMAmbient M) => Set.Icc (0 : ℝ) δ))),
        0 < eDeepRank0UnitGen M ha k p₀ hp1 hp2 u := by
  intro δ
  obtain ⟨B, hB0, hBle⟩ := eDeepRank0Unit_le_on_boxGen M ha k p₀ hp1 hp2 δ
  exact ⟨B, hB0, hBle,
    ae_restrict_of_ae (eDeepRank0Unit_ae_posGen M ha k hk p₀ hp1 hp2 hML hrdrop hcd)⟩

/-- **The general-`L` `deepRank = 0` achiever chart bundle** — `eDeepRank0PhiGen` with binding pivot
`eBlockPivotGen k`, the multi-axis `eDeepRank0_leafHGen`, unit `eDeepRank0UnitGen`, and the analytic
fields. General-`L` lift of `eDeepRank0NodeChart`. -/
noncomputable def eDeepRank0NodeChartGen (M : Fin (L + 1) → ℕ) (ha : StructAdm M (tach M))
    (k : Fin L) (hk : k.val ≠ L - 1) (hdr0 : Text M (tach M) L = 0)
    (hr : 0 < Text M (tach M) (k.val + 1) - Text M (tach M) (k.val + 2))
    (hc : 0 < Wext M (k.val + 1) - Text M (tach M) (k.val + 2))
    (hp1 : Text M (tach M) (k.val + 1 + 1) ≤ Text M (tach M) (k.val + 1))
    (hp2 : Text M (tach M) (k.val + 1 + 1) ≤ Wext M (k.val + 1))
    (hML : 0 < Wext M L)
    (hrdrop : Text M (tach M) (k.val + 2) < Text M (tach M) (k.val + 1))
    (hcd : ∀ b, k.val + 1 ≤ b → b < L → Text M (tach M) (b + 1) < Wext M b)
    (hpos : 1 ≤ minAdm M) :
    NodeAchieverChart M where
  hpos := hpos
  phi := eDeepRank0PhiGen M ha k (eBlockPivotGen M ha k hr hc) hp1 hp2
  p := eBlockPivotGen M ha k hr hc
  leafH := eDeepRank0_leafHGen M ha (eBlockPivotGen M ha k hr hc)
  leafH_pivot := eDeepRank0_leafHGen_pivot M ha (eBlockPivotGen M ha k hr hc)
  Ufun := eDeepRank0UnitGen M ha k (eBlockPivotGen M ha k hr hc) hp1 hp2
  Ubound := eDeepRank0_UboundGen M ha k hk (eBlockPivotGen M ha k hr hc) hp1 hp2 hML hrdrop hcd
  Umeas := measurable_eDeepRank0UnitGen M ha k (eBlockPivotGen M ha k hr hc) hp1 hp2
  leaf_integrand := fun c =>
    Filter.Eventually.of_forall (fun x =>
      leaf_integrand_of_rate (eBlockPivotGen M ha k hr hc)
        (eDeepRank0_leafHGen M ha (eBlockPivotGen M ha k hr hc))
        (fun y => routeMCore M (eDeepRank0PhiGen M ha k (eBlockPivotGen M ha k hr hc) hp1 hp2 y))
        (eDeepRank0UnitGen M ha k (eBlockPivotGen M ha k hr hc) hp1 hp2)
        (fun y => routeMCore_eDeepRank0PhiGen M ha k (eBlockPivotGen M ha k hr hc)
          (eBlockPivotGen_mem_activeMGen M ha k hk hr hc) hp1 hp2 y)
        (fun y => eDeepRank0UnitGen_nonneg M ha k (eBlockPivotGen M ha k hr hc) hp1 hp2 y) c x)
  cov := eDeepRank0_covGen M ha k hk hdr0 hr hc hp1 hp2
  image_subset := eDeepRank0_imageGen M ha k hk hdr0 hr hc hp1 hp2

/-- **The general-`L` `deepRank = 0` INTERIOR box-divergence atom** —
`∫⁻_{cubeBox N ε} |routeMCore M|^{−c'} = ⊤` for `c'` at-or-above `½·minAdm M`, every `ε > 0`, on the
`deepRank = 0` interior stratum with the chart boundary `k` aligned to the interior pivot (`k+1`
carries the row/col drops). Via the M-agnostic `routeMCore_box_diverges_of_nodeChart`. -/
theorem routeMCore_box_diverges_eDeepRank0Gen (M : Fin (L + 1) → ℕ) (ha : StructAdm M (tach M))
    (k : Fin L) (hk : k.val ≠ L - 1) (hdr0 : Text M (tach M) L = 0)
    (hr : 0 < Text M (tach M) (k.val + 1) - Text M (tach M) (k.val + 2))
    (hc : 0 < Wext M (k.val + 1) - Text M (tach M) (k.val + 2))
    (hp1 : Text M (tach M) (k.val + 1 + 1) ≤ Text M (tach M) (k.val + 1))
    (hp2 : Text M (tach M) (k.val + 1 + 1) ≤ Wext M (k.val + 1))
    (hML : 0 < Wext M L)
    (hrdrop : Text M (tach M) (k.val + 2) < Text M (tach M) (k.val + 1))
    (hcd : ∀ b, k.val + 1 ≤ b → b < L → Text M (tach M) (b + 1) < Wext M b)
    (hpos : 1 ≤ minAdm M)
    (c' : NNReal) (hc' : (minAdm M : ℝ≥0∞) / 2 ≤ (c' : ℝ≥0∞)) (ε : ℝ) (hε : 0 < ε) :
    ∫⁻ x in cubeBox (routeMAmbient M) ε,
      ENNReal.ofReal (|routeMCore M x| ^ (-(c' : ℝ))) = ⊤ :=
  routeMCore_box_diverges_of_nodeChart M
    (eDeepRank0NodeChartGen M ha k hk hdr0 hr hc hp1 hp2 hML hrdrop hcd hpos) c' hc' ε hε

/-! ## The `deepRank = 0` consumer form (the general-`L` interior gap complement)

The `deepRank M = 0` sub-stratum discharge, mirroring `interiorLiveGen_hInterior_of_deepRank_pos`
for the complementary stratum. The chart boundary `k = p* - 1` is ALIGNED to the `InteriorDrop`
pivot `p*` so that the ae-pos witness `wInt (k+1) = wInt p*` carries the full suffix survival data.
-/

/-- **The general-`L` interior `hInterior` discharge on the `deepRank = 0` sub-stratum.** For any
`M` with `2 ≤ L`, `InteriorDrop M`, and `deepRank M = 0`, the achiever box integral diverges at any
`c' ≥ ½·minAdm M`. Extracts the interior pivot `p*` from `InteriorDrop`, aligns the E-block chart to
`k = p* − 1`, and fires `routeMCore_box_diverges_eDeepRank0Gen`. -/
theorem routeMCore_box_diverges_eDeepRank0Gen_of_deepRank_zero (M : Fin (L + 1) → ℕ)
    (hL2 : 2 ≤ L) (hInt : InteriorDrop M) (hdr : deepRank M = 0)
    (hpos : 1 ≤ minAdm M)
    (c' : NNReal) (hc' : (minAdm M : ℝ≥0∞) / 2 ≤ (c' : ℝ≥0∞)) (ε : ℝ) (hε : 0 < ε) :
    BoxDiverges M c' ε := by
  have ha : StructAdm M (tach M) := structAdm_tach M (by omega)
  have hdr0 : Text M (tach M) L = 0 := hdr
  obtain ⟨hML, p, hp1p, hpL, hrp, hcdp⟩ := hInt
  -- align the chart boundary `k = p − 1`
  set k : Fin L := ⟨p - 1, by omega⟩ with hkdef
  have hkv1 : k.val + 1 = p := by simp only [hkdef]; omega
  have hk : k.val ≠ L - 1 := by simp only [hkdef]; omega
  -- transport the interior-pivot inequalities to the chart's `k`-indexed shapes
  have hrow : Text M (tach M) (k.val + 2) < Text M (tach M) (k.val + 1) := by
    rw [show k.val + 2 = p + 1 by omega, hkv1]; exact hrp
  have hcol : Text M (tach M) (k.val + 2) < Wext M (k.val + 1) := by
    rw [show k.val + 2 = p + 1 by omega, hkv1]; exact hcdp p (le_refl p) hpL
  have hr : 0 < Text M (tach M) (k.val + 1) - Text M (tach M) (k.val + 2) := by omega
  have hc : 0 < Wext M (k.val + 1) - Text M (tach M) (k.val + 2) := by omega
  have hp1 : Text M (tach M) (k.val + 1 + 1) ≤ Text M (tach M) (k.val + 1) := by
    rw [show k.val + 1 + 1 = k.val + 2 by omega]; exact le_of_lt hrow
  have hp2 : Text M (tach M) (k.val + 1 + 1) ≤ Wext M (k.val + 1) := by
    rw [show k.val + 1 + 1 = k.val + 2 by omega]; exact le_of_lt hcol
  have hcd : ∀ b, k.val + 1 ≤ b → b < L → Text M (tach M) (b + 1) < Wext M b := by
    intro b hb hbL; exact hcdp b (by omega) hbL
  exact routeMCore_box_diverges_eDeepRank0Gen M ha k hk hdr0 hr hc hp1 hp2 hML hrow hcd hpos
    c' hc' ε hε

/-- **The spine's `hInterior` slot, discharged on the `deepRank = 0` sub-stratum** — the
`∀ _ : 2 ≤ L`-shaped consumer form. Given `deepRank M = 0`, the interior branch obligation
`∀ _ : 2 ≤ L, InteriorDrop M → BoxDiverges M c' ε` holds by the `deepRank = 0` atom. Complements
`interiorLiveGen_hInterior_of_deepRank_pos` (the `0 < deepRank` sub-stratum). -/
theorem interiorLiveGen_hInterior_of_deepRank_zero (M : Fin (L + 1) → ℕ)
    (hdr : deepRank M = 0) (hpos : 1 ≤ minAdm M)
    (c' : NNReal) (hc' : (minAdm M : ℝ≥0∞) / 2 ≤ (c' : ℝ≥0∞)) (ε : ℝ) (hε : 0 < ε) :
    ∀ _ : 2 ≤ L, InteriorDrop M → BoxDiverges M c' ε :=
  fun hL2 hInt =>
    routeMCore_box_diverges_eDeepRank0Gen_of_deepRank_zero M hL2 hInt hdr hpos c' hc' ε hε

end DLNFibre.DLN.RLCT
