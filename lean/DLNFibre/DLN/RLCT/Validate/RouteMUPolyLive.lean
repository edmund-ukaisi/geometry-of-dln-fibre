import DLNFibre.DLN.RLCT.Validate.RouteMInteriorLiveContract
import DLNFibre.DLN.RLCT.Validate.RouteMAchieverVvalPoly

/-!
# `RouteMUPolyLive` — the a.e.-POSITIVITY atom for the LIVE-leaf interior unit (LEAF 1)

The SOUNDNESS PIN the `interiorLive_Ubound` slot of `RouteMInteriorLiveContract` needs: the a.e.-positivity
`∀ᵐ u, 0 < interiorLiveUnit ha h0r h0c u`. genm-ubound (correctly) refused to assert this without the
nonzero-polynomial encoding of the LDU-lensed unit; this module supplies it.

## Route (Codex + genm-ubound's note)

`interiorLiveUnit u = eval u (UPolyLive)` for a NAMED nonzero `UPolyLive : MvPolynomial (Fin N) ℝ`, then
`MvPolynomial.ae_eval_ne_zero` (the banked `Core.MeasureTheory.PolynomialZeroSet`) ⟹ the zero set is null,
and `interiorLiveUnit_nonneg` (sum of squares) upgrades `≠ 0` to `0 <`.

Three pieces:

* **(a) generic `kLens`/`kLDU` over a `CommRing`** (route-independent, reusable). The ℝ-only `kLens` is
  `matrixSplit.symm ∘ lduCoreMap ∘ matrixSplit` (a `LinearEquiv`/`FiniteDimensional` chain that does NOT
  generalize to a bare `CommRing`); but `kLens K = (1 + lowMat l)·diag q·(1 + upMat u)` reading `(l,q,u)`
  off `K`'s strict-lower/diag/strict-upper (`kLens_eq`). The generic `kLensGen` uses THAT explicit formula
  (`lowMatGen`/`upMatGen`/`diagonal`), bypassing the `LinearEquiv`. `kLensGen_map` (naturality under a ring
  hom, via `Matrix.map_mul`/`map_one`/`diagonal_map`), `kLensGen_eq_kLens` (the ℝ instance is `kLens`),
  `kLDUGen` + `kLDUGen_eval` (`eval u ∘ kLDUGen (Xvec) = kLDU u`).
* **(b) the live + `rfinFixedPivot` `GenBlk` over `MvPolynomial`** — the poly encoding of the decoder, with
  a `GenBlkMap` to the ℝ decoder under `eval u` (reusing the `Cgen_map`/`Agen_map`/`chainOfMt_map` engine).
* **(c) the NONZERO witness `UPolyLive_ne_zero`** for THIS chart: at the interior-drop witness `wInt` the
  K-blocks read the identity (`readK_wInt`), and `kLens 1 = 1` (`kLensGen_one`), so `kLDU wInt = wInt`; the
  unit at `wInt` is then the dead-leaf `achieverUfun`-style sum-of-squares, nonzero by the banked interior
  survival witness `achieverUfun_wInt_ne_zero`.

The TOP atom `interiorLiveUnit_ae_pos : ∀ᵐ u, 0 < interiorLiveUnit ha h0r h0c u` is what
`RouteMInteriorLiveContract.interiorLive_Ubound`'s a.e.-positivity conjunct consumes.

Axiom-clean `[propext, Classical.choice, Quot.sound]` (no S2; the nullity is the elementary
`MvPolynomial.volume_zeroSet_eq_zero`).
-/

open scoped BigOperators
open MvPolynomial Matrix MeasureTheory

namespace DLNFibre.DLN.RLCT

/-! ## (a) The generic-`CommRing` matrix LDU lens `kLensGen` (route-independent infra) -/

variable {t : ℕ}

/-- Generic strict-lower embedding (zero on/above the diagonal) — `lowMat` over any `Zero`. -/
def lowMatGen {𝕜 : Type*} [Zero 𝕜] (l : LowIdx t → 𝕜) : Matrix (Fin t) (Fin t) 𝕜 :=
  Matrix.of fun i j => if h : j < i then l ⟨(i, j), h⟩ else 0

/-- Generic strict-upper embedding (zero on/below the diagonal) — `upMat` over any `Zero`. -/
def upMatGen {𝕜 : Type*} [Zero 𝕜] (u : UpIdx t → 𝕜) : Matrix (Fin t) (Fin t) 𝕜 :=
  Matrix.of fun i j => if h : i < j then u ⟨(i, j), h⟩ else 0

/-- **The generic matrix LDU lens** `kLensGen K := (1 + lowMatGen l)·diag q·(1 + upMatGen u)`, reading the
LDU params `(l,q,u)` off `K`'s strict-lower/diag/strict-upper — the `kLens_eq` formula over a bare
`CommRing` (bypassing the ℝ-only `matrixSplit` `LinearEquiv`). -/
noncomputable def kLensGen {𝕜 : Type*} [CommRing 𝕜] (K : Matrix (Fin t) (Fin t) 𝕜) :
    Matrix (Fin t) (Fin t) 𝕜 :=
  (1 + lowMatGen (fun p => K p.1.1 p.1.2)) * Matrix.diagonal (fun i => K i i)
    * (1 + upMatGen (fun p => K p.1.1 p.1.2))

/-- `lowMatGen` naturality under any `0`-preserving map. -/
theorem lowMatGen_map {𝕜 𝕜' : Type*} [Zero 𝕜] [Zero 𝕜'] (l : LowIdx t → 𝕜) (f : 𝕜 → 𝕜')
    (hf : f 0 = 0) :
    (lowMatGen l).map f = lowMatGen (fun p => f (l p)) := by
  ext i j; simp only [lowMatGen, Matrix.map_apply, Matrix.of_apply]
  split <;> simp [hf]

/-- `upMatGen` naturality under any `0`-preserving map. -/
theorem upMatGen_map {𝕜 𝕜' : Type*} [Zero 𝕜] [Zero 𝕜'] (u : UpIdx t → 𝕜) (f : 𝕜 → 𝕜')
    (hf : f 0 = 0) :
    (upMatGen u).map f = upMatGen (fun p => f (u p)) := by
  ext i j; simp only [upMatGen, Matrix.map_apply, Matrix.of_apply]
  split <;> simp [hf]

/-- **`kLensGen` naturality** under a ring hom: `(kLensGen K).map f = kLensGen (K.map f)`. The triple
product distributes (`Matrix.map_mul`); the unit `1` and the strict-lower/upper/diagonal pieces are each
natural (`Matrix.map_one`, `lowMatGen_map`/`upMatGen_map`, `Matrix.diagonal_map`). -/
theorem kLensGen_map {𝕜 𝕜' : Type*} [CommRing 𝕜] [CommRing 𝕜']
    (K : Matrix (Fin t) (Fin t) 𝕜) (f : 𝕜 →+* 𝕜') :
    (kLensGen K).map f = kLensGen (K.map f) := by
  unfold kLensGen
  rw [Matrix.map_mul, Matrix.map_mul]
  congr 1
  · congr 1
    · rw [Matrix.map_add f (map_add f), Matrix.map_one f (map_zero f) (map_one f),
        lowMatGen_map _ _ (map_zero f)]
      rfl
    · rw [Matrix.diagonal_map (map_zero f)]
      rfl
  · rw [Matrix.map_add f (map_add f), Matrix.map_one f (map_zero f) (map_one f),
      upMatGen_map _ _ (map_zero f)]
    rfl

/-- **`kLensGen` over ℝ is the existing `kLens`** — the `kLens_eq` formula IS the `kLensGen` formula. -/
theorem kLensGen_eq_kLens (K : Matrix (Fin t) (Fin t) ℝ) : kLensGen K = kLens K := by
  rw [kLens_eq]; unfold kLensGen; rfl

/-- **`kLensGen 1 = 1`** — the identity's strict-lower/upper read `0`, its diagonal reads `1`, so the
triple product is `1·1·1`. The witness seed (`kLens 1 = 1` ⟹ `kLDU` fixes the identity-K-block witness). -/
theorem kLensGen_one {𝕜 : Type*} [CommRing 𝕜] :
    kLensGen (1 : Matrix (Fin t) (Fin t) 𝕜) = 1 := by
  unfold kLensGen
  have hlow : lowMatGen (fun p : LowIdx t => (1 : Matrix (Fin t) (Fin t) 𝕜) p.1.1 p.1.2) = 0 := by
    ext i j; simp only [lowMatGen, Matrix.of_apply, Matrix.zero_apply]
    split
    · rename_i h; rw [Matrix.one_apply, if_neg (ne_of_gt h)]
    · rfl
  have hup : upMatGen (fun p : UpIdx t => (1 : Matrix (Fin t) (Fin t) 𝕜) p.1.1 p.1.2) = 0 := by
    ext i j; simp only [upMatGen, Matrix.of_apply, Matrix.zero_apply]
    split
    · rename_i h; rw [Matrix.one_apply, if_neg (ne_of_lt h)]
    · rfl
  have hdiag : Matrix.diagonal (fun i => (1 : Matrix (Fin t) (Fin t) 𝕜) i i) = 1 := by
    ext i j; simp only [Matrix.diagonal_apply, Matrix.one_apply]
    split <;> rename_i h <;> simp
  rw [hlow, hup, hdiag]; simp

/-- **`kLens 1 = 1`** (the ℝ instance of `kLensGen_one`, the witness seed). -/
theorem kLens_one : kLens (1 : Matrix (Fin t) (Fin t) ℝ) = 1 := by
  rw [← kLensGen_eq_kLens, kLensGen_one]

/-! ## (a, cont.) The generic `kLDU` + its `eval`-naturality -/

variable {L : ℕ}

/-- **The generic `kLDU` over a `CommRing`** (`𝕜 : Type`), mirroring `kLDU` with `kLensGen`/generic
`readK`. The K-branch reads the LDU matrix `kLensGen (readK x k)`; identity off K. -/
noncomputable def kLDUGen (M t : Fin (L + 1) → ℕ) (ha : StructAdm M t) {𝕜 : Type} [CommRing 𝕜]
    (x : Fin (routeMAmbient M) → 𝕜) : Fin (routeMAmbient M) → 𝕜 := fun q =>
  match chartIdxEquiv M (tDesc M t) ha.h0 ha.hc ha.hL q with
  | ⟨k, Sum.inl s⟩ =>
    match frameSplitEquiv M t (k.val + 1) (ha.hdesc k.val k.isLt) (ha.hub k.val) s with
    | Sum.inl (Sum.inl (Sum.inl qK)) =>
      let ij := finProdFinEquiv.symm qK
      kLensGen (readK M t ha x k) ij.1 ij.2
    | _ => x q
  | ⟨_, Sum.inr _⟩ => x q

/-- **The key naturality** `eval u (kLDUGen (Xvec) q) = kLDU u q` (componentwise). On the K-branch the
`kLensGen` of the `Xvec`-read K-block maps under `eval u` to the `kLens` of the `u`-read K-block
(`kLensGen_map` + `readK_eval` + `kLensGen_eq_kLens`); off K both sides are the pass-through coordinate
(`eval_Xvec`). The `match`-scrutinee reduction follows the `continuous_kLDU` `rcases`/`simp only` pattern. -/
theorem kLDUGen_eval (M t : Fin (L + 1) → ℕ) (ha : StructAdm M t)
    (u : Fin (routeMAmbient M) → ℝ) (q : Fin (routeMAmbient M)) :
    MvPolynomial.eval u (kLDUGen M t ha (Xvec (routeMAmbient M)) q) = kLDU M t ha u q := by
  rcases hq : chartIdxEquiv M (tDesc M t) ha.h0 ha.hc ha.hL q with ⟨k, s⟩
  cases s with
  | inl sfr =>
    rcases hframe : frameSplitEquiv M t (k.val + 1) (ha.hdesc k.val k.isLt) (ha.hub k.val) sfr
      with (((qK | qX) | qN) | qE)
    · -- K-branch
      have hmap : Matrix.map (kLensGen (readK M t ha (Xvec (routeMAmbient M)) k))
            (MvPolynomial.eval u) = kLens (readK M t ha u k) := by
        rw [kLensGen_map (readK M t ha (Xvec (routeMAmbient M)) k) (MvPolynomial.eval u),
          readK_eval ha u k, kLensGen_eq_kLens]
      simp only [kLDUGen, kLDU, hq, hframe]
      calc MvPolynomial.eval u (kLensGen (readK M t ha (Xvec (routeMAmbient M)) k)
            (finProdFinEquiv.symm qK).1 (finProdFinEquiv.symm qK).2)
          = Matrix.map (kLensGen (readK M t ha (Xvec (routeMAmbient M)) k)) (MvPolynomial.eval u)
              (finProdFinEquiv.symm qK).1 (finProdFinEquiv.symm qK).2 := rfl
        _ = kLens (readK M t ha u k) (finProdFinEquiv.symm qK).1 (finProdFinEquiv.symm qK).2 := by
            rw [hmap]
    · simp only [kLDUGen, kLDU, hq, hframe, eval_Xvec]
    · simp only [kLDUGen, kLDU, hq, hframe, eval_Xvec]
    · simp only [kLDUGen, kLDU, hq, hframe, eval_Xvec]
  | inr sl => simp only [kLDUGen, kLDU, hq, eval_Xvec]

/-! ## (b) The reader naturality for an arbitrary `eval`-related vector pair

The readers `readK/X/N/E/W v k i j = v (idx)` are single-coordinate reads, so for any poly/ℝ vector pair
`(vp, vr)` related by `f ∘ vp = vr` (here `f = eval u`, `vp = kLDUGen (Xvec)`, `vr = kLDU u`, related by
`kLDUGen_eval`), the reader naturality `(reader vp k).map f = reader vr k` holds entrywise. This generalizes
the `Xvec`-specific `readK_eval` of `RouteMAchieverVvalPoly`. -/

section GenericMt
variable {M t : Fin (L + 1) → ℕ}

/-- Reader naturality from a vector-naturality `hv : ∀ q, f (vp q) = vr q`. -/
theorem readK_map_of {𝕜 𝕜' : Type} [CommRing 𝕜] [CommRing 𝕜'] (ha : StructAdm M t)
    (vp : Fin (routeMAmbient M) → 𝕜) (vr : Fin (routeMAmbient M) → 𝕜') (f : 𝕜 →+* 𝕜')
    (hv : ∀ q, f (vp q) = vr q) (k : Fin L) :
    Matrix.map (readK M t ha vp k) f = readK M t ha vr k := by
  ext i j; simp only [Matrix.map_apply, readK]; exact hv _

theorem readX_map_of {𝕜 𝕜' : Type} [CommRing 𝕜] [CommRing 𝕜'] (ha : StructAdm M t)
    (vp : Fin (routeMAmbient M) → 𝕜) (vr : Fin (routeMAmbient M) → 𝕜') (f : 𝕜 →+* 𝕜')
    (hv : ∀ q, f (vp q) = vr q) (k : Fin L) :
    Matrix.map (readX M t ha vp k) f = readX M t ha vr k := by
  ext i j; simp only [Matrix.map_apply, readX]; exact hv _

theorem readN_map_of {𝕜 𝕜' : Type} [CommRing 𝕜] [CommRing 𝕜'] (ha : StructAdm M t)
    (vp : Fin (routeMAmbient M) → 𝕜) (vr : Fin (routeMAmbient M) → 𝕜') (f : 𝕜 →+* 𝕜')
    (hv : ∀ q, f (vp q) = vr q) (k : Fin L) :
    Matrix.map (readN M t ha vp k) f = readN M t ha vr k := by
  ext i j; simp only [Matrix.map_apply, readN]; exact hv _

theorem readE_map_of {𝕜 𝕜' : Type} [CommRing 𝕜] [CommRing 𝕜'] (ha : StructAdm M t)
    (vp : Fin (routeMAmbient M) → 𝕜) (vr : Fin (routeMAmbient M) → 𝕜') (f : 𝕜 →+* 𝕜')
    (hv : ∀ q, f (vp q) = vr q) (k : Fin L) :
    Matrix.map (readE M t ha vp k) f = readE M t ha vr k := by
  ext i j; simp only [Matrix.map_apply, readE]; exact hv _

theorem readW_map_of {𝕜 𝕜' : Type} [CommRing 𝕜] [CommRing 𝕜'] (ha : StructAdm M t)
    (vp : Fin (routeMAmbient M) → 𝕜) (vr : Fin (routeMAmbient M) → 𝕜') (f : 𝕜 →+* 𝕜')
    (hv : ∀ q, f (vp q) = vr q) (k : Fin L) (hk : k.val + 1 < L) :
    Matrix.map (readW M t ha vp k hk) f = readW M t ha vr k hk := by
  ext i j; simp only [Matrix.map_apply, readW]; exact hv _

/-- **The `genBlkFlatStruct` `GenBlkMap` for an arbitrary `eval`-related vector pair** — generalizes
`genBlkFlatStruct_genBlkMap` (the `Xvec`/`x` case) off the specific vectors. Each block is `reindex 1`
(`k=0`) / `bmatStack`/`rmatPad` of readers / a reader / `0`, all natural via the `read*_map_of` lemmas. -/
theorem genBlkFlatStruct_genBlkMap_of {𝕜 𝕜' : Type} [CommRing 𝕜] [CommRing 𝕜'] (ha : StructAdm M t)
    (vp : Fin (routeMAmbient M) → 𝕜) (vr : Fin (routeMAmbient M) → 𝕜') (f : 𝕜 →+* 𝕜')
    (hv : ∀ q, f (vp q) = vr q) :
    GenBlkMap M t (genBlkFlatStruct M t ha vp) (genBlkFlatStruct M t ha vr) f := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · -- Bmat
    intro k
    match k with
    | 0 =>
      show (Matrix.reindex (Equiv.refl _) (finCongr (Text0_eq_Text1_struct M t ha.h0))
          (1 : Matrix (Fin (Text M t 0)) (Fin (Text M t 0)) 𝕜)).map f
        = Matrix.reindex (Equiv.refl _) (finCongr (Text0_eq_Text1_struct M t ha.h0))
          (1 : Matrix (Fin (Text M t 0)) (Fin (Text M t 0)) 𝕜')
      ext i j
      simp only [Matrix.reindex_apply, Matrix.submatrix_apply, Matrix.map_apply, Matrix.one_apply,
        apply_ite f, map_one, map_zero]
    | (k + 1) =>
      simp only [genBlkFlatStruct]
      by_cases hk : k < L
      · rw [dif_pos hk, dif_pos hk, bmatStack_map, readK_map_of ha vp vr f hv,
          readX_map_of ha vp vr f hv]
      · rw [dif_neg hk, dif_neg hk, Matrix.map_zero _ (map_zero _)]
  · -- Nblk
    intro k
    match k with
    | 0 => show (0 : Matrix _ _ _).map f = 0; rw [Matrix.map_zero _ (map_zero _)]
    | (k + 1) =>
      simp only [genBlkFlatStruct]
      by_cases hk : k < L
      · rw [dif_pos hk, dif_pos hk, readN_map_of ha vp vr f hv]
      · rw [dif_neg hk, dif_neg hk, Matrix.map_zero _ (map_zero _)]
  · -- Wblk
    intro k
    match k with
    | 0 => show (0 : Matrix _ _ _).map f = 0; rw [Matrix.map_zero _ (map_zero _)]
    | (k + 1) =>
      simp only [genBlkFlatStruct]
      by_cases hk : k < L
      · rw [dif_pos hk, dif_pos hk]
        by_cases hk2 : k + 1 < L
        · rw [dif_pos hk2, dif_pos hk2, readW_map_of ha vp vr f hv]
        · rw [dif_neg hk2, dif_neg hk2, Matrix.map_zero _ (map_zero _)]
      · rw [dif_neg hk, dif_neg hk, Matrix.map_zero _ (map_zero _)]
  · -- Rmat
    intro k
    match k with
    | 0 => show (0 : Matrix _ _ _).map f = 0; rw [Matrix.map_zero _ (map_zero _)]
    | (k + 1) =>
      simp only [genBlkFlatStruct]
      by_cases hk : k < L
      · rw [dif_pos hk, dif_pos hk, rmatPad_map, readE_map_of ha vp vr f hv]
      · rw [dif_neg hk, dif_neg hk, Matrix.map_zero _ (map_zero _)]
  · -- Rfin (always 0)
    intro k
    show (0 : Matrix _ _ _).map f = 0
    rw [Matrix.map_zero _ (map_zero _)]

end GenericMt

/-! ## (b, cont.) The live decoder over `MvPolynomial` + its `GenBlkMap`

The live decoder `genBlkFlatLive ha rfin x` is `genBlkFlatStruct ha x` with the leaf residual
`Rfin L := rfin` made live. The poly version reads from `kLDUGen (Xvec)` with the generic fixed-pivot leaf
`rfinFixedPivotGen`; its `GenBlkMap` to the ℝ decoder under `eval u` glues the shared-field map
(`genBlkFlatStruct_genBlkMap_of`) with the `Rfin` naturality. -/

/-- **The generic fixed-pivot leaf reader** — `(0,0) ↦ 1`, off `(0,0)` the leaf coordinate `v (leafSlot)`,
over any `CommRing`. Maps under `eval u` to `rfinFixedPivot (kLDU u)` when `v = kLDUGen (Xvec)`. -/
noncomputable def rfinFixedPivotGen (M : Fin (L + 1) → ℕ) (ha : StructAdm M (tach M)) (hL : 0 < L)
    {𝕜 : Type} [CommRing 𝕜] (x : Fin (routeMAmbient M) → 𝕜) :
    Matrix (Fin (Text M (tach M) L)) (Fin (Wext M L)) 𝕜 :=
  Matrix.of fun i j =>
    if i.val = 0 ∧ j.val = 0 then 1 else x (leafSlot M (tach M) ha hL i j)

/-- **The poly leaf reader maps to the ℝ one** under `eval u` (`vp = kLDUGen (Xvec)`, `vr = kLDU u`):
`(rfinFixedPivotGen (kLDUGen (Xvec))).map (eval u) = rfinFixedPivot (kLDU u)`. The `(0,0)` entry is the
literal `1 ↦ 1`; off `(0,0)` it is the coordinate `kLDUGen_eval`. -/
theorem rfinFixedPivotGen_map (M : Fin (L + 1) → ℕ) (ha : StructAdm M (tach M)) (hL : 0 < L)
    {𝕜 𝕜' : Type} [CommRing 𝕜] [CommRing 𝕜'] (vp : Fin (routeMAmbient M) → 𝕜)
    (vr : Fin (routeMAmbient M) → 𝕜') (f : 𝕜 →+* 𝕜') (hv : ∀ q, f (vp q) = vr q) :
    Matrix.map (rfinFixedPivotGen M ha hL vp) f = rfinFixedPivotGen M ha hL vr := by
  ext i j
  simp only [Matrix.map_apply, rfinFixedPivotGen, Matrix.of_apply]
  split
  · exact map_one f
  · exact hv _

/-- **`rfinFixedPivotGen` over ℝ is the original `rfinFixedPivot`** (same formula). -/
theorem rfinFixedPivotGen_eq (M : Fin (L + 1) → ℕ) (ha : StructAdm M (tach M)) (hL : 0 < L)
    (x : Fin (routeMAmbient M) → ℝ) :
    rfinFixedPivotGen M ha hL x = rfinFixedPivot M ha hL x := by
  ext i j
  simp only [rfinFixedPivotGen, rfinFixedPivot, Matrix.of_apply]

/-- **`sqSumHmat0` naturality** — a ring hom `f` pushes through `∑∑·²` and `Hmat 0` (`Hmat_zero_map`):
`f (sqSumHmat0 c) = sqSumHmat0 (c.map f)`. The clean entry-level bridge (no `convert`/`▸` on the
dependent `Hmat`). -/
theorem sqSumHmat0_map {n : ℕ} {𝕜 𝕜' : Type} [CommRing 𝕜] [CommRing 𝕜'] {u₀ : 𝕜}
    (c : Chain n u₀) (f : 𝕜 →+* 𝕜') :
    f (sqSumHmat0 c) = sqSumHmat0 (c.map f) := by
  unfold sqSumHmat0
  rw [map_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [map_sum]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [map_pow]
  have := congrFun (congrFun (Chain.Hmat_zero_map c f) i) j
  rw [Matrix.map_apply] at this
  rw [this]

/-- **The generic live decoder** `genBlkFlatLiveGen ha rfin x : GenBlk M t 𝕜` — `genBlkFlatStruct ha x`
with the leaf residual `Rfin L := rfin` made live (the `CommRing`-generic version of `genBlkFlatLive`). -/
noncomputable def genBlkFlatLiveGen (M t : Fin (L + 1) → ℕ) (ha : StructAdm M t)
    {𝕜 : Type} [CommRing 𝕜] (rfin : Matrix (Fin (Text M t L)) (Fin (Wext M L)) 𝕜)
    (x : Fin (routeMAmbient M) → 𝕜) : GenBlk M t 𝕜 where
  Bmat := (genBlkFlatStruct M t ha x).Bmat
  Nblk := (genBlkFlatStruct M t ha x).Nblk
  Wblk := (genBlkFlatStruct M t ha x).Wblk
  Rmat := (genBlkFlatStruct M t ha x).Rmat
  Rfin := fun k => if h : k = L then h ▸ rfin else 0

/-- **The generic live decoder over ℝ is `genBlkFlatLive`** (definitional — same fields). -/
theorem genBlkFlatLiveGen_eq_live (M t : Fin (L + 1) → ℕ) (ha : StructAdm M t)
    (rfin : Matrix (Fin (Text M t L)) (Fin (Wext M L)) ℝ) (x : Fin (routeMAmbient M) → ℝ) :
    genBlkFlatLiveGen M t ha rfin x = genBlkFlatLive M t ha rfin x := rfl

/-- **The live decoder's `GenBlkMap`** under `eval`-related vectors `(vp, vr)` with leaf residuals
`(rp, rr)` related by `(rp).map f = rr`. The four interior fields are `genBlkFlatStruct`'s
(`genBlkFlatStruct_genBlkMap_of`); the live `Rfin` transport `h ▸ rp` maps to `h ▸ rr` (cast commutes
with `Matrix.map`). -/
theorem genBlkFlatLiveGen_genBlkMap_of (M t : Fin (L + 1) → ℕ) {𝕜 𝕜' : Type} [CommRing 𝕜]
    [CommRing 𝕜'] (ha : StructAdm M t)
    (vp : Fin (routeMAmbient M) → 𝕜) (vr : Fin (routeMAmbient M) → 𝕜') (f : 𝕜 →+* 𝕜')
    (hv : ∀ q, f (vp q) = vr q) (rp : Matrix (Fin (Text M t L)) (Fin (Wext M L)) 𝕜)
    (rr : Matrix (Fin (Text M t L)) (Fin (Wext M L)) 𝕜') (hr : Matrix.map rp f = rr) :
    GenBlkMap M t (genBlkFlatLiveGen M t ha rp vp) (genBlkFlatLiveGen M t ha rr vr) f := by
  have hbase := genBlkFlatStruct_genBlkMap_of ha vp vr f hv
  refine ⟨hbase.hBmat, hbase.hNblk, hbase.hWblk, hbase.hRmat, ?_⟩
  intro k
  -- `Rfin k = if h : k = L then h ▸ r else 0` on both sides (the live override). Mirror the
  -- `genBlkFlatLive_zero_eq` `simp only … split … subst h; rfl` pattern for the `h ▸ r` transport.
  simp only [genBlkFlatLiveGen]
  split
  · rename_i h; subst h; rw [hr]
  · rw [Matrix.map_zero _ (map_zero _)]

/-! ## (c) The `UPolyLive` encoding + the nonzero witness

`interiorLiveUnit u = sqSumHmat0 (ℝ live decoder chain)` and the poly `UPolyLive` is `sqSumHmat0` of the
POLYNOMIAL live decoder chain (over `kLDUGen (Xvec)` with the generic fixed-pivot leaf). `eval u` pushes
through the `∑∑·²` and identifies the chains (`chainOfMt_map` + the live `GenBlkMap` + `Hmat_zero_map`). -/

variable {M : Fin (2 + 1) → ℕ}

/-- The poly pivot scalar `Xvec (kLDUGen-read) leafPivot` reduces (via `kLDUGen_eval` + `kLDU_leafPivot`)
to `eval u ↦ u leafPivot`. (`kLDU` fixes the leaf pivot; the `Xvec` pivot read is the bare coordinate.) -/
theorem eval_kLDUGen_leafPivot (ha : StructAdm M (tach M))
    (h0r : 0 < Text M (tach M) 2) (h0c : 0 < Wext M 2) (u : Fin (routeMAmbient M) → ℝ) :
    MvPolynomial.eval u (kLDUGen M (tach M) ha (Xvec (routeMAmbient M))
        (leafPivot M ha (by norm_num) h0r h0c))
      = u (leafPivot M ha (by norm_num) h0r h0c) := by
  rw [kLDUGen_eval M (tach M) ha u (leafPivot M ha (by norm_num) h0r h0c),
    kLDU_leafPivot ha h0r h0c u]

/-- **The named nonzero polynomial `UPolyLive`** — `sqSumHmat0` of the POLYNOMIAL live decoder chain
(decoder over `kLDUGen (Xvec)`, leaf `rfinFixedPivotGen (kLDUGen (Xvec))`, pivot `Xvec (kLDUGen) leafPivot`).
`eval u UPolyLive = interiorLiveUnit ha h0r h0c u`. -/
noncomputable def UPolyLive (ha : StructAdm M (tach M))
    (h0r : 0 < Text M (tach M) 2) (h0c : 0 < Wext M 2) :
    MvPolynomial (Fin (routeMAmbient M)) ℝ :=
  sqSumHmat0 (chainOfMt
    (kLDUGen M (tach M) ha (Xvec (routeMAmbient M)) (leafPivot M ha (by norm_num) h0r h0c))
    M (tach M)
    (genBlkFlatLiveGen M (tach M) ha
      (rfinFixedPivotGen M ha (by norm_num)
        (kLDUGen M (tach M) ha (Xvec (routeMAmbient M))))
      (kLDUGen M (tach M) ha (Xvec (routeMAmbient M))))
    (hleStruct M (tach M) ha)).toChain

/-- **`eval u UPolyLive = interiorLiveUnit u`.** `eval u` pushes through `∑∑·²` (a ring hom), and the
chain naturality (`chainOfMt_map` + the live `GenBlkMap` glued from `kLDUGen_eval` + `rfinFixedPivotGen_map`)
identifies the evaluated poly chain's `Hmat 0` with the ℝ live decoder chain's. The ℝ side is
`interiorLiveUnit` by `VvalGen_eq_sqSumHmat0`. -/
theorem eval_UPolyLive (ha : StructAdm M (tach M))
    (h0r : 0 < Text M (tach M) 2) (h0c : 0 < Wext M 2) (u : Fin (routeMAmbient M) → ℝ) :
    MvPolynomial.eval u (UPolyLive ha h0r h0c) = interiorLiveUnit ha h0r h0c u := by
  -- the live `GenBlkMap` for `eval u`
  have hmap : GenBlkMap M (tach M)
      (genBlkFlatLiveGen M (tach M) ha
        (rfinFixedPivotGen M ha (by norm_num) (kLDUGen M (tach M) ha (Xvec (routeMAmbient M))))
        (kLDUGen M (tach M) ha (Xvec (routeMAmbient M))))
      (genBlkFlatLive M (tach M) ha
        (rfinFixedPivot M ha (by norm_num) (kLDU M (tach M) ha u))
        (kLDU M (tach M) ha u))
      (MvPolynomial.eval u) := by
    have h := genBlkFlatLiveGen_genBlkMap_of M (tach M) ha
      (kLDUGen M (tach M) ha (Xvec (routeMAmbient M))) (kLDU M (tach M) ha u)
      (MvPolynomial.eval u) (kLDUGen_eval M (tach M) ha u)
      (rfinFixedPivotGen M ha (by norm_num) (kLDUGen M (tach M) ha (Xvec (routeMAmbient M))))
      (rfinFixedPivot M ha (by norm_num) (kLDU M (tach M) ha u))
      (by
        rw [← rfinFixedPivotGen_eq M ha (by norm_num) (kLDU M (tach M) ha u)]
        exact rfinFixedPivotGen_map M ha (by norm_num)
          (kLDUGen M (tach M) ha (Xvec (routeMAmbient M))) (kLDU M (tach M) ha u)
          (MvPolynomial.eval u) (kLDUGen_eval M (tach M) ha u))
    rw [← genBlkFlatLiveGen_eq_live]; exact h
  -- The chain naturality (poly pivot kept SYMBOLIC), then the pivot `eval u (poly-pivot) = u leafPivot`.
  have hchain := chainOfMt_map hmap
    (kLDUGen M (tach M) ha (Xvec (routeMAmbient M)) (leafPivot M ha (by norm_num) h0r h0c))
    (hleStruct M (tach M) ha)
  -- `eval u UPolyLive = sqSumHmat0 (poly chain).map (eval u) = sqSumHmat0 (ℝ chain at pivot eval u poly-pivot)`
  rw [interiorLiveUnit, VvalGen_eq_sqSumHmat0, UPolyLive, sqSumHmat0_map _ (MvPolynomial.eval u),
    hchain, eval_kLDUGen_leafPivot ha h0r h0c u]

/-- **`kLDU` fixes the interior-drop witness** `kLDU (wInt p) = wInt p`. On K-slots `kLDU` reads
`kLens (readK (wInt) k)`; `readK (wInt) k = I` (`readK_wInt`) and `kLens 1 = 1` (`kLens_one`), so the
K-slot is unchanged; off K, `kLDU` is identity. The witness seed (`interiorLiveUnit (wInt) =
VvalGen … (genBlkFlatLive … (wInt)) (wInt)`, the dead-leaf decoder). -/
theorem kLDU_wInt (ha : StructAdm M (tach M)) (p : ℕ) :
    kLDU M (tach M) ha (wInt M ha p) = wInt M ha p := by
  funext q
  rcases hq : chartIdxEquiv M (tDesc M (tach M)) ha.h0 ha.hc ha.hL q with ⟨k, s⟩
  cases s with
  | inl sfr =>
    rcases hframe : frameSplitEquiv M (tach M) (k.val + 1) (ha.hdesc k.val k.isLt) (ha.hub k.val) sfr
      with (((qK | qX) | qN) | qE)
    · -- K-branch: `kLens (readK wInt k) ij = (kLens 1) ij = (1:Matrix) ij = readK wInt k ij = wInt q`
      have hK1 : Matrix.of (readK M (tach M) ha (wInt M ha p) k)
          = (1 : Matrix (Fin (Text M (tach M) (k.val + 2))) (Fin (Text M (tach M) (k.val + 2))) ℝ) := by
        ext a b; rw [Matrix.of_apply, readK_wInt, Matrix.one_apply]
      have hkl : kLens (readK M (tach M) ha (wInt M ha p) k)
          = (1 : Matrix (Fin (Text M (tach M) (k.val + 2))) (Fin (Text M (tach M) (k.val + 2))) ℝ) := by
        rw [show readK M (tach M) ha (wInt M ha p) k
              = Matrix.of (readK M (tach M) ha (wInt M ha p) k) from rfl, hK1, kLens_one]
      simp only [kLDU, hq, hframe]
      rw [hkl]
      -- `(1:Matrix) ij = readK wInt k ij = wInt q`
      have hone : (1 : Matrix (Fin (Text M (tach M) (k.val + 2))) (Fin (Text M (tach M) (k.val + 2))) ℝ)
          (finProdFinEquiv.symm qK).1 (finProdFinEquiv.symm qK).2
          = readK M (tach M) ha (wInt M ha p) k (finProdFinEquiv.symm qK).1 (finProdFinEquiv.symm qK).2 :=
        congrFun (congrFun hK1.symm _) _
      rw [hone, readK, wInt]
      -- `readK wInt k ij = wInt q`: both are `wOnIdx` of a `chartIdxEquiv` slot; the LHS slot decodes
      -- (via `finProdFinEquiv`/`frameSplitEquiv`/`chartIdxEquiv` round-trips) to `⟨k, inl sfr⟩`, and
      -- `chartIdxEquiv q = ⟨k, inl sfr⟩` (`hq`). So both reduce to `wOnIdx ⟨k, inl sfr⟩`.
      simp only [Function.comp_apply, Equiv.apply_symm_apply, hq]
      congr 2
      rw [Prod.mk.eta, Equiv.apply_symm_apply, ← hframe, Equiv.symm_apply_apply]
    · simp only [kLDU, hq, hframe]
    · simp only [kLDU, hq, hframe]
    · simp only [kLDU, hq, hframe]
  | inr sl => simp only [kLDU, hq]

/-- **The LIVE interior unit is nonzero at the interior-drop witness** `interiorLiveUnit (wInt p) ≠ 0`.
Via `kLDU_wInt` (`kLDU` fixes `wInt`), the live unit is `sqSumHmat0` of the live decoder chain
`genBlkFlatLive ha (rfinFixedPivot ha (wInt)) (wInt)` at pivot `wInt leafPivot`. The surviving entry
`Hmat 0 (ρ, 0) = 1` is built by the SAME generic machinery (`Hmat_pivot`/`Hmat_row_thread`/`suffix_carrier`)
as `achieverUfun_wInt_ne_zero`, applied to the live decoder — the surviving entry reads only
`Bmat/Nblk/Wblk/Rmat` (definitionally shared with `genBlkFlatStruct ha (wInt)`), so it is `Rfin L`-blind,
and the generic lemmas conclude the literal `1` (scalar-`u`-blind). -/
theorem interiorLiveUnit_wInt_ne_zero (ha : StructAdm M (tach M))
    (h0r : 0 < Text M (tach M) 2) (h0c : 0 < Wext M 2) (hML : 0 < Wext M 2)
    (p : ℕ) (hp1 : 1 ≤ p) (hpL : p < 2)
    (hr : Text M (tach M) (p + 1) < Text M (tach M) p)
    (hcd : ∀ b, p ≤ b → b < 2 → Text M (tach M) (b + 1) < Wext M b) :
    interiorLiveUnit ha h0r h0c (wInt M ha p) ≠ 0 := by
  -- reduce to `sqSumHmat0` of the live decoder chain at `wInt` (`kLDU` fixes `wInt`)
  rw [interiorLiveUnit, kLDU_wInt ha p, VvalGen_eq_sqSumHmat0]
  set hle := hleStruct M (tach M) ha with hledef
  set u := wInt M ha p (leafPivot M ha (by norm_num) h0r h0c) with hudef
  set B := genBlkFlatLive M (tach M) ha (rfinFixedPivot M ha (by norm_num) (wInt M ha p)) (wInt M ha p)
    with hBdef
  set c := (chainOfMt u M (tach M) B hle).toChain with hcdef
  -- the descent facts (verbatim from `achieverUfun_wInt_ne_zero`)
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
  have hsurvW : ∀ s, p ≤ s → s ≤ 2 → survRowVal M (tach M) s < Wext M s := by
    intro s hps hsL
    by_cases hsl : s = 2
    · subst hsl; simpa [survRowVal] using hML
    · simp only [survRowVal, if_neg hsl]; exact hcd s hps (by omega)
  -- the live decoder's `Wblk`/`Bmat`/`Rmat` ARE the struct decoder's (definitional `rfl`)
  have hWblk : ∀ k, B.Wblk k = (genBlkFlatStruct M (tach M) ha (wInt M ha p)).Wblk k := fun _ => rfl
  -- (I-suffix) carrier survival — `A`'s surviving row reads `Wblk` (= struct), `Rfin L`-blind
  have hsuffix : ∀ s, p ≤ s → ∀ (r : Fin (Wext M s)), r.val = survRowVal M (tach M) s →
      ∀ (hsL : s ≤ 2), c.suffix s hsL r ⟨0, hML⟩ = 1 := by
    intro s hps r hr' hsL
    refine suffix_carrier hML (fun s' hps' hs' r' hr'' c' => ?_) hsurvW (2 - s) s (by omega) hps r hr'
    have hcds' : 0 < Wext M s' - Text M (tach M) (s' + 1) := by
      have := hcd s' hps' (by omega)
      simp only [survRowVal, if_neg (by omega : s' ≠ 2)] at hr''; omega
    have hrlift : r' = liftRow M (tach M) hle s' hs' ⟨0, hcds'⟩ := by
      apply Fin.ext
      simp only [liftRow, Fin.val_cast, Fin.val_natAdd, hr'']
      simp only [survRowVal, if_neg (by omega : s' ≠ 2), Nat.add_zero]
    rw [hrlift, chain_A_liftRow s' hs' _ c']
    obtain ⟨k, rfl⟩ : ∃ k, s' = k + 1 := ⟨s' - 1, by omega⟩
    show B.Wblk (k + 1) _ c' = _
    rw [hWblk, show (genBlkFlatStruct M (tach M) ha (wInt M ha p)).Wblk (k + 1)
          = (if hk : k < 2 then (if hk2 : k + 1 < 2 then
              readW M (tach M) ha (wInt M ha p) ⟨k, hk⟩ hk2 else 0) else 0) from rfl,
      dif_pos (by omega), dif_pos hs', readW_wInt]
    simp only [survCol, survRowVal, Fin.val_zero, true_and]
    rfl
  -- the pivot boundary `p = kp + 1` (here `kp = 0` since `p < 2`)
  obtain ⟨kp, rfl⟩ : ∃ kp, p = kp + 1 := ⟨p - 1, by omega⟩
  have hkpL : kp < 2 := by omega
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
      if_neg (by omega : kp + 1 ≠ 2)]
  -- (I-base) `Hmat (kp+1) (ρ, 0) = 1` (the pivot value — Bmat/Rmat reads, both shared with struct)
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
  -- the live `E s = 0` for `s ≠ p` (`Rmat s = 0` shared with struct ⟹ `E_s = Rmat_s · A_s = 0`)
  have hEzero : ∀ s, s < kp + 1 → c.E s = 0 := by
    intro s hs
    show B.Rmat s * Agen u M (tach M) B hle s = 0
    have hRz : B.Rmat s = 0 := by
      show (genBlkFlatStruct M (tach M) ha (wInt M ha (kp + 1))).Rmat s = 0
      match s with
      | 0 => rfl
      | (k + 1) => exact genBlk_Rmat_succ_zero ha (kp + 1) k (by omega) (by omega)
    rw [hRz, Matrix.zero_mul]
  -- (I-up) thread the row up to `0`
  have hHmat0 : c.Hmat 0 (Nat.zero_le 2) (rhoAt M (tach M) (kp + 1) 0 (hρT 0 (by omega)))
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

/-- **The nonzero witness `UPolyLive ≠ 0`** — from `interiorLiveUnit (wInt p) ≠ 0` (the interior-drop
witness) via `eval (wInt p) UPolyLive = interiorLiveUnit (wInt p)` (`eval_UPolyLive`). The pivot `p`
(`1 ≤ p < 2`, the strict row-drop `hr`, the tail column-drops `hcd`, the leaf `hML`) comes from
`InteriorDrop M`. -/
theorem UPolyLive_ne_zero (ha : StructAdm M (tach M))
    (h0r : 0 < Text M (tach M) 2) (h0c : 0 < Wext M 2)
    (hInt : InteriorDrop M) :
    UPolyLive ha h0r h0c ≠ 0 := by
  obtain ⟨hML, p, hp1, hpL, hrdrop, hcd⟩ := hInt
  intro h0
  refine interiorLiveUnit_wInt_ne_zero ha h0r h0c hML p hp1 hpL hrdrop hcd ?_
  rw [← eval_UPolyLive ha h0r h0c (wInt M ha p), h0, map_zero]

/-! ## The a.e.-positivity atom (the LEAF-1 deliverable) -/

/-- **The LEAF-1 atom: a.e.-positivity of the LIVE interior unit** —
`∀ᵐ u, 0 < interiorLiveUnit ha h0r h0c u`. Via `eval_UPolyLive` (`interiorLiveUnit = eval · UPolyLive`)
+ `MvPolynomial.ae_eval_ne_zero` (`UPolyLive ≠ 0` ⟹ the zero set is null) + `interiorLiveUnit_nonneg`
(`≠ 0 ⟹ > 0`). This is the soundness pin the contract's `interiorLive_Ubound` a.e.-positivity
conjunct consumes; genm-ubound-live assembles `interiorLive_Ubound` = its box-bound ∧ this atom. -/
theorem interiorLiveUnit_ae_pos (ha : StructAdm M (tach M))
    (h0r : 0 < Text M (tach M) 2) (h0c : 0 < Wext M 2)
    (hInt : InteriorDrop M) :
    ∀ᵐ u, 0 < interiorLiveUnit ha h0r h0c u := by
  have hae := MvPolynomial.ae_eval_ne_zero _ (UPolyLive_ne_zero ha h0r h0c hInt)
  filter_upwards [hae] with u hu
  rw [← eval_UPolyLive ha h0r h0c u] at *
  refine lt_of_le_of_ne ?_ (Ne.symm hu)
  rw [eval_UPolyLive ha h0r h0c u]; exact interiorLiveUnit_nonneg ha h0r h0c u

end DLNFibre.DLN.RLCT
