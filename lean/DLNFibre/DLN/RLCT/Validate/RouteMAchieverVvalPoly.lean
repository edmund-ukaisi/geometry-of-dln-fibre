import DLNFibre.DLN.RLCT.Validate.RouteMGenFlatStruct
import DLNFibre.Core.MeasureTheory.PolynomialZeroSet

/-!
# `RouteMAchieverVvalPoly` — the `VvalGen` MvPolynomial encoding + a.e.-positivity (the `Ubound` core)

The genuinely-remaining rate-side `NodeAchieverChart` field: `∀ᵐ x, 0 < achieverUfun x` (the `Ubound`
positivity), where `achieverUfun x = VvalGen (x p) M (tach M) (genBlkFlatStruct M (tach M) ha x) hle`.

Route (Codex `codex/mvpoly-encoding-route`): encode `achieverUfun` as `MvPolynomial.eval x` of a NAMED
nonzero `UPolyGen`, then `MvPolynomial.ae_eval_ne_zero` (the banked `Core.MeasureTheory.PolynomialZeroSet`)
gives the zero-set is null, so `> 0` a.e. (with `achieverUfun ≥ 0` banked, a sum of squares).

The encoding rides on the now-`CommRing`-generic chain engine (`Chain.map`/`HmatAux_map`, the chain-builder
stack, `genBlkFlatStruct`): the POLYNOMIAL chain `chainOfMt (X p) M t (genBlkFlatStruct … X) hle` (over
`MvPolynomial (Fin N) ℝ`, reading `X i` for coord `i`) maps under `eval x` to the ℝ chain
`chainOfMt (x p) M t (genBlkFlatStruct … x) hle` — block-by-block (`genBlkFlatStruct` reads single coords,
`eval x (X j) = x j`), so by `Chain.Hmat_zero_map` the polynomial `Hmat 0` evaluates to the ℝ `Hmat 0`,
hence `eval x UPolyGen = achieverUfun x`.

Axiom-clean `[propext, Classical.choice, Quot.sound]` (no S2; the nullity is the elementary
`MvPolynomial.volume_zeroSet_eq_zero`).
-/

open scoped BigOperators
open MvPolynomial Matrix MeasureTheory

namespace DLNFibre.DLN.RLCT

variable {L : ℕ}

/-! ## The `X`-coordinate vector + the polynomial decoder -/

/-- The `X`-coordinate vector `Fin N → MvPolynomial (Fin N) ℝ`, `i ↦ X i`; `eval x ∘ Xvec = x`. -/
noncomputable def Xvec (N : ℕ) : Fin N → MvPolynomial (Fin N) ℝ := fun i => MvPolynomial.X i

@[simp] theorem eval_Xvec {N : ℕ} (x : Fin N → ℝ) (i : Fin N) :
    MvPolynomial.eval x (Xvec N i) = x i := by simp [Xvec]

/-! ## `chainQ` / `chainA` `RingHom` naturality (`Matrix.map` pushes through the block constructors) -/

variable {𝕜 𝕜' : Type} [CommRing 𝕜] [CommRing 𝕜']

/-- **`chainQ` naturality**: `(chainQ h N).map f = chainQ h (N.map f)` — `chainQ` is `reindex` of a
`Sum.elim` of `1`/`N`-reindexes, all commuting with the ring hom `f` (`map_one`, `submatrix_map`). -/
theorem chainQ_map {M' t c : ℕ} (h : t + c = M') (N : Matrix (Fin t) (Fin c) 𝕜) (f : 𝕜 →+* 𝕜') :
    (chainQ h N).map f = chainQ h (N.map f) := by
  ext i j
  simp only [chainQ, Matrix.reindex_apply, Matrix.submatrix_apply, Matrix.map_apply, Matrix.of_apply,
    Equiv.symm_symm]
  rcases hs : finSplit (show t ≤ M' by omega) j with a | b <;>
    simp only [hs, Sum.elim_inl, Sum.elim_inr, Matrix.one_apply, apply_ite f, map_one, map_zero,
      Matrix.submatrix_apply, Matrix.map_apply]

/-- **`chainA` naturality**: `(chainA h N W C).map f = chainA h (N.map f) (W.map f) (C.map f)`. The lift
column `[C − N·W ; W]` reindexed; `map` distributes over `−`/`*` (`map_sub`/`Matrix.map_mul`). -/
theorem chainA_map {M' t c m' : ℕ} (h : t + c = M') (N : Matrix (Fin t) (Fin c) 𝕜)
    (W : Matrix (Fin c) (Fin m') 𝕜) (C : Matrix (Fin t) (Fin m') 𝕜) (f : 𝕜 →+* 𝕜') :
    (chainA h N W C).map f = chainA h (N.map f) (W.map f) (C.map f) := by
  ext i j
  simp only [chainA, Matrix.reindex_apply, Matrix.submatrix_apply, Matrix.map_apply, Matrix.of_apply,
    Equiv.symm_symm]
  rcases hs : finSplit (show t ≤ M' by omega) i with a | b
  · simp only [Sum.elim_inl, Matrix.sub_apply, map_sub, Matrix.map_apply]
    congr 1
    have hmm : (N * W).map f = N.map f * W.map f := Matrix.map_mul
    calc f ((N * W) a _) = ((N * W).map f) a _ := rfl
      _ = (N.map f * W.map f) a _ := by rw [hmm]
  · simp only [Sum.elim_inr, Matrix.submatrix_apply, Matrix.map_apply]

/-! ## `Cgen` / `Agen` `RingHom` naturality (block-data hypothesis form)

Given a ring hom `f` and two decoders `Bp : GenBlk M t 𝕜`, `Br : GenBlk M t 𝕜'` whose blocks correspond
under `f` (`(Bp.Bmat k).map f = Br.Bmat k`, &c.), `Cgen`/`Agen` of `Bp` at scalar `u` map under `f` to
those of `Br` at `f u`. `Cgen` is one-level (calls `chainQ`); `Agen k` calls `chainA` + `Cgen (k+1)`. -/

/-- The per-block `f`-correspondence between two decoders (the hypothesis bundle for `Cgen_map`/`Agen_map`). -/
structure GenBlkMap (M t : Fin (L + 1) → ℕ) (Bp : GenBlk M t 𝕜) (Br : GenBlk M t 𝕜')
    (f : 𝕜 →+* 𝕜') : Prop where
  hBmat : ∀ k, (Bp.Bmat k).map f = Br.Bmat k
  hNblk : ∀ k, (Bp.Nblk k).map f = Br.Nblk k
  hWblk : ∀ k, (Bp.Wblk k).map f = Br.Wblk k
  hRmat : ∀ k, (Bp.Rmat k).map f = Br.Rmat k
  hRfin : ∀ k, (Bp.Rfin k).map f = Br.Rfin k

/-- **`Cgen` naturality**: `(Cgen u Bp hle k).map f = Cgen (f u) Br hle k`. -/
theorem Cgen_map {M t : Fin (L + 1) → ℕ} {Bp : GenBlk M t 𝕜} {Br : GenBlk M t 𝕜'}
    {f : 𝕜 →+* 𝕜'} (hBM : GenBlkMap M t Bp Br f) (u : 𝕜)
    (hle : ∀ k, k < L → Text M t (k + 1) ≤ Wext M k) (k : ℕ) :
    (Cgen u M t Bp hle k).map f = Cgen (f u) M t Br hle k := by
  unfold Cgen
  by_cases hk : k < L
  · rw [dif_pos hk, dif_pos hk]
    rw [show (Bp.Bmat k * chainQ (genWidthEq M t hle k hk) (Bp.Nblk k) + u • Bp.Rmat k).map f
          = (Bp.Bmat k).map f * (chainQ (genWidthEq M t hle k hk) (Bp.Nblk k)).map f
            + f u • (Bp.Rmat k).map f from by
        rw [Chain.map_add_eq f, Matrix.map_mul, Chain.map_smul_eq f u (Bp.Rmat k)]]
    rw [chainQ_map, hBM.hBmat, hBM.hNblk, hBM.hRmat]
  · rw [dif_neg hk, dif_neg hk, Chain.map_smul_eq f u (Bp.Rfin k), hBM.hRfin]

/-- **`Agen` naturality**: `(Agen u Bp hle k).map f = Agen (f u) Br hle k`. -/
theorem Agen_map {M t : Fin (L + 1) → ℕ} {Bp : GenBlk M t 𝕜} {Br : GenBlk M t 𝕜'}
    {f : 𝕜 →+* 𝕜'} (hBM : GenBlkMap M t Bp Br f) (u : 𝕜)
    (hle : ∀ k, k < L → Text M t (k + 1) ≤ Wext M k) (k : ℕ) :
    (Agen u M t Bp hle k).map f = Agen (f u) M t Br hle k := by
  unfold Agen
  by_cases hk : k < L
  · rw [dif_pos hk, dif_pos hk, chainA_map, hBM.hNblk, hBM.hWblk, Cgen_map hBM u hle (k + 1)]
  · rw [dif_neg hk, dif_neg hk, Matrix.map_zero f (map_zero f)]

/-! ## The chain-level naturality + the `Hmat 0` / `HrGen` evaluation -/

/-- **The mapped chain equals the chain of the mapped decoder**: `(chainOfMt u Bp hle).toChain.map f
= (chainOfMt (f u) Br hle).toChain` — fieldwise (`Agen_map`/`Cgen_map`; `B`/`R` by `hBmat`/`hRfin`;
`E_k = Rmat_k · A_k` by `Matrix.map_mul` + `hRmat` + `Agen_map`). -/
theorem chainOfMt_map {M t : Fin (L + 1) → ℕ} {Bp : GenBlk M t 𝕜} {Br : GenBlk M t 𝕜'}
    {f : 𝕜 →+* 𝕜'} (hBM : GenBlkMap M t Bp Br f) (u : 𝕜)
    (hle : ∀ k, k < L → Text M t (k + 1) ≤ Wext M k) :
    (chainOfMt u M t Bp hle).toChain.map f = (chainOfMt (f u) M t Br hle).toChain := by
  have hA : ∀ k, ((chainOfMt u M t Bp hle).toChain.A k).map f
      = (chainOfMt (f u) M t Br hle).toChain.A k := fun k => Agen_map hBM u hle k
  have hC : ∀ k, ((chainOfMt u M t Bp hle).toChain.C k).map f
      = (chainOfMt (f u) M t Br hle).toChain.C k := fun k => Cgen_map hBM u hle k
  have hB : ∀ k, ((chainOfMt u M t Bp hle).toChain.B k).map f
      = (chainOfMt (f u) M t Br hle).toChain.B k := fun k => hBM.hBmat k
  have hE : ∀ k, ((chainOfMt u M t Bp hle).toChain.E k).map f
      = (chainOfMt (f u) M t Br hle).toChain.E k := by
    intro k
    show (Bp.Rmat k * Agen u M t Bp hle k).map f = Br.Rmat k * Agen (f u) M t Br hle k
    rw [Matrix.map_mul, hBM.hRmat, Agen_map hBM u hle k]
  have hR : ((chainOfMt u M t Bp hle).toChain.R).map f = (chainOfMt (f u) M t Br hle).toChain.R :=
    hBM.hRfin L
  -- assemble: both sides are `Chain.mk` with equal data fields; `step`/`base` proof-irrelevant.
  show Chain.mk _ _ _ _ _ _ _ _ _ = Chain.mk _ _ _ _ _ _ _ _ _
  congr 1 <;>
    first
      | (funext k; first | exact hA k | exact hC k | exact hB k | exact hE k)
      | exact hR
      | rfl

/-! ## `genBlkFlatStruct` decoder naturality (`eval x` on the `Xvec` decoder = the `x` decoder)

The readers `readK/X/N/E/W` return a single read coordinate, so `(reader (Xvec N) …).map (eval x) =
reader x …` (`eval x (X j) = x j`). The block constructors `bmatStack`/`rmatPad` commute with `Matrix.map`
of a ring hom (reindex/Sum.elim/fromBlocks/`X*K` all natural). Hence the `Xvec`-decoder's blocks map under
`eval x` to the `x`-decoder's blocks — a `GenBlkMap` for `eval x`. -/

variable {M t : Fin (L + 1) → ℕ}

/-- Reader naturality (`readK`, as a `Matrix.map`): each entry is a single read coord, `eval x (X j) = x j`. -/
theorem readK_eval (ha : StructAdm M t) (x : Fin (routeMAmbient M) → ℝ) (k : Fin L) :
    Matrix.map (readK M t ha (Xvec (routeMAmbient M)) k) (MvPolynomial.eval x)
      = readK M t ha x k := by
  ext i j; simp only [Matrix.map_apply, readK, eval_Xvec]

theorem readX_eval (ha : StructAdm M t) (x : Fin (routeMAmbient M) → ℝ) (k : Fin L) :
    Matrix.map (readX M t ha (Xvec (routeMAmbient M)) k) (MvPolynomial.eval x)
      = readX M t ha x k := by
  ext i j; simp only [Matrix.map_apply, readX, eval_Xvec]

theorem readN_eval (ha : StructAdm M t) (x : Fin (routeMAmbient M) → ℝ) (k : Fin L) :
    Matrix.map (readN M t ha (Xvec (routeMAmbient M)) k) (MvPolynomial.eval x)
      = readN M t ha x k := by
  ext i j; simp only [Matrix.map_apply, readN, eval_Xvec]

theorem readE_eval (ha : StructAdm M t) (x : Fin (routeMAmbient M) → ℝ) (k : Fin L) :
    Matrix.map (readE M t ha (Xvec (routeMAmbient M)) k) (MvPolynomial.eval x)
      = readE M t ha x k := by
  ext i j; simp only [Matrix.map_apply, readE, eval_Xvec]

theorem readW_eval (ha : StructAdm M t) (x : Fin (routeMAmbient M) → ℝ) (k : Fin L)
    (hk : k.val + 1 < L) :
    Matrix.map (readW M t ha (Xvec (routeMAmbient M)) k hk) (MvPolynomial.eval x)
      = readW M t ha x k hk := by
  ext i j; simp only [Matrix.map_apply, readW, eval_Xvec]

/-! ## `bmatStack` / `rmatPad` naturality (block constructors commute with `Matrix.map`) -/

/-- `bmatStack` naturality: `(bmatStack K X).map f = bmatStack (K.map f) (X.map f)` — `reindex` of a
`Sum.elim` of `K`/`X·K`, `map` distributes (`submatrix_map`/`Matrix.map_mul`). -/
theorem bmatStack_map {k : ℕ} (hdesc : Text M t (k + 1) ≤ Text M t k)
    (K : Matrix (Fin (Text M t (k + 1))) (Fin (Text M t (k + 1))) 𝕜)
    (X : Matrix (Fin (Text M t k - Text M t (k + 1))) (Fin (Text M t (k + 1))) 𝕜)
    (f : 𝕜 →+* 𝕜') :
    (bmatStack M t k hdesc K X).map f = bmatStack M t k hdesc (K.map f) (X.map f) := by
  ext i j
  simp only [bmatStack, Matrix.reindex_apply, Matrix.submatrix_apply, Matrix.map_apply,
    Matrix.of_apply, Equiv.refl_symm, Equiv.refl_apply]
  rcases hs : finSumFinEquiv.symm
      ((finCongr (show Text M t (k + 1) + (Text M t k - Text M t (k + 1)) = Text M t k by
          omega)).symm i) with a | b
  · simp only [hs, Sum.elim_inl]
  · simp only [hs, Sum.elim_inr]
    have hmm : (X * K).map f = X.map f * K.map f := Matrix.map_mul
    calc f ((X * K) b _) = ((X * K).map f) b _ := rfl
      _ = (X.map f * K.map f) b _ := by rw [hmm]

/-- `rmatPad` naturality: `(rmatPad E).map f = rmatPad (E.map f)` — `reindex` of `fromBlocks 0 0 0 E`,
`map` distributes (`fromBlocks_map`, `map_zero`). -/
theorem rmatPad_map {s : ℕ} (h1 : Text M t (s + 1) ≤ Text M t s) (h2 : Text M t (s + 1) ≤ Wext M s)
    (E : Matrix (Fin (Text M t s - Text M t (s + 1))) (Fin (Wext M s - Text M t (s + 1))) 𝕜)
    (f : 𝕜 →+* 𝕜') :
    (rmatPad M t s h1 h2 E).map f = rmatPad M t s h1 h2 (E.map f) := by
  have hfb : (Matrix.fromBlocks (0 : Matrix (Fin (Text M t (s + 1))) (Fin (Text M t (s + 1))) 𝕜)
        0 0 E).map f = Matrix.fromBlocks 0 0 0 (E.map f) := by
    rw [Matrix.fromBlocks_map]; simp only [Matrix.map_zero f (map_zero f)]
  ext i j
  simp only [rmatPad, Matrix.reindex_apply, Matrix.submatrix_apply, Matrix.map_apply]
  rw [show f (Matrix.fromBlocks 0 0 0 E _ _)
        = (Matrix.fromBlocks (0 : Matrix (Fin (Text M t (s + 1))) (Fin (Text M t (s + 1))) 𝕜)
            0 0 E).map f _ _ from rfl, hfb]

/-! ## The `genBlkFlatStruct` `GenBlkMap` under `eval x` -/

/-- **The decoder naturality**: `genBlkFlatStruct M t ha (Xvec N)` corresponds, under `eval x`, to
`genBlkFlatStruct M t ha x` — a `GenBlkMap`. Each block is `reindex 1` (`k=0`) / `bmatStack`/`rmatPad`
of readers / a reader / `0`, all natural under `eval x` (the reader + `bmatStack`/`rmatPad` maps). -/
theorem genBlkFlatStruct_genBlkMap (ha : StructAdm M t) (x : Fin (routeMAmbient M) → ℝ) :
    GenBlkMap M t (genBlkFlatStruct M t ha (Xvec (routeMAmbient M)))
      (genBlkFlatStruct M t ha x) (MvPolynomial.eval x) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · -- Bmat
    intro k
    match k with
    | 0 =>
      show (Matrix.reindex (Equiv.refl _) (finCongr (Text0_eq_Text1_struct M t ha.h0))
          (1 : Matrix (Fin (Text M t 0)) (Fin (Text M t 0)) (MvPolynomial (Fin (routeMAmbient M)) ℝ))).map
          (MvPolynomial.eval x)
        = Matrix.reindex (Equiv.refl _) (finCongr (Text0_eq_Text1_struct M t ha.h0))
          (1 : Matrix (Fin (Text M t 0)) (Fin (Text M t 0)) ℝ)
      ext i j
      simp only [Matrix.reindex_apply, Matrix.submatrix_apply, Matrix.map_apply, Matrix.one_apply,
        apply_ite (MvPolynomial.eval x), map_one, map_zero]
    | (k + 1) =>
      simp only [genBlkFlatStruct]
      by_cases hk : k < L
      · rw [dif_pos hk, dif_pos hk, bmatStack_map, readK_eval, readX_eval]
      · rw [dif_neg hk, dif_neg hk, Matrix.map_zero _ (map_zero _)]
  · -- Nblk
    intro k
    match k with
    | 0 => show (0 : Matrix _ _ _).map (MvPolynomial.eval x) = 0; rw [Matrix.map_zero _ (map_zero _)]
    | (k + 1) =>
      simp only [genBlkFlatStruct]
      by_cases hk : k < L
      · rw [dif_pos hk, dif_pos hk, readN_eval]
      · rw [dif_neg hk, dif_neg hk, Matrix.map_zero _ (map_zero _)]
  · -- Wblk
    intro k
    match k with
    | 0 => show (0 : Matrix _ _ _).map (MvPolynomial.eval x) = 0; rw [Matrix.map_zero _ (map_zero _)]
    | (k + 1) =>
      simp only [genBlkFlatStruct]
      by_cases hk : k < L
      · rw [dif_pos hk, dif_pos hk]
        by_cases hk2 : k + 1 < L
        · rw [dif_pos hk2, dif_pos hk2, readW_eval]
        · rw [dif_neg hk2, dif_neg hk2, Matrix.map_zero _ (map_zero _)]
      · rw [dif_neg hk, dif_neg hk, Matrix.map_zero _ (map_zero _)]
  · -- Rmat
    intro k
    match k with
    | 0 => show (0 : Matrix _ _ _).map (MvPolynomial.eval x) = 0; rw [Matrix.map_zero _ (map_zero _)]
    | (k + 1) =>
      simp only [genBlkFlatStruct]
      by_cases hk : k < L
      · rw [dif_pos hk, dif_pos hk, rmatPad_map, readE_eval]
      · rw [dif_neg hk, dif_neg hk, Matrix.map_zero _ (map_zero _)]
  · -- Rfin (always 0)
    intro k
    show (0 : Matrix _ _ _).map (MvPolynomial.eval x) = 0
    rw [Matrix.map_zero _ (map_zero _)]

end DLNFibre.DLN.RLCT
