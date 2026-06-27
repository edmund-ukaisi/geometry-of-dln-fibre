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

end DLNFibre.DLN.RLCT
