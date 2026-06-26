import Mathlib.LinearAlgebra.Determinant
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.Prod
import Mathlib.LinearAlgebra.Projection
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Data.Real.Basic

/-!
# `RouteMSchurFrameDet` — Phase A: the parametric Schur-frame Jacobian determinant engine

The **network-free, matrix-indexed** determinant engine for the general achiever chart, replacing
the per-instance `(3,3,3,3)` hand machinery (`frameB`, the 7×7 K/Kᵀ block, the 27-`have` `injOn`)
with one uniform block-triangular collapse. See
`expeditions/2026-06-20-aoyagi-full/threads/36-genM-jacobian-det/design.md` §1b/§2/§4 (Phase A).

The achiever-chart Schur frame of one boundary is `S(X,K,N,E) = [[K, K·N],[X·K, X·K·N + E]]`; its
differential is **block-lower-triangular** in the `(dK, dN, dX, dE)` increment pairing, so the
off-diagonal couplings drop and `|det DS| = |det K|^(r+c)`. NO per-instance SCC grading.

## Contents
* `lowerTri` / `lowerTri_det` — the abstract 2-block lower-triangular endomorphism of `M × N` and
  its determinant `f.det * g.det` (the reusable keystone, via `LinearMap.det_eq_det_mul_det`).
* `mulLeftMat` / `det_mulLeft_matrixSpace` — left-mult-by-`K` on `Matrix (Fin t) (Fin c) ℝ`,
  det `K.det^c`.
* `mulRightMat` / `det_mulRight_matrixSpace` — right-mult-by-`K` on `Matrix (Fin r) (Fin t) ℝ`,
  det `K.det^r`.
* `schurFrameDeriv` / `schurFrame_abs_det` — the Schur-frame differential (A2 keystone),
  `|det| = |K.det|^(r+c)`.
-/

open Matrix LinearMap

noncomputable section

namespace DLNFibre.DLN.RLCT

/-! ## The abstract 2-block lower-triangular determinant (the keystone helper)

For finite-dimensional real spaces `M`, `N`, the endomorphism `(m, n) ↦ (f m, g n + h m)` of `M × N`
is "block-lower-triangular": its determinant factors as `f.det * g.det`, the off-diagonal coupling
`h` contributing nothing. Proven via `LinearMap.det_eq_det_mul_det` on the invariant subspace
`W = Submodule.snd ≅ N` (restrict acts as `g`), with quotient `(M × N)/W ≅ M` (acts as `f`). -/

variable {M N : Type*} [AddCommGroup M] [Module ℝ M] [FiniteDimensional ℝ M]
  [AddCommGroup N] [Module ℝ N] [FiniteDimensional ℝ N]

/-- The block-lower-triangular endomorphism `(m, n) ↦ (f m, g n + h m)` of `M × N`. -/
def lowerTri (f : M →ₗ[ℝ] M) (g : N →ₗ[ℝ] N) (h : M →ₗ[ℝ] N) : M × N →ₗ[ℝ] M × N where
  toFun := fun p : M × N => (f p.1, g p.2 + h p.1)
  map_add' := by
    intro x y
    ext
    · simp
    · simp only [Prod.snd_add, map_add, Prod.fst_add]; abel
  map_smul' := by intro a x; ext <;> simp

/-- **The 2-block lower-triangular determinant**: `det (lowerTri f g h) = f.det * g.det`. The
coupling `h` does not affect the determinant. -/
theorem lowerTri_det (f : M →ₗ[ℝ] M) (g : N →ₗ[ℝ] N) (h : M →ₗ[ℝ] N) :
    LinearMap.det (lowerTri f g h) = f.det * g.det := by
  set e := lowerTri f g h with he
  set W : Submodule ℝ (M × N) := Submodule.snd ℝ M N with hW
  have hmemW : ∀ p : M × N, p ∈ W ↔ p.1 = 0 := by
    intro p; simp [hW, Submodule.snd, LinearMap.mem_ker]
  have hinv : W ≤ W.comap e := by
    intro p hp
    rw [hmemW] at hp
    simp only [Submodule.mem_comap]
    rw [hmemW]
    change (e p).1 = 0
    simp only [he, lowerTri, LinearMap.coe_mk, AddHom.coe_mk]
    rw [hp, LinearMap.map_zero]
  rw [LinearMap.det_eq_det_mul_det W e hinv, mul_comm f.det g.det]
  congr 1
  · -- (e.restrict hinv).det = g.det  via sndEquiv.symm : N ≅ W
    rw [← LinearMap.det_conj g (Submodule.sndEquiv ℝ M N).symm]
    congr 1
    apply LinearMap.ext
    intro w
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_symm]
    apply Subtype.ext
    rw [LinearMap.restrict_coe_apply]
    change (e w.1) = ((Submodule.sndEquiv ℝ M N).symm (g (Submodule.sndEquiv ℝ M N w))).1
    have hw1 : w.1.1 = 0 := (hmemW w.1).mp w.2
    simp only [he, lowerTri, LinearMap.coe_mk, AddHom.coe_mk, Submodule.sndEquiv]
    ext
    · simp [hw1]
    · simp [hw1]
  · -- (W.mapQ W e hinv).det = f.det  via (M × N)/W ≅ M
    have hcompl : IsCompl W (Submodule.fst ℝ M N) := by
      rw [hW]
      refine ⟨?_, ?_⟩
      · rw [Submodule.disjoint_def]
        intro x hx hxf
        rw [Submodule.snd, Submodule.mem_comap, Submodule.mem_bot, LinearMap.fst_apply] at hx
        rw [Submodule.fst, Submodule.mem_comap, Submodule.mem_bot, LinearMap.snd_apply] at hxf
        ext
        · exact hx
        · exact hxf
      · rw [codisjoint_iff, sup_comm]
        exact Submodule.fst_sup_snd ℝ M N
    set q : ((M × N) ⧸ W) ≃ₗ[ℝ] M :=
      (Submodule.quotientEquivOfIsCompl W (Submodule.fst ℝ M N) hcompl).trans
        (Submodule.fstEquiv ℝ M N) with hq
    have hqmk : ∀ p : M × N, q (Submodule.Quotient.mk p) = p.1 := by
      intro p
      have hmem : ((p.1, 0) : M × N) ∈ Submodule.fst ℝ M N := by
        simp [Submodule.fst]
      have heq : (Submodule.Quotient.mk p : (M × N) ⧸ W) = Submodule.Quotient.mk (p.1, 0) := by
        rw [Submodule.Quotient.eq, hW, Submodule.snd, Submodule.mem_comap, Submodule.mem_bot]
        simp
      rw [hq]
      simp only [LinearEquiv.trans_apply]
      rw [heq]
      have hcoe : (Submodule.Quotient.mk (p.1, 0) : (M × N) ⧸ W)
            = Submodule.Quotient.mk (↑(⟨(p.1, 0), hmem⟩ : Submodule.fst ℝ M N)) := rfl
      rw [hcoe, Submodule.quotientEquivOfIsCompl_apply_mk_coe]
      simp [Submodule.fstEquiv]
    rw [← LinearMap.det_conj f q.symm]
    congr 1
    apply LinearMap.ext
    intro x
    obtain ⟨p, rfl⟩ := Submodule.Quotient.mk_surjective W x
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_symm]
    rw [Submodule.mapQ_apply]
    apply q.injective
    rw [LinearEquiv.apply_symm_apply, hqmk, hqmk]
    change (e p).1 = f p.1
    simp only [he, lowerTri, LinearMap.coe_mk, AddHom.coe_mk]

/-! ## A1 — left/right multiplication on a matrix space

`mulLeftMat K : Matrix (Fin t) (Fin c) ℝ →ₗ _` sends `X ↦ K * X`; via the column equivalence
`Matrix (Fin t) (Fin c) ℝ ≃ₗ (Fin c → Fin t → ℝ)` it conjugates to `c` independent copies of
`K.mulVecLin`, so `det = K.det^c`. Right-mult is the transpose. -/

/-- Left-mult-by-`K` on the `t × c` matrix space. -/
def mulLeftMat {t c : ℕ} (K : Matrix (Fin t) (Fin t) ℝ) :
    Matrix (Fin t) (Fin c) ℝ →ₗ[ℝ] Matrix (Fin t) (Fin c) ℝ where
  toFun X := K * X
  map_add' X Y := by rw [Matrix.mul_add]
  map_smul' a X := by simp [Matrix.mul_smul]

/-- Right-mult-by-`K` on the `r × t` matrix space. -/
def mulRightMat {r t : ℕ} (K : Matrix (Fin t) (Fin t) ℝ) :
    Matrix (Fin r) (Fin t) ℝ →ₗ[ℝ] Matrix (Fin r) (Fin t) ℝ where
  toFun X := X * K
  map_add' X Y := by rw [Matrix.add_mul]
  map_smul' a X := by simp [Matrix.smul_mul]

/-- The column equivalence `Matrix (Fin t) (Fin c) ℝ ≃ₗ (Fin c → Fin t → ℝ)` (a matrix to its
columns). -/
def colEquiv {t c : ℕ} : Matrix (Fin t) (Fin c) ℝ ≃ₗ[ℝ] (Fin c → (Fin t → ℝ)) :=
  (Matrix.transposeLinearEquiv (Fin t) (Fin c) ℝ ℝ).trans (Matrix.ofLinearEquiv ℝ).symm

@[simp] theorem colEquiv_apply {t c : ℕ} (X : Matrix (Fin t) (Fin c) ℝ) (j : Fin c) (i : Fin t) :
    colEquiv X j i = X i j := rfl

/-- **A1 (left)**: left-mult-by-`K` on `Matrix (Fin t) (Fin c) ℝ` has determinant `K.det^c`. -/
theorem det_mulLeft_matrixSpace {t c : ℕ} (K : Matrix (Fin t) (Fin t) ℝ) :
    LinearMap.det (mulLeftMat (c := c) K) = K.det ^ c := by
  -- Conjugate by colEquiv to the block-diagonal of `c` copies of `K.mulVecLin`.
  have hconj :
      (colEquiv (t := t) (c := c)).toLinearMap ∘ₗ (mulLeftMat K) ∘ₗ
          (colEquiv (t := t) (c := c)).symm.toLinearMap
        = LinearMap.pi (fun j : Fin c => (K.mulVecLin).comp (LinearMap.proj j)) := by
    apply LinearMap.ext
    intro v
    apply funext; intro j
    apply funext; intro i
    simp only [LinearMap.comp_apply, LinearMap.pi_apply, LinearMap.proj_apply,
      Matrix.mulVecLin_apply, LinearEquiv.coe_coe, colEquiv_apply]
    change (K * (colEquiv.symm v)) i j = (K *ᵥ v j) i
    rw [Matrix.mul_apply, Matrix.mulVec]
    rfl
  have hdet := LinearMap.det_conj (mulLeftMat (c := c) K) colEquiv
  rw [hconj] at hdet
  rw [← hdet, LinearMap.det_pi (fun _ : Fin c => K.mulVecLin)]
  simp only [show K.mulVecLin = Matrix.toLin' K from rfl, LinearMap.det_toLin']
  rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]

/-- **A1 (right)**: right-mult-by-`K` on `Matrix (Fin r) (Fin t) ℝ` has determinant `K.det^r`. -/
theorem det_mulRight_matrixSpace {r t : ℕ} (K : Matrix (Fin t) (Fin t) ℝ) :
    LinearMap.det (mulRightMat (r := r) K) = K.det ^ r := by
  -- transpose conjugates right-mult-by-K to left-mult-by-Kᵀ; det Kᵀ = det K.
  set τ := Matrix.transposeLinearEquiv (Fin r) (Fin t) ℝ ℝ with hτ
  have hconj : τ.toLinearMap ∘ₗ (mulRightMat K) ∘ₗ τ.symm.toLinearMap
        = mulLeftMat (c := r) Kᵀ := by
    apply LinearMap.ext
    intro Y
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
    change ((Yᵀ * K)ᵀ) = Kᵀ * Y
    rw [Matrix.transpose_mul, Matrix.transpose_transpose]
  have hdet := LinearMap.det_conj (mulRightMat (r := r) K) τ
  rw [hconj] at hdet
  rw [← hdet, det_mulLeft_matrixSpace, Matrix.det_transpose]

/-! ## A2 — the Schur-frame differential and its determinant

The differential of the boundary Schur frame `S(X,K,N,E) = [[K, K·N],[X·K, X·K·N + E]]`, read off as
a linear map on increments `(dK, dN, dX, dE)`. In the natural block pairing it is
block-lower-triangular, so `|det| = |K.det|^(r+c)`. We assemble it as a 3-fold nest of `lowerTri`
over the diagonal blocks `dK ↦ dK` (det 1), `dN ↦ K·dN` (det `K.det^c`), `dX ↦ dX·K`
(det `K.det^r`), `dE ↦ dE` (det 1). -/

/-- The increment space of the Schur frame: `(dK, dN, dX, dE)`. -/
abbrev SchurInc (t r c : ℕ) : Type :=
  Matrix (Fin t) (Fin t) ℝ ×
    (Matrix (Fin t) (Fin c) ℝ ×
      (Matrix (Fin r) (Fin t) ℝ × Matrix (Fin r) (Fin c) ℝ))

/-- `h₃ : dX ↦ dX·K·N` — the coupling from `dX` into `dE`. -/
def h₃ {t r c : ℕ} (K : Matrix (Fin t) (Fin t) ℝ) (N : Matrix (Fin t) (Fin c) ℝ) :
    Matrix (Fin r) (Fin t) ℝ →ₗ[ℝ] Matrix (Fin r) (Fin c) ℝ where
  toFun dX := dX * K * N
  map_add' a b := by simp [Matrix.add_mul]
  map_smul' a b := by simp [Matrix.smul_mul]

/-- The innermost block `(dX, dE) ↦ (dX·K, dE + dX·K·N)` — diagonal `mulRight K` on `dX`, `id` on
`dE`. -/
def g₂ {t r c : ℕ} (K : Matrix (Fin t) (Fin t) ℝ) (N : Matrix (Fin t) (Fin c) ℝ) :
    (Matrix (Fin r) (Fin t) ℝ × Matrix (Fin r) (Fin c) ℝ) →ₗ[ℝ]
      (Matrix (Fin r) (Fin t) ℝ × Matrix (Fin r) (Fin c) ℝ) :=
  lowerTri (mulRightMat K) LinearMap.id (h₃ K N)

/-- `h₂ : dN ↦ (0, X·K·dN)` — the coupling from `dN` into `(dX, dE)`. -/
def h₂ {t r c : ℕ} (X : Matrix (Fin r) (Fin t) ℝ) (K : Matrix (Fin t) (Fin t) ℝ) :
    Matrix (Fin t) (Fin c) ℝ →ₗ[ℝ]
      (Matrix (Fin r) (Fin t) ℝ × Matrix (Fin r) (Fin c) ℝ) where
  toFun dN := (0, X * K * dN)
  map_add' := by intro a b; simp [Matrix.mul_add]
  map_smul' := by intro a b; simp [Matrix.mul_smul]

/-- The middle block `(dN, dX, dE) ↦ (K·dN, dX·K + X·K·dN, dE + dX·K·N)` — diagonal `mulLeft K` on
`dN`, then `g₂` on `(dX, dE)`. -/
def g₁ {t r c : ℕ} (X : Matrix (Fin r) (Fin t) ℝ) (K : Matrix (Fin t) (Fin t) ℝ)
    (N : Matrix (Fin t) (Fin c) ℝ) :
    (Matrix (Fin t) (Fin c) ℝ × (Matrix (Fin r) (Fin t) ℝ × Matrix (Fin r) (Fin c) ℝ)) →ₗ[ℝ]
      (Matrix (Fin t) (Fin c) ℝ × (Matrix (Fin r) (Fin t) ℝ × Matrix (Fin r) (Fin c) ℝ)) :=
  lowerTri (mulLeftMat K) (g₂ K N) (h₂ X K)

/-- `h₁ : dK ↦ (dK·N, X·dK, X·dK·N)` — the coupling from `dK` into `(dN, dX, dE)`. -/
def h₁ {t r c : ℕ} (X : Matrix (Fin r) (Fin t) ℝ) (N : Matrix (Fin t) (Fin c) ℝ) :
    Matrix (Fin t) (Fin t) ℝ →ₗ[ℝ]
      (Matrix (Fin t) (Fin c) ℝ × (Matrix (Fin r) (Fin t) ℝ × Matrix (Fin r) (Fin c) ℝ)) where
  toFun dK := (dK * N, (X * dK, X * dK * N))
  map_add' := by intro a b; simp [Matrix.add_mul, Matrix.mul_add]
  map_smul' := by intro a b; simp [Matrix.smul_mul, Matrix.mul_smul]

/-- **The Schur-frame differential** `DS` on the increment space `(dK, dN, dX, dE)`:
`(dK, dN, dX, dE) ↦ (dK, K·dN + dK·N, dX·K + X·dK, dE + X·dK·N + X·K·dN + dX·K·N)`. -/
def schurFrameDeriv {t r c : ℕ} (X : Matrix (Fin r) (Fin t) ℝ) (K : Matrix (Fin t) (Fin t) ℝ)
    (N : Matrix (Fin t) (Fin c) ℝ) : SchurInc t r c →ₗ[ℝ] SchurInc t r c :=
  lowerTri LinearMap.id (g₁ X K N) (h₁ X N)

/-- The Schur-frame differential evaluated, confirming the block structure of `DS` matches
`S(X,K,N,E) = [[K, K·N],[X·K, X·K·N + E]]` linearised: the four output blocks are
`dK`, `K·dN + dK·N`, `dX·K + X·dK`, `dE + X·dK·N + X·K·dN + dX·K·N`. -/
theorem schurFrameDeriv_apply {t r c : ℕ} (X : Matrix (Fin r) (Fin t) ℝ)
    (K : Matrix (Fin t) (Fin t) ℝ) (N : Matrix (Fin t) (Fin c) ℝ) (p : SchurInc t r c) :
    schurFrameDeriv X K N p =
      (p.1, K * p.2.1 + p.1 * N,
        (p.2.2.1 * K + X * p.1, p.2.2.2 + (X * p.1 * N + X * K * p.2.1 + p.2.2.1 * K * N))) := by
  have h1 : (schurFrameDeriv X K N p).1 = p.1 := rfl
  have h2 : (schurFrameDeriv X K N p).2.1 = K * p.2.1 + p.1 * N := rfl
  have h3 : (schurFrameDeriv X K N p).2.2.1 = p.2.2.1 * K + 0 + X * p.1 := rfl
  have h4 : (schurFrameDeriv X K N p).2.2.2 =
      p.2.2.2 + p.2.2.1 * K * N + X * K * p.2.1 + X * p.1 * N := rfl
  refine Prod.ext h1 (Prod.ext h2 (Prod.ext ?_ ?_))
  · rw [h3, add_zero]
  · rw [h4]; abel

/-- **A2 (keystone)**: the Schur-frame differential has determinant `K.det^(r+c)`. -/
theorem schurFrameDeriv_det {t r c : ℕ} (X : Matrix (Fin r) (Fin t) ℝ)
    (K : Matrix (Fin t) (Fin t) ℝ) (N : Matrix (Fin t) (Fin c) ℝ) :
    LinearMap.det (schurFrameDeriv X K N) = K.det ^ (r + c) := by
  rw [schurFrameDeriv, lowerTri_det, LinearMap.det_id, one_mul, g₁, lowerTri_det,
    det_mulLeft_matrixSpace, g₂, lowerTri_det, det_mulRight_matrixSpace, LinearMap.det_id, mul_one]
  ring

/-- **A2 (keystone, abs form)**: `|det DS| = |K.det|^(r+c)`. This is the parametric, route-free
replacement for the `(3,3,3,3)` hand `Frame3333Deriv_det`. -/
theorem schurFrame_abs_det {t r c : ℕ} (X : Matrix (Fin r) (Fin t) ℝ)
    (K : Matrix (Fin t) (Fin t) ℝ) (N : Matrix (Fin t) (Fin c) ℝ) :
    |LinearMap.det (schurFrameDeriv X K N)| = |K.det| ^ (r + c) := by
  rw [schurFrameDeriv_det, abs_pow]

/-! ## Validation against the `(3,3,3,3)` hand determinant `Frame3333Deriv_det`

`Frame3333Deriv_det = (z 0)^5 · (z 9)^3 · (z 1·z 4 − z 2·z 3)^2`
(`RouteM3333Atom.Frame3333Deriv_det`). With `t = (3,2,1,0)`, the two Schur-frame boundaries are:

* `s = 1`: `t₁ = 2, r₁ = t₀ − t₁ = 1, c₁ = M₁ − t₁ = 1`, with `K₁` the `2×2` LDU core
  `[[a, a·α], [γ·a, γ·a·α + δ]]`, `det K₁ = a·δ` (`= z 1·z 4 − z 2·z 3`). The general law gives
  `|det K₁|^(r₁+c₁) = |det K₁|^2 = (a·δ)^2` — the hand `(z 1·z 4 − z 2·z 3)^2` block.
* `s = 2`: `t₂ = 1, r₂ = 1, c₂ = 2`, with `K₂ = [[b]]`, `det K₂ = b` (`= z 9`). The general law
  gives `|det K₂|^(r₂+c₂) = |det K₂|^3 = |b|^3` — the hand `(z 9)^3` block.

These theorems instantiate `schurFrame_abs_det` at the boundary parameters and confirm both K-blocks
of the hand det arise from the single uniform `|det Kₛ|^(rₛ+cₛ)` law. (The remaining `(z 0)^5` is
the radial blow-up factor, not part of the Schur frame.) -/

/-- Validation, boundary `s = 1` of `(3,3,3,3)`: `t = 2, r = c = 1`, so the frame contributes
`|det K|^2`. With `det K₁ = a·δ` this is the hand `(z 1·z 4 − z 2·z 3)^2` block. -/
theorem schurFrame_abs_det_3333_boundary1 (X : Matrix (Fin 1) (Fin 2) ℝ)
    (K : Matrix (Fin 2) (Fin 2) ℝ) (N : Matrix (Fin 2) (Fin 1) ℝ) :
    |LinearMap.det (schurFrameDeriv X K N)| = |K.det| ^ 2 := by
  rw [schurFrame_abs_det]

/-- Validation, boundary `s = 2` of `(3,3,3,3)`: `t = 1, r = 1, c = 2`, so the frame contributes
`|det K|^3`. With `K = [[b]]` (`det K₂ = b`) this is the hand `(z 9)^3 = |b|^3` block. -/
theorem schurFrame_abs_det_3333_boundary2 (X : Matrix (Fin 1) (Fin 1) ℝ)
    (K : Matrix (Fin 1) (Fin 1) ℝ) (N : Matrix (Fin 1) (Fin 2) ℝ) :
    |LinearMap.det (schurFrameDeriv X K N)| = |K.det| ^ 3 := by
  rw [schurFrame_abs_det]

/-- A `1×1` `K = [[b]]` has `|det K|^3 = |b|^3` (the `z 9³` block, fully concrete). -/
theorem schurFrame_abs_det_3333_boundary2_value (X : Matrix (Fin 1) (Fin 1) ℝ)
    (b : ℝ) (N : Matrix (Fin 1) (Fin 2) ℝ) :
    |LinearMap.det (schurFrameDeriv X (Matrix.of fun _ _ => b) N)| = |b| ^ 3 := by
  rw [schurFrame_abs_det, Matrix.det_unique, Matrix.of_apply]

end DLNFibre.DLN.RLCT
