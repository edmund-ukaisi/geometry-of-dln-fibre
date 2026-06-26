import Mathlib.LinearAlgebra.Determinant
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.Prod
import Mathlib.LinearAlgebra.Projection
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Order.Interval.Finset.Fin
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

/-! ## A3 — the LDU-core parametrization Jacobian determinant

Parametrize a `t × t` matrix `K = L · diag(q) · U` by its strict-lower, diagonal, strict-upper free
entries (`LDUParam t`). The Fréchet derivative of `(L_free, q, U_free) ↦ K` has determinant
`∏_i q_i^{2(t−1−i)}` (independent of the `L, U` point — they are det-1 unit-triangular factors). The
LDU-core factor of the achiever chart; combines with the Schur frame's spectator
`|det Kₛ|^{rₛ+cₛ}`. -/

/-- Strict-lower index set `{(i,j) : j < i}`. -/
abbrev LowIdx (t : ℕ) := {p : Fin t × Fin t // p.2 < p.1}
/-- Strict-upper index set `{(i,j) : i < j}`. -/
abbrev UpIdx (t : ℕ) := {p : Fin t × Fin t // p.1 < p.2}
/-- The LDU parameter space: strict-lower entries, diagonal, strict-upper entries. -/
abbrev LDUParam (t : ℕ) := (LowIdx t → ℝ) × (Fin t → ℝ) × (UpIdx t → ℝ)

/-- Embed strict-lower free entries into a matrix (zero on/above the diagonal). -/
def lowMat {t : ℕ} (l : LowIdx t → ℝ) : Matrix (Fin t) (Fin t) ℝ :=
  Matrix.of fun i j => if h : j < i then l ⟨(i, j), h⟩ else 0

/-- Embed strict-upper free entries into a matrix (zero on/below the diagonal). -/
def upMat {t : ℕ} (u : UpIdx t → ℝ) : Matrix (Fin t) (Fin t) ℝ :=
  Matrix.of fun i j => if h : i < j then u ⟨(i, j), h⟩ else 0

/-- The entry of the assembled matrix `lowMat l + diagonal d + upMat u`. -/
theorem assemble_apply {t : ℕ} (l : LowIdx t → ℝ) (d : Fin t → ℝ) (u : UpIdx t → ℝ) (i j : Fin t) :
    (lowMat l + Matrix.diagonal d + upMat u) i j =
      if h : j < i then l ⟨(i, j), h⟩ else if h : i < j then u ⟨(i, j), h⟩ else d i := by
  simp only [lowMat, upMat, Matrix.add_apply, Matrix.of_apply, Matrix.diagonal_apply]
  rcases lt_trichotomy i j with h | h | h
  · rw [dif_neg (asymm h), dif_pos h, dif_neg (asymm h), dif_pos h, if_neg (ne_of_lt h)]
    ring
  · subst h
    rw [dif_neg (lt_irrefl _), dif_neg (lt_irrefl _), dif_neg (lt_irrefl _), dif_neg (lt_irrefl _),
      if_pos rfl]
    ring
  · rw [dif_pos h, dif_pos h, if_neg (Ne.symm (ne_of_lt h)), dif_neg (asymm h)]
    ring

/-- The LDU coordinate split: a `t×t` matrix ↔ its strict-lower, diagonal, strict-upper entries. -/
def matrixSplit {t : ℕ} : Matrix (Fin t) (Fin t) ℝ ≃ₗ[ℝ] LDUParam t where
  toFun M := (fun p => M p.1.1 p.1.2, fun i => M i i, fun p => M p.1.1 p.1.2)
  map_add' M N := by refine Prod.ext rfl (Prod.ext rfl rfl)
  map_smul' a M := by refine Prod.ext rfl (Prod.ext rfl rfl)
  invFun w := lowMat w.1 + Matrix.diagonal w.2.1 + upMat w.2.2
  left_inv M := by
    ext i j
    change (lowMat (fun p => M p.1.1 p.1.2) + Matrix.diagonal (fun i => M i i)
          + upMat (fun p => M p.1.1 p.1.2)) i j = M i j
    rw [assemble_apply]
    rcases lt_trichotomy i j with h | h | h
    · rw [dif_neg (asymm h), dif_pos h]
    · subst h; rw [dif_neg (lt_irrefl _), dif_neg (lt_irrefl _)]
    · rw [dif_pos h]
  right_inv w := by
    obtain ⟨l, d, u⟩ := w
    refine Prod.ext ?_ (Prod.ext ?_ ?_)
    · ext p; obtain ⟨⟨i, j⟩, hp⟩ := p
      change (lowMat l + Matrix.diagonal d + upMat u) i j = _
      rw [assemble_apply, dif_pos hp]
    · ext i
      change (lowMat l + Matrix.diagonal d + upMat u) i i = _
      rw [assemble_apply, dif_neg (lt_irrefl _), dif_neg (lt_irrefl _)]
    · ext p; obtain ⟨⟨i, j⟩, hp⟩ := p
      change (lowMat l + Matrix.diagonal d + upMat u) i j = _
      rw [assemble_apply, dif_neg (asymm hp), dif_pos hp]

/-! ### The diagonal-point LDU Jacobian determinant

At the diagonal point `L = U = 1` (so `K = diag q`), the LDU differential
`(dl, dq, du) ↦ lowMat dl · diag q + diag dq + diag q · upMat du` is **block-diagonal** under
`matrixSplit`: the strict-lower output reads only `dl` (scaled by `q` columnwise), the diagonal
reads `dq`, the strict-upper reads only `du` (scaled by `q` rowwise). Its determinant is
`∏_i q_i^{2(t−1−i)}`.

(The general-`L,U` LDU Jacobian has the SAME determinant — the unit-triangular `L, U` factors are
det 1 — but its proof additionally needs the unit-factor conjugation + a triangular-det over
`LowIdx`; see `design.md` §4 "Phase A build status". The diagonal-point case is the load-bearing
core and is what the rate identity evaluates at the achiever pivot.) -/

/-- The columnwise `q`-scaling on strict-lower coordinates: `dl ↦ (p ↦ dl p · q p.col)`. -/
def lowerScale {t : ℕ} (q : Fin t → ℝ) : (LowIdx t → ℝ) →ₗ[ℝ] (LowIdx t → ℝ) :=
  LinearMap.pi (fun p : LowIdx t => (LinearMap.mulRight ℝ (q p.1.2)).comp (LinearMap.proj p))

/-- The rowwise `q`-scaling on strict-upper coordinates: `du ↦ (p ↦ du p · q p.row)`. -/
def upperScale {t : ℕ} (q : Fin t → ℝ) : (UpIdx t → ℝ) →ₗ[ℝ] (UpIdx t → ℝ) :=
  LinearMap.pi (fun p : UpIdx t => (LinearMap.mulRight ℝ (q p.1.1)).comp (LinearMap.proj p))

/-- **The multiplicity count (strict-lower)**: `∏_{(i,j): j<i} q_j = ∏_j q_j^{t−1−j}`. -/
theorem prod_lowIdx_col {t : ℕ} (q : Fin t → ℝ) :
    (∏ p : LowIdx t, q (p.1).2) = ∏ j : Fin t, (q j) ^ ((t : ℕ) - 1 - (j : ℕ)) := by
  rw [← Finset.prod_subtype (Finset.univ.filter (fun p : Fin t × Fin t => p.2 < p.1))
        (fun p => by simp) (fun p => q p.2)]
  rw [← Finset.prod_fiberwise_of_maps_to (t := (Finset.univ : Finset (Fin t)))
        (g := fun p : Fin t × Fin t => p.2) (fun x _ => Finset.mem_univ _) (fun p => q p.2)]
  apply Finset.prod_congr rfl
  intro j _
  rw [Finset.prod_congr rfl (fun p hp => by
    simp only [Finset.mem_filter] at hp; rw [hp.2])]
  rw [Finset.prod_const]
  congr 1
  rw [← Fin.card_Ioi (a := j)]
  apply Finset.card_bij (fun p _ => p.1)
  · intro p hp; simp only [Finset.mem_filter] at hp; simp [Finset.mem_Ioi, ← hp.2, hp.1]
  · intro p hp q hq h
    simp only [Finset.mem_filter] at hp hq
    apply Prod.ext h; rw [hp.2, hq.2]
  · intro i hi; simp only [Finset.mem_Ioi] at hi
    exact ⟨(i, j), by simp [Finset.mem_filter, hi], rfl⟩

/-- **The multiplicity count (strict-upper)**: `∏_{(i,j): i<j} q_i = ∏_i q_i^{t−1−i}`. -/
theorem prod_upIdx_row {t : ℕ} (q : Fin t → ℝ) :
    (∏ p : UpIdx t, q (p.1).1) = ∏ i : Fin t, (q i) ^ ((t : ℕ) - 1 - (i : ℕ)) := by
  rw [← Finset.prod_subtype (Finset.univ.filter (fun p : Fin t × Fin t => p.1 < p.2))
        (fun p => by simp) (fun p => q p.1)]
  rw [← Finset.prod_fiberwise_of_maps_to (t := (Finset.univ : Finset (Fin t)))
        (g := fun p : Fin t × Fin t => p.1) (fun x _ => Finset.mem_univ _) (fun p => q p.1)]
  apply Finset.prod_congr rfl
  intro i _
  rw [Finset.prod_congr rfl (fun p hp => by
    simp only [Finset.mem_filter] at hp; rw [hp.2])]
  rw [Finset.prod_const]
  congr 1
  rw [← Fin.card_Ioi (a := i)]
  apply Finset.card_bij (fun p _ => p.2)
  · intro p hp; simp only [Finset.mem_filter] at hp; simp [Finset.mem_Ioi, ← hp.2, hp.1]
  · intro p hp q hq h
    simp only [Finset.mem_filter] at hp hq
    apply Prod.ext (by rw [hp.2, hq.2]) h
  · intro j hj; simp only [Finset.mem_Ioi] at hj
    exact ⟨(i, j), by simp [Finset.mem_filter, hj], rfl⟩

/-- The strict-lower `q`-scaling block has determinant `∏_j q_j^{t−1−j}`. -/
theorem lowerScale_det {t : ℕ} (q : Fin t → ℝ) :
    LinearMap.det (lowerScale q) = ∏ j : Fin t, (q j) ^ ((t : ℕ) - 1 - (j : ℕ)) := by
  rw [lowerScale, LinearMap.det_pi]
  rw [Finset.prod_congr rfl (fun p _ => by simp [LinearMap.det_ring] :
    ∀ p ∈ Finset.univ, LinearMap.det (LinearMap.mulRight ℝ (q (p : LowIdx t).1.2)) = q p.1.2)]
  exact prod_lowIdx_col q

/-- The strict-upper `q`-scaling block has determinant `∏_i q_i^{t−1−i}`. -/
theorem upperScale_det {t : ℕ} (q : Fin t → ℝ) :
    LinearMap.det (upperScale q) = ∏ i : Fin t, (q i) ^ ((t : ℕ) - 1 - (i : ℕ)) := by
  rw [upperScale, LinearMap.det_pi]
  rw [Finset.prod_congr rfl (fun p _ => by simp [LinearMap.det_ring] :
    ∀ p ∈ Finset.univ, LinearMap.det (LinearMap.mulRight ℝ (q (p : UpIdx t).1.1)) = q p.1.1)]
  exact prod_upIdx_row q

/-- **The diagonal-point LDU Jacobian** as a block-diagonal endomorphism of `LDUParam`:
strict-lower scaled columnwise by `q`, diagonal fixed, strict-upper scaled rowwise by `q`. The
differential of `(L_free, q, U_free) ↦ L · diag q · U` at `L = U = 1`, read in LDU coordinates. -/
def lduCoreDerivDiag {t : ℕ} (q : Fin t → ℝ) : LDUParam t →ₗ[ℝ] LDUParam t :=
  (lowerScale q).prodMap (LinearMap.id.prodMap (upperScale q))

/-- **A3 (diagonal point)**: `det (lduCoreDerivDiag q) = ∏_i q_i^{2(t−1−i)}`. -/
theorem lduCoreDerivDiag_det {t : ℕ} (q : Fin t → ℝ) :
    LinearMap.det (lduCoreDerivDiag q) = ∏ i : Fin t, (q i) ^ (2 * ((t : ℕ) - 1 - (i : ℕ))) := by
  rw [lduCoreDerivDiag, LinearMap.det_prodMap, LinearMap.det_prodMap, LinearMap.det_id,
    lowerScale_det, upperScale_det, one_mul, ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro i _
  rw [← pow_add, two_mul]

/-- **A3 (diagonal point, abs form)**: `|det (lduCoreDerivDiag q)| = ∏_i |q_i|^{2(t−1−i)}`. -/
theorem lduCoreDerivDiag_abs_det {t : ℕ} (q : Fin t → ℝ) :
    |LinearMap.det (lduCoreDerivDiag q)| = ∏ i : Fin t, |q i| ^ (2 * ((t : ℕ) - 1 - (i : ℕ))) := by
  rw [lduCoreDerivDiag_det, Finset.abs_prod]
  apply Finset.prod_congr rfl
  intro i _
  rw [abs_pow]

/-- Validation, the `(3,3,3,3)` LDU core at boundary `s = 1` (`t = 2`): the A3 exponent product
collapses to `q_0^2`, matching the hand `Kparam3333Deriv_det = (x 1)^2 = a^2` (`q_0 = a = x 1`). -/
theorem lduCoreDerivDiag_det_3333_boundary1 (q : Fin 2 → ℝ) :
    LinearMap.det (lduCoreDerivDiag q) = (q 0) ^ 2 := by
  rw [lduCoreDerivDiag_det, Fin.prod_univ_two]
  norm_num

/-! ### The general-`L,U` LDU Jacobian determinant

The LDU core `K = L · diag q · U` at a GENERAL point (`L = 1 + lowMat l` unit-lower,
`U = 1 + upMat u`
unit-upper). The Fréchet derivative `lduCoreDeriv l q u : LDUParam → LDUParam` (in LDU coords) has
determinant `∏_i q_i^{2(t−1−i)}` — the SAME as the diagonal point, since `L, U` are det-1
unit-triangular factors. This is what Phase B's `phiFlat_abs_det` needs (the achiever LDU core is at
a general point,
`Kparam3333 u 2 = u1·u2` ⟹ `L ≠ 1`).

Route: factor `lduDerivMat = L · lduCoreMat · U` (the conjugated core), where `lduCoreMat` is
block-diagonal under `matrixSplit` into `lowerBlock L⁻¹`, `id`, `upperBlock U⁻¹`; the unit
conjugation
contributes `det = (det L)^t · (det U)^t = 1`. -/

/-- `lowMat` as a linear map on the strict-lower coordinates. -/
def lowMatL {t : ℕ} : (LowIdx t → ℝ) →ₗ[ℝ] Matrix (Fin t) (Fin t) ℝ where
  toFun := lowMat
  map_add' a b := by
    ext i j; simp only [lowMat, Matrix.of_apply, Matrix.add_apply, Pi.add_apply]; split_ifs <;> simp
  map_smul' c a := by
    ext i j
    simp only [lowMat, Matrix.of_apply, Matrix.smul_apply, Pi.smul_apply, smul_eq_mul,
      RingHom.id_apply]
    split_ifs <;> simp

/-- `upMat` as a linear map on the strict-upper coordinates. -/
def upMatL {t : ℕ} : (UpIdx t → ℝ) →ₗ[ℝ] Matrix (Fin t) (Fin t) ℝ where
  toFun := upMat
  map_add' a b := by
    ext i j; simp only [upMat, Matrix.of_apply, Matrix.add_apply, Pi.add_apply]; split_ifs <;> simp
  map_smul' c a := by
    ext i j
    simp only [upMat, Matrix.of_apply, Matrix.smul_apply, Pi.smul_apply, smul_eq_mul,
      RingHom.id_apply]
    split_ifs <;> simp

@[simp] theorem lowMatL_apply {t : ℕ} (l : LowIdx t → ℝ) (i j : Fin t) :
    lowMatL l i j = if h : j < i then l ⟨(i, j), h⟩ else 0 := rfl
@[simp] theorem upMatL_apply {t : ℕ} (u : UpIdx t → ℝ) (i j : Fin t) :
    upMatL u i j = if h : i < j then u ⟨(i, j), h⟩ else 0 := rfl

/-- `lowMatL` of a single basis coordinate is the single-entry matrix at `(p'.row, p'.col)`. -/
theorem lowMatL_single {t : ℕ} (p' : LowIdx t) (i j : Fin t) :
    lowMatL (Pi.single p' 1) i j = if (i = p'.1.1 ∧ j = p'.1.2) then 1 else 0 := by
  rw [lowMatL_apply]
  by_cases hji : j < i
  · rw [dif_pos hji, Pi.single_apply]
    by_cases hp : (i = p'.1.1 ∧ j = p'.1.2)
    · rw [if_pos hp, if_pos]; obtain ⟨h1, h2⟩ := hp; exact Subtype.ext (Prod.ext h1 h2)
    · rw [if_neg hp, if_neg]; intro hc; apply hp
      have := Subtype.ext_iff.mp hc; exact ⟨congrArg Prod.fst this, congrArg Prod.snd this⟩
  · rw [dif_neg hji, if_neg]; rintro ⟨rfl, rfl⟩; exact hji p'.2

/-- `upMatL` of a single basis coordinate is the single-entry matrix at `(p'.row, p'.col)`. -/
theorem upMatL_single {t : ℕ} (p' : UpIdx t) (i j : Fin t) :
    upMatL (Pi.single p' 1) i j = if (i = p'.1.1 ∧ j = p'.1.2) then 1 else 0 := by
  rw [upMatL_apply]
  by_cases hij : i < j
  · rw [dif_pos hij, Pi.single_apply]
    by_cases hp : (i = p'.1.1 ∧ j = p'.1.2)
    · rw [if_pos hp, if_pos]; obtain ⟨h1, h2⟩ := hp; exact Subtype.ext (Prod.ext h1 h2)
    · rw [if_neg hp, if_neg]; intro hc; apply hp
      have := Subtype.ext_iff.mp hc; exact ⟨congrArg Prod.fst this, congrArg Prod.snd this⟩
  · rw [dif_neg hij, if_neg]; rintro ⟨rfl, rfl⟩; exact hij p'.2

theorem lowMatSingle_mulLeft {t : ℕ} (A : Matrix (Fin t) (Fin t) ℝ) (p' : LowIdx t) (i c : Fin t) :
    (A * lowMatL (Pi.single p' 1)) i c = if c = p'.1.2 then A i p'.1.1 else 0 := by
  rw [Matrix.mul_apply, Finset.sum_eq_single p'.1.1]
  · rw [lowMatL_single]
    by_cases hc : c = p'.1.2
    · rw [if_pos hc, if_pos ⟨rfl, hc⟩, mul_one]
    · rw [if_neg hc, if_neg (by rintro ⟨_, h2⟩; exact hc h2), mul_zero]
  · intro b _ hb; rw [lowMatL_single, if_neg (by rintro ⟨h1, _⟩; exact hb h1), mul_zero]
  · intro h; exact absurd (Finset.mem_univ _) h

theorem upMatSingle_mulRight {t : ℕ} (B : Matrix (Fin t) (Fin t) ℝ) (p' : UpIdx t) (r c : Fin t) :
    (upMatL (Pi.single p' 1) * B) r c = if r = p'.1.1 then B p'.1.2 c else 0 := by
  rw [Matrix.mul_apply, Finset.sum_eq_single p'.1.2]
  · rw [upMatL_single]
    by_cases hr : r = p'.1.1
    · rw [if_pos hr, if_pos ⟨hr, rfl⟩, one_mul]
    · rw [if_neg hr, if_neg (by rintro ⟨h1, _⟩; exact hr h1), zero_mul]
  · intro b _ hb; rw [upMatL_single, if_neg (by rintro ⟨_, h2⟩; exact hb h2), zero_mul]
  · intro h; exact absurd (Finset.mem_univ _) h

/-- The row-major lex order on `LowIdx`, making the lower block matrix lower-triangular. -/
noncomputable instance lowOrd {t : ℕ} : LinearOrder (LowIdx t) :=
  LinearOrder.lift' (fun p => (toLex p.1 : Fin t ×ₗ Fin t))
    (fun _ _ h => Subtype.ext (toLex.injective h))
/-- The row-major lex order on `UpIdx`. -/
noncomputable instance upOrd {t : ℕ} : LinearOrder (UpIdx t) :=
  LinearOrder.lift' (fun p => (toLex p.1 : Fin t ×ₗ Fin t))
    (fun _ _ h => Subtype.ext (toLex.injective h))

/-- Extract strict-lower coordinates from a matrix. -/
def lowerProj {t : ℕ} : Matrix (Fin t) (Fin t) ℝ →ₗ[ℝ] (LowIdx t → ℝ) where
  toFun M p := M p.1.1 p.1.2
  map_add' a b := by funext p; simp
  map_smul' c a := by funext p; simp
/-- Extract strict-upper coordinates from a matrix. -/
def upperProj {t : ℕ} : Matrix (Fin t) (Fin t) ℝ →ₗ[ℝ] (UpIdx t → ℝ) where
  toFun M p := M p.1.1 p.1.2
  map_add' a b := by funext p; simp
  map_smul' c a := by funext p; simp
/-- Extract diagonal coordinates from a matrix. -/
def diagProj {t : ℕ} : Matrix (Fin t) (Fin t) ℝ →ₗ[ℝ] (Fin t → ℝ) where
  toFun M i := M i i
  map_add' a b := by funext i; simp
  map_smul' c a := by funext i; simp
/-- Embed diagonal coordinates as a diagonal matrix, linearly. -/
def diagAsMat {t : ℕ} : (Fin t → ℝ) →ₗ[ℝ] Matrix (Fin t) (Fin t) ℝ where
  toFun := Matrix.diagonal
  map_add' a b := by
    ext i j
    simp only [Matrix.diagonal, Matrix.of_apply, Matrix.add_apply, Pi.add_apply]
    split_ifs <;> simp
  map_smul' c a := by
    ext i j
    simp only [Matrix.diagonal, Matrix.of_apply, Matrix.smul_apply, Pi.smul_apply, smul_eq_mul,
      RingHom.id_apply]
    split_ifs <;> simp
@[simp] theorem diagAsMat_apply {t : ℕ} (v : Fin t → ℝ) : diagAsMat v = Matrix.diagonal v := rfl

/-- The lower block of the conjugated core: `dl ↦ lower-coords (A · lowMat dl · diag q)`. -/
def lowerBlock {t : ℕ} (A : Matrix (Fin t) (Fin t) ℝ) (q : Fin t → ℝ) :
    (LowIdx t → ℝ) →ₗ[ℝ] (LowIdx t → ℝ) :=
  lowerProj.comp ((LinearMap.mulRight ℝ (Matrix.diagonal q)).comp
    ((LinearMap.mulLeft ℝ A).comp lowMatL))
/-- The upper block of the conjugated core: `du ↦ upper-coords (diag q · upMat du · B)`. -/
def upperBlock {t : ℕ} (B : Matrix (Fin t) (Fin t) ℝ) (q : Fin t → ℝ) :
    (UpIdx t → ℝ) →ₗ[ℝ] (UpIdx t → ℝ) :=
  upperProj.comp ((LinearMap.mulLeft ℝ (Matrix.diagonal q)).comp
    ((LinearMap.mulRight ℝ B).comp upMatL))

theorem lowerBlock_entry {t : ℕ} (A : Matrix (Fin t) (Fin t) ℝ) (q : Fin t → ℝ) (p p' : LowIdx t) :
    LinearMap.toMatrix' (lowerBlock A q) p p'
      = if p'.1.2 = p.1.2 then A p.1.1 p'.1.1 * q p.1.2 else 0 := by
  rw [LinearMap.toMatrix'_apply]
  change (A * lowMatL (Pi.single p' 1) * Matrix.diagonal q) p.1.1 p.1.2 = _
  rw [Matrix.mul_apply, Finset.sum_eq_single p.1.2]
  · rw [Matrix.diagonal_apply_eq, lowMatSingle_mulLeft]
    by_cases hc : p'.1.2 = p.1.2
    · rw [if_pos hc, if_pos hc.symm]
    · rw [if_neg hc, if_neg (fun h => hc h.symm), zero_mul]
  · intro b _ hb; rw [Matrix.diagonal_apply_ne _ hb, mul_zero]
  · intro h; exact absurd (Finset.mem_univ _) h

theorem upperBlock_entry {t : ℕ} (B : Matrix (Fin t) (Fin t) ℝ) (q : Fin t → ℝ) (p p' : UpIdx t) :
    LinearMap.toMatrix' (upperBlock B q) p p'
      = if p'.1.1 = p.1.1 then q p.1.1 * B p'.1.2 p.1.2 else 0 := by
  rw [LinearMap.toMatrix'_apply]
  change (Matrix.diagonal q * (upMatL (Pi.single p' 1) * B)) p.1.1 p.1.2 = _
  rw [Matrix.mul_apply, Finset.sum_eq_single p.1.1]
  · rw [Matrix.diagonal_apply_eq, upMatSingle_mulRight]
    by_cases hr : p'.1.1 = p.1.1
    · rw [if_pos hr, if_pos hr.symm]
    · rw [if_neg hr, if_neg (fun h => hr h.symm), mul_zero]
  · intro b _ hb; rw [Matrix.diagonal_apply_ne' _ hb, zero_mul]
  · intro h; exact absurd (Finset.mem_univ _) h

/-- The lower block of a unit-lower-triangular `A` has det `∏ q_j^{t−1−j}` (`A` triangular ⟹ the
block is lower-triangular in lex order, with diagonal `q p.col`). -/
theorem lowerBlock_det {t : ℕ} (A : Matrix (Fin t) (Fin t) ℝ)
    (hAdiag : ∀ i, A i i = 1) (hAtri : A.BlockTriangular OrderDual.toDual) (q : Fin t → ℝ) :
    LinearMap.det (lowerBlock A q) = ∏ p : LowIdx t, q p.1.2 := by
  rw [← LinearMap.det_toMatrix' (lowerBlock A q), Matrix.det_of_lowerTriangular]
  · apply Finset.prod_congr rfl
    intro p _
    rw [lowerBlock_entry, if_pos rfl, hAdiag, one_mul]
  · intro p p' hpp'
    have hpp'2 : @LT.lt (LowIdx t) (lowOrd).toLT p p' := hpp'
    rw [lowerBlock_entry]
    by_cases hcol : p'.1.2 = p.1.2
    · rw [if_pos hcol]
      have hrow : p.1.1 < p'.1.1 := by
        have hlex : toLex p.1 < toLex p'.1 := hpp'
        rw [Prod.Lex.lt_iff] at hlex
        rcases hlex with h | ⟨_, h2⟩
        · exact h
        · exact absurd hcol.symm (ne_of_lt h2)
      rw [hAtri (by rw [OrderDual.toDual_lt_toDual]; exact hrow), zero_mul]
    · rw [if_neg hcol]

/-- The upper block of a unit-upper-triangular `B` has det `∏ q_i^{t−1−i}`. -/
theorem upperBlock_det {t : ℕ} (B : Matrix (Fin t) (Fin t) ℝ)
    (hBdiag : ∀ i, B i i = 1) (hBtri : B.BlockTriangular _root_.id) (q : Fin t → ℝ) :
    LinearMap.det (upperBlock B q) = ∏ p : UpIdx t, q p.1.1 := by
  rw [← LinearMap.det_toMatrix' (upperBlock B q), Matrix.det_of_lowerTriangular]
  · apply Finset.prod_congr rfl
    intro p _
    rw [upperBlock_entry, if_pos rfl, hBdiag, mul_one]
  · intro p p' hpp'
    have hpp'2 : @LT.lt (UpIdx t) (upOrd).toLT p p' := hpp'
    rw [upperBlock_entry]
    by_cases hrow : p'.1.1 = p.1.1
    · rw [if_pos hrow]
      have hcol : p.1.2 < p'.1.2 := by
        have hlex : toLex p.1 < toLex p'.1 := hpp'
        rw [Prod.Lex.lt_iff] at hlex
        rcases hlex with h | ⟨_, h2⟩
        · exact absurd hrow.symm (ne_of_lt h)
        · exact h2
      rw [hBtri hcol, mul_zero]
    · rw [if_neg hrow]

/-- `L' = 1 + lowMat l` is lower-triangular. -/
theorem unitLow_blockTri {t : ℕ} (l : LowIdx t → ℝ) :
    (1 + lowMatL l : Matrix (Fin t) (Fin t) ℝ).BlockTriangular OrderDual.toDual := by
  intro i j hij
  rw [OrderDual.toDual_lt_toDual] at hij
  simp only [Matrix.add_apply, lowMatL_apply, Matrix.one_apply, dif_neg (asymm hij)]
  simp [ne_of_lt hij]
/-- `det (1 + lowMat l) = 1`. -/
theorem unitLow_det {t : ℕ} (l : LowIdx t → ℝ) :
    (1 + lowMatL l : Matrix (Fin t) (Fin t) ℝ).det = 1 := by
  rw [Matrix.det_of_lowerTriangular _ (unitLow_blockTri l)]
  apply Finset.prod_eq_one; intro i _; simp [lowMatL_apply]
theorem unitLow_isUnit {t : ℕ} (l : LowIdx t → ℝ) :
    IsUnit (1 + lowMatL l : Matrix (Fin t) (Fin t) ℝ).det := by rw [unitLow_det]; exact isUnit_one
/-- The inverse of `1 + lowMat l` has unit diagonal. -/
theorem unitLow_inv_diag {t : ℕ} (l : LowIdx t → ℝ) (i : Fin t) :
    (1 + lowMatL l : Matrix (Fin t) (Fin t) ℝ)⁻¹ i i = 1 := by
  set L := (1 + lowMatL l : Matrix (Fin t) (Fin t) ℝ) with hL
  haveI : Invertible L := L.invertibleOfIsUnitDet (unitLow_isUnit l)
  have hinvtri : (L⁻¹).BlockTriangular OrderDual.toDual :=
    Matrix.blockTriangular_inv_of_blockTriangular (unitLow_blockTri l)
  have h1 : (L⁻¹ * L) i i = 1 := by rw [Matrix.nonsing_inv_mul L (unitLow_isUnit l)]; simp
  rw [Matrix.mul_apply, Finset.sum_eq_single i] at h1
  · have hLii : L i i = 1 := by
      rw [hL]; simp [lowMatL_apply, Matrix.one_apply_eq]
    rw [hLii, mul_one] at h1; exact h1
  · intro k _ hk
    rcases lt_or_gt_of_ne hk with h | h
    · have : L k i = 0 := by
        rw [hL]; simp only [Matrix.add_apply, Matrix.one_apply, lowMatL_apply, dif_neg (asymm h)]
        simp [ne_of_lt h]
      rw [this, mul_zero]
    · rw [hinvtri (by rw [OrderDual.toDual_lt_toDual]; exact h), zero_mul]
  · intro hi; exact absurd (Finset.mem_univ i) hi
theorem unitLow_inv_blockTri {t : ℕ} (l : LowIdx t → ℝ) :
    (1 + lowMatL l : Matrix (Fin t) (Fin t) ℝ)⁻¹.BlockTriangular OrderDual.toDual := by
  haveI : Invertible (1 + lowMatL l : Matrix (Fin t) (Fin t) ℝ) :=
    (1 + lowMatL l).invertibleOfIsUnitDet (unitLow_isUnit l)
  exact Matrix.blockTriangular_inv_of_blockTriangular (unitLow_blockTri l)

/-- `U' = 1 + upMat u` is upper-triangular. -/
theorem unitUp_blockTri {t : ℕ} (u : UpIdx t → ℝ) :
    (1 + upMatL u : Matrix (Fin t) (Fin t) ℝ).BlockTriangular _root_.id := by
  intro i j hij
  simp only [_root_.id] at hij
  simp only [Matrix.add_apply, upMatL_apply, Matrix.one_apply, dif_neg (asymm hij)]
  simp [ne_of_gt hij]
/-- `det (1 + upMat u) = 1`. -/
theorem unitUp_det {t : ℕ} (u : UpIdx t → ℝ) :
    (1 + upMatL u : Matrix (Fin t) (Fin t) ℝ).det = 1 := by
  rw [Matrix.det_of_upperTriangular (unitUp_blockTri u)]
  apply Finset.prod_eq_one; intro i _; simp [upMatL_apply]
theorem unitUp_isUnit {t : ℕ} (u : UpIdx t → ℝ) :
    IsUnit (1 + upMatL u : Matrix (Fin t) (Fin t) ℝ).det := by rw [unitUp_det]; exact isUnit_one
/-- The inverse of `1 + upMat u` has unit diagonal. -/
theorem unitUp_inv_diag {t : ℕ} (u : UpIdx t → ℝ) (i : Fin t) :
    (1 + upMatL u : Matrix (Fin t) (Fin t) ℝ)⁻¹ i i = 1 := by
  set U := (1 + upMatL u : Matrix (Fin t) (Fin t) ℝ) with hU
  haveI : Invertible U := U.invertibleOfIsUnitDet (unitUp_isUnit u)
  have hinvtri : (U⁻¹).BlockTriangular _root_.id :=
    Matrix.blockTriangular_inv_of_blockTriangular (unitUp_blockTri u)
  have h1 : (U * U⁻¹) i i = 1 := by rw [Matrix.mul_nonsing_inv U (unitUp_isUnit u)]; simp
  rw [Matrix.mul_apply, Finset.sum_eq_single i] at h1
  · have hUii : U i i = 1 := by
      rw [hU]; simp [upMatL_apply, Matrix.one_apply_eq]
    rw [hUii, one_mul] at h1; exact h1
  · intro k _ hk
    rcases lt_or_gt_of_ne hk with h | h
    · have : U i k = 0 := by
        rw [hU]; simp only [Matrix.add_apply, Matrix.one_apply, upMatL_apply, dif_neg (asymm h)]
        simp [ne_of_gt h]
      rw [this, zero_mul]
    · rw [hinvtri h, mul_zero]
  · intro hi; exact absurd (Finset.mem_univ i) hi
theorem unitUp_inv_blockTri {t : ℕ} (u : UpIdx t → ℝ) :
    (1 + upMatL u : Matrix (Fin t) (Fin t) ℝ)⁻¹.BlockTriangular _root_.id := by
  haveI : Invertible (1 + upMatL u : Matrix (Fin t) (Fin t) ℝ) :=
    (1 + upMatL u).invertibleOfIsUnitDet (unitUp_isUnit u)
  exact Matrix.blockTriangular_inv_of_blockTriangular (unitUp_blockTri u)

/-- The raw LDU differential matrix `M(dl,dq,du) = lowMat dl · D · U' + L' · diag dq · U' + L' · D ·
upMat du` (the Fréchet derivative of `(L,q,U) ↦ L · diag q · U`). -/
def lduDerivMat {t : ℕ} (l : LowIdx t → ℝ) (q : Fin t → ℝ) (u : UpIdx t → ℝ) :
    LDUParam t →ₗ[ℝ] Matrix (Fin t) (Fin t) ℝ :=
  let Lp := (1 + lowMatL l : Matrix (Fin t) (Fin t) ℝ)
  let Up := (1 + upMatL u : Matrix (Fin t) (Fin t) ℝ)
  let D := Matrix.diagonal q
  ((LinearMap.mulRight ℝ (D * Up)).comp (lowMatL.comp (LinearMap.fst ℝ _ _)))
  + ((LinearMap.mulRight ℝ Up).comp ((LinearMap.mulLeft ℝ Lp).comp
      (diagAsMat.comp ((LinearMap.fst ℝ _ _).comp (LinearMap.snd ℝ _ _)))))
  + ((LinearMap.mulLeft ℝ (Lp * D)).comp (upMatL.comp
      ((LinearMap.snd ℝ _ _).comp (LinearMap.snd ℝ _ _))))

theorem lduDerivMat_apply {t : ℕ} (l : LowIdx t → ℝ) (q : Fin t → ℝ) (u : UpIdx t → ℝ)
    (w : LDUParam t) :
    lduDerivMat l q u w
      = lowMatL w.1 * (Matrix.diagonal q * (1 + upMatL u))
        + (1 + lowMatL l) * (Matrix.diagonal w.2.1) * (1 + upMatL u)
        + ((1 + lowMatL l) * Matrix.diagonal q) * upMatL w.2.2 := by
  simp only [lduDerivMat, LinearMap.add_apply, LinearMap.comp_apply, LinearMap.mulRight_apply,
    LinearMap.mulLeft_apply, LinearMap.fst_apply, LinearMap.snd_apply, diagAsMat_apply,
    Matrix.mul_assoc]

/-- The conjugated (block-diagonal) core matrix `N'(dl,dq,du) = L'⁻¹ · lowMat dl · D + diag dq + D ·
upMat du · U'⁻¹`. -/
def lduCoreMat {t : ℕ} (l : LowIdx t → ℝ) (q : Fin t → ℝ) (u : UpIdx t → ℝ) :
    LDUParam t →ₗ[ℝ] Matrix (Fin t) (Fin t) ℝ :=
  let Lpi := (1 + lowMatL l : Matrix (Fin t) (Fin t) ℝ)⁻¹
  let Upi := (1 + upMatL u : Matrix (Fin t) (Fin t) ℝ)⁻¹
  let D := Matrix.diagonal q
  ((LinearMap.mulRight ℝ D).comp ((LinearMap.mulLeft ℝ Lpi).comp
      (lowMatL.comp (LinearMap.fst ℝ _ _))))
  + (diagAsMat.comp ((LinearMap.fst ℝ _ _).comp (LinearMap.snd ℝ _ _)))
  + ((LinearMap.mulLeft ℝ D).comp ((LinearMap.mulRight ℝ Upi).comp (upMatL.comp
      ((LinearMap.snd ℝ _ _).comp (LinearMap.snd ℝ _ _)))))

theorem lduCoreMat_apply {t : ℕ} (l : LowIdx t → ℝ) (q : Fin t → ℝ) (u : UpIdx t → ℝ)
    (w : LDUParam t) :
    lduCoreMat l q u w
      = (1 + lowMatL l)⁻¹ * lowMatL w.1 * Matrix.diagonal q + Matrix.diagonal w.2.1
        + Matrix.diagonal q * (upMatL w.2.2 * (1 + upMatL u)⁻¹) := by
  simp only [lduCoreMat, LinearMap.add_apply, LinearMap.comp_apply, LinearMap.mulRight_apply,
    LinearMap.mulLeft_apply, LinearMap.fst_apply, LinearMap.snd_apply, diagAsMat_apply,
    Matrix.mul_assoc]

/-- The factorization `L' · N' · U' = M`: the unit factors recombine to the raw differential. -/
theorem lduDerivMat_factor {t : ℕ} (l : LowIdx t → ℝ) (q : Fin t → ℝ) (u : UpIdx t → ℝ)
    (w : LDUParam t) :
    (1 + lowMatL l) * (lduCoreMat l q u w) * (1 + upMatL u) = lduDerivMat l q u w := by
  have hL : (1 + lowMatL l : Matrix (Fin t) (Fin t) ℝ) * (1 + lowMatL l)⁻¹ = 1 :=
    Matrix.mul_nonsing_inv _ (unitLow_isUnit l)
  have hU : (1 + upMatL u : Matrix (Fin t) (Fin t) ℝ)⁻¹ * (1 + upMatL u) = 1 :=
    Matrix.nonsing_inv_mul _ (unitUp_isUnit u)
  rw [lduCoreMat_apply, lduDerivMat_apply]
  set Lp := (1 + lowMatL l : Matrix (Fin t) (Fin t) ℝ) with hLp
  set Up := (1 + upMatL u : Matrix (Fin t) (Fin t) ℝ) with hUp
  set D := Matrix.diagonal q with hD
  set X := lowMatL w.1 with hX
  set Y := Matrix.diagonal w.2.1 with hY
  set Z := upMatL w.2.2 with hZ
  have expand : Lp * (Lp⁻¹ * X * D + Y + D * (Z * Up⁻¹)) * Up
      = Lp * (Lp⁻¹ * X * D) * Up + Lp * Y * Up + Lp * (D * (Z * Up⁻¹)) * Up := by noncomm_ring
  rw [expand]
  have t1 : Lp * (Lp⁻¹ * X * D) * Up = X * (D * Up) := by
    have e1 : Lp * (Lp⁻¹ * X * D) = (Lp * Lp⁻¹) * (X * D) := by noncomm_ring
    rw [e1, hL, Matrix.one_mul, Matrix.mul_assoc]
  have t3 : Lp * (D * (Z * Up⁻¹)) * Up = (Lp * D) * Z := by
    have e3 : Lp * (D * (Z * Up⁻¹)) * Up = ((Lp * D) * Z) * (Up⁻¹ * Up) := by noncomm_ring
    rw [e3, hU, Matrix.mul_one]
  rw [t1, t3]

/-- The conjugated core, in LDU coordinates, is block-diagonal: lower block `lowerBlock L'⁻¹`,
diagonal identity, upper block `upperBlock U'⁻¹`. -/
def lduCore {t : ℕ} (l : LowIdx t → ℝ) (q : Fin t → ℝ) (u : UpIdx t → ℝ) :
    LDUParam t →ₗ[ℝ] LDUParam t :=
  (lowerBlock (1 + lowMatL l : Matrix (Fin t) (Fin t) ℝ)⁻¹ q).prodMap
    ((LinearMap.id).prodMap (upperBlock (1 + upMatL u : Matrix (Fin t) (Fin t) ℝ)⁻¹ q))

/-- `Lpi · lowMatL dl · D` is strictly lower-triangular: zero on and above the diagonal. -/
theorem lowProd_upper_zero {t : ℕ} (l : LowIdx t → ℝ) (dl : LowIdx t → ℝ) (q : Fin t → ℝ)
    (i j : Fin t) (hij : i ≤ j) :
    ((1 + lowMatL l : Matrix (Fin t) (Fin t) ℝ)⁻¹ * lowMatL dl * Matrix.diagonal q) i j = 0 := by
  haveI : Invertible (1 + lowMatL l : Matrix (Fin t) (Fin t) ℝ) :=
    (1 + lowMatL l).invertibleOfIsUnitDet (unitLow_isUnit l)
  have hLpi := unitLow_inv_blockTri l
  rw [Matrix.mul_apply]
  apply Finset.sum_eq_zero
  intro k _
  by_cases hjk : j = k
  · subst hjk
    rw [Matrix.diagonal_apply_eq, Matrix.mul_apply]
    have : ∀ m, (1 + lowMatL l : Matrix (Fin t) (Fin t) ℝ)⁻¹ i m = 0 ∨ lowMatL dl m j = 0 := by
      intro m
      by_cases hmi : m < i
      · right
        rw [lowMatL_apply, dif_neg]
        exact not_lt.mpr (le_of_lt (lt_of_lt_of_le hmi hij))
      · rcases eq_or_lt_of_le (not_lt.mp hmi) with heq | hlt
        · right; rw [lowMatL_apply, dif_neg]
          rw [← heq]; exact not_lt.mpr hij
        · left; exact hLpi (by rw [OrderDual.toDual_lt_toDual]; exact hlt)
    rw [Finset.sum_eq_zero, zero_mul]
    intro m _
    rcases this m with h | h
    · rw [h, zero_mul]
    · rw [h, mul_zero]
  · rw [Matrix.diagonal_apply_ne _ (fun h => hjk h.symm), mul_zero]

/-- `D · (upMatL du · Bpi)` is upper-triangular: zero strictly below the diagonal. -/
theorem upProd_lower_zero {t : ℕ} (u : UpIdx t → ℝ) (du : UpIdx t → ℝ) (q : Fin t → ℝ)
    (i j : Fin t) (hij : j < i) :
    (Matrix.diagonal q * (upMatL du * (1 + upMatL u : Matrix (Fin t) (Fin t) ℝ)⁻¹)) i j = 0 := by
  haveI : Invertible (1 + upMatL u : Matrix (Fin t) (Fin t) ℝ) :=
    (1 + upMatL u).invertibleOfIsUnitDet (unitUp_isUnit u)
  have hUpi := unitUp_inv_blockTri u
  rw [Matrix.mul_apply]
  apply Finset.sum_eq_zero
  intro k _
  by_cases hik : i = k
  · subst hik
    rw [Matrix.diagonal_apply_eq, Matrix.mul_apply]
    have : ∀ m, upMatL du i m = 0 ∨ (1 + upMatL u : Matrix (Fin t) (Fin t) ℝ)⁻¹ m j = 0 := by
      intro m
      by_cases him : i < m
      · right; exact hUpi (lt_trans hij him)
      · left; rw [upMatL_apply, dif_neg him]
    rw [Finset.sum_eq_zero, mul_zero]
    intro m _
    rcases this m with h | h
    · rw [h, zero_mul]
    · rw [h, mul_zero]
  · rw [Matrix.diagonal_apply_ne _ (by exact hik), zero_mul]

/-- `matrixSplit ∘ lduCoreMat = lduCore`: the conjugated core, read in LDU coordinates, is the
block-diagonal map (lower block, identity on the diagonal, upper block). -/
theorem matrixSplit_lduCoreMat {t : ℕ} (l : LowIdx t → ℝ) (q : Fin t → ℝ) (u : UpIdx t → ℝ) :
    (matrixSplit (t := t)).toLinearMap.comp (lduCoreMat l q u) = lduCore l q u := by
  apply LinearMap.ext
  intro w
  rw [lduCore, LinearMap.comp_apply, lduCoreMat_apply]
  refine Prod.ext ?_ (Prod.ext ?_ ?_)
  · -- lower component
    funext p
    change ((1 + lowMatL l)⁻¹ * lowMatL w.1 * Matrix.diagonal q + Matrix.diagonal w.2.1
          + Matrix.diagonal q * (upMatL w.2.2 * (1 + upMatL u)⁻¹)) p.1.1 p.1.2 = _
    rw [Matrix.add_apply, Matrix.add_apply,
      Matrix.diagonal_apply_ne _ (ne_of_gt p.2), upProd_lower_zero u w.2.2 q _ _ p.2,
      add_zero, add_zero]
    rfl
  · -- diagonal component
    funext i
    change ((1 + lowMatL l)⁻¹ * lowMatL w.1 * Matrix.diagonal q + Matrix.diagonal w.2.1
          + Matrix.diagonal q * (upMatL w.2.2 * (1 + upMatL u)⁻¹)) i i = _
    have hup0 : (Matrix.diagonal q * (upMatL w.2.2 * (1 + upMatL u)⁻¹)) i i = 0 := by
      haveI : Invertible (1 + upMatL u : Matrix (Fin t) (Fin t) ℝ) :=
        (1 + upMatL u).invertibleOfIsUnitDet (unitUp_isUnit u)
      have hUpi := unitUp_inv_blockTri u
      rw [Matrix.mul_apply]
      apply Finset.sum_eq_zero
      intro k _
      by_cases hik : i = k
      · subst hik
        rw [Matrix.diagonal_apply_eq, Matrix.mul_apply, Finset.sum_eq_zero, mul_zero]
        intro m _
        by_cases him : i < m
        · rw [hUpi him, mul_zero]
        · rw [upMatL_apply, dif_neg him, zero_mul]
      · rw [Matrix.diagonal_apply_ne _ (by exact hik), zero_mul]
    rw [Matrix.add_apply, Matrix.add_apply,
      lowProd_upper_zero l w.1 q i i (le_refl i), hup0, zero_add, add_zero,
      Matrix.diagonal_apply_eq]
    rfl
  · -- upper component
    funext p
    change ((1 + lowMatL l)⁻¹ * lowMatL w.1 * Matrix.diagonal q + Matrix.diagonal w.2.1
          + Matrix.diagonal q * (upMatL w.2.2 * (1 + upMatL u)⁻¹)) p.1.1 p.1.2 = _
    rw [Matrix.add_apply, Matrix.add_apply,
      lowProd_upper_zero l w.1 q _ _ (le_of_lt p.2),
      Matrix.diagonal_apply_ne _ (ne_of_lt p.2), zero_add, zero_add]
    rfl

/-- The general-`L,U` LDU Jacobian (read in LDU coordinates): `matrixSplit ∘ lduDerivMat`. -/
def lduCoreDeriv {t : ℕ} (l : LowIdx t → ℝ) (q : Fin t → ℝ) (u : UpIdx t → ℝ) :
    LDUParam t →ₗ[ℝ] LDUParam t :=
  (matrixSplit (t := t)).toLinearMap.comp (lduDerivMat l q u)

/-- The block-diagonal core's determinant: `(∏ q_j^{t−1−j}) · (∏ q_i^{t−1−i})`. -/
theorem lduCore_det {t : ℕ} (l : LowIdx t → ℝ) (q : Fin t → ℝ) (u : UpIdx t → ℝ) :
    LinearMap.det (lduCore l q u)
      = (∏ p : LowIdx t, q p.1.2) * (∏ p : UpIdx t, q p.1.1) := by
  rw [lduCore, LinearMap.det_prodMap, LinearMap.det_prodMap, LinearMap.det_id, one_mul,
    lowerBlock_det _ (unitLow_inv_diag l) (unitLow_inv_blockTri l) q,
    upperBlock_det _ (unitUp_inv_diag u) (unitUp_inv_blockTri u) q]

/-- **A3 (general `L,U`)**: `det (lduCoreDeriv l q u) = ∏_i q_i^{2(t−1−i)}` — the LDU Jacobian at an
arbitrary point. The unit-triangular `L, U` factors contribute `det 1`; the value matches the
diagonal
point. -/
theorem lduCoreDeriv_det {t : ℕ} (l : LowIdx t → ℝ) (q : Fin t → ℝ) (u : UpIdx t → ℝ) :
    LinearMap.det (lduCoreDeriv l q u)
      = ∏ i : Fin t, (q i) ^ (2 * ((t : ℕ) - 1 - (i : ℕ))) := by
  -- lduDerivMat = mulLeft L' ∘ mulRight U' ∘ lduCoreMat, so
  -- matrixSplit ∘ lduDerivMat = (matrixSplit ∘ mulLeft L' ∘ mulRight U' ∘ msplit.symm) ∘ lduCore
  have hfac : lduCoreDeriv l q u
      = ((matrixSplit (t := t)).toLinearMap.comp
          ((LinearMap.mulLeft ℝ (1 + lowMatL l)).comp
            ((LinearMap.mulRight ℝ (1 + upMatL u)).comp
              (matrixSplit (t := t)).symm.toLinearMap))).comp (lduCore l q u) := by
    apply LinearMap.ext
    intro w
    rw [lduCoreDeriv, LinearMap.comp_apply, LinearMap.comp_apply, ← matrixSplit_lduCoreMat,
      LinearMap.comp_apply, LinearMap.comp_apply, LinearMap.comp_apply, LinearMap.comp_apply]
    simp only [LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply, LinearMap.mulLeft_apply,
      LinearMap.mulRight_apply]
    rw [← lduDerivMat_factor l q u w, Matrix.mul_assoc]
  rw [hfac, LinearMap.det_comp]
  -- det of the conjugation E = 1
  have hE : LinearMap.det ((matrixSplit (t := t)).toLinearMap.comp
      ((LinearMap.mulLeft ℝ (1 + lowMatL l)).comp
        ((LinearMap.mulRight ℝ (1 + upMatL u)).comp
          (matrixSplit (t := t)).symm.toLinearMap))) = 1 := by
    have hcomp : (matrixSplit (t := t)).toLinearMap.comp
        ((LinearMap.mulLeft ℝ (1 + lowMatL l)).comp
          ((LinearMap.mulRight ℝ (1 + upMatL u)).comp (matrixSplit (t := t)).symm.toLinearMap))
        = ((matrixSplit (t := t)) : Matrix (Fin t) (Fin t) ℝ →ₗ[ℝ] _) ∘ₗ
            ((LinearMap.mulLeft ℝ (1 + lowMatL l)).comp (LinearMap.mulRight ℝ (1 + upMatL u))) ∘ₗ
            ((matrixSplit (t := t)).symm : LDUParam t →ₗ[ℝ] _) := by
      simp only [LinearMap.comp_assoc]
    rw [hcomp, LinearMap.det_conj, LinearMap.det_comp]
    rw [show LinearMap.mulLeft ℝ (1 + lowMatL l : Matrix (Fin t) (Fin t) ℝ)
          = mulLeftMat (1 + lowMatL l) from rfl,
        show LinearMap.mulRight ℝ (1 + upMatL u : Matrix (Fin t) (Fin t) ℝ)
          = mulRightMat (1 + upMatL u) from rfl,
        det_mulLeft_matrixSpace, det_mulRight_matrixSpace, unitLow_det, unitUp_det]
    simp
  rw [hE, one_mul, lduCore_det, prod_lowIdx_col, prod_upIdx_row, ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro i _
  rw [← pow_add, two_mul]

/-- **A3 (general `L,U`, abs form)**: `|det (lduCoreDeriv l q u)| = ∏_i |q_i|^{2(t−1−i)}`. -/
theorem lduCoreDeriv_abs_det {t : ℕ} (l : LowIdx t → ℝ) (q : Fin t → ℝ) (u : UpIdx t → ℝ) :
    |LinearMap.det (lduCoreDeriv l q u)| = ∏ i : Fin t, |q i| ^ (2 * ((t : ℕ) - 1 - (i : ℕ))) := by
  rw [lduCoreDeriv_det, Finset.abs_prod]
  apply Finset.prod_congr rfl
  intro i _
  rw [abs_pow]

/-- The general LDU Jacobian det equals the diagonal-point one (the unit factors are det 1). -/
theorem lduCoreDeriv_det_eq_diag {t : ℕ} (l : LowIdx t → ℝ) (q : Fin t → ℝ) (u : UpIdx t → ℝ) :
    LinearMap.det (lduCoreDeriv l q u) = LinearMap.det (lduCoreDerivDiag q) := by
  rw [lduCoreDeriv_det, lduCoreDerivDiag_det]

/-- Validation, the `(3,3,3,3)` LDU core at boundary `s = 1` (`t = 2`) at a GENERAL point: the
general LDU Jacobian det collapses to `q_0^2`, matching `Kparam3333Deriv_det = (x 1)^2 = a^2`. -/
theorem lduCoreDeriv_det_3333_boundary1 (l : LowIdx 2 → ℝ) (q : Fin 2 → ℝ) (u : UpIdx 2 → ℝ) :
    LinearMap.det (lduCoreDeriv l q u) = (q 0) ^ 2 := by
  rw [lduCoreDeriv_det, Fin.prod_univ_two]
  norm_num

end DLNFibre.DLN.RLCT
