import Mathlib.LinearAlgebra.Matrix.Vec
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Data.Real.StarOrdered

set_option linter.style.longLine false

/-!
# `RouteMSJFrontGram` — the D–H covariance (front-Gram) Kronecker-sum primitive (module (ii)(a))

**Thread `genm-sj5-stepbuild` (aoyagi-full Stage 2), step-3 module (ii)(a)** — the recommended
self-contained primitive from `genm-stepdesign/design.md §2.2/§2.4`.

The joint front map `L(U,B) = P·U + B·D` (`u×b`, `P : u×u` invertible pivot, `D : b×b`) is the
`B`-shear image of the outer front (incidence-cert §3b step (3), `H = PU + BD`). The crux de-risk
(design §2.1) is that the naive tube (`chart4` standalone over `ℝ^{ub}`) DIVERGES via a false
`|det D|^{d−a−u}` weight; the resolution (§2.2) keeps `(U,B)` together and uses the **covariance
(front-Gram)** of the vectorised map `(vec U, vec B) ↦ vec L`, a Kronecker SUM

    Σ = frontGram P D = I_b ⊗ (P Pᵀ) + (Dᵀ D) ⊗ I_u,

whose honest joint weight `(det Σ)^{−1/2} = ∏(pᵢ²+σⱼ²)^{−1/2}` (`pᵢ, σⱼ` the singular values of
`P, D`) automatically interpolates the two `D`-radial regimes with no enlargement.

This file banks the **algebraic** core of the primitive:
- `vec_frontMap` — the vectorisation `vec (PU+BD) = (I_b⊗P)·vec U + (Dᵀ⊗I_u)·vec B` (grounds Σ as a
  genuine Gram of the map, not a free-floating identity);
- `frontGram_eq_gram` — `Σ = K_P K_Pᵀ + K_D K_Dᵀ` with `K_P = I_b⊗P`, `K_D = Dᵀ⊗I_u` (Σ IS the
  covariance `[K_P|K_D][K_P|K_D]ᵀ`);
- `frontGram_factors_commute` — the two summands commute (both `= (DᵀD)⊗(PPᵀ)`), so Σ is a Kronecker
  sum of two commuting PSD matrices — the simultaneous-diagonalisation handle for the later
  eigenvalue/determinant `det Σ = ∏(pᵢ²+σⱼ²)`;
- `frontGram_posSemidef` — `Σ` is positive semidefinite (a sum of two `M Mᵀ` Grams).

The eigenvalue / determinant `det Σ = ∏(pᵢ²+σⱼ²)` and the pushforward-density bound (module (ii)(b))
build on these; deferred to the next sub-tide (design §2.4(b), Codex-concurred defer).
-/

namespace DLNFibre.DLN.RLCT

open Matrix
open scoped Kronecker

/-- Transpose of a Kronecker product: `(A ⊗ₖ B)ᵀ = Aᵀ ⊗ₖ Bᵀ` (no `transpose_kronecker` at the pin;
built from the general `kroneckerMap_transpose`). -/
theorem transpose_kronecker' {la ma lb mb : Type*} (A : Matrix la ma ℝ) (B : Matrix lb mb ℝ) :
    (A ⊗ₖ B)ᵀ = Aᵀ ⊗ₖ Bᵀ :=
  (kroneckerMap_transpose (· * ·) A B).symm

/-- **`PosSemidef` is closed under `+`** (no `Matrix.PosSemidef.add` at the pin). Hermitian sum +
per-vector `star x ⬝ᵥ (M *ᵥ x)` additivity. -/
theorem posSemidef_add {N : Type*} [Finite N] {X Y : Matrix N N ℝ}
    (hX : X.PosSemidef) (hY : Y.PosSemidef) : (X + Y).PosSemidef := by
  have := Fintype.ofFinite N
  refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg (hX.1.add hY.1) (fun x => ?_)
  rw [Matrix.add_mulVec, dotProduct_add]
  exact add_nonneg (hX.dotProduct_mulVec_nonneg x) (hY.dotProduct_mulVec_nonneg x)

variable {u b : Type*} [Fintype u] [DecidableEq u] [Fintype b] [DecidableEq b]

/-- **The vectorised front map** — `vec (P·U + B·D) = (I_b ⊗ P)·vec U + (Dᵀ ⊗ I_u)·vec B`. This ties
the front-Gram `Σ` below to the actual map `L = PU + BD`: `Σ = [K_P|K_D][K_P|K_D]ᵀ` is the Gram of the
linear map `(vec U, vec B) ↦ vec L` with blocks `K_P = I_b⊗P`, `K_D = Dᵀ⊗I_u`. (`vec_mul_eq_mulVec`
for the `P·U` block; `kronecker_mulVec_vec` for the `B·D` block.) -/
theorem vec_frontMap (P : Matrix u u ℝ) (D : Matrix b b ℝ) (U B : Matrix u b ℝ) :
    Matrix.vec (P * U + B * D)
      = ((1 : Matrix b b ℝ) ⊗ₖ P) *ᵥ Matrix.vec U
        + (Dᵀ ⊗ₖ (1 : Matrix u u ℝ)) *ᵥ Matrix.vec B := by
  rw [Matrix.vec_add, Matrix.vec_mul_eq_mulVec P U]
  congr 1
  rw [Matrix.kronecker_mulVec_vec, Matrix.transpose_transpose, Matrix.one_mul]

/-- **The front-Gram (covariance) matrix** `Σ = I_b ⊗ (P Pᵀ) + (Dᵀ D) ⊗ I_u` — the covariance of the
vectorised front map `vec (PU + BD)` (design §2.2). A Kronecker sum, indexed by `b × u`. -/
noncomputable def frontGram (P : Matrix u u ℝ) (D : Matrix b b ℝ) : Matrix (b × u) (b × u) ℝ :=
  ((1 : Matrix b b ℝ) ⊗ₖ (P * Pᵀ)) + ((Dᵀ * D) ⊗ₖ (1 : Matrix u u ℝ))

/-- **`frontGram` IS the Gram `[K_P|K_D][K_P|K_D]ᵀ`** — `Σ = K_P K_Pᵀ + K_D K_Dᵀ` with `K_P = I_b⊗P`,
`K_D = Dᵀ⊗I_u`. Each summand collapses by the Kronecker mixed-product `mul_kronecker_mul`:
`(I_b⊗P)(I_b⊗Pᵀ) = I_b⊗(PPᵀ)`, `(Dᵀ⊗I_u)(D⊗I_u) = (DᵀD)⊗I_u`. Confirms `frontGram` is the genuine
covariance of the map `vec_frontMap`, not a free-floating identity. -/
theorem frontGram_eq_gram (P : Matrix u u ℝ) (D : Matrix b b ℝ) :
    frontGram P D
      = ((1 : Matrix b b ℝ) ⊗ₖ P) * ((1 : Matrix b b ℝ) ⊗ₖ P)ᵀ
        + (Dᵀ ⊗ₖ (1 : Matrix u u ℝ)) * (Dᵀ ⊗ₖ (1 : Matrix u u ℝ))ᵀ := by
  rw [frontGram]
  congr 1
  · rw [transpose_kronecker', transpose_one, ← mul_kronecker_mul, Matrix.one_mul]
  · rw [transpose_kronecker', transpose_one, transpose_transpose, ← mul_kronecker_mul,
      Matrix.mul_one]

/-- **The two front-Gram summands commute** — `(I_b⊗PPᵀ)((DᵀD)⊗I_u) = ((DᵀD)⊗I_u)(I_b⊗PPᵀ)`, both
`= (DᵀD)⊗(PPᵀ)` by the mixed product. So `Σ` is a Kronecker sum of two COMMUTING PSD matrices — the
handle for simultaneous diagonalisation ⟹ `eigenvalues Σ = {pᵢ²+σⱼ²}`, `det Σ = ∏(pᵢ²+σⱼ²)` (the
later determinant module). -/
theorem frontGram_factors_commute (P : Matrix u u ℝ) (D : Matrix b b ℝ) :
    ((1 : Matrix b b ℝ) ⊗ₖ (P * Pᵀ)) * ((Dᵀ * D) ⊗ₖ (1 : Matrix u u ℝ))
      = ((Dᵀ * D) ⊗ₖ (1 : Matrix u u ℝ)) * ((1 : Matrix b b ℝ) ⊗ₖ (P * Pᵀ)) := by
  have e1 : ((1 : Matrix b b ℝ) ⊗ₖ (P * Pᵀ)) * ((Dᵀ * D) ⊗ₖ (1 : Matrix u u ℝ))
      = (Dᵀ * D) ⊗ₖ (P * Pᵀ) := by
    rw [← mul_kronecker_mul, Matrix.one_mul, Matrix.mul_one]
  have e2 : ((Dᵀ * D) ⊗ₖ (1 : Matrix u u ℝ)) * ((1 : Matrix b b ℝ) ⊗ₖ (P * Pᵀ))
      = (Dᵀ * D) ⊗ₖ (P * Pᵀ) := by
    rw [← mul_kronecker_mul, Matrix.mul_one, Matrix.one_mul]
  rw [e1, e2]

/-- **The front-Gram is positive semidefinite** — `Σ = K_P K_Pᵀ + K_D K_Dᵀ` is a sum of two Grams
`M Mᵀ` (each PSD), so PSD. (PosDef under `IsUnit P`/`IsUnit D` is a later strengthening; PSD is the
weakest form the density bound needs to define `det Σ^{−1/2}`.) -/
theorem frontGram_posSemidef (P : Matrix u u ℝ) (D : Matrix b b ℝ) :
    (frontGram P D).PosSemidef := by
  rw [frontGram_eq_gram]
  refine posSemidef_add ?_ ?_
  · rw [show (((1 : Matrix b b ℝ) ⊗ₖ P))ᵀ = (((1 : Matrix b b ℝ) ⊗ₖ P))ᴴ from
        (conjTranspose_eq_transpose_of_trivial _).symm]
    exact posSemidef_self_mul_conjTranspose _
  · rw [show ((Dᵀ ⊗ₖ (1 : Matrix u u ℝ)))ᵀ = ((Dᵀ ⊗ₖ (1 : Matrix u u ℝ)))ᴴ from
        (conjTranspose_eq_transpose_of_trivial _).symm]
    exact posSemidef_self_mul_conjTranspose _

end DLNFibre.DLN.RLCT
