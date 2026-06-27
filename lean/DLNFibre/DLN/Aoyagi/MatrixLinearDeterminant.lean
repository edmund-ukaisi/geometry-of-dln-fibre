import Mathlib.Data.Matrix.Bilinear
import Mathlib.LinearAlgebra.Determinant
import Mathlib.LinearAlgebra.Matrix.ToLin

/-!
# Determinants of rectangular matrix multiplication maps

This file records small linear-algebra API needed by the Aoyagi
retained-passive Jacobian calculation.  It is only determinant arithmetic for
left and right multiplication on rectangular matrix spaces.
-/

noncomputable section

open Matrix

namespace DLNFibre
namespace DLN
namespace Aoyagi

/-- Read a matrix as a family of columns. -/
def matrixColumnLinearEquiv (R : Type*) [Semiring R] (m n : Type*) :
    Matrix m n R ≃ₗ[R] (n → m → R) where
  toFun X := fun j i => X i j
  invFun f := fun i j => f j i
  left_inv := by
    intro X
    rfl
  right_inv := by
    intro f
    rfl
  map_add' := by
    intro X Y
    rfl
  map_smul' := by
    intro a X
    rfl

/-- The determinant of left multiplication by a square matrix on rectangular
matrices is the determinant of the multiplier to the number of columns. -/
theorem linearMap_det_mulLeftLinearMap
    {R m n : Type*} [CommRing R]
    [Fintype m] [DecidableEq m] [Fintype n]
    (A : Matrix m m R) :
    LinearMap.det (mulLeftLinearMap n R A :
      Matrix m n R →ₗ[R] Matrix m n R) =
        A.det ^ Fintype.card n := by
  let e := matrixColumnLinearEquiv R m n
  let L : Matrix m n R →ₗ[R] Matrix m n R := mulLeftLinearMap n R A
  let P : (n → m → R) →ₗ[R] (n → m → R) :=
    LinearMap.pi (fun j : n => (Matrix.toLin' A).comp (LinearMap.proj j))
  have hconj :
      ((e : Matrix m n R →ₗ[R] (n → m → R)).comp
          (L.comp (e.symm : (n → m → R) →ₗ[R] Matrix m n R))) = P := by
    apply LinearMap.ext
    intro v
    funext j i
    simp [e, matrixColumnLinearEquiv, L, P, mulLeftLinearMap, Matrix.toLin'_apply,
      Matrix.mulVec, dotProduct, Matrix.mul_apply]
  calc
    LinearMap.det L =
        LinearMap.det
          ((e : Matrix m n R →ₗ[R] (n → m → R)).comp
            (L.comp (e.symm : (n → m → R) →ₗ[R] Matrix m n R))) := by
          rw [LinearMap.det_conj L e]
    _ = LinearMap.det P := by rw [hconj]
    _ = ∏ _j : n, LinearMap.det (Matrix.toLin' A) := by
          simpa [P] using
            (LinearMap.det_pi (R := R) (ι := n) (M := m → R)
              (fun _j : n => Matrix.toLin' A))
    _ = A.det ^ Fintype.card n := by
          simp

/-- The determinant of right multiplication by a square matrix on rectangular
matrices is the determinant of the multiplier to the number of rows. -/
theorem linearMap_det_mulRightLinearMap
    {R m n : Type*} [CommRing R]
    [Fintype m] [Fintype n] [DecidableEq n]
    (B : Matrix n n R) :
    LinearMap.det (mulRightLinearMap m R B :
      Matrix m n R →ₗ[R] Matrix m n R) =
        B.det ^ Fintype.card m := by
  let e := Matrix.transposeLinearEquiv m n R R
  let L : Matrix m n R →ₗ[R] Matrix m n R := mulRightLinearMap m R B
  let P : Matrix n m R →ₗ[R] Matrix n m R := mulLeftLinearMap m R Bᵀ
  have hconj :
      ((e : Matrix m n R →ₗ[R] Matrix n m R).comp
          (L.comp (e.symm : Matrix n m R →ₗ[R] Matrix m n R))) = P := by
    apply LinearMap.ext
    intro X
    ext i j
    simp [e, L, P, Matrix.transposeLinearEquiv, mulRightLinearMap, mulLeftLinearMap,
      Matrix.mul_apply, mul_comm]
  calc
    LinearMap.det L =
        LinearMap.det
          ((e : Matrix m n R →ₗ[R] Matrix n m R).comp
            (L.comp (e.symm : Matrix n m R →ₗ[R] Matrix m n R))) := by
          rw [LinearMap.det_conj L e]
    _ = LinearMap.det P := by rw [hconj]
    _ = (Bᵀ).det ^ Fintype.card m := by
          exact linearMap_det_mulLeftLinearMap (R := R) (m := n) (n := m) Bᵀ
    _ = B.det ^ Fintype.card m := by
          rw [Matrix.det_transpose]

end Aoyagi
end DLN
end DLNFibre
