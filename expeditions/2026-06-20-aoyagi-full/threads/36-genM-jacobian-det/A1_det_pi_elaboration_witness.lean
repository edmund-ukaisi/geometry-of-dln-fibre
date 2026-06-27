import Mathlib

open Matrix LinearMap

-- Piece 1: det of K.mulVecLin = K.det
example {t : ℕ} (K : Matrix (Fin t) (Fin t) ℝ) :
    LinearMap.det (K.mulVecLin) = K.det := by
  rw [show K.mulVecLin = Matrix.toLin' K from rfl, LinearMap.det_toLin']

-- Piece 2 (corrected): det_pi for the block-diagonal of c copies of K.mulVecLin.
-- det_pi (f : ι → M →ₗ M) : (LinearMap.pi (fun i => (f i).comp (proj i))).det = ∏ i, (f i).det
example {t c : ℕ} (K : Matrix (Fin t) (Fin t) ℝ) :
    (LinearMap.pi (fun i : Fin c => (K.mulVecLin).comp (LinearMap.proj i))).det
      = ∏ _i : Fin c, LinearMap.det (K.mulVecLin) :=
  LinearMap.det_pi (fun _ : Fin c => K.mulVecLin)

-- Piece 3: collapse to a power, combined with piece 1
example {t c : ℕ} (K : Matrix (Fin t) (Fin t) ℝ) :
    (LinearMap.pi (fun i : Fin c => (K.mulVecLin).comp (LinearMap.proj i))).det = K.det ^ c := by
  rw [LinearMap.det_pi (fun _ : Fin c => K.mulVecLin)]
  simp only [show K.mulVecLin = Matrix.toLin' K from rfl, LinearMap.det_toLin']
  rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]

-- Piece 4 (the matrix-space conjugation): Matrix (Fin t) (Fin c) ≃ₗ (Fin c → Fin t → ℝ) exists
-- (the goal of the FULL A1 lemma is to conjugate the block-diag pi map back to left-mult; here we
-- just confirm the column-equiv and det_conj are available API).
example {t c : ℕ} (e : Matrix (Fin t) (Fin c) ℝ ≃ₗ[ℝ] (Fin c → (Fin t → ℝ)))
    (f : Matrix (Fin t) (Fin c) ℝ →ₗ[ℝ] Matrix (Fin t) (Fin c) ℝ) :
    LinearMap.det ((e : _ →ₗ[ℝ] _) ∘ₗ f ∘ₗ (e.symm : _ →ₗ[ℝ] _)) = LinearMap.det f :=
  LinearMap.det_conj f e
