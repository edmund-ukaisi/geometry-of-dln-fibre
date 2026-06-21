import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Matrix.Mul
import Mathlib.Data.Real.Basic
import Mathlib.Topology.Constructions

/-!
# `DLNFibre.DLN.RLCT.Foundations.Loss` — the deep-linear-network loss

The parameter space `Params H` of composable real matrix tuples, the multiplication map `prod`,
the square-Frobenius loss `dlnLoss`, and the fibre `optimalSet = mult⁻¹(B)`.

Pure polynomial layer (no measure theory). Faithful to Aoyagi 2023, §0–1 (design-spec §0–1):
the `L`-layer model `Y = (∏_{s=1}^L A⁽ˢ⁾) X + noise`, widths `H : Fin (L+1) → ℕ` with `H⁽¹⁾ = H 0`
the **output** dimension and `H⁽ᴸ⁺¹⁾ = H (last)` the **input** dimension, layer `s` a matrix of size
`H⁽ˢ⁾ × H⁽ˢ⁺¹⁾`. The identity-covariance square-Frobenius loss is RLCT-faithful (`Σ_X` drops out by
the regular whitening change of coordinates; design-spec §0).
-/

namespace DLNFibre.DLN.RLCT

open Matrix

variable {L : ℕ}

/-- A network parameter: a composable tuple of layer matrices, layer `s` of size
`H⁽ˢ⁾ × H⁽ˢ⁺¹⁾ = H s.castSucc × H s.succ`. Definitionally a function space (a `Pi` of `Pi`s),
so it inherits `TopologicalSpace`/`MeasurableSpace`/`MeasureSpace` by `inferInstanceAs`. -/
def Params (H : Fin (L + 1) → ℕ) : Type :=
  ∀ s : Fin L, Matrix (Fin (H s.castSucc)) (Fin (H s.succ)) ℝ

/-- The product of the first `k` layer matrices `A⁽¹⁾·…·A⁽ᵏ⁾`, of size `H 0 × H k`. -/
def prodAux (H : Fin (L + 1) → ℕ) (A : Params H) :
    (k : ℕ) → (hk : k < L + 1) → Matrix (Fin (H 0)) (Fin (H ⟨k, hk⟩)) ℝ
  | 0, _ => (1 : Matrix (Fin (H 0)) (Fin (H 0)) ℝ)
  | k + 1, hk => by
      have hk' : k < L + 1 := Nat.lt_of_succ_lt hk
      have hkL : k < L := Nat.lt_of_succ_lt_succ hk
      refine (prodAux H A k hk') * ?_
      have e1 : (⟨k, hk'⟩ : Fin (L + 1)) = (⟨k, hkL⟩ : Fin L).castSucc := by
        apply Fin.ext; simp [Fin.castSucc]
      have e2 : (⟨k + 1, hk⟩ : Fin (L + 1)) = (⟨k, hkL⟩ : Fin L).succ := by
        apply Fin.ext; simp [Fin.succ]
      rw [e1, e2]; exact A ⟨k, hkL⟩

/-- The multiplication map: the layer product `A⁽¹⁾·A⁽²⁾·…·A⁽ᴸ⁾`, of size
`H⁽¹⁾ × H⁽ᴸ⁺¹⁾ = H 0 × H (last)`. -/
def prod (H : Fin (L + 1) → ℕ) (A : Params H) :
    Matrix (Fin (H 0)) (Fin (H (Fin.last L))) ℝ :=
  prodAux H A L (Nat.lt_succ_self L)

/-- The square-Frobenius loss `‖prod A − B‖²_F = ∑ᵢⱼ ((prod A − B)ᵢⱼ)²`. An honest polynomial in the
entries of `A`, hence real-analytic. Faithful to Aoyagi's Kullback function `K(w)` for the Gaussian
model (design-spec §1). -/
def dlnLoss (H : Fin (L + 1) → ℕ)
    (B : Matrix (Fin (H 0)) (Fin (H (Fin.last L))) ℝ) (A : Params H) : ℝ :=
  ∑ i, ∑ j, ((prod H A - B) i j) ^ 2

/-- The fibre `mult⁻¹(B) = {A | prod A = B}`, the zero-set of `dlnLoss B` (a sum of squares). -/
def optimalSet (H : Fin (L + 1) → ℕ)
    (B : Matrix (Fin (H 0)) (Fin (H (Fin.last L))) ℝ) : Set (Params H) :=
  { A | prod H A = B }

/-- `optimalSet` is exactly the zero-set of `dlnLoss B`: the loss is a sum of squares, zero iff
`prod A = B`. -/
theorem optimalSet_eq_loss_zero (H : Fin (L + 1) → ℕ)
    (B : Matrix (Fin (H 0)) (Fin (H (Fin.last L))) ℝ) :
    optimalSet H B = { A | dlnLoss H B A = 0 } := by
  ext A
  simp only [optimalSet, dlnLoss, Set.mem_setOf_eq]
  constructor
  · intro h; simp [h]
  · intro h
    -- a finite sum of squares is zero iff each square is zero
    have hsq : ∀ i, ∀ j, ((prod H A - B) i j) ^ 2 = 0 := by
      have hnn : ∀ i, (0 : ℝ) ≤ ∑ j, ((prod H A - B) i j) ^ 2 := fun i =>
        Finset.sum_nonneg fun j _ => sq_nonneg _
      have hi : ∀ i, ∑ j, ((prod H A - B) i j) ^ 2 = 0 := fun i =>
        (Finset.sum_eq_zero_iff_of_nonneg fun i _ => hnn i).1 h i (Finset.mem_univ i)
      intro i j
      exact (Finset.sum_eq_zero_iff_of_nonneg fun j _ => sq_nonneg _).1 (hi i) j (Finset.mem_univ j)
    funext i j
    have hij : (prod H A - B) i j = 0 := by
      have := hsq i j; nlinarith [this]
    have := sub_eq_zero.1 (by simpa [Matrix.sub_apply] using hij)
    simpa using this

/-- **`dlnLoss` is nonnegative.** A sum of squares: `0 ≤ dlnLoss H B A`. Reusable bedrock — needed
for the sqrt-wrapper `Real.sqrt (dlnLoss …) ^ 2 = dlnLoss …` that feeds `rlct_additive_smooth_block`
(the smooth-block split), and for the homogeneous-core work. -/
theorem dlnLoss_nonneg (H : Fin (L + 1) → ℕ)
    (B : Matrix (Fin (H 0)) (Fin (H (Fin.last L))) ℝ) (A : Params H) :
    0 ≤ dlnLoss H B A :=
  Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => sq_nonneg _

end DLNFibre.DLN.RLCT
