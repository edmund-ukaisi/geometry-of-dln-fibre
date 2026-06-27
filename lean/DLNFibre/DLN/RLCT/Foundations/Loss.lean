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
the `L`-layer model `Y = (∏_{s=1}^L A⁽ˢ⁾) X + noise`, widths `H : Fin (L + 1) → ℕ` with `H⁽¹⁾ = H 0`
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

/-! ## The `prodAux` succ-step recursion (the native LAST-layer peel)

`prodAux`/`prod` are LEFT-associated prefix folds, so the natural unfold peels the LAST layer. These two
forms of the succ-step — the reindex-explicit `prodAux_succ` and the block-cast `prodAux_succ_layer` —
are the recursion handles every fold over the layer product (value / derivative / telescope / front-peel)
reuses. They live here, beside `prodAux`, so a consumer needs only `Foundations.Loss` (not the heavier
`Validate.Deepest*` analysis subtree) to peel a layer. -/

/-- **`prodAux` recursion, reindex-explicit.** The `k+1` fold is the running product times the `k`-th
layer, transported to the running-width type by `Matrix.reindex (finCongr ·) (finCongr ·)` — the explicit
form of the def's `rw [e1,e2]; exact A …`. -/
theorem prodAux_succ (H : Fin (L + 1) → ℕ) (A : Params H) (k : ℕ) (hk : k + 1 < L + 1)
    (e1 : H (⟨k, Nat.lt_of_succ_lt hk⟩ : Fin (L + 1))
        = H ((⟨k, Nat.lt_of_succ_lt_succ hk⟩ : Fin L).castSucc))
    (e2 : H (⟨k + 1, hk⟩ : Fin (L + 1))
        = H ((⟨k, Nat.lt_of_succ_lt_succ hk⟩ : Fin L).succ)) :
    prodAux H A (k + 1) hk
      = (prodAux H A k (Nat.lt_of_succ_lt hk)) *
          (Matrix.reindex (finCongr e1.symm) (finCongr e2.symm) (A ⟨k, Nat.lt_of_succ_lt_succ hk⟩)) := by
  obtain rfl : e1 = rfl := Subsingleton.elim _ _
  obtain rfl : e2 = rfl := Subsingleton.elim _ _
  rfl

/-- **SHARED step-cast helper** (the family kernel). If the `k`-th layer of `A` is the reindexed
block `Matrix.reindex eC.symm eS.symm M` at the running widths, then the `prodAux` succ-step is the clean
product `prodAux k * reindex eC.symm eS.symm M` — the def's `Eq.mpr` cast is collapsed by the index-level
`cases e1; cases e2` idiom. All three folds (value / deriv / telescope) apply this then their own
block-composition. `eC, eS` are the threshold splits at `H ⟨k,hk'⟩`, `H ⟨k+1,hk⟩`. -/
theorem prodAux_succ_layer (H : Fin (L + 1) → ℕ) (A : Params H) (k : ℕ) (hk : k + 1 < L + 1)
    {p q : ℕ} (eC : Fin (H (⟨k, Nat.lt_of_succ_lt hk⟩ : Fin (L + 1))) ≃ Fin p ⊕ Fin q)
    {p' q' : ℕ} (eS : Fin (H (⟨k + 1, hk⟩ : Fin (L + 1))) ≃ Fin p' ⊕ Fin q')
    (M : Matrix (Fin p ⊕ Fin q) (Fin p' ⊕ Fin q') ℝ)
    (hlayer : A (⟨k, Nat.lt_of_succ_lt_succ hk⟩ : Fin L)
      = (by rw [show (⟨k, Nat.lt_of_succ_lt_succ hk⟩ : Fin L).castSucc
                = (⟨k, Nat.lt_of_succ_lt hk⟩ : Fin (L + 1)) from by apply Fin.ext; simp [Fin.castSucc],
              show (⟨k, Nat.lt_of_succ_lt_succ hk⟩ : Fin L).succ
                = (⟨k + 1, hk⟩ : Fin (L + 1)) from by apply Fin.ext; simp [Fin.succ]]
            exact Matrix.reindex eC.symm eS.symm M :
          Matrix (Fin (H (⟨k, Nat.lt_of_succ_lt_succ hk⟩ : Fin L).castSucc))
            (Fin (H (⟨k, Nat.lt_of_succ_lt_succ hk⟩ : Fin L).succ)) ℝ)) :
    prodAux H A (k + 1) hk
      = prodAux H A k (Nat.lt_of_succ_lt hk) * Matrix.reindex eC.symm eS.symm M := by
  have hkL : k < L := Nat.lt_of_succ_lt_succ hk
  have hk' : k < L + 1 := Nat.lt_of_succ_lt hk
  have e1 : (⟨k, hk'⟩ : Fin (L + 1)) = (⟨k, hkL⟩ : Fin L).castSucc := by
    apply Fin.ext; simp [Fin.castSucc]
  have e2 : (⟨k + 1, hk⟩ : Fin (L + 1)) = (⟨k, hkL⟩ : Fin L).succ := by
    apply Fin.ext; simp [Fin.succ]
  show prodAux H A k hk' *
      ((by rw [e1, e2]; exact A ⟨k, hkL⟩ :
        Matrix (Fin (H ⟨k, hk'⟩)) (Fin (H ⟨k + 1, hk⟩)) ℝ)) = _
  refine congrArg (prodAux H A k hk' * ·) ?_
  rw [hlayer]; cases e1; cases e2; rfl

end DLNFibre.DLN.RLCT
