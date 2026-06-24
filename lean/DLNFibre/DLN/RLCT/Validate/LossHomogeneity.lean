import DLNFibre.DLN.RLCT.Foundations.Loss

/-!
# `DLNFibre.DLN.RLCT.Validate.LossHomogeneity` — `dlnLoss` is degree-2 homogeneous per layer (fm3)

The `dlnLoss`-side instance of the per-node homogeneity hypothesis G2 (`NodeHomogeneity.lean`)
abstracts over: the DLN core loss is degree-2 homogeneous in EACH single layer block. The load-bearing
fact is the multilinearity of the matrix-chain product — scaling one layer `A⁽ˢ⁾` by `c` scales
`prod = A⁽¹⁾⋯A⁽ᴸ⁾` by `c` (`Matrix.smul_mul` / `Matrix.mul_smul` move the scalar out), hence the
square-Frobenius loss at the deepest point (`B = 0`) by `c²`.

This connects G2's abstract `hhomog` hypothesis to the actual `dlnLoss`: the active block is one
layer's entries, and scaling them by `c` is `prodScaleLayer`/`scaleLayer` here.

Route (Codex-confirmed, prefix-invariant): `scaleLayer c s = Function.update A s (c • A s)`; the
product-scaling is `prodAux (scaleLayer c s A) k = (if (s:ℕ) < k then c else 1) • prodAux A k` by
induction on `k`, splitting only on whether the current layer is `s`.
-/

open Matrix
open scoped BigOperators
namespace DLNFibre.DLN.RLCT

variable {L : ℕ}

/-- The `prodAux` recursion-step with the dependent-`Fin` cast discharged by HEq (local copy of the
`Skeleton` private helper): if `A ⟨k,_⟩` is HEq to `Mstep` (typed at the `prodAux` dims), then
`prodAux (k+1) = prodAux k * Mstep`. Lets the induction unfold the successor WITHOUT exposing the
`Eq.mpr` cast — the scalar `c` then rides on a clean `Mstep` (Codex-confirmed route). -/
private theorem prodAux_step (H : Fin (L + 1) → ℕ) (A : Params H) (k : ℕ) (hk : k + 1 < L + 1)
    (Mstep : Matrix (Fin (H ⟨k, Nat.lt_of_succ_lt hk⟩)) (Fin (H ⟨k + 1, hk⟩)) ℝ)
    (hheq : HEq (A ⟨k, Nat.lt_of_succ_lt_succ hk⟩) Mstep) :
    prodAux H A (k + 1) hk = prodAux H A k (Nat.lt_of_succ_lt hk) * Mstep := by
  rw [prodAux]; congr 1; rw [eq_comm]; apply eq_of_heq
  exact hheq.symm.trans (heq_of_eqRec_eq rfl rfl)

/-- Scale layer `s` of a parameter tuple by `c`, leaving the other layers fixed:
`Function.update A s (c • A s)`. The per-layer scaling under which `dlnLoss … 0` is degree-2
homogeneous (the `Params`-level analog of `NodeHomogeneity.scaleActiveBy` on one layer's coords). -/
def scaleLayer (H : Fin (L + 1) → ℕ) (c : ℝ) (s : Fin L) (A : Params H) : Params H :=
  Function.update A s (c • A s)

/-- **The prefix product scales by `c` once the scaled layer is passed.** `prodAux` of the
layer-`s`-scaled tuple equals `(c if s < k else 1) • prodAux`: the scalar `c` appears exactly when the
prefix `A⁽¹⁾⋯A⁽ᵏ⁾` includes the scaled layer `s` (`s < k`). Induction on `k`; at the successor step,
split on whether the current layer `⟨k, _⟩ = s` (`Function.update_self` vs `Function.update_of_ne`),
move the scalar out with `Matrix.smul_mul` / `Matrix.mul_smul`. -/
theorem prodAux_scaleLayer (H : Fin (L + 1) → ℕ) (c : ℝ) (s : Fin L) (A : Params H) :
    ∀ (k : ℕ) (hk : k < L + 1),
      prodAux H (scaleLayer H c s A) k hk
        = (if (s : ℕ) < k then c else 1) • prodAux H A k hk := by
  intro k
  induction k with
  | zero => intro hk; simp only [prodAux, Nat.not_lt_zero, if_false, one_smul]
  | succ k ih =>
      intro hk
      have hkL : k < L := Nat.lt_of_succ_lt_succ hk
      have hk' : k < L + 1 := Nat.lt_of_succ_lt hk
      have ihk := ih hk'
      -- The clean transported step matrix for the UNSCALED tuple, HEq to `A ⟨k,hkL⟩` (sidesteps the
      -- prodAux Eq.mpr cast — the scalar then rides on the clean `Mstep`).
      let Mstep : Matrix (Fin (H ⟨k, hk'⟩)) (Fin (H ⟨k + 1, hk⟩)) ℝ := by
        have e1 : (⟨k, hk'⟩ : Fin (L + 1)) = (⟨k, hkL⟩ : Fin L).castSucc := by
          apply Fin.ext; simp [Fin.castSucc]
        have e2 : (⟨k + 1, hk⟩ : Fin (L + 1)) = (⟨k, hkL⟩ : Fin L).succ := by
          apply Fin.ext; simp [Fin.succ]
        rw [e1, e2]; exact A ⟨k, hkL⟩
      have hM : HEq (A ⟨k, hkL⟩) Mstep := by dsimp only [Mstep]; exact heq_of_eqRec_eq rfl rfl
      rw [prodAux_step H A k hk Mstep hM]
      -- `(scaleLayer..) ⟨k,hkL⟩` is `A ⟨k,hkL⟩` off `s`, `c • A ⟨k,hkL⟩` at `s`.
      rcases lt_trichotomy (s : ℕ) k with hlt | heq | hgt
      · -- s < k ⟹ s < k+1 (scalar c); layer k ≠ s so scaleLayer is identity there ⟹ Mstep
        have hne : (⟨k, hkL⟩ : Fin L) ≠ s := fun h => by
          have : (s : ℕ) = k := by rw [← h]
          omega
        have hMs : HEq ((scaleLayer H c s A) ⟨k, hkL⟩) Mstep := by
          rw [scaleLayer, Function.update_of_ne hne]; exact hM
        rw [prodAux_step H (scaleLayer H c s A) k hk Mstep hMs]
        rw [if_pos hlt] at ihk
        rw [if_pos (by omega : (s : ℕ) < k + 1), ihk, Matrix.smul_mul]
      · -- s = k ⟹ s < k+1 (scalar c); layer k = s ⟹ scaleLayer = c • A ⟹ c • Mstep
        have hsk : (⟨k, hkL⟩ : Fin L) = s := Fin.ext heq.symm
        have hMs : HEq ((scaleLayer H c s A) ⟨k, hkL⟩) (c • Mstep) := by
          have h1 : (scaleLayer H c s A) ⟨k, hkL⟩ = c • A ⟨k, hkL⟩ := by
            rw [scaleLayer, hsk, Function.update_self]
          rw [h1]; cases hM; rfl
        rw [prodAux_step H (scaleLayer H c s A) k hk (c • Mstep) hMs]
        rw [if_neg (by omega : ¬ (s : ℕ) < k)] at ihk
        rw [if_pos (by omega : (s : ℕ) < k + 1), ihk, one_smul, Matrix.mul_smul]
      · -- s > k ⟹ ¬ s<k+1 (scalar 1); layer k ≠ s ⟹ Mstep; ¬ s<k ⟹ ih scalar 1
        have hne : (⟨k, hkL⟩ : Fin L) ≠ s := fun h => by
          have : (s : ℕ) = k := by rw [← h]
          omega
        have hMs : HEq ((scaleLayer H c s A) ⟨k, hkL⟩) Mstep := by
          rw [scaleLayer, Function.update_of_ne hne]; exact hM
        rw [prodAux_step H (scaleLayer H c s A) k hk Mstep hMs]
        rw [if_neg (by omega : ¬ (s : ℕ) < k)] at ihk
        rw [if_neg (by omega : ¬ (s : ℕ) < k + 1), ihk, one_smul, one_smul]

/-- **`prod` scales linearly in one layer.** `prod (scaleLayer c s A) = c • prod A`: the full product
includes every layer, so the scaled layer `s` is always in the prefix (`s < L`), giving the scalar
`c`. Specialises `prodAux_scaleLayer` at `k = L`. -/
theorem prod_scaleLayer (H : Fin (L + 1) → ℕ) (c : ℝ) (s : Fin L) (A : Params H) :
    prod H (scaleLayer H c s A) = c • prod H A := by
  have h := prodAux_scaleLayer H c s A L (Nat.lt_succ_self L)
  rw [prod, prod]
  rwa [if_pos s.isLt] at h

/-- **`dlnLoss … 0` is degree-2 homogeneous in each layer block.** Scaling layer `s` by `c` scales the
square-Frobenius loss at the deepest point by `c²`: `dlnLoss H 0 (scaleLayer c s A) = c² · dlnLoss H 0 A`.
From `prod_scaleLayer` (entries scale by `c`) + sum-of-squares (each square by `c²`, the sum by `c²`).
This is the `dlnLoss` instance of G2's `hhomog` (active block = one layer's entries). -/
theorem dlnLoss_homogeneous_layer (H : Fin (L + 1) → ℕ) (c : ℝ) (s : Fin L) (A : Params H) :
    dlnLoss H 0 (scaleLayer H c s A) = c ^ 2 * dlnLoss H 0 A := by
  unfold dlnLoss
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  have hp : prod H (scaleLayer H c s A) = c • prod H A := prod_scaleLayer H c s A
  simp only [Matrix.sub_apply, Matrix.zero_apply, sub_zero, hp, Matrix.smul_apply, smul_eq_mul]
  ring

end DLNFibre.DLN.RLCT
