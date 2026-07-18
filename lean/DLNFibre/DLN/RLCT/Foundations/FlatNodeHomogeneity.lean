import DLNFibre.DLN.RLCT.Foundations.S1NodeFlatHomog
import DLNFibre.DLN.RLCT.Foundations.ParamsFlatLinear
import DLNFibre.DLN.RLCT.Foundations.LossContinuity

/-!
# `DLNFibre.DLN.RLCT.Foundations.FlatNodeHomogeneity` — all-layer scaling homogeneity

The degree-`2L` homogeneity of the deepest core `dlnLoss M 0` and its flat shadow `flatNodeLoss M`
under an all-layer (equivalently, all-coordinate) scaling, plus flat-shadow measurability. Extracted
from `D1L2ExplicitCoreProducer` into this light `Foundations` module so the homogeneity facts (which
`D1L2ExplicitCoreProducer`, `RegionGlueGlobalize`, and the region-glue globalization all consume) sit
on a small import cone — `S1NodeFlatHomog` + `ParamsFlatLinear` + `LossContinuity` — rather than the
full explicit-core producer chain (`DeepestMinRlct` / `R1ResolutionInterfaceL2` / …).
`D1L2ExplicitCoreProducer` imports this module back, so no name moves namespace and no downstream
consumer's imports change.

Delivers:
* `prodAux_smul_pow` / `prod_smul_pow` — the layer product scales by `c ^ k` / `c ^ L`.
* `dlnLoss_zero_smul` — `dlnLoss M 0 (c • A) = c ^ (2L) · dlnLoss M 0 A`.
* `paramsEquivFlat_symm_eq_linear` — the measurable/linear `symm` agreement.
* `flatNodeLoss_smul` — the flat shadow's homogeneity (feeds `deepest_le_of_homogeneous_core`).
* `measurable_flatNodeLoss` — flat-shadow measurability.
-/

open MeasureTheory
open scoped ENNReal Topology BigOperators
namespace DLNFibre.DLN.RLCT

variable {L : ℕ}

/-! ## Full (all-layer) homogeneity of the deepest core `dlnLoss M 0` -/

/-- The `prodAux` recursion-step with the dependent-`Fin` cast discharged by HEq (local copy of the
`LossHomogeneity` private helper). -/
private theorem prodAux_step' (H : Fin (L + 1) → ℕ) (A : Params H) (k : ℕ) (hk : k + 1 < L + 1)
    (Mstep : Matrix (Fin (H ⟨k, Nat.lt_of_succ_lt hk⟩)) (Fin (H ⟨k + 1, hk⟩)) ℝ)
    (hheq : HEq (A ⟨k, Nat.lt_of_succ_lt_succ hk⟩) Mstep) :
    prodAux H A (k + 1) hk = prodAux H A k (Nat.lt_of_succ_lt hk) * Mstep := by
  rw [prodAux]; congr 1; rw [eq_comm]; apply eq_of_heq
  exact hheq.symm.trans (heq_of_eqRec_eq rfl rfl)

/-- **The prefix product scales by `c ^ k` under an all-layer scaling.** `prodAux (c • A) k = c ^ k •
prodAux A k`: each of the first `k` layers contributes one factor of `c`. Induction on `k`; the
successor step pulls one `c` out of the current layer (`Matrix.mul_smul`) and folds it into the
prefix power. -/
theorem prodAux_smul_pow (H : Fin (L + 1) → ℕ) (c : ℝ) (A : Params H) :
    ∀ (k : ℕ) (hk : k < L + 1),
      prodAux H (c • A) k hk = c ^ k • prodAux H A k hk := by
  intro k
  induction k with
  | zero => intro hk; simp only [prodAux, pow_zero, one_smul]
  | succ k ih =>
      intro hk
      have hkL : k < L := Nat.lt_of_succ_lt_succ hk
      have hk' : k < L + 1 := Nat.lt_of_succ_lt hk
      -- clean transported step matrix for the UNSCALED tuple (sidesteps the prodAux Eq.mpr cast).
      let Mstep : Matrix (Fin (H ⟨k, hk'⟩)) (Fin (H ⟨k + 1, hk⟩)) ℝ := by
        have e1 : (⟨k, hk'⟩ : Fin (L + 1)) = (⟨k, hkL⟩ : Fin L).castSucc := by
          apply Fin.ext; simp [Fin.castSucc]
        have e2 : (⟨k + 1, hk⟩ : Fin (L + 1)) = (⟨k, hkL⟩ : Fin L).succ := by
          apply Fin.ext; simp [Fin.succ]
        rw [e1, e2]; exact A ⟨k, hkL⟩
      have hM : HEq (A ⟨k, hkL⟩) Mstep := by dsimp only [Mstep]; exact heq_of_eqRec_eq rfl rfl
      -- the scaled tuple's layer `k` is `c • A ⟨k,hkL⟩` (Pi smul), HEq to `c • Mstep`.
      have hMs : HEq ((c • A) ⟨k, hkL⟩) (c • Mstep) := by
        have h1 : (c • A) ⟨k, hkL⟩ = c • A ⟨k, hkL⟩ := rfl
        rw [h1]; cases hM; rfl
      rw [prodAux_step' H (c • A) k hk (c • Mstep) hMs,
          prodAux_step' H A k hk Mstep hM, ih hk',
          Matrix.smul_mul, Matrix.mul_smul, smul_smul, ← pow_succ]

/-- **`prod` scales by `c ^ L` under an all-layer scaling** (`prod (c • A) = c ^ L • prod A`).
Specialises `prodAux_smul_pow` at `k = L`. -/
theorem prod_smul_pow (H : Fin (L + 1) → ℕ) (c : ℝ) (A : Params H) :
    prod H (c • A) = c ^ L • prod H A := by
  rw [prod, prod]; exact prodAux_smul_pow H c A L (Nat.lt_succ_self L)

/-- **The deepest core `dlnLoss M 0` is degree-`2L` homogeneous** (all-layer scaling). From
`prod_smul_pow` (the product scales by `c ^ L`) + the sum-of-squares (each square by `(c ^ L) ^ 2 =
c ^ (2L)`). This is the `hhomog` input Aoyagi Theorem 4 (`deepest_le_of_homogeneous_core`) needs. -/
theorem dlnLoss_zero_smul (H : Fin (L + 1) → ℕ) (c : ℝ) (A : Params H) :
    dlnLoss H 0 (c • A) = c ^ (2 * L) * dlnLoss H 0 A := by
  unfold dlnLoss
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  have hp : prod H (c • A) = c ^ L • prod H A := prod_smul_pow H c A
  simp only [Matrix.sub_apply, Matrix.zero_apply, sub_zero, hp, Matrix.smul_apply, smul_eq_mul]
  rw [mul_pow, ← pow_mul, Nat.mul_comm L 2]

/-! ## The flat shadow + measurability -/

/-- The measurable-equiv inverse `(paramsEquivFlat M).symm` agrees with the linear-equiv inverse
`(paramsEquivFlatLinear M).symm` (both invert the same forward function). -/
theorem paramsEquivFlat_symm_eq_linear (M : Fin (L + 1) → ℕ) (y : Fin (flatDim M) → ℝ) :
    (paramsEquivFlat M).symm y = (paramsEquivFlatLinear M).symm y := by
  apply (paramsEquivFlat M).injective
  rw [(paramsEquivFlat M).apply_symm_apply, ← paramsEquivFlatLinear_coe,
    (paramsEquivFlatLinear M).apply_symm_apply]

/-- **The flat node loss is degree-`2L` homogeneous** (all-coordinate scaling): `flatNodeLoss M (c • x)
= c ^ (2L) · flatNodeLoss M x`. The flat `symm` is linear, so all-coordinate scaling pulls back to an
all-layer scaling of the matrices, where `dlnLoss_zero_smul` applies. -/
theorem flatNodeLoss_smul (M : Fin (L + 1) → ℕ) (c : ℝ) (x : Fin (flatDim M) → ℝ) :
    flatNodeLoss M (c • x) = c ^ (2 * L) * flatNodeLoss M x := by
  unfold flatNodeLoss
  rw [paramsEquivFlat_symm_eq_linear, map_smul, ← paramsEquivFlat_symm_eq_linear,
    dlnLoss_zero_smul]

/-- `flatNodeLoss M` is measurable (a polynomial `dlnLoss` composed with the continuous flat inverse). -/
theorem measurable_flatNodeLoss (M : Fin (L + 1) → ℕ) : Measurable (flatNodeLoss M) :=
  (measurable_dlnLoss M 0).comp (paramsEquivFlat M).symm.measurable

end DLNFibre.DLN.RLCT
