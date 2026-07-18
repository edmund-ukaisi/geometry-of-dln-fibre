import DLNFibre.DLN.RLCT.Foundations.S1ScalingBridge
import DLNFibre.DLN.RLCT.Foundations.S1NodeFlatHomog
import DLNFibre.DLN.RLCT.Foundations.ParamsFlatLinear

/-!
# `DLNFibre.DLN.RLCT.Foundations.S1ScalingBridgeDLN` — the DLN loss is degree-`2L` homogeneous
  under the FULL (all-layers) scaling, and the scaling bridge instantiated for the flat node loss

The scaling bridge (`S1ScalingBridge`) takes the homogeneity of the integrand as a hypothesis. This
module supplies that input for the DLN loss under the FULL module scaling `A ↦ c • A` (every layer
scaled at once — distinct from the banked per-layer `dlnLoss_homogeneous_layer`, degree 2 in ONE
layer). The layer product is a product of `L` matrices, each scaled by `c`, so `prod M (c • A) =
c^L • prod M A`, hence `dlnLoss M 0 (c • A) = c^(2L) · dlnLoss M 0 A` and the flat shadow
`flatNodeLoss M (c • x) = c^(2L) · flatNodeLoss M x` — the degree-`2L` homogeneity the scaling
bridge consumes (`D = 2L`).

`lintegral_flatNodeLoss_smul_bridge` is the ready-to-use form for `region_glue`'s box: on the flat
coordinates `Fin (flatDim M) → ℝ`, `∫_{ε•K} flatNodeLoss^{-c'} = ε^(flatDim M − 2L·c') · ∫_K …`.
-/

open MeasureTheory Matrix
open scoped ENNReal BigOperators Pointwise

namespace DLNFibre.DLN.RLCT

variable {L : ℕ}

/-- **The prefix layer product scales by `c^k` under the full scaling.** `prodAux M (c • A) k =
c^k • prodAux M A k`: each of the first `k` layers of `c • A` is `c • (layer)`, so the product picks
up `c^k`. Induction on `k` reusing `prodAux_succ` (the reindex-explicit step); the reindex commutes
with `•` (`submatrix_smul`) and the scalars collect by `smul_mul_assoc` / `mul_smul_comm`. -/
theorem prodAux_smul (M : Fin (L + 1) → ℕ) (c : ℝ) (A : Params M) :
    ∀ (k : ℕ) (hk : k < L + 1), prodAux M (c • A) k hk = c ^ k • prodAux M A k hk := by
  intro k
  induction k with
  | zero => intro hk; simp only [prodAux, pow_zero, one_smul]
  | succ k ih =>
      intro hk
      have hkL : k < L := Nat.lt_of_succ_lt_succ hk
      have hk' : k < L + 1 := Nat.lt_of_succ_lt hk
      have e1 : M (⟨k, hk'⟩ : Fin (L + 1)) = M ((⟨k, hkL⟩ : Fin L).castSucc) :=
        congrArg M (by apply Fin.ext; simp [Fin.castSucc])
      have e2 : M (⟨k + 1, hk⟩ : Fin (L + 1)) = M ((⟨k, hkL⟩ : Fin L).succ) :=
        congrArg M (by apply Fin.ext; simp [Fin.succ])
      rw [prodAux_succ M (c • A) k hk e1 e2, prodAux_succ M A k hk e1 e2, ih hk']
      have hlayer : (c • A) (⟨k, hkL⟩ : Fin L) = c • A (⟨k, hkL⟩ : Fin L) := rfl
      have hreidx : Matrix.reindex (finCongr e1.symm) (finCongr e2.symm) (c • A (⟨k, hkL⟩ : Fin L))
          = c • Matrix.reindex (finCongr e1.symm) (finCongr e2.symm) (A (⟨k, hkL⟩ : Fin L)) := by
        rw [Matrix.reindex_apply, Matrix.reindex_apply]; ext i j; rfl
      rw [hlayer, hreidx, Matrix.smul_mul, Matrix.mul_smul, smul_smul, ← pow_succ]

/-- **The full layer product scales by `c^L`.** `prod M (c • A) = c^L • prod M A` — every layer is
in the product, so all `L` scalars collect. Specialises `prodAux_smul` at `k = L`. -/
theorem prod_smul (M : Fin (L + 1) → ℕ) (c : ℝ) (A : Params M) :
    prod M (c • A) = c ^ L • prod M A := by
  unfold prod
  exact prodAux_smul M c A L (Nat.lt_succ_self L)

/-- **The DLN loss at target `0` is degree-`2L` homogeneous in the FULL parameter** (all layers
scaled together): `dlnLoss M 0 (c • A) = c^(2L) · dlnLoss M 0 A`. The product scales by `c^L`
(`prod_smul`), so each squared entry by `c^(2L)`. This is the degree-`D` homogeneity (`D = 2L`) the
scaling bridge needs — the full-scaling companion of the per-layer `dlnLoss_homogeneous_layer`. -/
theorem dlnLoss_zero_smul (M : Fin (L + 1) → ℕ) (c : ℝ) (A : Params M) :
    dlnLoss M 0 (c • A) = c ^ (2 * L) * dlnLoss M 0 A := by
  unfold dlnLoss
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  have hp : prod M (c • A) = c ^ L • prod M A := prod_smul M c A
  simp only [Matrix.sub_apply, Matrix.zero_apply, sub_zero, hp, Matrix.smul_apply, smul_eq_mul]
  rw [mul_pow, ← pow_mul, Nat.mul_comm L 2]

/-- **The flat node loss is degree-`2L` homogeneous under the flat scaling** `x ↦ c • x`:
`flatNodeLoss M (c • x) = c^(2L) · flatNodeLoss M x`. The flat scaling pulls back through the LINEAR
`(paramsEquivFlat M).symm` to the matrix scaling `c • A`, then `dlnLoss_zero_smul` gives `c^(2L)`.
This is the homogeneity input the flat-coordinate scaling bridge (`region_glue`) consumes. -/
theorem flatNodeLoss_smul (M : Fin (L + 1) → ℕ) (c : ℝ) (x : Fin (flatDim M) → ℝ) :
    flatNodeLoss M (c • x) = c ^ (2 * L) * flatNodeLoss M x := by
  have hcoe : ⇑(paramsEquivFlat M) = ⇑(paramsEquivFlatLinear M) :=
    (paramsEquivFlatLinear_coe M).symm
  have hsymm : ⇑(paramsEquivFlat M).symm = ⇑(paramsEquivFlatLinear M).symm := by
    funext y
    apply (paramsEquivFlat M).injective
    rw [(paramsEquivFlat M).apply_symm_apply, hcoe, (paramsEquivFlatLinear M).apply_symm_apply]
  have hlin : (paramsEquivFlat M).symm (c • x) = c • (paramsEquivFlat M).symm x := by
    rw [hsymm]; exact map_smul (paramsEquivFlatLinear M).symm c x
  unfold flatNodeLoss
  rw [hlin, dlnLoss_zero_smul]

/-- **The scaling bridge for the flat node loss** — the ready form for `region_glue`. On the flat
coordinates `Fin (flatDim M) → ℝ`, for `ε > 0` and measurable `K`:

    ∫_{ε • K} flatNodeLoss M ^{-c'} = ε^(flatDim M − 2L·c') · ∫_K flatNodeLoss M ^{-c'}.

Instantiates `lintegral_rpow_neg_smul_bridge` at `F = flatNodeLoss M`, `D = 2L`, with nonnegativity
(`dlnLoss_nonneg`) and homogeneity (`flatNodeLoss_smul`). -/
theorem lintegral_flatNodeLoss_smul_bridge (M : Fin (L + 1) → ℕ) (c' ε : ℝ)
    (K : Set (Fin (flatDim M) → ℝ)) (hε : 0 < ε) (hK : MeasurableSet K) :
    ∫⁻ y in ε • K, ENNReal.ofReal (flatNodeLoss M y ^ (-c'))
      = ENNReal.ofReal (ε ^ ((flatDim M : ℝ) - (2 * L) * c'))
          * ∫⁻ x in K, ENNReal.ofReal (flatNodeLoss M x ^ (-c')) := by
  have hbridge := lintegral_rpow_neg_smul_bridge (flatNodeLoss M) (2 * L) c' ε K
    (fun x => dlnLoss_nonneg M 0 _) (fun c w => flatNodeLoss_smul M c w) hε hK
  rw [hbridge]
  norm_num

end DLNFibre.DLN.RLCT
