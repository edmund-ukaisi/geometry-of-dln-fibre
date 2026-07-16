import DLNFibre.DLN.RLCT.Validate.RouteMSJGramResidual
import DLNFibre.DLN.RLCT.Validate.RouteMSJProductTube
import DLNFibre.DLN.RLCT.Validate.RouteMSchurRectCharged
import DLNFibre.DLN.RLCT.Validate.RouteMSchurPSDDetMono

set_option linter.style.longLine false

/-!
# `RouteMSchurWishartWeight` — the b-general charge-weight (Wishart) finiteness

The shallow-cell charge-weight bound for the CHARGED corank recursion (couplerad §w3-atlas): for a `b×m`
matrix `B` (`b ≤ m`), the matrix-variate integral `∫_{B∈matBox b m T} det(B·Bᵀ)^{−a/2}` is finite when
`a < m − b + 1` (corneradj's confirmed threshold, at the rank-`m` floor). The `b=1` case is the banked
`corankWeight_lt_top`; general `b` peels one row via the banked Gram-det row-residual recursion
`RouteMSJGramResidual.det_gram_cons` (`det(gram(cons w u)) = det(gram u)·‖P_{V⊥}w‖²`), reducing to the
lower-`b` weight times a projection-radial integral `∫_w ‖P_{V⊥}w‖^{−a}` (finite for `a < dim V⊥`,
`dim V⊥ ≥ m−(b−1)`). Non-spectral.

## Status + RESUME LADDER (handoff, off HEAD @784eef727)

LANDED: `det_mulTranspose_eq_det_gram` (the Gram bridge — the entry point to `det_gram_cons`).

RESUME LADDER (build order; the pieces are banked, this is assembly-at-scale, no wall — corneradj-confirmed
convergence, couplerad §w3-atlas/§w3-deep design):
1. **Shallow Wishart weight** `∫_{B∈matBox b m T} det(B·Bᵀ)^{−a/2} < ⊤` for `a < m−b+1`. Peel one row via
   `det_gram_cons` (`RouteMSJGramResidual.lean:194`, `det(gram(cons w u)) = det(gram u)·‖P_{V⊥}w‖²`) through
   the Gram bridge above; Fubini (Tonelli, `∫⁻` nonneg) + the projection-radial integrability
   `∫_w ‖P_{V⊥}w‖^{−a} ≤ C` (finite/uniform for `a < dim V⊥`, `dim V⊥ ≥ m−(b−1)`; reduce to a radial
   integral in the `dim V⊥`-subspace). `b=1` is the banked `corankWeight_lt_top`
   (`RouteMSJOffSectorB1.lean:124`, with the full-rank floor `hZ`).
2. **S-rank-flag cover**: instantiate the banked `deepCover_aux` spine at `S` over `matBox n p` —
   `rankEqLocus_eq_iUnion_pivot_inter` (`RouteMSJDeepCover:50`), `exists_nonsingular_submatrix_of_le_rank`
   (`RouteMSJPivotChart:266`), `generalPivot_reduce_rank(_of)` (`RouteMSJDeepPivot:106/142`);
   `deepRankLE_lintegral_lt_top` glues. Per-cell σ-measure CoV = a new pivot-minor-det Jacobian (standard).
3. **Shallow bolt-on cells** (`rank S ≥ a+b`): on the pivot chart, det-monotone `(A) det_le_det_of_posSemidef_sub`
   (`RouteMSchurPSDDetMono.lean`) reduces `det(A_cor·SSᵀ·A_corᵀ) ≥ det(A_cor·(δ²·rank-(a+b))·A_corᵀ)`, so
   charge ≤ Wishart const (step 1); residual = banked uncharged `routeMBoxThresholdFinite_mnp`.
4. **b=1 deep cell** (`rank S ≤ 1`, all 3 witnesses a=1): charge weight `W(S) ~ ln(1/σ)` (couplerad §w3-deep),
   killed by the codim-`c≥1` σ-measure; Lean route (option II) `ln(1/σ) ≤ C_ε·σ^{−ε}` (any `ε∈(0,1)`, uniform
   since `c≥1` always) → `σ^{−ε}·σ^{c−1}` integrable; track `L(S)` finite via the uncharged mnp on the cell;
   `δ=0` so it doesn't eat the loss budget. (`a≥2`/`b≥2` deep cells use couplerad's power E-recursion §w3-atlas
   — PING couplerad for the exact per-step inequality; NOT needed for the 3 b=1 witnesses.)
5. **Assemble** the interior endpoint `ChargedRectSchurCore m n p a b c' T` scoped `a+b ≤ ρ` (ρ = min n p =
   tailMinWidth), finite for `c' < ½·minAdm(![m,n,p])`. THIS IS item-4 hfin: the coupledBox re-architecture
   (arch1build @1691dd192) routes `shellSpine ≤ ∫coupledBox → in-regime(a+b≤ρ) via coupledCell_le_frontCell
   → item-4`, so the IN-REGIME cells consume this directly. Edge `a+b=ρ+1` is (D)/dbuild's, NOT here.

The scaffold's `ChargedRectSchurRecStep`/`ChargedRectSchurLowerIH`/`chargedRectCore_schurGen_lt_top`
(`RouteMSchurRectCharged.lean`) are VESTIGIAL (the charge can't be carried down the shared-rank drop — H1);
replace with the direct endpoint above.
-/

open Matrix MeasureTheory
open scoped Matrix InnerProductSpace BigOperators ENNReal

namespace DLNFibre.DLN.RLCT

/-- **Gram bridge.** `det(B·Bᵀ)` equals the determinant of the Gram matrix of `B`'s rows viewed as
Euclidean vectors — the entry point to the banked `det_gram_cons` row-residual recursion. -/
theorem det_mulTranspose_eq_det_gram {b m : ℕ} (B : Fin b → Fin m → ℝ) :
    ((Matrix.of B) * (Matrix.of B)ᵀ).det
      = (Matrix.gram ℝ (fun i => (WithLp.equiv 2 (Fin m → ℝ)).symm (B i))).det := by
  congr 1
  ext i j
  rw [Matrix.gram_apply,
    show ⟪(WithLp.equiv 2 (Fin m → ℝ)).symm (B i), (WithLp.equiv 2 (Fin m → ℝ)).symm (B j)⟫_ℝ
        = (B j) ⬝ᵥ star (B i) from rfl,
    Matrix.mul_apply]
  simp only [dotProduct, star_trivial, Matrix.transpose_apply, Matrix.of_apply]
  exact Finset.sum_congr rfl (fun k _ => by ring)

/-! ## The general-`b` charged Wishart weight (full deep-rank / ρ = n core) -/

/-- The raw matrix product `rmatMul` is `Matrix.of`-matrix multiplication. -/
theorem of_rmatMul {b n p : ℕ} (Acor : Fin b → Fin n → ℝ) (S : Fin n → Fin p → ℝ) :
    Matrix.of (rmatMul Acor S) = Matrix.of Acor * Matrix.of S := by
  ext i j
  simp only [Matrix.of_apply, rmatMul, Matrix.mul_apply]

/-- **Charge Gram, product form.** `chargeGramDet Acor S = det(A · (S·Sᵀ) · Aᵀ)` with `A = Matrix.of
Acor`, `S = Matrix.of S` — the Gram of `A·S` re-associated through the deep coupling `S·Sᵀ`. -/
theorem chargeGramDet_eq_conj {b n p : ℕ} (Acor : Fin b → Fin n → ℝ) (S : Fin n → Fin p → ℝ) :
    chargeGramDet Acor S
      = (Matrix.of Acor * ((Matrix.of S) * (Matrix.of S)ᵀ) * (Matrix.of Acor)ᵀ).det := by
  unfold chargeGramDet
  rw [of_rmatMul]
  congr 1
  rw [Matrix.transpose_mul]
  simp only [← Matrix.mul_assoc]

/-- **The charge vanishes on the rank-deficient corank locus.** If the corank Gram `A·Aᵀ` is singular
(`det = 0`), then the charge Gram `det((A·S)(A·S)ᵀ)` is `0` too: a null vector `v` of `A·Aᵀ` gives
`Aᵀ·v = 0` (via `‖Aᵀv‖² = 0`), hence `(A·S)ᵀ·v = Sᵀ·(Aᵀ·v) = 0`, so `(A·S)(A·S)ᵀ·v = 0`. This is the
`det = 0` branch of the pointwise power bound (mirrors `corankWeight_lt_top`'s zero handling). -/
theorem chargeGramDet_eq_zero_of_corank_singular {b n p : ℕ} (Acor : Fin b → Fin n → ℝ)
    (S : Fin n → Fin p → ℝ) (hd : ((Matrix.of Acor) * (Matrix.of Acor)ᵀ).det = 0) :
    chargeGramDet Acor S = 0 := by
  set A := Matrix.of Acor with hA
  obtain ⟨v, hv_ne, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hd
  set w : Fin n → ℝ := Aᵀ *ᵥ v with hw
  -- `A ·ᵥ w = (A Aᵀ) ·ᵥ v = 0`
  have hAw : A *ᵥ w = 0 := by rw [hw, Matrix.mulVec_mulVec]; exact hv
  -- `w ⬝ᵥ w = v ⬝ᵥ (A ·ᵥ w) = 0`, so `w = 0`
  have hww : w ⬝ᵥ w = 0 := by
    calc w ⬝ᵥ w = (Aᵀ *ᵥ v) ⬝ᵥ w := by rw [hw]
      _ = (v ᵥ* A) ⬝ᵥ w := by rw [Matrix.mulVec_transpose]
      _ = v ⬝ᵥ (A *ᵥ w) := by rw [← Matrix.dotProduct_mulVec]
      _ = v ⬝ᵥ 0 := by rw [hAw]
      _ = 0 := dotProduct_zero _
  have hw0 : w = 0 := dotProduct_self_eq_zero.mp hww
  -- transport the null vector to the charge Gram
  have hMt : (Matrix.of (rmatMul Acor S))ᵀ *ᵥ v = 0 := by
    rw [of_rmatMul, ← hA, Matrix.transpose_mul, ← Matrix.mulVec_mulVec, ← hw, hw0,
      Matrix.mulVec_zero]
  have hMv : ((Matrix.of (rmatMul Acor S)) * (Matrix.of (rmatMul Acor S))ᵀ) *ᵥ v = 0 := by
    rw [← Matrix.mulVec_mulVec, hMt, Matrix.mulVec_zero]
  unfold chargeGramDet
  exact Matrix.exists_mulVec_eq_zero_iff.mp ⟨v, hv_ne, hMv⟩

/-- **The (A) det-monotone charge lower bound.** With the full-deep-rank Loewner floor `S·Sᵀ ⪰ δ²·I`,
the charge Gram dominates the isotropic corank Gram: `(δ²)^b · det(A·Aᵀ) ≤ det((A·S)(A·S)ᵀ)`. Via the
banked non-spectral `det_le_det_of_posSemidef_sub` applied to `X = A·(S·Sᵀ)·Aᵀ`, `Y = δ²·(A·Aᵀ)`
(`X − Y = A·(S·Sᵀ − δ²I)·Aᵀ ⪰ 0`, `Y ⪰ 0`; `det Y = (δ²)^b·det(A·Aᵀ)` by `det_smul`). -/
theorem charge_ge_isotropic {b n p : ℕ} (S : Fin n → Fin p → ℝ) (δ : ℝ)
    (hS : (((Matrix.of S) * (Matrix.of S)ᵀ) - δ ^ 2 • (1 : Matrix (Fin n) (Fin n) ℝ)).PosSemidef)
    (Acor : Fin b → Fin n → ℝ) :
    (δ ^ 2) ^ b * ((Matrix.of Acor) * (Matrix.of Acor)ᵀ).det ≤ chargeGramDet Acor S := by
  set A := Matrix.of Acor with hA
  set G := (Matrix.of S) * (Matrix.of S)ᵀ with hG
  -- Y = δ²•(A Aᵀ) is PSD
  have hYpsd : ((δ ^ 2) • (A * Aᵀ)).PosSemidef :=
    (posSemidef_mul_transpose A).smul (by positivity)
  -- X − Y = A·(G − δ²I)·Aᵀ is PSD
  have hXYpsd : ((A * G * Aᵀ) - (δ ^ 2) • (A * Aᵀ)).PosSemidef := by
    have hconj := hS.mul_mul_conjTranspose_same A
    rw [Matrix.conjTranspose_eq_transpose_of_trivial] at hconj
    have hmateq : A * (G - δ ^ 2 • (1 : Matrix (Fin n) (Fin n) ℝ)) * Aᵀ
        = (A * G * Aᵀ) - (δ ^ 2) • (A * Aᵀ) := by
      rw [Matrix.mul_sub, Matrix.sub_mul]
      congr 1
      rw [Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul]
    rw [hmateq] at hconj
    exact hconj
  have hdet := det_le_det_of_posSemidef_sub (A * G * Aᵀ) ((δ ^ 2) • (A * Aᵀ)) hYpsd hXYpsd
  rw [Matrix.det_smul, Fintype.card_fin] at hdet
  rw [chargeGramDet_eq_conj, ← hA, ← hG]
  exact hdet

/-- **The charged Wishart weight is finite (full deep-rank / ρ = n core).** For a deep factor `S : n×p`
with the FULL-deep-rank Loewner floor `hS : S·Sᵀ ⪰ δ²·I` (`δ > 0`, forcing `rank S = n`), and the
interior charge exponent `a + b ≤ n`, the charged corank weight
`∫_{A_cor ∈ matBox b n 1} det((A_cor·S)(A_cor·S)ᵀ)^{−a/2}` is finite. The `b`-general lift of the banked
`b = 1` `corankWeight_lt_top`: the banked (A) `det_le_det_of_posSemidef_sub` reduces the charge to the
isotropic corank Gram, and `∫ det(A_cor·A_corᵀ)^{−a/2}` is finite by the banked `detGram_lintegral_lt_top`
(`a < n − b + 1 ⟺ a + b ≤ n`). NON-SPECTRAL. Scope: this needs `S·Sᵀ ⪰ δ²·I` (`ρ = n`); the rank-`ρ<n`
cell lift (row-space Loewner floor) is separate. -/
theorem chargedWishartWeight_lt_top {a b n p : ℕ} (S : Fin n → Fin p → ℝ) (δ : ℝ) (hδ : 0 < δ)
    (hab : a + b ≤ n)
    (hS : (((Matrix.of S) * (Matrix.of S)ᵀ) - δ ^ 2 • (1 : Matrix (Fin n) (Fin n) ℝ)).PosSemidef) :
    (∫⁻ Acor in matBox b n 1,
        ENNReal.ofReal ((chargeGramDet Acor S) ^ (-(a : ℝ) / 2))) < ⊤ := by
  classical
  set s : ℝ := -(a : ℝ) / 2 with hs
  have hsnonpos : s ≤ 0 := by
    rw [hs]; have h0 : (0 : ℝ) ≤ (a : ℝ) := Nat.cast_nonneg a; linarith
  have hδ2 : (0 : ℝ) < δ ^ 2 := by positivity
  have hCpos : (0 : ℝ) < (δ ^ 2) ^ b := by positivity
  -- pointwise power bound: charge^s ≤ ((δ²)^b)^s · det(A Aᵀ)^s
  have hpt : ∀ Acor : Fin b → Fin n → ℝ,
      (chargeGramDet Acor S) ^ s
        ≤ ((δ ^ 2) ^ b) ^ s * (((Matrix.of Acor) * (Matrix.of Acor)ᵀ).det) ^ s := by
    intro Acor
    have hge := charge_ge_isotropic S δ hS Acor
    have hdetnn : 0 ≤ ((Matrix.of Acor) * (Matrix.of Acor)ᵀ).det :=
      (posSemidef_mul_transpose (Matrix.of Acor)).det_nonneg
    rcases eq_or_lt_of_le hdetnn with hd | hd
    · -- det(A Aᵀ) = 0 ⟹ charge = 0
      rw [chargeGramDet_eq_zero_of_corank_singular Acor S hd.symm, ← hd]
      rcases eq_or_lt_of_le hsnonpos with hs0 | hspos
      · rw [hs0]; simp
      · simp [Real.zero_rpow (ne_of_lt hspos)]
    · -- 0 < det(A Aᵀ): antitone rpow on the positive lower bound
      have hposlow : (0 : ℝ) < (δ ^ 2) ^ b * ((Matrix.of Acor) * (Matrix.of Acor)ᵀ).det :=
        mul_pos hCpos hd
      calc (chargeGramDet Acor S) ^ s
          ≤ ((δ ^ 2) ^ b * ((Matrix.of Acor) * (Matrix.of Acor)ᵀ).det) ^ s :=
            Real.rpow_le_rpow_of_nonpos hposlow hge hsnonpos
        _ = ((δ ^ 2) ^ b) ^ s * (((Matrix.of Acor) * (Matrix.of Acor)ᵀ).det) ^ s :=
            Real.mul_rpow hCpos.le hdetnn
  -- integrate the pointwise bound; pull the constant; apply the banked det-Gram integral
  calc ∫⁻ Acor in matBox b n 1, ENNReal.ofReal ((chargeGramDet Acor S) ^ s)
      ≤ ∫⁻ Acor in matBox b n 1,
          ENNReal.ofReal (((δ ^ 2) ^ b) ^ s)
            * ENNReal.ofReal ((((Matrix.of Acor) * (Matrix.of Acor)ᵀ).det) ^ s) := by
        refine lintegral_mono (fun Acor => ?_)
        rw [← ENNReal.ofReal_mul (by positivity)]
        exact ENNReal.ofReal_le_ofReal (hpt Acor)
    _ = ENNReal.ofReal (((δ ^ 2) ^ b) ^ s)
          * ∫⁻ Acor in matBox b n 1,
              ENNReal.ofReal ((((Matrix.of Acor) * (Matrix.of Acor)ᵀ).det) ^ s) :=
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ < ⊤ := by
        refine ENNReal.mul_lt_top ENNReal.ofReal_lt_top ?_
        have hbn : b ≤ n := by omega
        have haq : (a : ℝ) < (n : ℝ) - b + 1 := by
          have hab' : (a : ℝ) + (b : ℝ) ≤ (n : ℝ) := by exact_mod_cast hab
          linarith
        have h := detGram_lintegral_lt_top (r := b) (n := n) hbn (a := (a : ℝ)) haq
        rw [hs]
        simpa using h

end DLNFibre.DLN.RLCT
