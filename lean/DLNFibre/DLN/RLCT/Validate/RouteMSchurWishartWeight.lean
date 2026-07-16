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

/-- **The identity matrix over `ℝ` is PosSemidef** (Mathlib v4.29 lacks a direct instance; derived from the
banked Gram fact `1 = 1·1ᵀ`). -/
theorem posSemidef_one_real {n : ℕ} : (1 : Matrix (Fin n) (Fin n) ℝ).PosSemidef := by
  have h := posSemidef_mul_transpose (1 : Matrix (Fin n) (Fin n) ℝ)
  rwa [Matrix.transpose_one, Matrix.mul_one] at h

/-- **The (A) det-monotone charge lower bound, GENERAL floor** — the shared (A)-route brick. For any PSD
floor `F` with the Loewner bound `S·Sᵀ ⪰ δ²·F`, the charge Gram dominates the conjugated floor Gram:
`(δ²)^b · det(A·F·Aᵀ) ≤ det((A·S)(A·S)ᵀ)` (`A = Matrix.of Acor`). Via the banked non-spectral
`det_le_det_of_posSemidef_sub` applied to `X = A·(S·Sᵀ)·Aᵀ`, `Y = δ²·(A·F·Aᵀ)`
(`X − Y = A·(S·Sᵀ − δ²F)·Aᵀ ⪰ 0`, `Y ⪰ 0`; `det Y = (δ²)^b·det(A·F·Aᵀ)` by `det_smul`). `F = I` gives the
isotropic full-deep-rank atom; `F = P_J` (coordinate projection) the rank-ρ lift; `F = δ₀²·P_top + P_last`
the graded per-shell bound the tight-interior log-integrability consumes. -/
theorem charge_ge_floor {b n p : ℕ} (S : Fin n → Fin p → ℝ) (δ : ℝ)
    (F : Matrix (Fin n) (Fin n) ℝ) (hF : F.PosSemidef)
    (hS : (((Matrix.of S) * (Matrix.of S)ᵀ) - δ ^ 2 • F).PosSemidef)
    (Acor : Fin b → Fin n → ℝ) :
    (δ ^ 2) ^ b * ((Matrix.of Acor) * F * (Matrix.of Acor)ᵀ).det ≤ chargeGramDet Acor S := by
  set A := Matrix.of Acor with hA
  set G := (Matrix.of S) * (Matrix.of S)ᵀ with hG
  -- Y = δ²•(A F Aᵀ) is PSD (F PSD ⟹ A F Aᵀ PSD by conjugation, then nonneg smul)
  have hYpsd : ((δ ^ 2) • (A * F * Aᵀ)).PosSemidef := by
    have hconjF := hF.mul_mul_conjTranspose_same A
    rw [Matrix.conjTranspose_eq_transpose_of_trivial] at hconjF
    exact hconjF.smul (by positivity)
  -- X − Y = A·(G − δ²F)·Aᵀ is PSD
  have hXYpsd : ((A * G * Aᵀ) - (δ ^ 2) • (A * F * Aᵀ)).PosSemidef := by
    have hconj := hS.mul_mul_conjTranspose_same A
    rw [Matrix.conjTranspose_eq_transpose_of_trivial] at hconj
    have hmateq : A * (G - δ ^ 2 • F) * Aᵀ = (A * G * Aᵀ) - (δ ^ 2) • (A * F * Aᵀ) := by
      rw [Matrix.mul_sub, Matrix.sub_mul]
      congr 1
      rw [Matrix.mul_smul, Matrix.smul_mul]
    rw [hmateq] at hconj
    exact hconj
  have hdet := det_le_det_of_posSemidef_sub (A * G * Aᵀ) ((δ ^ 2) • (A * F * Aᵀ)) hYpsd hXYpsd
  rw [Matrix.det_smul, Fintype.card_fin] at hdet
  rw [chargeGramDet_eq_conj, ← hA, ← hG]
  exact hdet

/-- **The (A) charge lower bound, isotropic (`F = I`) instance** — the full-deep-rank atom's engine:
`(δ²)^b · det(A·Aᵀ) ≤ det((A·S)(A·S)ᵀ)` when `S·Sᵀ ⪰ δ²·I`. -/
theorem charge_ge_isotropic {b n p : ℕ} (S : Fin n → Fin p → ℝ) (δ : ℝ)
    (hS : (((Matrix.of S) * (Matrix.of S)ᵀ) - δ ^ 2 • (1 : Matrix (Fin n) (Fin n) ℝ)).PosSemidef)
    (Acor : Fin b → Fin n → ℝ) :
    (δ ^ 2) ^ b * ((Matrix.of Acor) * (Matrix.of Acor)ᵀ).det ≤ chargeGramDet Acor S := by
  have h := charge_ge_floor S δ (1 : Matrix (Fin n) (Fin n) ℝ) posSemidef_one_real hS Acor
  rwa [Matrix.mul_one] at h

/-- **The charged Wishart weight is finite (full deep-rank / ρ = n core).** For a deep factor `S : n×p`
with the FULL-deep-rank Loewner floor `hS : S·Sᵀ ⪰ δ²·I` (`δ > 0`, forcing `rank S = n`), and the
interior charge exponent `a + b ≤ n`, the charged corank weight
`∫_{A_cor ∈ matBox b n 1} det((A_cor·S)(A_cor·S)ᵀ)^{−a/2}` is finite. The `b`-general lift of the banked
`b = 1` `corankWeight_lt_top`: the banked (A) `det_le_det_of_posSemidef_sub` reduces the charge to the
isotropic corank Gram, and `∫ det(A_cor·A_corᵀ)^{−a/2}` is finite by the banked `detGram_lintegral_lt_top`
(`a < n − b + 1 ⟺ a + b ≤ n`). NON-SPECTRAL. Scope: this needs `S·Sᵀ ⪰ δ²·I` (`ρ = n`); the rank-`ρ<n`
cell lift (row-space Loewner floor) is separate. -/
theorem chargedWishartWeight_fullDeepRank_lt_top {a b n p : ℕ} (S : Fin n → Fin p → ℝ) (δ : ℝ)
    (hδ : 0 < δ) (hab : a + b ≤ n)
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

/-- **Non-vacuity of the full-deep-rank floor `hS`.** The identity deep factor `S = 1` (`p = n`) with
`0 < δ ≤ 1` satisfies `S·Sᵀ ⪰ δ²·I` — so `chargedWishartWeight_fullDeepRank_lt_top`'s hypotheses are
consistent (the atom is not vacuous; `rank S = n`). -/
example (n : ℕ) (δ : ℝ) (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) :
    ∃ S : Fin n → Fin n → ℝ,
      ((Matrix.of S * (Matrix.of S)ᵀ) - δ ^ 2 • (1 : Matrix (Fin n) (Fin n) ℝ)).PosSemidef := by
  refine ⟨fun i j => (1 : Matrix (Fin n) (Fin n) ℝ) i j, ?_⟩
  have hof : Matrix.of (fun i j => (1 : Matrix (Fin n) (Fin n) ℝ) i j)
      = (1 : Matrix (Fin n) (Fin n) ℝ) := rfl
  rw [hof, Matrix.transpose_one, Matrix.mul_one,
    show (1 : Matrix (Fin n) (Fin n) ℝ) - δ ^ 2 • (1 : Matrix (Fin n) (Fin n) ℝ)
        = (1 - δ ^ 2) • (1 : Matrix (Fin n) (Fin n) ℝ) from by rw [sub_smul, one_smul]]
  have hone : (1 : Matrix (Fin n) (Fin n) ℝ).PosSemidef := posSemidef_one_real
  exact hone.smul (by nlinarith [hδ0, hδ1] : (0 : ℝ) ≤ 1 - δ ^ 2)

/-! ## The det-lower-bound → uniform-Loewner-floor bridge (non-spectral)

The producer of `chargedWishartWeight_fullDeepRank_lt_top`'s hypothesis `hS` from a determinant lower
bound: on the couplerad det-shell `|det S| ≥ ε` (square `S`), with a box bound on the adjugate Frobenius
norm, `S·Sᵀ ⪰ (ε/C)²·I`. Non-spectral — via the adjugate identity `det(S)·v = adj(Sᵀ)·(Sᵀv)` + a
discrete Cauchy–Schwarz, dodging the eigenvalue/`σ_min` whnf trap. -/

/-- **Frobenius square is transpose-invariant.** `frobSq Mᵀ = frobSq M`. -/
theorem frobSq_transpose {m n : ℕ} (M : Matrix (Fin m) (Fin n) ℝ) : frobSq Mᵀ = frobSq M := by
  unfold frobSq
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => by
    rw [Matrix.transpose_apply]))

/-- **Discrete Cauchy–Schwarz for `mulVec`.** `‖M·w‖² ≤ ‖M‖_F²·‖w‖²` in dot-product form:
`(M·w)⬝(M·w) ≤ frobSq M · (w⬝w)` (per-row `Finset.sum_mul_sq_le_sq_mul_sq`, then sum the rows). -/
theorem mulVec_dotProduct_self_le_frobSq {m n : ℕ} (M : Matrix (Fin m) (Fin n) ℝ) (w : Fin n → ℝ) :
    (M *ᵥ w) ⬝ᵥ (M *ᵥ w) ≤ frobSq M * (w ⬝ᵥ w) := by
  have hww : w ⬝ᵥ w = ∑ j, w j ^ 2 :=
    Finset.sum_congr rfl (fun j _ => (sq (w j)).symm)
  have hlhs : (M *ᵥ w) ⬝ᵥ (M *ᵥ w) = ∑ i, (∑ j, M i j * w j) ^ 2 :=
    Finset.sum_congr rfl (fun i _ => by rw [← sq]; rfl)
  rw [hlhs, frobSq, Finset.sum_mul]
  refine Finset.sum_le_sum (fun i _ => ?_)
  refine le_trans (Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun j => M i j) (fun j => w j)) ?_
  rw [hww]

/-- **Det-lower-bound → uniform Loewner floor (square `S`, non-spectral).** For a square `S` with
`ε ≤ |det S|` (`ε > 0`) and the adjugate Frobenius bound `frobSq (adjugate S) ≤ C²` (`C > 0`), the deep
Gram has the uniform floor `S·Sᵀ ⪰ (ε/C)²·I`. This produces `chargedWishartWeight_fullDeepRank_lt_top`'s
`hS` from couplerad's det-shell + box bound. Route: `adj(Sᵀ)·(Sᵀv) = det(S)·v` (`adjugate_mul` +
`det_transpose`), so `det(S)²·(v⬝v) = ‖adj(Sᵀ)·(Sᵀv)‖² ≤ frobSq(adj S)·‖Sᵀv‖² ≤ C²·‖Sᵀv‖²`
(`mulVec_dotProduct_self_le_frobSq` + `frobSq_transpose`); with `ε² ≤ det²` this gives `‖Sᵀv‖² ≥
(ε/C)²·(v⬝v)`, i.e. the Loewner floor. NON-SPECTRAL. -/
theorem loewner_floor_of_abs_det_ge {n : ℕ} (S : Matrix (Fin n) (Fin n) ℝ) (ε C : ℝ)
    (hε : 0 < ε) (hC : 0 < C) (hdet : ε ≤ |S.det|) (hadj : frobSq S.adjugate ≤ C ^ 2) :
    ((S * Sᵀ) - (ε / C) ^ 2 • (1 : Matrix (Fin n) (Fin n) ℝ)).PosSemidef := by
  have hHerm : ((S * Sᵀ) - (ε / C) ^ 2 • (1 : Matrix (Fin n) (Fin n) ℝ)).IsHermitian :=
    (posSemidef_mul_transpose S).isHermitian.sub
      (posSemidef_one_real.smul (by positivity : (0 : ℝ) ≤ (ε / C) ^ 2)).isHermitian
  refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg hHerm (fun x => ?_)
  have hstar : (star x : Fin n → ℝ) = x := funext (fun i => star_trivial (x i))
  rw [hstar]
  set w : Fin n → ℝ := Sᵀ *ᵥ x with hw
  have hxx : 0 ≤ x ⬝ᵥ x := Finset.sum_nonneg (fun i _ => mul_self_nonneg _)
  have hww : 0 ≤ w ⬝ᵥ w := Finset.sum_nonneg (fun i _ => mul_self_nonneg _)
  -- adjugate identity `(adj S)ᵀ · w = det(S) • x`
  have hadjid : (S.adjugate)ᵀ *ᵥ w = S.det • x := by
    have h : (S.adjugate)ᵀ * Sᵀ = S.det • (1 : Matrix (Fin n) (Fin n) ℝ) := by
      rw [Matrix.adjugate_transpose, Matrix.adjugate_mul, Matrix.det_transpose]
    have h2 : (S.adjugate)ᵀ *ᵥ (Sᵀ *ᵥ x) = ((S.adjugate)ᵀ * Sᵀ) *ᵥ x :=
      Matrix.mulVec_mulVec x (S.adjugate)ᵀ Sᵀ
    rw [hw, h2, h, Matrix.smul_mulVec, Matrix.one_mulVec]
  -- det²·(x⬝x) = ‖(adj S)ᵀ·w‖² ≤ C²·(w⬝w)
  have hdet2xx : S.det ^ 2 * (x ⬝ᵥ x) = ((S.adjugate)ᵀ *ᵥ w) ⬝ᵥ ((S.adjugate)ᵀ *ᵥ w) := by
    rw [hadjid, smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul]; ring
  have hchain : S.det ^ 2 * (x ⬝ᵥ x) ≤ C ^ 2 * (w ⬝ᵥ w) := by
    rw [hdet2xx]
    refine le_trans (mulVec_dotProduct_self_le_frobSq (S.adjugate)ᵀ w) ?_
    rw [frobSq_transpose]
    exact mul_le_mul_of_nonneg_right hadj hww
  have hεdet : ε ^ 2 ≤ S.det ^ 2 := by
    rw [← sq_abs S.det]; exact pow_le_pow_left₀ hε.le hdet 2
  -- reduce the quadratic form and conclude
  rw [Matrix.sub_mulVec, dotProduct_sub, Matrix.smul_mulVec, Matrix.one_mulVec,
    dotProduct_smul, smul_eq_mul]
  have hquad : x ⬝ᵥ ((S * Sᵀ) *ᵥ x) = w ⬝ᵥ w := by
    have e1 : (S * Sᵀ) *ᵥ x = S *ᵥ (Sᵀ *ᵥ x) := (Matrix.mulVec_mulVec x S Sᵀ).symm
    rw [e1, Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, ← hw]
  rw [hquad]
  have hfin : (ε / C) ^ 2 * (x ⬝ᵥ x) ≤ w ⬝ᵥ w := by
    rw [div_pow, div_mul_eq_mul_div, div_le_iff₀ (by positivity : (0 : ℝ) < C ^ 2)]
    calc ε ^ 2 * (x ⬝ᵥ x) ≤ S.det ^ 2 * (x ⬝ᵥ x) := mul_le_mul_of_nonneg_right hεdet hxx
      _ ≤ C ^ 2 * (w ⬝ᵥ w) := hchain
      _ = w ⬝ᵥ w * C ^ 2 := by ring
  linarith [hfin]

end DLNFibre.DLN.RLCT
