import DLNFibre.DLN.RLCT.Validate.RouteMSJSigMin
import DLNFibre.DLN.RLCT.Validate.RouteMSJRayleigh
import DLNFibre.DLN.RLCT.Validate.RouteMSJQBoxCore
import DLNFibre.DLN.RLCT.Validate.MatMulFibre
import DLNFibre.DLN.RLCT.Validate.RouteMBoxThresholdRR4
import Mathlib.Analysis.Normed.Lp.Matrix

set_option linter.style.longLine false

/-!
# `DLNFibre.DLN.RLCT.Validate.RouteMSJProductTube` — LAYER 2, the σ-min product-tube integrability

**Thread `genm-vswire` (aoyagi-full), the (b)-integrability layer of the (3,3,3,4) deeper-strata
finiteness.** The front-first majorant of (a) produces a weight `σ_r(P)^{−α}` in the smallest
singular value of the product `P = A₀·A₁`; this module proves that weight is integrable over the
factor box, by:

* **`sigMin M`** — the smallest singular value of `M`, defined as `minStretch (Mᵀ)` (banked
  `RouteMSJSigMin.minStretch`, no `LinearMap.singularValues`).
* **the Rayleigh bridge** `⨅ eigenvalues(M Mᵀ) ≤ sigMin M ^ 2` (one direction of `gram_rayleigh_lb`,
  no eigenvector construction), giving `det(M Mᵀ) ≤ sigMin M ^ 2 · trace^{r−1}`.
* **the box comparison** `sigMin M ^ (−α) ≤ C · det(M Mᵀ)^{−α/2}` on the entries-≤-`T` box (trace
  bounded), reducing `∫ sigMin^{−α}` to the banked `qbox_lintegral_lt_top`.
* **the exact Gram factorisation** `det((A₀A₁)(A₀A₁)ᵀ) = det(A₀A₀ᵀ)·det(A₁A₁ᵀ)` (`det_product_gram`,
  valid because the front factor `A₀` is SQUARE), Tonelli-splitting `∫ σ_r(P)^{−α}` over the product box
  into the two per-factor determinant integrals. (The banked `minStretch_comp_ge` gives the honest
  submultiplicativity `sigMin (A₀·A₁) ≥ sigMin A₀ · sigMin A₁`, recorded as the standalone `sigMin_mul_le`;
  the *integrability* assembly rides the EXACT `det_product_gram` instead — a strict improvement, since the
  submult inequality's zero-stratum would itself need `det_product_gram`. `sigMin_mul_le` is therefore not
  load-bearing for the headlines.)

The (3,3,3,4) tail is 2 layers, so `P = A₀·A₁` with `A₀` free `3×3` (threshold `α<1`) and `A₁` free
`3×4` (threshold `α<2`); the binding factor is `A₀` at `α<1`, i.e. `c'<7/2 = ½·minAdm(3,3,3,4)`. The
singular locus `{det(A₀A₀ᵀ)=0} ∪ {det(A₁A₁ᵀ)=0}` (where the `Real.rpow` convention `0^{−α}=0` makes the
majorant vanish) is a codim-≥1 determinantal null set; the genuine near-locus blow-up of `det^{−α/2}` is
what the banked `qbox_lintegral_lt_top` integrates to a finite value.

Network-free (pure matrix spectral theory + measure theory over the banked bricks). Intended axiom
footprint `[propext, Classical.choice, Quot.sound]`.
-/

namespace DLNFibre.DLN.RLCT

open Matrix MeasureTheory
open scoped BigOperators ENNReal InnerProductSpace

variable {r n : ℕ}

/-- **The transpose continuous-linear map** `y ↦ Mᵀ *ᵥ y` on Euclidean space, `Mᵀ` viewed through
`Matrix.toLpLin`. Its minimum stretch is the smallest singular value of `M`. -/
noncomputable def sigMinCLM (M : Matrix (Fin r) (Fin n) ℝ) :
    EuclideanSpace ℝ (Fin r) →L[ℝ] EuclideanSpace ℝ (Fin n) :=
  LinearMap.toContinuousLinearMap (Matrix.toLpLin 2 2 Mᵀ)

/-- **The smallest singular value** of `M`: the minimum stretch of the transpose map. -/
noncomputable def sigMin (M : Matrix (Fin r) (Fin n) ℝ) : ℝ :=
  minStretch (sigMinCLM M)

/-- `sigMinCLM M y = Mᵀ *ᵥ y` (through the `WithLp` identification). -/
theorem ofLp_sigMinCLM (M : Matrix (Fin r) (Fin n) ℝ) (y : EuclideanSpace ℝ (Fin r)) :
    WithLp.ofLp (sigMinCLM M y) = Mᵀ *ᵥ (WithLp.ofLp y) := by
  simp only [sigMinCLM, LinearMap.coe_toContinuousLinearMap']
  rw [Matrix.ofLp_toLpLin, Matrix.toLin'_apply]

/-- **The norm-square ↔ Gram quadratic-form identity** `‖Mᵀ y‖² = star y ⬝ᵥ (M Mᵀ *ᵥ y)`, the bridge
feeding `gram_rayleigh_lb` with `G = M Mᵀ`. -/
theorem norm_sq_sigMinCLM (M : Matrix (Fin r) (Fin n) ℝ) (y : EuclideanSpace ℝ (Fin r)) :
    ‖sigMinCLM M y‖ ^ 2 = star (WithLp.ofLp y) ⬝ᵥ ((M * Mᵀ) *ᵥ (WithLp.ofLp y)) := by
  set v : Fin r → ℝ := WithLp.ofLp y with hv
  rw [EuclideanSpace.norm_sq_eq]
  have hcoe : ∀ j, sigMinCLM M y j = (Mᵀ *ᵥ v) j := by
    intro j; exact congrArg (fun w => w j) (ofLp_sigMinCLM M y)
  have hsum : ∑ j, ‖sigMinCLM M y j‖ ^ 2 = (Mᵀ *ᵥ v) ⬝ᵥ (Mᵀ *ᵥ v) := by
    rw [dotProduct]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [hcoe j, Real.norm_eq_abs, sq_abs, pow_two]
  rw [hsum]
  have hstar : star v = v := by funext i; exact star_trivial _
  have e1 : (M * Mᵀ) *ᵥ v = M *ᵥ (Mᵀ *ᵥ v) := (Matrix.mulVec_mulVec v M Mᵀ).symm
  have e2 : v ⬝ᵥ (M *ᵥ (Mᵀ *ᵥ v)) = (v ᵥ* M) ⬝ᵥ (Mᵀ *ᵥ v) :=
    Matrix.dotProduct_mulVec v M (Mᵀ *ᵥ v)
  have e3 : v ᵥ* M = Mᵀ *ᵥ v := (Matrix.mulVec_transpose M v).symm
  rw [hstar, e1, e2, e3]

/-- **`M Mᵀ` is positive semidefinite** (hence Hermitian). -/
theorem posSemidef_mul_transpose (M : Matrix (Fin r) (Fin n) ℝ) : (M * Mᵀ).PosSemidef := by
  have h := Matrix.posSemidef_self_mul_conjTranspose M
  rwa [Matrix.conjTranspose_eq_transpose_of_trivial] at h

/-- The dot product `star (ofLp y) ⬝ᵥ (ofLp y)` is the squared Euclidean norm of `y`. -/
theorem dotProduct_ofLp_self (y : EuclideanSpace ℝ (Fin r)) :
    star (WithLp.ofLp y) ⬝ᵥ (WithLp.ofLp y) = ‖y‖ ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq, dotProduct]
  have hstar : star (WithLp.ofLp y) = WithLp.ofLp y := by funext i; exact star_trivial _
  rw [hstar]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [Real.norm_eq_abs, sq_abs, pow_two]

/-- **The Rayleigh bridge** `⨅ eigenvalues(M Mᵀ) ≤ sigMin M ^ 2` — the smallest eigenvalue of the Gram
matrix is at most the smallest singular value squared. One direction of `gram_rayleigh_lb` (no
eigenvector construction): take the infimum over the unit sphere of `⨅λ ≤ ‖Mᵀ y‖²`, via square roots. -/
theorem iInf_eigenvalues_le_sigMin_sq (M : Matrix (Fin r) (Fin n) ℝ) (hr : 0 < r) :
    (⨅ i, (posSemidef_mul_transpose M).isHermitian.eigenvalues i) ≤ sigMin M ^ 2 := by
  haveI : Nonempty (Fin r) := ⟨⟨0, hr⟩⟩
  haveI : Nontrivial (EuclideanSpace ℝ (Fin r)) :=
    Module.nontrivial_of_finrank_pos (R := ℝ) (by rw [finrank_euclideanSpace_fin]; exact hr)
  haveI : Nonempty (Metric.sphere (0 : EuclideanSpace ℝ (Fin r)) 1) :=
    (NormedSpace.sphere_nonempty.mpr zero_le_one).to_subtype
  set hG := posSemidef_mul_transpose M with hGdef
  set lam : ℝ := ⨅ i, hG.isHermitian.eigenvalues i with hlam
  have hlam0 : 0 ≤ lam := le_ciInf (fun i => hG.eigenvalues_nonneg i)
  -- pointwise: √lam ≤ ‖sigMinCLM M y‖ on the unit sphere
  have hsqrt : ∀ y : Metric.sphere (0 : EuclideanSpace ℝ (Fin r)) 1,
      Real.sqrt lam ≤ ‖sigMinCLM M (y : EuclideanSpace ℝ (Fin r))‖ := by
    intro y
    have hy1 : ‖(y : EuclideanSpace ℝ (Fin r))‖ = 1 := mem_sphere_zero_iff_norm.mp y.2
    have hyy : star (WithLp.ofLp (y : EuclideanSpace ℝ (Fin r))) ⬝ᵥ
        (WithLp.ofLp (y : EuclideanSpace ℝ (Fin r))) = 1 := by
      rw [dotProduct_ofLp_self, hy1, one_pow]
    have hray := gram_rayleigh_lb hG.isHermitian (WithLp.ofLp (y : EuclideanSpace ℝ (Fin r)))
    rw [hyy, mul_one, ← norm_sq_sigMinCLM] at hray
    -- hray : lam ≤ ‖sigMinCLM M y‖²
    calc Real.sqrt lam ≤ Real.sqrt (‖sigMinCLM M (y : EuclideanSpace ℝ (Fin r))‖ ^ 2) :=
          Real.sqrt_le_sqrt hray
      _ = ‖sigMinCLM M (y : EuclideanSpace ℝ (Fin r))‖ := Real.sqrt_sq (norm_nonneg _)
  have hle : Real.sqrt lam ≤ sigMin M :=
    le_ciInf (fun y => hsqrt y)
  -- square
  have hsq : lam ≤ sigMin M ^ 2 := by
    have h1 : Real.sqrt lam ^ 2 = lam := Real.sq_sqrt hlam0
    calc lam = Real.sqrt lam ^ 2 := h1.symm
      _ ≤ sigMin M ^ 2 := pow_le_pow_left₀ (Real.sqrt_nonneg _) hle 2
  exact hsq

/-- **The det ≤ σ² · trace^{r−1} bound** (always). Combines the PSD determinant bound
`posSemidef_det_le_iInf_mul_trace_pow` with the Rayleigh bridge. -/
theorem det_gram_le_sigMin_sq_mul_trace_pow (M : Matrix (Fin r) (Fin n) ℝ) (hr : 0 < r) :
    (M * Mᵀ).det ≤ sigMin M ^ 2 * (Matrix.trace (M * Mᵀ)) ^ (r - 1) := by
  set hG := posSemidef_mul_transpose M with hGdef
  have hdet := posSemidef_det_le_iInf_mul_trace_pow hG hr
  have hray := iInf_eigenvalues_le_sigMin_sq M hr
  have htr0 : 0 ≤ (Matrix.trace (M * Mᵀ)) ^ (r - 1) := by
    apply pow_nonneg
    exact hG.trace_nonneg
  calc (M * Mᵀ).det ≤ (⨅ i, hG.isHermitian.eigenvalues i) * (Matrix.trace (M * Mᵀ)) ^ (r - 1) := hdet
    _ ≤ sigMin M ^ 2 * (Matrix.trace (M * Mᵀ)) ^ (r - 1) :=
        mul_le_mul_of_nonneg_right hray htr0

/-- **The zero helper** `det(M Mᵀ) = 0 → sigMin M = 0`. If the Gram determinant vanishes, `M Mᵀ` is
singular, so some nonzero `v` has `Mᵀ v = 0`, whence the transpose map has a zero on the sphere and the
minimum stretch is `0`. -/
theorem sigMin_eq_zero_of_det_gram_eq_zero (M : Matrix (Fin r) (Fin n) ℝ)
    (hdet : (M * Mᵀ).det = 0) : sigMin M = 0 := by
  classical
  obtain ⟨v, hv0, hvz⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet
  haveI : Nonempty (Fin r) := by
    by_contra h
    rw [not_nonempty_iff] at h
    exact hv0 (Subsingleton.elim v 0)
  set y : EuclideanSpace ℝ (Fin r) := WithLp.toLp 2 v with hy
  have hofLp : WithLp.ofLp y = v := rfl
  -- `‖sigMinCLM M y‖ = 0` since `‖·‖² = star v ⬝ᵥ (M Mᵀ *ᵥ v) = star v ⬝ᵥ 0 = 0`
  have hnorm0 : ‖sigMinCLM M y‖ = 0 := by
    have h2 : ‖sigMinCLM M y‖ ^ 2 = 0 := by
      rw [norm_sq_sigMinCLM, hofLp, hvz, dotProduct_zero]
    exact (pow_eq_zero_iff two_ne_zero).mp h2
  have hnormy : (0 : ℝ) < ‖y‖ := by
    rw [norm_pos_iff]
    intro hy0
    exact hv0 (by rw [← hofLp, hy0]; rfl)
  have hmul := minStretch_mul_le (sigMinCLM M) y
  rw [hnorm0] at hmul
  have hge : 0 ≤ sigMin M := minStretch_nonneg (sigMinCLM M)
  have hle0 : sigMin M ≤ 0 := by
    by_contra hpos
    rw [not_le] at hpos
    have : 0 < sigMin M * ‖y‖ := mul_pos hpos hnormy
    simp only [sigMin] at this
    linarith
  linarith

/-- **The abstract rpow majorant** (Codex-designed): from `d ≤ s² · C` and `d = 0 → s = 0`, the
`ENNReal.ofReal` weight `s^{−a}` is bounded by `C^{a/2} · d^{−a/2}`. All the `Real.rpow`-at-zero
bookkeeping is isolated here. -/
theorem ofReal_rpow_le_det_majorant {s d C a : ℝ}
    (hs : 0 ≤ s) (hd : 0 ≤ d) (hC : 0 < C) (ha : 0 ≤ a)
    (hbound : d ≤ s ^ 2 * C) (hzero : d = 0 → s = 0) :
    ENNReal.ofReal (s ^ (-a)) ≤ ENNReal.ofReal (C ^ (a / 2)) * ENNReal.ofReal (d ^ (-a / 2)) := by
  have hreal : s ^ (-a) ≤ C ^ (a / 2) * d ^ (-a / 2) := by
    rcases eq_or_lt_of_le ha with ha0 | ha0
    · rw [← ha0]; simp [Real.rpow_zero]
    · rcases eq_or_lt_of_le hs with hs0 | hs0
      · rw [← hs0, Real.zero_rpow (by linarith : -a ≠ 0)]; positivity
      · have hdpos : 0 < d := by
          rcases eq_or_lt_of_le hd with hd0 | hd0
          · exact absurd (hzero hd0.symm) (by linarith)
          · exact hd0
        have hanti : (s ^ 2 * C) ^ (-a / 2) ≤ d ^ (-a / 2) :=
          Real.rpow_le_rpow_of_nonpos hdpos hbound (by linarith)
        have hcompute : C ^ (a / 2) * (s ^ 2 * C) ^ (-a / 2) = s ^ (-a) := by
          rw [Real.mul_rpow (by positivity) hC.le, ← Real.rpow_natCast s 2, ← Real.rpow_mul hs]
          rw [show ((2 : ℕ) : ℝ) * (-a / 2) = -a from by push_cast; ring]
          rw [show C ^ (a / 2) * (s ^ (-a) * C ^ (-a / 2))
                = s ^ (-a) * (C ^ (a / 2) * C ^ (-a / 2)) from by ring,
            ← Real.rpow_add hC, show a / 2 + (-a / 2) = 0 from by ring, Real.rpow_zero, mul_one]
        calc s ^ (-a) = C ^ (a / 2) * (s ^ 2 * C) ^ (-a / 2) := hcompute.symm
          _ ≤ C ^ (a / 2) * d ^ (-a / 2) := mul_le_mul_of_nonneg_left hanti (by positivity)
  rw [← ENNReal.ofReal_mul (by positivity)]
  exact ENNReal.ofReal_le_ofReal hreal

/-- **The determinant product identity** `det((A₀A₁)(A₀A₁)ᵀ) = det(A₀A₀ᵀ)·det(A₁A₁ᵀ)` — for the SQUARE
first factor `A₀` (the (3,3,3,4) front matrix). `(A₀A₁)(A₀A₁)ᵀ = A₀·(A₁A₁ᵀ)·A₀ᵀ`, so the determinant
factors through `det A₀ · det(A₁A₁ᵀ) · det A₀ᵀ`. -/
theorem det_product_gram {m : ℕ} (A₀ : Matrix (Fin r) (Fin r) ℝ) (A₁ : Matrix (Fin r) (Fin m) ℝ) :
    ((A₀ * A₁) * (A₀ * A₁)ᵀ).det = (A₀ * A₀ᵀ).det * (A₁ * A₁ᵀ).det := by
  have hP : (A₀ * A₁) * (A₀ * A₁)ᵀ = A₀ * (A₁ * A₁ᵀ) * A₀ᵀ := by
    rw [Matrix.transpose_mul]
    simp only [← Matrix.mul_assoc]
  rw [hP]
  simp only [Matrix.det_mul]
  ring

/-- **Singular-value submultiplicativity** `sigMin A₀ · sigMin A₁ ≤ sigMin (A₀·A₁)` (consuming the
banked `minStretch_comp_ge`): the transpose map of a product factors as a composition of transpose
maps, `(A₀A₁)ᵀ = A₁ᵀ ∘ A₀ᵀ`. -/
theorem sigMin_mul_le {m : ℕ} (A₀ : Matrix (Fin r) (Fin m) ℝ) (A₁ : Matrix (Fin m) (Fin n) ℝ)
    (hr : 0 < r) (hm : 0 < m) :
    sigMin A₀ * sigMin A₁ ≤ sigMin (A₀ * A₁) := by
  haveI : Nonempty (Fin r) := ⟨⟨0, hr⟩⟩
  haveI : Nonempty (Fin m) := ⟨⟨0, hm⟩⟩
  haveI : Nontrivial (EuclideanSpace ℝ (Fin r)) :=
    Module.nontrivial_of_finrank_pos (R := ℝ) (by rw [finrank_euclideanSpace_fin]; exact hr)
  haveI : Nontrivial (EuclideanSpace ℝ (Fin m)) :=
    Module.nontrivial_of_finrank_pos (R := ℝ) (by rw [finrank_euclideanSpace_fin]; exact hm)
  have hcomp : sigMinCLM (A₀ * A₁) = (sigMinCLM A₁).comp (sigMinCLM A₀) := by
    ext x
    simp only [sigMinCLM, ContinuousLinearMap.comp_apply, LinearMap.coe_toContinuousLinearMap']
    rw [Matrix.transpose_mul, Matrix.toLpLin_mul 2 2 2]
    rfl
  have hsub := minStretch_comp_ge (sigMinCLM A₁) (sigMinCLM A₀)
  rw [← hcomp] at hsub
  calc sigMin A₀ * sigMin A₁ = sigMin A₁ * sigMin A₀ := by rw [mul_comm]
    _ ≤ sigMin (A₀ * A₁) := hsub

/-- `sigMin` is nonnegative (needs `0 < r` for the nontrivial domain). -/
theorem sigMin_nonneg (M : Matrix (Fin r) (Fin n) ℝ) (hr : 0 < r) : 0 ≤ sigMin M := by
  haveI : Nonempty (Fin r) := ⟨⟨0, hr⟩⟩
  haveI : Nontrivial (EuclideanSpace ℝ (Fin r)) :=
    Module.nontrivial_of_finrank_pos (R := ℝ) (by rw [finrank_euclideanSpace_fin]; exact hr)
  exact minStretch_nonneg (sigMinCLM M)

/-- **The trace bound on the box** `trace(M Mᵀ) ≤ r·n·T²` for `M ∈ matBox r n T`. -/
theorem trace_gram_le_of_mem_box (M : Matrix (Fin r) (Fin n) ℝ) {T : ℝ}
    (hM : M ∈ matBox r n T) : Matrix.trace (M * Mᵀ) ≤ (r : ℝ) * n * T ^ 2 := by
  have hdiag : ∀ i, (M * Mᵀ) i i = ∑ j, M i j * M i j := by
    intro i
    rw [Matrix.mul_apply]
    exact Finset.sum_congr rfl (fun j _ => by rw [Matrix.transpose_apply])
  rw [Matrix.trace]
  simp only [Matrix.diag_apply]
  calc ∑ i, (M * Mᵀ) i i = ∑ i : Fin r, ∑ j : Fin n, M i j * M i j := by
        exact Finset.sum_congr rfl (fun i _ => hdiag i)
    _ ≤ ∑ _i : Fin r, ∑ _j : Fin n, T ^ 2 := by
        refine Finset.sum_le_sum (fun i _ => Finset.sum_le_sum (fun j _ => ?_))
        have h := hM i j
        rw [Set.mem_Icc] at h
        nlinarith [h.1, h.2]
    _ = (r : ℝ) * n * T ^ 2 := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        ring

/-- **The box comparison** `sigMin M ^ (−a) ≤ C · det(M Mᵀ)^{−a/2}` for `M ∈ matBox r n T`, with the
explicit constant `C = ((r·n·T²)^{r−1})^{a/2}`. Combines the det ≤ σ²·trace^{r−1} bound, the trace box
bound, and the abstract rpow majorant (zero handled by `sigMin_eq_zero_of_det_gram_eq_zero`). -/
theorem sigMin_rpow_le_det_rpow_of_mem_box (M : Matrix (Fin r) (Fin n) ℝ)
    (hr : 0 < r) (hn : 0 < n) {a T : ℝ} (ha : 0 ≤ a) (hT : 0 < T) (hM : M ∈ matBox r n T) :
    ENNReal.ofReal (sigMin M ^ (-a)) ≤
      ENNReal.ofReal ((((r : ℝ) * n * T ^ 2) ^ (r - 1)) ^ (a / 2)) *
        ENNReal.ofReal ((M * Mᵀ).det ^ (-a / 2)) := by
  set C₀ : ℝ := ((r : ℝ) * n * T ^ 2) ^ (r - 1) with hC₀
  have hC₀pos : 0 < C₀ := by rw [hC₀]; positivity
  have hbound : (M * Mᵀ).det ≤ sigMin M ^ 2 * C₀ := by
    have h1 := det_gram_le_sigMin_sq_mul_trace_pow M hr
    have htr0 : 0 ≤ Matrix.trace (M * Mᵀ) := (posSemidef_mul_transpose M).trace_nonneg
    have h2 : (Matrix.trace (M * Mᵀ)) ^ (r - 1) ≤ C₀ :=
      pow_le_pow_left₀ htr0 (trace_gram_le_of_mem_box M hM) (r - 1)
    calc (M * Mᵀ).det ≤ sigMin M ^ 2 * (Matrix.trace (M * Mᵀ)) ^ (r - 1) := h1
      _ ≤ sigMin M ^ 2 * C₀ := mul_le_mul_of_nonneg_left h2 (sq_nonneg _)
  exact ofReal_rpow_le_det_majorant (sigMin_nonneg M hr)
    ((posSemidef_mul_transpose M).det_nonneg) hC₀pos ha hbound
    (fun hd => sigMin_eq_zero_of_det_gram_eq_zero M hd)

/-! ## Part B — the measure bridge and per-factor determinant integral -/

/-- The measure-preserving identification of the raw matrix (row) space with the Euclidean-space row
tuple: `(Fin r → Fin n → ℝ) ≃ᵐ (Fin r → EuclideanSpace ℝ (Fin n))`. -/
noncomputable def rowsEquiv (r n : ℕ) :
    (Fin r → Fin n → ℝ) ≃ᵐ (Fin r → EuclideanSpace ℝ (Fin n)) :=
  MeasurableEquiv.arrowCongr' (Equiv.refl (Fin r)) (MeasurableEquiv.toLp 2 (Fin n → ℝ))

@[simp] theorem rowsEquiv_apply (r n : ℕ) (X : Fin r → Fin n → ℝ) (i : Fin r) :
    rowsEquiv r n X i = WithLp.toLp 2 (X i) := rfl

theorem measurePreserving_rowsEquiv (r n : ℕ) :
    MeasurePreserving (rowsEquiv r n)
      (volume : Measure (Fin r → Fin n → ℝ)) (volume : Measure (Fin r → EuclideanSpace ℝ (Fin n))) :=
  volume_preserving_arrowCongr' (Equiv.refl (Fin r)) (MeasurableEquiv.toLp 2 (Fin n → ℝ))
    (PiLp.volume_preserving_toLp (Fin n))

/-- **The Gram identity** `gram ℝ (rowsEquiv X) = X · Xᵀ` — the Euclidean Gram matrix of the rows is the
matrix `X Xᵀ`. -/
theorem gram_rowsEquiv (X : Fin r → Fin n → ℝ) :
    Matrix.gram ℝ (rowsEquiv r n X) = Matrix.of X * (Matrix.of X)ᵀ := by
  ext i j
  simp only [Matrix.gram_apply, rowsEquiv_apply, Matrix.mul_apply, Matrix.of_apply,
    Matrix.transpose_apply, WithLp.ofLp_toLp, dotProduct, Pi.star_apply, star_trivial]
  exact Finset.sum_congr rfl (fun k _ => mul_comm _ _)

/-- **The per-factor determinant integral is finite** `∫_{matBox r n 1} det(X Xᵀ)^{−a/2} < ⊤` whenever
`a < n − r + 1` (`r ≤ n`), by transport to the Euclidean row-tuple representation, enclosing the cube in
the ball of radius `n+1`, and the banked `qbox_lintegral_lt_top`. -/
theorem detGram_lintegral_lt_top {r n : ℕ} (hrn : r ≤ n) {a : ℝ}
    (haq : a < (n : ℝ) - r + 1) :
    (∫⁻ X in matBox r n 1, ENNReal.ofReal ((Matrix.of X * (Matrix.of X)ᵀ).det ^ (-a / 2)))
      < ⊤ := by
  set e := rowsEquiv r n with he
  set F : (Fin r → EuclideanSpace ℝ (Fin n)) → ℝ≥0∞ :=
    fun Q => ENNReal.ofReal ((Matrix.gram ℝ Q).det ^ (-a / 2)) with hF
  set T : Set (Fin r → EuclideanSpace ℝ (Fin n)) :=
    {Q | ∀ i j, (Q i) j ∈ Set.Icc (-(1 : ℝ)) 1} with hT
  -- the cube pulls back to `T`
  have hpre : e ⁻¹' T = matBox r n 1 := by
    ext X
    simp only [Set.mem_preimage, hT, Set.mem_setOf_eq, matBox, rowsEquiv_apply]
    rfl
  -- transport: `∫_{matBox} ofReal(det(X Xᵀ)^..) = ∫_T F`
  have hmp := measurePreserving_rowsEquiv r n
  have hCoV := hmp.setLIntegral_comp_preimage_emb e.measurableEmbedding F T
  rw [hpre] at hCoV
  have hleft : (∫⁻ X in matBox r n 1,
        ENNReal.ofReal ((Matrix.of X * (Matrix.of X)ᵀ).det ^ (-a / 2)))
      = ∫⁻ X in matBox r n 1, F (e X) := by
    refine setLIntegral_congr_fun (matBox_measurableSet r n 1) (fun X _ => ?_)
    rw [hF]; simp only; rw [gram_rowsEquiv]
  rw [hleft, hCoV]
  -- enclose `T` in the ball box and apply qbox
  have hsub : T ⊆ Set.univ.pi (fun _ : Fin r => Metric.ball (0 : EuclideanSpace ℝ (Fin n)) (n + 1)) := by
    intro Q hQ
    simp only [Set.mem_pi, Set.mem_univ, true_implies, Metric.mem_ball, dist_zero_right]
    intro i
    have hsq : ‖Q i‖ ^ 2 ≤ (n : ℝ) := by
      rw [EuclideanSpace.norm_sq_eq]
      calc ∑ j, ‖(Q i) j‖ ^ 2 ≤ ∑ _j : Fin n, (1 : ℝ) := by
            refine Finset.sum_le_sum (fun j _ => ?_)
            have h := hQ i j
            rw [Set.mem_Icc] at h
            rw [Real.norm_eq_abs, sq_abs]
            nlinarith [h.1, h.2]
        _ = (n : ℝ) := by simp
    have hnn : (0 : ℝ) ≤ ‖Q i‖ := norm_nonneg _
    nlinarith [hsq, hnn, Nat.cast_nonneg (α := ℝ) n]
  calc (∫⁻ Q in T, F Q) ≤ ∫⁻ Q in Set.univ.pi
          (fun _ : Fin r => Metric.ball (0 : EuclideanSpace ℝ (Fin n)) (n + 1)), F Q :=
        lintegral_mono_set hsub
    _ < ⊤ := qbox_lintegral_lt_top r hrn (by linarith) (n + 1)

/-- Measurability of the determinant-Gram integrand over the raw matrix space. -/
theorem measurable_detGram (r n : ℕ) (a : ℝ) :
    Measurable (fun X : Fin r → Fin n → ℝ =>
      ENNReal.ofReal ((Matrix.of X * (Matrix.of X)ᵀ).det ^ (-a / 2))) := by
  apply ENNReal.measurable_ofReal.comp
  apply Measurable.comp (g := fun t : ℝ => t ^ (-a / 2)) (by fun_prop)
  apply Continuous.measurable
  apply Continuous.matrix_det
  refine continuous_matrix (fun i j => ?_)
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.of_apply]
  fun_prop

/-- `rmatMul` is `Matrix.of`-matrix multiplication. -/
theorem rmatMul_eq_mul {p m q : ℕ} (A₀ : Fin p → Fin m → ℝ) (A₁ : Fin m → Fin q → ℝ) :
    rmatMul A₀ A₁ = Matrix.of A₀ * Matrix.of A₁ := rfl

/-- A product of two entries-≤-1 matrices has entries in `[−m, m]` (`m` the contracted dimension). -/
theorem rmatMul_mem_matBox {p m q : ℕ} {A₀ : Fin p → Fin m → ℝ} {A₁ : Fin m → Fin q → ℝ}
    (h0 : A₀ ∈ matBox p m 1) (h1 : A₁ ∈ matBox m q 1) : rmatMul A₀ A₁ ∈ matBox p q (m : ℝ) := by
  intro i j
  rw [Set.mem_Icc]
  have habs : |rmatMul A₀ A₁ i j| ≤ (m : ℝ) := by
    calc |rmatMul A₀ A₁ i j| = |∑ k, A₀ i k * A₁ k j| := rfl
      _ ≤ ∑ k, |A₀ i k * A₁ k j| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _k : Fin m, (1 : ℝ) := by
          refine Finset.sum_le_sum (fun k _ => ?_)
          rw [abs_mul]
          have hk0 := h0 i k; have hk1 := h1 k j
          rw [Set.mem_Icc] at hk0 hk1
          have ha0 : |A₀ i k| ≤ 1 := abs_le.mpr hk0
          have ha1 : |A₁ k j| ≤ 1 := abs_le.mpr hk1
          nlinarith [abs_nonneg (A₀ i k), abs_nonneg (A₁ k j)]
      _ = (m : ℝ) := by simp
  exact abs_le.mp habs

/-- **LAYER-2 headline (product-box form).** The σ-min majorant `sigMin(A₀·A₁)^{−α}` is integrable over
the product box `matBox 3 3 1 ×ˢ matBox 3 4 1` for every `0 ≤ α < 1` — the binding threshold
`α < 1 = q − b + 1` of the square `3×3` first factor. Route: the box comparison bounds the majorant by
`C · det((A₀A₁)(A₀A₁)ᵀ)^{−α/2}`; the determinant factorises (`det_product_gram`, `A₀` square) into the
two per-factor Gram determinants, and Tonelli splits the product-box integral into the two per-factor
integrals, each finite by `detGram_lintegral_lt_top`. -/
theorem sjProductTube_lintegral_lt_top {a : ℝ} (ha0 : 0 ≤ a) (ha1 : a < 1) :
    (∫⁻ p in matBox 3 3 1 ×ˢ matBox 3 4 1,
      ENNReal.ofReal (sigMin (rmatMul p.1 p.2) ^ (-a))) < ⊤ := by
  set Cbox : ℝ := ((((3 : ℕ) : ℝ) * ((4 : ℕ) : ℝ) * (((3 : ℕ) : ℝ)) ^ 2) ^ (3 - 1)) ^ (a / 2)
    with hCbox
  -- pointwise majorant on the product box
  have hpt : ∀ p ∈ matBox 3 3 1 ×ˢ matBox 3 4 1,
      ENNReal.ofReal (sigMin (rmatMul p.1 p.2) ^ (-a)) ≤
        ENNReal.ofReal Cbox *
          (ENNReal.ofReal ((Matrix.of p.1 * (Matrix.of p.1)ᵀ).det ^ (-a / 2)) *
            ENNReal.ofReal ((Matrix.of p.2 * (Matrix.of p.2)ᵀ).det ^ (-a / 2))) := by
    rintro ⟨A₀, A₁⟩ hp
    simp only [Set.mem_prod] at hp
    obtain ⟨h0, h1⟩ := hp
    have hP : rmatMul A₀ A₁ ∈ matBox 3 4 ((3 : ℕ) : ℝ) := by
      have := rmatMul_mem_matBox h0 h1
      simpa using this
    -- box comparison at M = rmatMul A₀ A₁ (r = 3, n = 4, T = 3)
    have hbc := sigMin_rpow_le_det_rpow_of_mem_box (rmatMul A₀ A₁) (by norm_num) (by norm_num)
      ha0 (by norm_num : (0 : ℝ) < ((3 : ℕ) : ℝ)) hP
    -- rewrite `rmatMul` to `of A₀ * of A₁` and factor the Gram determinant (`det_product_gram`)
    rw [rmatMul_eq_mul, det_product_gram (Matrix.of A₀) (Matrix.of A₁)] at hbc
    -- split the ofReal of the product of determinants
    have hd0 : (0 : ℝ) ≤ (Matrix.of A₀ * (Matrix.of A₀)ᵀ).det :=
      (posSemidef_mul_transpose _).det_nonneg
    have hd1 : (0 : ℝ) ≤ (Matrix.of A₁ * (Matrix.of A₁)ᵀ).det :=
      (posSemidef_mul_transpose _).det_nonneg
    have hsplit : ((Matrix.of A₀ * (Matrix.of A₀)ᵀ).det * (Matrix.of A₁ * (Matrix.of A₁)ᵀ).det)
          ^ (-a / 2)
        = (Matrix.of A₀ * (Matrix.of A₀)ᵀ).det ^ (-a / 2)
            * (Matrix.of A₁ * (Matrix.of A₁)ᵀ).det ^ (-a / 2) :=
      Real.mul_rpow hd0 hd1
    rw [hsplit, ENNReal.ofReal_mul (Real.rpow_nonneg hd0 _)] at hbc
    rw [rmatMul_eq_mul]
    exact hbc
  -- integrate the majorant
  have hmeas0 := measurable_detGram 3 3 a
  have hmeas1 := measurable_detGram 3 4 a
  have hprodmeas : Measurable (fun p : (Fin 3 → Fin 3 → ℝ) × (Fin 3 → Fin 4 → ℝ) =>
      ENNReal.ofReal ((Matrix.of p.1 * (Matrix.of p.1)ᵀ).det ^ (-a / 2)) *
        ENNReal.ofReal ((Matrix.of p.2 * (Matrix.of p.2)ᵀ).det ^ (-a / 2))) :=
    (hmeas0.comp measurable_fst).mul (hmeas1.comp measurable_snd)
  calc ∫⁻ p in matBox 3 3 1 ×ˢ matBox 3 4 1,
          ENNReal.ofReal (sigMin (rmatMul p.1 p.2) ^ (-a))
      ≤ ∫⁻ p in matBox 3 3 1 ×ˢ matBox 3 4 1, ENNReal.ofReal Cbox *
          (ENNReal.ofReal ((Matrix.of p.1 * (Matrix.of p.1)ᵀ).det ^ (-a / 2)) *
            ENNReal.ofReal ((Matrix.of p.2 * (Matrix.of p.2)ᵀ).det ^ (-a / 2))) := by
        refine lintegral_mono_ae (ae_restrict_of_forall_mem
          ((matBox_measurableSet 3 3 1).prod (matBox_measurableSet 3 4 1)) ?_)
        intro p hp; exact hpt p hp
    _ = ENNReal.ofReal Cbox * ∫⁻ p in matBox 3 3 1 ×ˢ matBox 3 4 1,
          (ENNReal.ofReal ((Matrix.of p.1 * (Matrix.of p.1)ᵀ).det ^ (-a / 2)) *
            ENNReal.ofReal ((Matrix.of p.2 * (Matrix.of p.2)ᵀ).det ^ (-a / 2))) :=
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ < ⊤ := by
        refine ENNReal.mul_lt_top ENNReal.ofReal_lt_top ?_
        rw [Measure.volume_eq_prod (Fin 3 → Fin 3 → ℝ) (Fin 3 → Fin 4 → ℝ),
          setLIntegral_prod _ hprodmeas.aemeasurable]
        have hinner : ∀ A₀ : Fin 3 → Fin 3 → ℝ,
            (∫⁻ A₁ in matBox 3 4 1,
              ENNReal.ofReal ((Matrix.of A₀ * (Matrix.of A₀)ᵀ).det ^ (-a / 2)) *
                ENNReal.ofReal ((Matrix.of A₁ * (Matrix.of A₁)ᵀ).det ^ (-a / 2)))
            = ENNReal.ofReal ((Matrix.of A₀ * (Matrix.of A₀)ᵀ).det ^ (-a / 2)) *
                (∫⁻ A₁ in matBox 3 4 1,
                  ENNReal.ofReal ((Matrix.of A₁ * (Matrix.of A₁)ᵀ).det ^ (-a / 2))) :=
          fun A₀ => lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
        simp_rw [hinner]
        rw [lintegral_mul_const' _ _
          (detGram_lintegral_lt_top (by norm_num) (by push_cast; linarith : a < (4:ℝ) - 3 + 1)).ne]
        exact ENNReal.mul_lt_top
          (detGram_lintegral_lt_top (by norm_num) (by push_cast; linarith : a < (3:ℝ) - 3 + 1))
          (detGram_lintegral_lt_top (by norm_num) (by push_cast; linarith : a < (4:ℝ) - 3 + 1))

/-- **LAYER-2 headline (Params-box form).** The σ-min majorant of the two-layer product
`rmatMul (A 0) (A 1)` is integrable over the `Params (![3,3,4])` box, for every `0 ≤ α < 1`. Reshapes
the parameter box to the two per-layer matrix boxes via the banked `eParamsRR4` measure-preserving
equiv, then `sjProductTube_lintegral_lt_top`. The layer product equals `prod (![3,3,4]) A` — the
deeper-strata majorant — via the banked `prod_two_layer_rr4`. -/
theorem sjProductTube_params_lintegral_lt_top {a : ℝ} (ha0 : 0 ≤ a) (ha1 : a < 1) :
    (∫⁻ A in paramsBoxM (![3, 3, 4] : Fin 3 → ℕ) 1,
      ENNReal.ofReal (sigMin (rmatMul (A 0) (A 1)) ^ (-a))) < ⊤ := by
  have hpre := (measurePreserving_eParamsRR4 3).setLIntegral_comp_preimage_emb
    (MeasurableEquiv.measurableEmbedding (eParamsRR4 3))
    (fun p : (Fin 3 → Fin 3 → ℝ) × (Fin 3 → Fin 4 → ℝ) =>
      ENNReal.ofReal (sigMin (rmatMul p.1 p.2) ^ (-a)))
    (matBox 3 3 1 ×ˢ matBox 3 4 1)
  rw [eParamsRR4_preimage_box] at hpre
  have hstep : (∫⁻ A in paramsBoxM (![3, 3, 4] : Fin 3 → ℕ) 1,
        ENNReal.ofReal (sigMin (rmatMul (A 0) (A 1)) ^ (-a)))
      = ∫⁻ p in matBox 3 3 1 ×ˢ matBox 3 4 1,
          ENNReal.ofReal (sigMin (rmatMul p.1 p.2) ^ (-a)) := hpre
  rw [hstep]
  exact sjProductTube_lintegral_lt_top ha0 ha1

end DLNFibre.DLN.RLCT
