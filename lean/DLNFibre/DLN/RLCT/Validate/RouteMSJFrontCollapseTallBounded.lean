import DLNFibre.DLN.RLCT.Validate.RouteMSJFrontCollapseWide
import DLNFibre.DLN.RLCT.Validate.RouteMSJFrontCollapseTall
import Mathlib.Analysis.Matrix.Order

set_option linter.style.longLine false

/-!
# `DLNFibre.DLN.RLCT.Validate.RouteMSJFrontCollapseTallBounded` — the `b=0` TALL BOUNDED arm

**Thread `genm-b0bdd` (Lane-1 front-collapse, the `b=0` tall wing, bounded regime).** The mirror of
the LANDED wide bounded arm `frontCollapse_wide_bounded_lt_top` (`RouteMSJFrontCollapseWide`) for a
TALL front (`M₁ ≤ M₀`, full COLUMN rank `M₁`) in the bounded density regime (`M₂ < M₀ − M₁ + 1`,
i.e. `M₂ ≤ s = M₀ − M₁`): GIVEN the plain one-shorter strong IH `hIH`, below the geometric threshold
(`c' < ½·minAdm M`), the front-factor box integral over `wingFrontBox M × paramsBoxM(tailChain M)`
is finite.

## Route (cleaner than a column-complement — no `exists_ortho_complement_cols`)

`frobSq (F · X)` reads only the column Gram `Fᵀ·F` (`= ∑_j (Y_{·j})ᵀ (FᵀF) (Y_{·j})`), so it is
INVARIANT under replacing the tall `F` by the SQUARE SPD root `P = CFC.sqrt(FᵀF)` (`M₁×M₁`,
`PᵀP = FᵀF`, `det P² = det(FᵀF)`). This is `frobSq_rmatMul_eq_of_gramEq`. The fixed-`F` bound
(`fixedF_tall_cov_bound`) then runs a plain SQUARE left-multiplication change of variables
`A₁ ↦ P·A₁` (`lintegral_comp_rmatMulLeft`, banked from `RouteMSJFrontCoV`), whose Jacobian is
`det(FᵀF)^{−M₂/2}`, and whose `[−1,1]`-box image sits in a fixed radius box (entry bound via
`frobSq P = frobSq F ≤ M₀·M₁`). The residual `M₁×M₂` box integral is the reduced-chain box (finite
via the IH, `redChain M₁ M` = `redChain (min M₀ M₁) M`), scaled to the larger radius by the
`(−2c')`-homogeneity of the deep-tail integrand. The free-`F` density factor is closed by the banked
tall Gram brick `front_gram_qbox_tall_lt_top`.

Axiom target `[propext, Classical.choice, Quot.sound]` (CFC.sqrt is classical, sorry-free).
-/

namespace DLNFibre.DLN.RLCT

open MeasureTheory
open scoped ENNReal BigOperators Matrix MatrixOrder ComplexOrder

variable {L : ℕ}

/-! ## The Gram-invariance of the matrix-product loss -/

/-- **The matrix-product loss as a column-Gram quadratic form.** `frobSq (W·Y)` reads `W` only
through the column Gram `Wᵀ·W`: `frobSq (rmatMul W Y) = ∑_j ∑_k ∑_l (WᵀW)_{kl}·Y_{kj}·Y_{lj}`. -/
theorem frobSq_rmatMul_gram_sum {a r c : ℕ} (W : Fin a → Fin r → ℝ) (Y : Fin r → Fin c → ℝ) :
    frobSq (rmatMul W Y)
      = ∑ j, ∑ k, ∑ l, ((Matrix.of W)ᵀ * Matrix.of W) k l * (Y k j * Y l j) := by
  classical
  have hrhs : ∀ k l : Fin r, ((Matrix.of W)ᵀ * Matrix.of W) k l = ∑ i, W i k * W i l := by
    intro k l
    simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.of_apply]
  simp_rw [hrhs]
  unfold frobSq rmatMul
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp_rw [sq, Finset.sum_mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun l _ => ?_
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

/-- **The matrix-product loss depends only on the column Gram.** Two pre-factors `W`, `W'` (possibly
different row counts) with equal column Grams `Wᵀ·W = W'ᵀ·W'` give the same product loss. -/
theorem frobSq_rmatMul_eq_of_gramEq {a b r c : ℕ}
    (W : Fin a → Fin r → ℝ) (W' : Fin b → Fin r → ℝ) (Y : Fin r → Fin c → ℝ)
    (hG : (Matrix.of W)ᵀ * Matrix.of W = (Matrix.of W')ᵀ * Matrix.of W') :
    frobSq (rmatMul W Y) = frobSq (rmatMul W' Y) := by
  rw [frobSq_rmatMul_gram_sum W Y, frobSq_rmatMul_gram_sum W' Y, hG]

/-! ## The fixed-`F` tall change-of-variables bound -/

/-- **The fixed-`F` tall two-matrix CoV bound (SQUARE-root route, NO column-complement).** For a
fixed tall full-column-rank front `F : M₀×M₁` (`M₁ ≤ M₀`, entries in `[−1,1]`, column Gram
`Fᵀ·F` nonsingular), and integrands `g` (reading `M₀×M₂`) / `ĝ` (reading `M₁×M₂`) that agree on
column-Gram-equal arguments (`hgg`), the box integral over the free tail `A₁` of `g(F·A₁)` is
bounded by the free-`F` Gram Jacobian `det(FᵀF)^{−M₂/2}` times the residual radius-`R` box integral
of `ĝ`. The change of variables `A₁ ↦ P·A₁` (`P = CFC.sqrt(FᵀF)`, `M₁×M₁` SPD, `det P² = det(FᵀF)`)
is invertible; `g(F·A₁) = ĝ(P·A₁)` (`hgg`, Gram-equal), and `‖P‖`-entries are bounded
(`frobSq P = frobSq F ≤ M₀·M₁`) so the image stays in the radius-`R` box. -/
theorem fixedF_tall_cov_bound {M₀ M₁ M₂ : ℕ} (hmn : M₁ ≤ M₀)
    (F : Fin M₀ → Fin M₁ → ℝ) (hFbox : ∀ i j, F i j ∈ Set.Icc (-1 : ℝ) 1)
    (hFdet : ((Matrix.of F)ᵀ * (Matrix.of F)).det ≠ 0)
    (g : (Fin M₀ → Fin M₂ → ℝ) → ℝ≥0∞)
    (ĝ : (Fin M₁ → Fin M₂ → ℝ) → ℝ≥0∞) (hĝ : Measurable ĝ)
    (hgg : ∀ (V : Fin M₀ → Fin M₂ → ℝ) (V' : Fin M₁ → Fin M₂ → ℝ),
       (Matrix.of V)ᵀ * Matrix.of V = (Matrix.of V')ᵀ * Matrix.of V' → g V = ĝ V') :
    ∫⁻ A₁ in matBox M₁ M₂ 1, g (rmatMul F A₁)
      ≤ ENNReal.ofReal (((Matrix.of F)ᵀ * (Matrix.of F)).det ^ (-(M₂ : ℝ) / 2))
        * ∫⁻ V in matBox M₁ M₂ (((M₁ : ℝ) + 1) * ((M₀ : ℝ) * M₁ + 1)), ĝ V := by
  classical
  set R : ℝ := ((M₁ : ℝ) + 1) * ((M₀ : ℝ) * M₁ + 1) with hRdef
  have hRpos : 0 < R := by rw [hRdef]; positivity
  -- The column Gram and its SPD square root.
  set A : Matrix (Fin M₁) (Fin M₁) ℝ := (Matrix.of F)ᵀ * (Matrix.of F) with hAdef
  have hApsd : A.PosSemidef := by
    rw [hAdef]; simpa using Matrix.posSemidef_conjTranspose_mul_self (Matrix.of F)
  have hAnn : (0 : Matrix (Fin M₁) (Fin M₁) ℝ) ≤ A := hApsd.nonneg
  set P : Matrix (Fin M₁) (Fin M₁) ℝ := CFC.sqrt A with hPdef
  have hPP : P * P = A := by rw [hPdef]; exact CFC.sqrt_mul_sqrt_self A hAnn
  have hPpsd : P.PosSemidef := (Matrix.nonneg_iff_posSemidef).mp (hPdef ▸ CFC.sqrt_nonneg A)
  have hPherm : Pᵀ = P := by
    have h := hPpsd.isHermitian
    simpa [Matrix.IsHermitian, Matrix.conjTranspose] using h
  have hPtP : Pᵀ * P = A := by rw [hPherm, hPP]
  -- `det P² = det A`, hence `det P ≠ 0` and the Jacobian rpow identity.
  have hPsq : (P.det) ^ 2 = A.det := by rw [sq, ← Matrix.det_mul, hPP]
  have hPdet : P.det ≠ 0 := by
    have hpm : P.det * P.det = A.det := by rw [← pow_two, hPsq]
    intro h
    rw [h, zero_mul] at hpm
    exact hFdet hpm.symm
  have hAnonneg : (0 : ℝ) ≤ A.det := hApsd.det_nonneg
  have hrpow : (A.det) ^ (-(M₂ : ℝ) / 2) = (|P.det| ^ M₂)⁻¹ := by
    rw [← hPsq, ← sq_abs P.det, ← Real.rpow_natCast (|P.det|) 2,
      ← Real.rpow_mul (abs_nonneg _),
      show ((2 : ℕ) : ℝ) * (-(M₂ : ℝ) / 2) = -(M₂ : ℝ) by push_cast; ring,
      Real.rpow_neg (abs_nonneg _), Real.rpow_natCast]
  -- Entry bound on `P` via `frobSq P = frobSq F ≤ M₀·M₁`.
  have hfrobP : frobSq P ≤ (M₀ : ℝ) * M₁ := by
    have h1 : frobSq P = ((Matrix.of F) * (Matrix.of F)ᵀ).trace := by
      rw [frobSq_eq_trace, hPherm, hPP, hAdef, Matrix.trace_mul_comm]
    rw [h1, ← frobSq_eq_trace]
    unfold frobSq
    calc ∑ i, ∑ j, ((Matrix.of F) i j) ^ 2
        ≤ ∑ _i : Fin M₀, ∑ _j : Fin M₁, (1 : ℝ) := by
          refine Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => ?_
          simp only [Matrix.of_apply]
          have hb := hFbox i j
          nlinarith [hb.1, hb.2]
      _ = (M₀ : ℝ) * M₁ := by
          simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
  have hPentry : ∀ k l : Fin M₁, |P k l| ≤ (M₀ : ℝ) * M₁ + 1 := by
    intro k l
    have hle : (P k l) ^ 2 ≤ frobSq P := by
      unfold frobSq
      calc (P k l) ^ 2 ≤ ∑ l', (P k l') ^ 2 :=
            Finset.single_le_sum (fun l' _ => sq_nonneg _) (Finset.mem_univ l)
        _ ≤ ∑ k', ∑ l', (P k' l') ^ 2 :=
            Finset.single_le_sum (fun k' _ => Finset.sum_nonneg fun l' _ => sq_nonneg _)
              (Finset.mem_univ k)
    have hsq : (P k l) ^ 2 ≤ (M₀ : ℝ) * M₁ := hle.trans hfrobP
    nlinarith [sq_abs (P k l), abs_nonneg (P k l), hsq, sq_nonneg (|P k l| - 1),
      mul_nonneg (Nat.cast_nonneg M₀ : (0:ℝ) ≤ M₀) (Nat.cast_nonneg M₁ : (0:ℝ) ≤ M₁)]
  -- The image box membership: `A₁ ∈ box(1) ⟹ P·A₁ ∈ box(R)`.
  have himg : ∀ A₁ ∈ matBox M₁ M₂ 1, rmatMul P A₁ ∈ matBox M₁ M₂ R := by
    intro A₁ hA₁ i j
    rw [Set.mem_Icc, ← abs_le]
    calc |rmatMul P A₁ i j| = |∑ k, P i k * A₁ k j| := rfl
      _ ≤ ∑ k, |P i k * A₁ k j| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _k : Fin M₁, ((M₀ : ℝ) * M₁ + 1) * 1 := by
          refine Finset.sum_le_sum fun k _ => ?_
          rw [abs_mul]
          exact mul_le_mul (hPentry i k) (abs_le.mpr ⟨(hA₁ k j).1, (hA₁ k j).2⟩)
            (abs_nonneg _) (by positivity)
      _ = (M₁ : ℝ) * ((M₀ : ℝ) * M₁ + 1) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; ring
      _ ≤ R := by
          rw [hRdef]
          have h0 : (0 : ℝ) ≤ (M₀ : ℝ) * M₁ + 1 := by positivity
          nlinarith [h0, Nat.cast_nonneg M₁ (α := ℝ)]
  -- The indicator of the residual box.
  set φ : (Fin M₁ → Fin M₂ → ℝ) → ℝ≥0∞ := (matBox M₁ M₂ R).indicator ĝ with hφ
  have hφmeas : Measurable φ := by
    rw [hφ]; exact hĝ.indicator (matBox_measurableSet M₁ M₂ R)
  -- The chain: Gram-bridge, then the square CoV.
  calc ∫⁻ A₁ in matBox M₁ M₂ 1, g (rmatMul F A₁)
      = ∫⁻ A₁ in matBox M₁ M₂ 1, φ (rmatMul P A₁) := by
        refine setLIntegral_congr_fun (matBox_measurableSet M₁ M₂ 1) fun A₁ hA₁ => ?_
        have hbridge : g (rmatMul F A₁) = ĝ (rmatMul P A₁) := by
          refine hgg _ _ ?_
          rw [of_rmatMul, of_rmatMul, Matrix.transpose_mul, Matrix.transpose_mul]
          simp only [Matrix.mul_assoc]
          congr 1
          rw [← Matrix.mul_assoc, ← Matrix.mul_assoc]
          congr 1
          rw [← hAdef]
          exact hPtP.symm
        rw [hbridge, hφ, Set.indicator_of_mem (himg A₁ hA₁)]
    _ ≤ ∫⁻ A₁ : Fin M₁ → Fin M₂ → ℝ, φ (rmatMul P A₁) := by
        conv_rhs => rw [← setLIntegral_univ]
        exact lintegral_mono_set (Set.subset_univ _)
    _ = ENNReal.ofReal (|P.det| ^ M₂)⁻¹ * ∫⁻ B, φ B :=
        lintegral_comp_rmatMulLeft P hPdet φ hφmeas
    _ = ENNReal.ofReal (|P.det| ^ M₂)⁻¹ * ∫⁻ V in matBox M₁ M₂ R, ĝ V := by
        rw [hφ, lintegral_indicator (matBox_measurableSet M₁ M₂ R)]
    _ = ENNReal.ofReal (((Matrix.of F)ᵀ * (Matrix.of F)).det ^ (-(M₂ : ℝ) / 2))
          * ∫⁻ V in matBox M₁ M₂ R, ĝ V := by rw [hAdef.symm, hrpow]

/-! ## The `b=0` tall bounded arm -/

/-- **The `b=0` TALL BOUNDED arm of the front-collapse atom.** For a tall front (`M₁ ≤ M₀`) in the
bounded density regime (`M₂ < M₀ − M₁ + 1`), GIVEN the plain one-shorter strong IH `hIH`, below the
geometric threshold (`c' < ½·minAdm M`), the front-factor box integral over
`wingFrontBox M × paramsBoxM(tailChain M)` is finite. Mirror of the wide arm
`frontCollapse_wide_bounded_lt_top`. -/
theorem frontCollapse_tall_bounded_lt_top (M : Fin (L + 1 + 1 + 1) → ℕ)
    (htall : M 1 ≤ M 0) (hbnd : (M 2 : ℝ) < (M 0 : ℝ) - M 1 + 1)
    (hIH : ∀ M' : Fin (L + 1 + 1) → ℕ, RouteMBoxThresholdFinite M')
    (c' : NNReal) (hc' : (c' : ℝ) < (minAdm M : ℝ) / 2) :
    (∫⁻ F in wingFrontBox M, ∫⁻ A' in paramsBoxM (tailChain M) 1,
        ENNReal.ofReal ((frobSq (rmatMul F (prod (tailChain M) A'))) ^ (-(c' : ℝ)))) < ⊤ := by
  classical
  -- the deep chain `D = (M₂, M₃, …, M_last)` and the two deep-tail fibre integrands (M₀×M₂ / M₁×M₂).
  set D : Fin (L + 1) → ℕ := Mtail (tailChain M) with hDdef
  set g : (Fin (M 0) → Fin (M 2) → ℝ) → ℝ≥0∞ := fun W =>
      ∫⁻ A'' in paramsBoxM D 1,
        ENNReal.ofReal ((frobSq (rmatMul W (prod D A''))) ^ (-(c' : ℝ))) with hgdef
  set ĝ : (Fin (M 1) → Fin (M 2) → ℝ) → ℝ≥0∞ := fun V =>
      ∫⁻ A'' in paramsBoxM D 1,
        ENNReal.ofReal ((frobSq (rmatMul V (prod D A''))) ^ (-(c' : ℝ))) with hĝdef
  set R : ℝ := ((M 1 : ℝ) + 1) * ((M 0 : ℝ) * (M 1) + 1) with hRdef
  -- (hĝ) measurability of the reduced deep-tail integrand (parametric lintegral, Tonelli).
  have hĝ : Measurable ĝ := by
    have hcont : Continuous (fun p : (Fin (M 1) → Fin (M 2) → ℝ) × Params D =>
        frobSq (rmatMul p.1 (prod D p.2))) := by
      have hP : Continuous (fun p : (Fin (M 1) → Fin (M 2) → ℝ) × Params D => prod D p.2) :=
        (continuous_prod D).comp continuous_snd
      have hR : Continuous (fun p : (Fin (M 1) → Fin (M 2) → ℝ) × Params D =>
          rmatMul p.1 (prod D p.2)) := by
        unfold rmatMul
        refine continuous_pi (fun i => continuous_pi (fun j => ?_))
        refine continuous_finset_sum _ (fun k _ => Continuous.mul ?_ (hP.matrix_elem k j))
        exact (continuous_apply k).comp ((continuous_apply i).comp continuous_fst)
      unfold frobSq
      exact continuous_finset_sum _ (fun i _ => continuous_finset_sum _
        (fun j _ => (hR.matrix_elem i j).pow 2))
    have hf : Measurable (fun p : (Fin (M 1) → Fin (M 2) → ℝ) × Params D =>
        ENNReal.ofReal ((frobSq (rmatMul p.1 (prod D p.2))) ^ (-(c' : ℝ)))) :=
      ENNReal.measurable_ofReal.comp
        (Measurable.comp (g := fun t : ℝ => t ^ (-(c' : ℝ))) (by fun_prop) hcont.measurable)
    rw [hĝdef]
    exact hf.lintegral_prod_right'
  -- (hgg) `g` and `ĝ` agree on column-Gram-equal arguments (via `frobSq_rmatMul_eq_of_gramEq`).
  have hgg : ∀ (V : Fin (M 0) → Fin (M 2) → ℝ) (V' : Fin (M 1) → Fin (M 2) → ℝ),
      (Matrix.of V)ᵀ * Matrix.of V = (Matrix.of V')ᵀ * Matrix.of V' → g V = ĝ V' := by
    intro V V' hVeq
    simp only [hgdef, hĝdef]
    refine lintegral_congr fun A'' => ?_
    rw [frobSq_rmatMul_eq_of_gramEq V V' (prod D A'') hVeq]
  -- (hsplit) the fixed-`F` fibre split (front-peel `A₁ = A' 0` + Tonelli); generic in the wing.
  have hsplit : ∀ F : Fin (M 0) → Fin (M 1) → ℝ,
      (∫⁻ A' in paramsBoxM (tailChain M) 1,
        ENNReal.ofReal ((frobSq (rmatMul F (prod (tailChain M) A'))) ^ (-(c' : ℝ))))
      = ∫⁻ A₁ in matBox (M 1) (M 2) 1, g (rmatMul F A₁) := by
    intro F
    refine (frontFactor_split (tailChain M) F (c' : ℝ)).trans ?_
    rw [hgdef]
    rfl
  -- (hK1) the residual radius-1 box IS the reduced-chain box (front width `M₁`), finite via the IH.
  have hK1eq : (∫⁻ V in matBox (M 1) (M 2) 1, ĝ V)
      = routeMLayerBoxIntegral (redChain (M 1) M) (c' : ℝ) 1 := by
    have key := frontFactor_split (redChain (M 1) M)
      (1 : Matrix (Fin (redChain (M 1) M 0)) (Fin (redChain (M 1) M 0)) ℝ) (c' : ℝ)
    simp only [rmatMul_one_left] at key
    rw [routeMLayerBoxIntegral, hĝdef]
    exact key.symm
  have hK1 : (∫⁻ V in matBox (M 1) (M 2) 1, ĝ V) < ⊤ := by
    rw [hK1eq]
    have hred := redChain_box_lt_top M hIH c' hc'
    rwa [min_eq_right htall] at hred
  -- (hKfin) the residual radius-`R` box is finite (scaling of the radius-1 box, `R > 0`).
  have hRpos : 0 < R := by rw [hRdef]; positivity
  have hKfin : (∫⁻ V in matBox (M 1) (M 2) R, ĝ V) < ⊤ := by
    set G : Matrix (Fin (M 1)) (Fin (M 1)) ℝ := R • 1 with hGdef
    have hGdet : G.det ≠ 0 := by
      rw [hGdef, Matrix.det_smul, Matrix.det_one, mul_one]
      exact pow_ne_zero _ (ne_of_gt hRpos)
    have hGmul : ∀ A : Fin (M 1) → Fin (M 2) → ℝ,
        (fun i j => ∑ k, G i k * A k j) = R • A := by
      intro A; funext i j
      have h1 : ∑ k, (1 : Matrix (Fin (M 1)) (Fin (M 1)) ℝ) i k * A k j = A i j :=
        congrFun (congrFun (rmatMul_one_left A) i) j
      calc ∑ k, G i k * A k j
          = ∑ k, R * ((1 : Matrix (Fin (M 1)) (Fin (M 1)) ℝ) i k * A k j) := by
            refine Finset.sum_congr rfl (fun k _ => ?_)
            rw [hGdef]; simp only [Matrix.smul_apply, smul_eq_mul]; ring
        _ = R * ∑ k, (1 : Matrix (Fin (M 1)) (Fin (M 1)) ℝ) i k * A k j :=
            (Finset.mul_sum _ _ _).symm
        _ = R * A i j := by rw [h1]
        _ = (R • A) i j := by simp [Pi.smul_apply]
    have hhom : ∀ A : Fin (M 1) → Fin (M 2) → ℝ,
        ĝ (R • A) = ENNReal.ofReal ((R ^ 2) ^ (-(c' : ℝ))) * ĝ A := by
      intro A
      simp only [hĝdef]
      rw [← lintegral_const_mul' (ENNReal.ofReal ((R ^ 2) ^ (-(c' : ℝ)))) _ ENNReal.ofReal_ne_top]
      refine lintegral_congr fun A'' => ?_
      rw [frobSq_rmatMul_smul R A (prod D A''), Real.mul_rpow (by positivity) (frobSq_nonneg _),
        ENNReal.ofReal_mul (by positivity)]
    have hmem : ∀ A : Fin (M 1) → Fin (M 2) → ℝ,
        ((R • A) ∈ matBox (M 1) (M 2) R) ↔ (A ∈ matBox (M 1) (M 2) 1) := by
      intro A
      simp only [matBox, Set.mem_setOf_eq, Pi.smul_apply, smul_eq_mul, Set.mem_Icc]
      constructor
      · intro h i k; obtain ⟨h1, h2⟩ := h i k; constructor <;> nlinarith [hRpos]
      · intro h i k; obtain ⟨h1, h2⟩ := h i k; constructor <;> nlinarith [hRpos]
    have hcov := lintegral_comp_rmatMulLeft G hGdet ((matBox (M 1) (M 2) R).indicator ĝ)
      (hĝ.indicator (matBox_measurableSet (M 1) (M 2) R))
    simp only [hGmul] at hcov
    have hRi : (∫⁻ B, (matBox (M 1) (M 2) R).indicator ĝ B)
        = ∫⁻ V in matBox (M 1) (M 2) R, ĝ V :=
      lintegral_indicator (matBox_measurableSet (M 1) (M 2) R) ĝ
    have hL : (∫⁻ A, (matBox (M 1) (M 2) R).indicator ĝ (R • A))
        = ENNReal.ofReal ((R ^ 2) ^ (-(c' : ℝ))) * ∫⁻ V in matBox (M 1) (M 2) 1, ĝ V := by
      have hpt : ∀ A : Fin (M 1) → Fin (M 2) → ℝ,
          (matBox (M 1) (M 2) R).indicator ĝ (R • A)
            = (matBox (M 1) (M 2) 1).indicator
                (fun A => ENNReal.ofReal ((R ^ 2) ^ (-(c' : ℝ))) * ĝ A) A := by
        intro A
        by_cases hA : A ∈ matBox (M 1) (M 2) 1
        · rw [Set.indicator_of_mem ((hmem A).mpr hA), Set.indicator_of_mem hA, hhom A]
        · rw [Set.indicator_of_notMem (fun hc => hA ((hmem A).mp hc)),
            Set.indicator_of_notMem hA]
      simp only [hpt]
      rw [lintegral_indicator (matBox_measurableSet (M 1) (M 2) 1),
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    have hcancel : ENNReal.ofReal (|G.det| ^ (M 2))
        * ENNReal.ofReal ((|G.det| ^ (M 2))⁻¹) = 1 := by
      rw [← ENNReal.ofReal_mul (by positivity),
        mul_inv_cancel₀ (pow_ne_zero _ (abs_ne_zero.mpr hGdet)), ENNReal.ofReal_one]
    have hKval : (∫⁻ B, (matBox (M 1) (M 2) R).indicator ĝ B)
        = ENNReal.ofReal (|G.det| ^ (M 2))
          * (∫⁻ A, (matBox (M 1) (M 2) R).indicator ĝ (R • A)) := by
      rw [hcov, ← mul_assoc, hcancel, one_mul]
    rw [← hRi, hKval, hL]
    exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top
      (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hK1)
  -- (hdet) the tall column Gram is nonsingular on `wingFrontBox` (columns lin. indep.).
  have hdet : ∀ F ∈ wingFrontBox M, ((Matrix.of F)ᵀ * (Matrix.of F)).det ≠ 0 := by
    intro F hF
    set colF : Fin (M 1) → EuclideanSpace ℝ (Fin (M 0)) :=
      fun j => WithLp.toLp 2 (fun i => F i j) with hcolF
    have hgram : Matrix.gram ℝ colF = (Matrix.of F)ᵀ * (Matrix.of F) := by
      ext i j
      simp only [hcolF, Matrix.gram_apply, PiLp.inner_apply, Matrix.mul_apply,
        Matrix.transpose_apply, Matrix.of_apply]
      exact Finset.sum_congr rfl fun k _ => mul_comm _ _
    have hli : LinearIndependent ℝ colF := by
      rw [Fintype.linearIndependent_iff]
      intro c hc
      have hcoord : ∀ i : Fin (M 0), ∑ j, c j * F i j = 0 := by
        intro i
        have h0 : (∑ j, c j • colF j) i = (0 : EuclideanSpace ℝ (Fin (M 0))) i := by rw [hc]
        simpa [hcolF, Finset.sum_apply, Pi.smul_apply, smul_eq_mul] using h0
      set e : Fin (M 1) ≃ Fin (min (M 0) (M 1)) := (finCongr (min_eq_right htall)).symm with he
      have hBunit : IsUnit ((leadingBlock M F).submatrix e e) :=
        (Matrix.isUnit_submatrix_equiv e e).mpr hF.2
      have hcast : ∀ j : Fin (M 1), Fin.castLE (min_le_right (M 0) (M 1)) (e j) = j := by
        intro j
        apply Fin.ext
        rw [Fin.val_castLE, he, finCongr_symm_apply_coe]
      have hcb : ((leadingBlock M F).submatrix e e) *ᵥ c = 0 := by
        funext a
        have hj := hcoord (Fin.castLE (min_le_left (M 0) (M 1)) (e a))
        simp only [Matrix.mulVec, dotProduct, Matrix.submatrix_apply, leadingBlock,
          Matrix.of_apply, Pi.zero_apply]
        rw [← hj]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [hcast j, mul_comm]
      have hc0 : c = 0 :=
        (Matrix.mulVec_injective_iff_isUnit.mpr hBunit) (hcb.trans (Matrix.mulVec_zero _).symm)
      exact fun j => congrFun hc0 j
    have hpd : (Matrix.gram ℝ colF).PosDef := Matrix.posDef_gram_iff_linearIndependent.mpr hli
    rw [← hgram]
    exact isUnit_iff_ne_zero.mp ((Matrix.isUnit_iff_isUnit_det _).mp
      ((Matrix.posSemidef_gram ℝ colF).posDef_iff_isUnit.mp hpd))
  -- (hDetMeas) measurability of the free-`F` column-Gram density factor.
  have hdetcont : Continuous
      (fun F : Fin (M 0) → Fin (M 1) → ℝ => ((Matrix.of F)ᵀ * (Matrix.of F)).det) := by
    refine Continuous.matrix_det ?_
    exact continuous_matrix (fun i j => by
      simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.of_apply]
      fun_prop)
  have hrpowm : Measurable (fun t : ℝ => t ^ (-(M 2 : ℝ) / 2)) := by fun_prop
  have hDetMeas : Measurable
      (fun F : Fin (M 0) → Fin (M 1) → ℝ =>
        ENNReal.ofReal (((Matrix.of F)ᵀ * (Matrix.of F)).det ^ (-(M 2 : ℝ) / 2))) :=
    ENNReal.measurable_ofReal.comp (hrpowm.comp hdetcont.measurable)
  -- assemble: pointwise `fixedF_tall_cov_bound`, monotone over `F`, then the two finite factors.
  have hmono : (∫⁻ F in wingFrontBox M, ∫⁻ A' in paramsBoxM (tailChain M) 1,
        ENNReal.ofReal ((frobSq (rmatMul F (prod (tailChain M) A'))) ^ (-(c' : ℝ))))
      ≤ (∫⁻ V in matBox (M 1) (M 2) R, ĝ V) * ∫⁻ F in matBox (M 0) (M 1) 1,
          ENNReal.ofReal (((Matrix.of F)ᵀ * (Matrix.of F)).det ^ (-(M 2 : ℝ) / 2)) := by
    calc (∫⁻ F in wingFrontBox M, ∫⁻ A' in paramsBoxM (tailChain M) 1,
            ENNReal.ofReal ((frobSq (rmatMul F (prod (tailChain M) A'))) ^ (-(c' : ℝ))))
        = ∫⁻ F in wingFrontBox M, ∫⁻ A₁ in matBox (M 1) (M 2) 1, g (rmatMul F A₁) := by
          refine setLIntegral_congr_fun (measurableSet_wingFrontBox M) (fun F _ => ?_)
          exact hsplit F
      _ ≤ ∫⁻ F in wingFrontBox M,
            ENNReal.ofReal (((Matrix.of F)ᵀ * (Matrix.of F)).det ^ (-(M 2 : ℝ) / 2))
              * ∫⁻ V in matBox (M 1) (M 2) R, ĝ V := by
          refine setLIntegral_mono (hDetMeas.mul measurable_const) ?_
          intro F hF
          exact fixedF_tall_cov_bound htall F hF.1 (hdet F hF) g ĝ hĝ hgg
      _ = (∫⁻ V in matBox (M 1) (M 2) R, ĝ V) * ∫⁻ F in wingFrontBox M,
            ENNReal.ofReal (((Matrix.of F)ᵀ * (Matrix.of F)).det ^ (-(M 2 : ℝ) / 2)) := by
          rw [← lintegral_const_mul' (∫⁻ V in matBox (M 1) (M 2) R, ĝ V) _ hKfin.ne]
          refine lintegral_congr fun F => ?_
          rw [mul_comm]
      _ ≤ (∫⁻ V in matBox (M 1) (M 2) R, ĝ V) * ∫⁻ F in matBox (M 0) (M 1) 1,
            ENNReal.ofReal (((Matrix.of F)ᵀ * (Matrix.of F)).det ^ (-(M 2 : ℝ) / 2)) := by
          exact mul_le_mul' (le_refl _) (lintegral_mono_set (fun F hF => hF.1))
  refine lt_of_le_of_lt hmono ?_
  exact ENNReal.mul_lt_top hKfin (front_gram_qbox_tall_lt_top (M 2) htall hbnd)

end DLNFibre.DLN.RLCT
