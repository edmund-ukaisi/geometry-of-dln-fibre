import DLNFibre.DLN.RLCT.Validate.RouteMSJOffSectorB1
import DLNFibre.DLN.RLCT.Validate.RouteMSJCorankSurvival
import DLNFibre.DLN.RLCT.Validate.RouteMSJUnitsBridge
import DLNFibre.DLN.RLCT.Validate.RouteMSJGramSqrt
import DLNFibre.DLN.RLCT.Validate.RouteMSJGammaAtom

set_option linter.style.longLine false

/-!
# `DLNFibre.DLN.RLCT.Validate.RouteMSJOffSectorBPos` — the `b>1` corank-integrability lemma (Obl-2, convergent regime)

**Thread `genm-sj5-domination` off-sector, Obligation 2 (convergent regime).** The `b>1` generalisation
of Obl-1 (`corankOffSector_b1_le`), for a general corank block of `b` rows. For the corank-block integral
(freed inner `Γ`-integral over any finite-measure domain `sΓ`, integrated over the free corank block
`A_cor ∈ matBox b M₂ 1`), on the full-rank tail chart (`Z.rank = M₂`), in the CONVERGENT regime
`a < M₂ − b + 1`:

    ∫_{A_cor} [ ∫_{Γ∈sΓ} (w + frobSq (Ccross + Γ·(A_cor·Z)))^{−c'} ] dA_cor  ≤  C₁ · w^{−(c'−ab/2)}.

## The design (`offsector-il-design-cert.md` §2b; decorrelated-Codex-re-derived, `codex/obl2-scoping-answer.md`)

The design cert's "`σ_min`-only splitting UNDERSHOOTS for `b>1`" is a criticism of using the *smallest
singular value* `τ_min²` as the weight; the correct object is the FULL Gram determinant
`det(Q_bQ_bᵀ) = ∏_k τ_k²`, which retains the anisotropy. With that weight the `b>1` case closes with a
SINGLE atom bound at the level-0 flag charge — no multi-level flag — because:

* **The atom applies a.e.** For a.e. `A_cor` the corank block `Q_b = A_cor·Z` has full row rank `b`
  (`corank_survival_ae`, `Z.rank = M₂ ≥ b`), so `Q_bQ_bᵀ` is PosDef (`posDef_gram_of_rank_eq`) and the
  banked atom (`corankBlock_morsePeel_setLE`, `Apiv := 0`) gives the pointwise bound
  `det(Q_bQ_bᵀ)^{−a/2}·Cresid(ab)·w^{−(c'−ab/2)}` (the core `≥ w`, exponent `< 0`). The rank-drop locus
  `{rank < b}` is Lebesgue-null and contributes `0` (any nonneg integrand integrates to `0` on a null set).
* **The corank weight is finite.** `Wenn := ∫_{matBox b M₂ 1} det(Q_bQ_bᵀ)^{−a/2} < ⊤` in the convergent
  regime `a < M₂ − b + 1` (`corankWeight_bpos_lt_top`), by normalising the Gram `ZZᵀ = L Lᵀ`
  (`exists_gram_normalizer`), a linear change of variables `A ↦ A·L` (`lintegral_comp_rightMulₚ`), and the
  banked box-clipped determinant integral (`detGram_lintegral_box_lt_top`, `r = b ≤ M₂`).

The charge `ab = peelCharge` is the design's level-0 FREED contribution (NOT `C₀ = ab + minAdm(redChain) =
minAdm(M)`); fed to the level-0 reduced IH it needs `c' − ab/2 < ½·minAdm(redChain@t)`, i.e.
`c' < ½·minAdm(M) = carrierThreshold(M)` — the exact threshold.

## Scope (the caveats live here — `codex/obl2-scoping-answer.md` Q5)

* **Convergent regime only.** `a < M₂ − b + 1` (strict). At every genuine (`a ≥ 1`) `b>1` binding cut
  `a ≤ M₂ − b + 1` holds (convexity `R_{t+1}−R_t ≥ a+b−1` + incidence `R_{t+1}−R_t ≤ M₂`); the equality
  BORDERLINE `a = M₂ − b + 1` (the `(3,3,3)@t=1` case) carries a log divergence of `Wenn` and is a tracked
  follow-up (mirroring b=1's `a = M₂`), reachable by a θ-interpolation of the atom/bounded bricks, NOT built
  here.
* **Fixed full-rank tail.** `Z.rank = M₂` is fixed; the tail-collapse region (where `Z` itself degenerates,
  the coercivity constant becoming non-uniform) is a DEEPER flag level — Obl-3's uniform adapted-chart job,
  NOT this lemma.

S2-FREE: the banked corank atom + Gram normaliser + CoV + box-clipped determinant integral + polynomial
null set (`corank_survival_ae`); no `monomial_rlct`. Intended axiom footprint
`[propext, Classical.choice, Quot.sound]`.
-/

namespace DLNFibre.DLN.RLCT

open Matrix MeasureTheory
open scoped BigOperators ENNReal

/-! ## The box-clipped determinant integral at general side length `T` -/

/-- **The per-factor determinant integral is finite on the box of side `T`.**
`∫_{matBox r n T} det(X Xᵀ)^{−a/2} < ⊤` whenever `a < n − r + 1` (`r ≤ n`), for any `T`. The `T = 1`
version is `detGram_lintegral_lt_top`; the proof is identical (transport to the Euclidean row-tuple, enclose
the `T`-cube's rows in a ball of radius `n·T² + 1`, banked `qbox_lintegral_lt_top`). -/
theorem detGram_lintegral_box_lt_top {r n : ℕ} (hrn : r ≤ n) {a : ℝ}
    (haq : a < (n : ℝ) - r + 1) (T : ℝ) :
    (∫⁻ X in matBox r n T, ENNReal.ofReal ((Matrix.of X * (Matrix.of X)ᵀ).det ^ (-a / 2)))
      < ⊤ := by
  set e := rowsEquiv r n with he
  set F : (Fin r → EuclideanSpace ℝ (Fin n)) → ℝ≥0∞ :=
    fun Q => ENNReal.ofReal ((Matrix.gram ℝ Q).det ^ (-a / 2)) with hF
  set S : Set (Fin r → EuclideanSpace ℝ (Fin n)) :=
    {Q | ∀ i j, (Q i) j ∈ Set.Icc (-T) T} with hS
  have hpre : e ⁻¹' S = matBox r n T := by
    ext X
    simp only [Set.mem_preimage, hS, Set.mem_setOf_eq, matBox]
    rfl
  have hmp := measurePreserving_rowsEquiv r n
  have hCoV := hmp.setLIntegral_comp_preimage_emb e.measurableEmbedding F S
  rw [hpre] at hCoV
  have hleft : (∫⁻ X in matBox r n T,
        ENNReal.ofReal ((Matrix.of X * (Matrix.of X)ᵀ).det ^ (-a / 2)))
      = ∫⁻ X in matBox r n T, F (e X) := by
    refine setLIntegral_congr_fun (matBox_measurableSet r n T) (fun X _ => ?_)
    rw [hF]; simp only; rw [gram_rowsEquiv]
  rw [hleft, hCoV]
  set R : ℝ := (n : ℝ) * T ^ 2 + 1 with hR
  have hsub : S ⊆ Set.univ.pi (fun _ : Fin r => Metric.ball (0 : EuclideanSpace ℝ (Fin n)) R) := by
    intro Q hQ
    simp only [Set.mem_pi, Set.mem_univ, true_implies, Metric.mem_ball, dist_zero_right]
    intro i
    have hsq : ‖Q i‖ ^ 2 ≤ (n : ℝ) * T ^ 2 := by
      rw [EuclideanSpace.norm_sq_eq]
      calc ∑ j, ‖(Q i) j‖ ^ 2 ≤ ∑ _j : Fin n, T ^ 2 := by
            refine Finset.sum_le_sum (fun j _ => ?_)
            have h := hQ i j
            rw [Set.mem_Icc] at h
            rw [Real.norm_eq_abs, sq_abs]
            nlinarith [h.1, h.2]
        _ = (n : ℝ) * T ^ 2 := by simp
    have hnn : (0 : ℝ) ≤ ‖Q i‖ := norm_nonneg _
    nlinarith [hsq, hnn, sq_nonneg (‖Q i‖ - 1)]
  calc (∫⁻ Q in S, F Q) ≤ ∫⁻ Q in Set.univ.pi
          (fun _ : Fin r => Metric.ball (0 : EuclideanSpace ℝ (Fin n)) R), F Q :=
        lintegral_mono_set hsub
    _ < ⊤ := qbox_lintegral_lt_top r hrn (by linarith) R

/-! ## The `b>1` corank weight is finite (convergent regime) -/

/-- **The `b>1` corank weight is finite (box-clipped, convergent regime).** For a full-rank tail
`Z.rank = M₂` (so `ZZᵀ` PosDef), `b ≤ M₂`, and the strict convergent bound `a < M₂ − b + 1`, the corank
weight `∫_{matBox b M₂ 1} det((A·Z)(A·Z)ᵀ)^{−a/2}` is finite. Normalise `ZZᵀ = L Lᵀ`
(`exists_gram_normalizer`, `L = (ZZᵀ)^{1/2}`), change variables `A ↦ A·L` (`lintegral_comp_rightMulₚ`,
Jacobian `(det L)^{-b}`) so `det((A·Z)(A·Z)ᵀ) = det((A·L)(A·L)ᵀ)`, enclose the transformed box in
`matBox b M₂ T`, and apply `detGram_lintegral_box_lt_top`. -/
theorem corankWeight_bpos_lt_top {a b M₂ n : ℕ} (Z : Matrix (Fin M₂) (Fin n) ℝ)
    (hbM : b ≤ M₂) (haM : (a : ℝ) < (M₂ : ℝ) - b + 1) (hZrank : Z.rank = M₂) :
    ∫⁻ A in matBox b M₂ 1,
      ENNReal.ofReal (((Matrix.of A * Z) * (Matrix.of A * Z)ᵀ).det ^ (-(a : ℝ) / 2)) < ⊤ := by
  classical
  -- `G = ZZᵀ` PosDef; its normaliser `Mn = G^{−1/2}`, `L = Mn⁻¹ = G^{1/2}`.
  have hG : (Z * Zᵀ).PosDef := posDef_gram_of_rank_eq Z hZrank
  obtain ⟨Mn, hMsymm, hMGM, hMdet, _hMabs⟩ := exists_gram_normalizer (Z * Zᵀ) hG
  have hMunit : IsUnit Mn.det := (isUnit_iff_ne_zero).mpr hMdet
  set L : Matrix (Fin M₂) (Fin M₂) ℝ := Mn⁻¹ with hLdef
  have hLdet : L.det ≠ 0 := by
    rw [hLdef, Matrix.det_nonsing_inv, Ring.inverse_eq_inv]; exact inv_ne_zero hMdet
  have hLsymm : Lᵀ = L := by rw [hLdef, Matrix.transpose_nonsing_inv, hMsymm]
  have hMGM' : Mn * (Z * Zᵀ) * Mn = 1 := by rw [hMsymm] at hMGM; exact hMGM
  -- `L Lᵀ = ZZᵀ`
  have hLLT : L * Lᵀ = Z * Zᵀ := by
    rw [hLsymm, hLdef]
    symm
    calc Z * Zᵀ
        = Mn⁻¹ * Mn * (Z * Zᵀ) * (Mn * Mn⁻¹) := by
            rw [Matrix.nonsing_inv_mul Mn hMunit, Matrix.mul_nonsing_inv Mn hMunit,
              Matrix.one_mul, Matrix.mul_one]
      _ = Mn⁻¹ * (Mn * (Z * Zᵀ) * Mn) * Mn⁻¹ := by simp only [Matrix.mul_assoc]
      _ = Mn⁻¹ * 1 * Mn⁻¹ := by rw [hMGM']
      _ = Mn⁻¹ * Mn⁻¹ := by rw [Matrix.mul_one]
  -- the transported integrand `f`
  set f : (Fin b → Fin M₂ → ℝ) → ℝ≥0∞ :=
    fun Y => ENNReal.ofReal ((Matrix.of Y * (Matrix.of Y)ᵀ).det ^ (-(a : ℝ) / 2)) with hfdef
  have hfmeas : Measurable f := measurable_detGram b M₂ (a : ℝ)
  -- `Matrix.of (fun i ↦ A i ᵥ* L) = Matrix.of A * L`
  have hof : ∀ A : Fin b → Fin M₂ → ℝ, (Matrix.of (fun i => A i ᵥ* L)) = Matrix.of A * L := by
    intro A; ext i j
    simp only [Matrix.of_apply, Matrix.mul_apply, Matrix.vecMul, dotProduct]
  -- the Gram equality `(A·L)(A·L)ᵀ = (A·Z)(A·Z)ᵀ`
  have hGeq : ∀ A : Fin b → Fin M₂ → ℝ,
      (Matrix.of A * L) * (Matrix.of A * L)ᵀ = (Matrix.of A * Z) * (Matrix.of A * Z)ᵀ := by
    intro A
    have lhs : (Matrix.of A * L) * (Matrix.of A * L)ᵀ
        = Matrix.of A * (L * Lᵀ) * (Matrix.of A)ᵀ := by
      rw [Matrix.transpose_mul]; simp only [Matrix.mul_assoc]
    have rhs : (Matrix.of A * Z) * (Matrix.of A * Z)ᵀ
        = Matrix.of A * (Z * Zᵀ) * (Matrix.of A)ᵀ := by
      rw [Matrix.transpose_mul]; simp only [Matrix.mul_assoc]
    rw [lhs, rhs, hLLT]
  -- the integrand rewrite `weight A = f (fun i ↦ A i ᵥ* L)`
  have hint : ∀ A : Fin b → Fin M₂ → ℝ,
      ENNReal.ofReal (((Matrix.of A * Z) * (Matrix.of A * Z)ᵀ).det ^ (-(a : ℝ) / 2))
        = f (fun i => A i ᵥ* L) := by
    intro A
    rw [hfdef]; simp only [hof A, hGeq A]
  -- the transformed box `s = preimage of matBox under `· ᵥ* Mn``
  set s : Set (Fin b → Fin M₂ → ℝ) := {Γ | (fun i => Γ i ᵥ* Mn) ∈ matBox b M₂ 1} with hsdef
  have hmapmeas : Measurable (fun Γ : Fin b → Fin M₂ → ℝ => (fun i => Γ i ᵥ* Mn)) := by
    refine measurable_pi_lambda _ (fun i => measurable_pi_lambda _ (fun j => ?_))
    simp only [Matrix.vecMul, dotProduct]
    exact Finset.measurable_sum _ (fun k _ =>
      (((measurable_pi_apply k).comp (measurable_pi_apply i)).mul measurable_const))
  have hsmeas : MeasurableSet s := hmapmeas (matBox_measurableSet b M₂ 1)
  -- membership: `(fun i ↦ A i ᵥ* L) ∈ s ↔ A ∈ matBox`
  have hfun : ∀ A : Fin b → Fin M₂ → ℝ, (fun i => (A i ᵥ* L) ᵥ* Mn) = A := by
    intro A; funext i
    rw [Matrix.vecMul_vecMul, hLdef, Matrix.nonsing_inv_mul Mn hMunit, Matrix.vecMul_one]
  have hmem : ∀ A : Fin b → Fin M₂ → ℝ, (fun i => A i ᵥ* L) ∈ s ↔ A ∈ matBox b M₂ 1 := by
    intro A
    simp only [hsdef, Set.mem_setOf_eq, hfun A]
  -- enclose `s ⊆ matBox b M₂ T`, `T = ∑ₖⱼ |L k j|`
  set T : ℝ := ∑ k : Fin M₂, ∑ j : Fin M₂, |L k j| with hTdef
  have hsub : s ⊆ matBox b M₂ T := by
    intro Γ hΓ
    simp only [hsdef, Set.mem_setOf_eq, matBox, Set.mem_setOf_eq] at hΓ ⊢
    intro i j
    rw [Set.mem_Icc]
    have hΓrec : (Γ i ᵥ* Mn) ᵥ* L = Γ i := by
      rw [Matrix.vecMul_vecMul, hLdef, Matrix.mul_nonsing_inv Mn hMunit, Matrix.vecMul_one]
    have hentry : Γ i j = ∑ k, (Γ i ᵥ* Mn) k * L k j := by
      conv_lhs => rw [← hΓrec]
      simp only [Matrix.vecMul, dotProduct]
    have habs : |Γ i j| ≤ T := by
      rw [hentry]
      calc |∑ k, (Γ i ᵥ* Mn) k * L k j|
          ≤ ∑ k, |(Γ i ᵥ* Mn) k * L k j| := Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ k, |L k j| := by
            refine Finset.sum_le_sum (fun k _ => ?_)
            rw [abs_mul]
            have hmb := hΓ i k
            rw [Set.mem_Icc] at hmb
            have h1 : |(Γ i ᵥ* Mn) k| ≤ 1 := abs_le.mpr hmb
            nlinarith [abs_nonneg (L k j), h1]
        _ ≤ T := by
            rw [hTdef]
            exact Finset.sum_le_sum (fun k _ =>
              Finset.single_le_sum (f := fun j' => |L k j'|)
                (fun j' _ => abs_nonneg _) (Finset.mem_univ j))
    exact abs_le.mp habs
  -- assemble: rewrite integrand, indicator-CoV, box enclosure
  rw [show (∫⁻ A in matBox b M₂ 1,
        ENNReal.ofReal (((Matrix.of A * Z) * (Matrix.of A * Z)ᵀ).det ^ (-(a : ℝ) / 2)))
      = ∫⁻ A in matBox b M₂ 1, f (fun i => A i ᵥ* L) from lintegral_congr (fun A => hint A)]
  rw [← lintegral_indicator (matBox_measurableSet b M₂ 1)]
  rw [show (∫⁻ A, (matBox b M₂ 1).indicator (fun A => f (fun i => A i ᵥ* L)) A)
      = ∫⁻ A, (s.indicator f) (fun i => A i ᵥ* L) from lintegral_congr (fun A => by
        by_cases hA : A ∈ matBox b M₂ 1
        · rw [Set.indicator_of_mem hA, Set.indicator_of_mem ((hmem A).mpr hA)]
        · rw [Set.indicator_of_notMem hA,
            Set.indicator_of_notMem (fun h => hA ((hmem A).mp h))])]
  rw [lintegral_comp_rightMulₚ b L hLdet (s.indicator f) (hfmeas.indicator hsmeas),
    lintegral_indicator hsmeas]
  refine ENNReal.mul_lt_top ENNReal.ofReal_lt_top ?_
  calc ∫⁻ A in s, f A ≤ ∫⁻ A in matBox b M₂ T, f A := lintegral_mono_set hsub
    _ < ⊤ := detGram_lintegral_box_lt_top hbM haM T

/-! ## The main lemma — the `b>1` corank-integrability bound (convergent regime) -/

/-- **Obl-2 (convergent regime): the `b>1` corank-integrability bound.** For a corank block of `b` rows,
a fixed pivot energy `w > 0`, cross-shift `Ccross`, the deeper product `Z` on the full-rank tail chart
(`Z.rank = M₂`, `b ≤ M₂`), the convergent regime `a < M₂ − b + 1`, and `c'` above the block Morse
threshold `ab/2`, the corank-block integral (freed inner `Γ`-integral over any finite-measure domain `sΓ`,
integrated over the free corank block `A_cor ∈ matBox b M₂ 1`) is bounded by a finite, `w`-independent
constant times the shifted power of `w`:

    ∫_{A_cor} [ ∫_{Γ∈sΓ} (w + frobSq (Ccross + Γ·(A_cor·Z)))^{−c'} ] dA_cor  ≤  C₁ · w^{−(c'−ab/2)}.

For a.e. `A_cor` the block is full row rank (`corank_survival_ae`), so the atom applies pointwise
(`corankBlock_morsePeel_setLE`, `Apiv := 0`), dropping the core to `w^{−(c'−ab/2)}`; the rank-drop locus
is null; the corank weight is finite (`corankWeight_bpos_lt_top`). -/
theorem corankOffSector_bpos_le {a b M₂ n : ℕ} (Z : Matrix (Fin M₂) (Fin n) ℝ)
    (Ccross : Matrix (Fin a) (Fin n) ℝ) (w c' : ℝ)
    (hw : 0 < w) (hbM : b ≤ M₂) (haM : (a : ℝ) < (M₂ : ℝ) - b + 1)
    (hZrank : Z.rank = M₂) (hc' : (a * b : ℝ) / 2 < c')
    (sΓ : Set (Fin a → Fin b → ℝ)) :
    ∃ C₁ : ℝ≥0∞, C₁ < ⊤ ∧
      ∫⁻ A_cor in matBox b M₂ 1,
          ∫⁻ Γ in sΓ, ENNReal.ofReal
            ((w + frobSq (Ccross + (Matrix.of Γ) * (Matrix.of A_cor * Z))) ^ (-c'))
        ≤ C₁ * ENNReal.ofReal (w ^ (-(c' - (a * b : ℝ) / 2))) := by
  classical
  -- the inner freed-corner integral, as a function of the corank block `A_cor`
  set F : (Fin b → Fin M₂ → ℝ) → ℝ≥0∞ := fun A =>
    ∫⁻ Γ in sΓ, ENNReal.ofReal
      ((w + frobSq (Ccross + (Matrix.of Γ) * (Matrix.of A * Z))) ^ (-c')) with hFdef
  -- the finite corank weight (box-clipped, convergent regime)
  set Wenn : ℝ≥0∞ := ∫⁻ A in matBox b M₂ 1,
      ENNReal.ofReal (((Matrix.of A * Z) * (Matrix.of A * Z)ᵀ).det ^ (-(a : ℝ) / 2)) with hWdef
  have hWfin : Wenn < ⊤ := corankWeight_bpos_lt_top Z hbM haM hZrank
  refine ⟨ENNReal.ofReal (Cresid (a * b) c') * Wenn,
    ENNReal.mul_lt_top ENNReal.ofReal_lt_top hWfin, ?_⟩
  have hmeasbox : MeasurableSet (matBox b M₂ 1) := matBox_measurableSet b M₂ 1
  have hbZ : b ≤ Z.rank := by rw [hZrank]; exact hbM
  -- pointwise atom bound on the full-row-rank set (the a.e. set)
  have hfz : frobSq (0 : Matrix (Fin 0) (Fin n) ℝ) = 0 := by simp [frobSq]
  have hcorepow : ∀ X : Matrix (Fin a) (Fin n) ℝ,
      (w + frobSq (0 : Matrix (Fin 0) (Fin n) ℝ) + frobSq X) ^ (-(c' - (a * b : ℝ) / 2))
        ≤ w ^ (-(c' - (a * b : ℝ) / 2)) := fun X =>
    Real.rpow_le_rpow_of_nonpos hw
      (by rw [hfz, add_zero]; exact le_add_of_nonneg_right (frobSq_nonneg _))
      (by linarith [hc'])
  have hpt : ∀ A : Fin b → Fin M₂ → ℝ, (Matrix.of A * Z).rank = b →
      F A ≤ ENNReal.ofReal (Cresid (a * b) c' * w ^ (-(c' - (a * b : ℝ) / 2)))
              * ENNReal.ofReal (((Matrix.of A * Z) * (Matrix.of A * Z)ᵀ).det ^ (-(a : ℝ) / 2)) := by
    intro A hrank
    have hPD := posDef_gram_of_rank_eq (Matrix.of A * Z) hrank
    have hatom := corankBlock_morsePeel_setLE (Apiv := (0 : Matrix (Fin 0) (Fin n) ℝ))
      (Ccross := Ccross) (Qb := Matrix.of A * Z) hPD c' hc' w hw sΓ
    have hFeq : F A = ∫⁻ Γ in sΓ, ENNReal.ofReal
        ((w + frobSq (0 : Matrix (Fin 0) (Fin n) ℝ)
          + frobSq (Ccross + (Matrix.of Γ) * (Matrix.of A * Z))) ^ (-c')) := by
      simp only [hFdef]
      exact lintegral_congr (fun Γ => by rw [hfz, add_zero])
    rw [hFeq]
    refine le_trans hatom ?_
    rw [← ENNReal.ofReal_mul
      (mul_nonneg (Cresid_nonneg (a * b) c') (Real.rpow_nonneg hw.le _))]
    refine ENNReal.ofReal_le_ofReal ?_
    rw [show Cresid (a * b) c' * w ^ (-(c' - (a * b : ℝ) / 2))
          * ((Matrix.of A * Z) * (Matrix.of A * Z)ᵀ).det ^ (-(a : ℝ) / 2)
        = ((Matrix.of A * Z) * (Matrix.of A * Z)ᵀ).det ^ (-(a : ℝ) / 2)
            * Cresid (a * b) c' * w ^ (-(c' - (a * b : ℝ) / 2)) from by ring]
    exact mul_le_mul_of_nonneg_left (hcorepow _)
      (mul_nonneg (Real.rpow_nonneg (posSemidef_mul_transpose _).det_nonneg _)
        (Cresid_nonneg (a * b) c'))
  -- integrate the a.e. bound, pull out the constant, box-clip the weight
  calc ∫⁻ A in matBox b M₂ 1, F A
      ≤ ∫⁻ A in matBox b M₂ 1,
          ENNReal.ofReal (Cresid (a * b) c' * w ^ (-(c' - (a * b : ℝ) / 2)))
            * ENNReal.ofReal (((Matrix.of A * Z) * (Matrix.of A * Z)ᵀ).det ^ (-(a : ℝ) / 2)) := by
        refine lintegral_mono_ae ((ae_restrict_iff' hmeasbox).mpr ?_)
        filter_upwards [corank_survival_ae Z hbZ] with A hrank _hAbox
        exact hpt A hrank
    _ = ENNReal.ofReal (Cresid (a * b) c' * w ^ (-(c' - (a * b : ℝ) / 2))) * Wenn :=
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ = ENNReal.ofReal (Cresid (a * b) c') * Wenn
          * ENNReal.ofReal (w ^ (-(c' - (a * b : ℝ) / 2))) := by
        rw [ENNReal.ofReal_mul (Cresid_nonneg (a * b) c')]; ring

end DLNFibre.DLN.RLCT
