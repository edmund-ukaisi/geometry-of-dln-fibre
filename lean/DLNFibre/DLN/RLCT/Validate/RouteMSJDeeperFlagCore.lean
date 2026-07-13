import DLNFibre.DLN.RLCT.Validate.RouteMSJStrongBlock
import DLNFibre.DLN.RLCT.Validate.RouteMSJCornerComparator
import DLNFibre.DLN.RLCT.Validate.RouteMSJShellCharge
import DLNFibre.DLN.RLCT.Validate.RouteMSJResolution
import DLNFibre.DLN.RLCT.Validate.RouteMSJChartShear

set_option linter.style.longLine false

/-!
# `RouteMSJDeeperFlagCore` — L1 (off-sector core → comparator) + the headline `deeperFlag_shell_le`

**Thread `genm-inj-injon` (aoyagi-full Stage 2), T-Obl3b OWED-3, the CORRECTED deeper-cut route.** The
controller's L1-first ladder (de-risk gate STEP 1 → STEP 2). This module lands, sorry-free, the
reachable analytic content of the mountain and STATES the headline reduced to the single genuinely-new
seam **S1** (the head-split spine→core CoV, isolated as ONE correct-statement `sorry`).

## What lands here (the analytic labour, sorry-free)

* **`strongBlock_lintegral_le_unif`** (S3) — the reduced strong-block weight is bounded by a
  `U_s`-UNIFORM finite constant: the orthogonal extension `U` of `U_s` has entries `≤ 1`, so the rotated
  box sits inside the fixed box `matBox b' M₂ (M₂²)`, and the right-mult CoV Jacobian `|det U| = 1`.
  Strengthens `strongBlock_lintegral_lt_top` from `< ⊤` to a uniform `≤ C_strong_unif`.
* **`shellCorankWeight_le_unif`** (S3) — the shell corank weight `∫ det((A·Z)(A·Z)ᵀ)^{−a/2}` is bounded
  by `ε^{−ab}·C_strong_unif`, a constant INDEPENDENT of `Z` (given the shell PSD hypothesis).
* **`shell_corankOffSector_le_unif`** (S3) — `shell_corankOffSector_le` with the `Z`-uniform constant:
  `∀ w > 0, ∫_{A_cor}∫_Γ (w + frobSq(Ccross + Γ·(A_cor·Z)))^{−c'} ≤ Cunif · w^{−(c'−ab/2)}`, `Cunif` free
  of `Z`, `Ccross`, `w`.
* **`deeperFlag_shell_core_le`** (L1) — the per-shell domination at the off-sector-core level: the core
  integrand integrated over the reduced params `z ∈ paramsBoxM (redChain u M) 1` and exceptional
  coordinates `v ∈ unitBox d`, with the pivot energy `w = commonDivisor(v)²·frobSq(prod (redChain u M) z)`
  (S4, definitional), is bounded by `Cunif · (cornerComparator (redChain u M) k jc).integral (c' −
  ½·peelCharge M u)`. Consumes `shell_corankOffSector_le_unif` + `cornerComparator_decLoss`.

## The single isolated seam (S1, a correct-statement `sorry`)

* **`deeperFlag_spineToCore`** — the head-split spine→core reduction: the literal cut-`u`/shell-`S_j`
  freed-Γ triple (the `RouteMSJDecoratedPeelStep.innerCorankDescent` shape) is bounded by L1's core
  integrand. This is the ~65–75%-genuinely-new decorated-peel head-split CoV that `RouteMSJDecorated`
  flagged (Tonelli-factor `∫_{A'}` into leading-layer × deep-tail; head-split `prod_headSplit` exposes
  the corank block `Q_b = A_cor·Z_deep`; separate the pivot rows feeding the energy `w`). Statement
  CORRECT — the binding-cut lower bound `1 ≤ t★` and the chain nondegeneracy `∀ i, 1 ≤ M i` are
  LOAD-BEARING (without them `redChain 0 M 0 = 0` / a zero-width deep layer collapses the comparator
  index / product, making the carried `hpos : decLoss > 0 a.e.` unsatisfiable and the statement FALSE).

* **`deeperFlag_shell_le`** — the headline = `deeperFlag_spineToCore` (S1) ∘ `deeperFlag_shell_core_le`
  (L1) + the decorated IH via `cornerComparator_adm` + `flagShift_lt_carrierThreshold`. Everything above
  S1 is clean.

S2-FREE. Axiom-clean `[propext, Classical.choice, Quot.sound]` for the sorry-free results.
-/

namespace DLNFibre.DLN.RLCT

open Matrix MeasureTheory
open scoped ENNReal BigOperators

/-! ## S3 — the `U_s`-uniform reduced strong-block weight -/

/-- **The reduced strong-block weight is bounded by a `U_s`-uniform finite constant.** For `U_s : M₂×m`
with `U_sᵀU_s = 1`, `b' ≤ m`, in the convergent regime `a' < m − b' + 1`, the reduced corank weight over
`A·U_s` is bounded by the integral over the FIXED box `matBox b' M₂ (M₂²)` of the `m`-first-columns Gram
weight — a constant free of `U_s`. Route: `strongBlock_lintegral_lt_top` verbatim through the
right-mult CoV, then (i) the orthogonal extension `U` has `|det U| = 1` so the CoV Jacobian is `1`, and
(ii) `U`'s entries are `≤ 1` (orthonormal columns), so its `[−T,T]` bounding box has `T ≤ M₂²` and the
rotated domain `s ⊆ matBox b' M₂ (M₂²)`. -/
theorem strongBlock_lintegral_le_unif {b' m M₂ : ℕ} (hmM : m ≤ M₂)
    (U_s : Matrix (Fin M₂) (Fin m) ℝ) (hUs : U_sᵀ * U_s = 1) {a' : ℝ} :
    (∫⁻ A in matBox b' M₂ 1,
        ENNReal.ofReal (((Matrix.of A * U_s) * (Matrix.of A * U_s)ᵀ).det ^ (-a' / 2)))
      ≤ ∫⁻ X in matBox b' M₂ ((M₂ : ℝ) ^ 2),
          ENNReal.ofReal
            ((((Matrix.of X).submatrix id ⇑(Fin.castLEEmb hmM))
                * ((Matrix.of X).submatrix id ⇑(Fin.castLEEmb hmM))ᵀ).det ^ (-a' / 2)) := by
  classical
  set κ : Fin m ↪ Fin M₂ := Fin.castLEEmb hmM with hκdef
  obtain ⟨U, hUU, hUsub⟩ := exists_ortho_ext hmM U_s hUs
  have hUUt : U * Uᵀ = 1 := mul_eq_one_comm.mp hUU
  have hUdet : U.det ≠ 0 := by
    intro h
    have h1 : (Uᵀ * U).det = 1 := by rw [hUU, Matrix.det_one]
    rw [Matrix.det_mul, Matrix.det_transpose, h, mul_zero] at h1
    exact zero_ne_one h1
  have hUsub' : U.submatrix id (⇑κ) = U_s := hUsub
  -- `|det U| = 1`
  have hdetU_abs : |U.det| = 1 := by
    have h1 : (Uᵀ * U).det = 1 := by rw [hUU, Matrix.det_one]
    rw [Matrix.det_mul, Matrix.det_transpose] at h1
    have : U.det ^ 2 = 1 := by rw [sq]; linarith [h1]
    have h2 : |U.det| ^ 2 = 1 := by rw [sq_abs]; exact this
    nlinarith [abs_nonneg U.det, h2]
  -- entries of `U` bounded by 1 (columns orthonormal)
  have hUentry : ∀ i j : Fin M₂, |U i j| ≤ 1 := by
    intro i j
    have hcol : ∑ k, U k j * U k j = 1 := by
      have := congrFun (congrFun hUU j) j
      simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply_eq] at this
      exact this
    have hle : (U i j) ^ 2 ≤ ∑ k, U k j * U k j := by
      rw [sq]
      refine Finset.single_le_sum (f := fun k => U k j * U k j) (fun k _ => mul_self_nonneg _)
        (Finset.mem_univ i)
    rw [hcol] at hle
    nlinarith [abs_nonneg (U i j), sq_abs (U i j)]
  -- the column-restricted integrand `g`
  set g : (Fin b' → Fin M₂ → ℝ) → ℝ≥0∞ :=
    fun Y => ENNReal.ofReal
      ((((Matrix.of Y).submatrix id (⇑κ)) * ((Matrix.of Y).submatrix id (⇑κ))ᵀ).det ^ (-a' / 2))
    with hgdef
  have hcolmeas : Measurable (fun Y : Fin b' → Fin M₂ → ℝ => (fun i k => Y i (κ k))) :=
    measurable_pi_lambda _ (fun i =>
      measurable_pi_lambda _ (fun k => (measurable_pi_apply (κ k)).comp (measurable_pi_apply i)))
  have hgmeas : Measurable g := (measurable_detGram b' m a').comp hcolmeas
  have hof : ∀ A : Fin b' → Fin M₂ → ℝ, Matrix.of (fun i => A i ᵥ* U) = Matrix.of A * U := by
    intro A; ext i j
    simp only [Matrix.of_apply, Matrix.mul_apply, Matrix.vecMul, dotProduct]
  have hsubmul : ∀ A : Fin b' → Fin M₂ → ℝ,
      (Matrix.of A * U).submatrix id (⇑κ) = Matrix.of A * (U.submatrix id (⇑κ)) := by
    intro A; ext i k
    simp only [Matrix.submatrix_apply, Matrix.mul_apply, id_eq, Matrix.of_apply]
  have hint : ∀ A : Fin b' → Fin M₂ → ℝ,
      ENNReal.ofReal (((Matrix.of A * U_s) * (Matrix.of A * U_s)ᵀ).det ^ (-a' / 2))
        = g (fun i => A i ᵥ* U) := by
    intro A
    rw [hgdef]
    have hstep : (Matrix.of (fun i => A i ᵥ* U)).submatrix id (⇑κ) = Matrix.of A * U_s := by
      rw [hof A, hsubmul A, hUsub']
    simp only [hstep]
  set s : Set (Fin b' → Fin M₂ → ℝ) := {Y | (fun i => Y i ᵥ* Uᵀ) ∈ matBox b' M₂ 1} with hsdef
  have hsmeasmap : Measurable (fun Y : Fin b' → Fin M₂ → ℝ => (fun i => Y i ᵥ* Uᵀ)) := by
    refine measurable_pi_lambda _ (fun i => measurable_pi_lambda _ (fun j => ?_))
    simp only [Matrix.vecMul, dotProduct]
    exact Finset.measurable_sum _ (fun k _ =>
      (((measurable_pi_apply k).comp (measurable_pi_apply i)).mul measurable_const))
  have hsmeas : MeasurableSet s := hsmeasmap (matBox_measurableSet b' M₂ 1)
  have hfun : ∀ A : Fin b' → Fin M₂ → ℝ, (fun i => (A i ᵥ* U) ᵥ* Uᵀ) = A := by
    intro A; funext i
    rw [Matrix.vecMul_vecMul, hUUt, Matrix.vecMul_one]
  have hmem : ∀ A : Fin b' → Fin M₂ → ℝ,
      (fun i => A i ᵥ* U) ∈ s ↔ A ∈ matBox b' M₂ 1 := by
    intro A; simp only [hsdef, Set.mem_setOf_eq, hfun A]
  -- the box enclosure `s ⊆ matBox b' M₂ (M₂²)` (entries of `U` ≤ 1 ⟹ `T ≤ M₂²`)
  have hsub : s ⊆ matBox b' M₂ ((M₂ : ℝ) ^ 2) := by
    intro Y hY
    simp only [hsdef, Set.mem_setOf_eq, matBox, Set.mem_setOf_eq] at hY ⊢
    intro i j
    rw [Set.mem_Icc]
    have hYrec : (Y i ᵥ* Uᵀ) ᵥ* U = Y i := by
      rw [Matrix.vecMul_vecMul, hUU, Matrix.vecMul_one]
    have hentry : Y i j = ∑ k, (Y i ᵥ* Uᵀ) k * U k j := by
      conv_lhs => rw [← hYrec]
      simp only [Matrix.vecMul, dotProduct]
    have habs : |Y i j| ≤ (M₂ : ℝ) ^ 2 := by
      rw [hentry]
      calc |∑ k, (Y i ᵥ* Uᵀ) k * U k j|
          ≤ ∑ k, |(Y i ᵥ* Uᵀ) k * U k j| := Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ _k : Fin M₂, (1 : ℝ) := by
            refine Finset.sum_le_sum (fun k _ => ?_)
            rw [abs_mul]
            have hmb := hY i k
            rw [Set.mem_Icc] at hmb
            have h1 : |(Y i ᵥ* Uᵀ) k| ≤ 1 := abs_le.mpr hmb
            nlinarith [hUentry k j, abs_nonneg ((Y i ᵥ* Uᵀ) k), abs_nonneg (U k j), h1]
        _ = (M₂ : ℝ) := by simp
        _ ≤ (M₂ : ℝ) ^ 2 := by exact_mod_cast Nat.le_self_pow (by norm_num) M₂
    exact abs_le.mp habs
  -- assemble
  rw [show (∫⁻ A in matBox b' M₂ 1,
        ENNReal.ofReal (((Matrix.of A * U_s) * (Matrix.of A * U_s)ᵀ).det ^ (-a' / 2)))
      = ∫⁻ A in matBox b' M₂ 1, g (fun i => A i ᵥ* U) from lintegral_congr (fun A => hint A)]
  rw [← lintegral_indicator (matBox_measurableSet b' M₂ 1)]
  rw [show (∫⁻ A, (matBox b' M₂ 1).indicator (fun A => g (fun i => A i ᵥ* U)) A)
      = ∫⁻ A, (s.indicator g) (fun i => A i ᵥ* U) from lintegral_congr (fun A => by
        by_cases hA : A ∈ matBox b' M₂ 1
        · rw [Set.indicator_of_mem hA, Set.indicator_of_mem ((hmem A).mpr hA)]
        · rw [Set.indicator_of_notMem hA,
            Set.indicator_of_notMem (fun h => hA ((hmem A).mp h))])]
  rw [lintegral_comp_rightMulₚ b' U hUdet (s.indicator g) (hgmeas.indicator hsmeas),
    lintegral_indicator hsmeas]
  rw [hdetU_abs, one_pow, inv_one, ENNReal.ofReal_one, one_mul]
  calc ∫⁻ A in s, g A
      ≤ ∫⁻ A in matBox b' M₂ ((M₂ : ℝ) ^ 2), g A := lintegral_mono_set hsub
    _ = _ := rfl

/-- **The fixed-box uniform strong-block constant is finite.** `∫_{matBox b' M₂ (M₂²)} det(Gram of the
first `m` columns)^{−a'/2} < ⊤` in the convergent regime `a' < m − b' + 1` — a `U_s`-free finite
majorant (`detGram_firstCols_lintegral_box_lt_top` at `T = M₂²`). -/
theorem strongBlock_unif_const_lt_top {b' m M₂ : ℕ} (hmM : m ≤ M₂) (hbm : b' ≤ m) {a' : ℝ}
    (ha' : a' < (m : ℝ) - b' + 1) :
    (∫⁻ X in matBox b' M₂ ((M₂ : ℝ) ^ 2),
        ENNReal.ofReal
          ((((Matrix.of X).submatrix id ⇑(Fin.castLEEmb hmM))
              * ((Matrix.of X).submatrix id ⇑(Fin.castLEEmb hmM))ᵀ).det ^ (-a' / 2))) < ⊤ :=
  detGram_firstCols_lintegral_box_lt_top (Fin.castLEEmb hmM) hbm ha' ((M₂ : ℝ) ^ 2)

/-- **The shell corank weight is bounded by a `Z`-uniform finite constant.** On the shell
`Z Zᵀ ⪰ ε²·(U_s U_sᵀ)`, the corank weight `∫ det((A·Z)(A·Z)ᵀ)^{−a/2}` is bounded by
`ε^{−ab} · C_strong_unif`, where `C_strong_unif` is the fixed-box strong-block constant — a value free
of `Z` (given `hshell` holds). Composes OWED-1 `uniformWenn_proj_le` (Wenn ≤ ε^{−ab}·strong block) with
the uniform strong-block bound `strongBlock_lintegral_le_unif`. -/
theorem shellCorankWeight_le_unif {a b M₂ m n : ℕ} (Z : Matrix (Fin M₂) (Fin n) ℝ)
    (U_s : Matrix (Fin M₂) (Fin m) ℝ) (hUs : U_sᵀ * U_s = 1) (hbm : b ≤ m) (hmM : m ≤ M₂)
    {ε : ℝ} (hε : 0 < ε)
    (hshell : (Z * Zᵀ - (ε ^ 2) • (U_s * U_sᵀ)).PosSemidef) :
    (∫⁻ A in matBox b M₂ 1,
        ENNReal.ofReal (((Matrix.of A * Z) * (Matrix.of A * Z)ᵀ).det ^ (-(a : ℝ) / 2)))
      ≤ ENNReal.ofReal (ε ^ (-((a : ℝ) * b)))
        * ∫⁻ X in matBox b M₂ ((M₂ : ℝ) ^ 2),
            ENNReal.ofReal
              ((((Matrix.of X).submatrix id ⇑(Fin.castLEEmb hmM))
                  * ((Matrix.of X).submatrix id ⇑(Fin.castLEEmb hmM))ᵀ).det ^ (-(a : ℝ) / 2)) :=
  le_trans (uniformWenn_proj_le Z U_s hUs hbm hε hshell)
    (mul_le_mul_left' (strongBlock_lintegral_le_unif hmM U_s hUs) _)

/-- **The `Z`-uniform per-shell constant.** `Cresid(ab)c' · (ε^{−ab} · C_strong_unif)` — the finite,
`Z`/`Ccross`/`w`-free constant of the per-shell interior bound. Named so `shell_corankOffSector_le_unif`
and L1 (`deeperFlag_shell_core_le`) reference the identical term (avoids the nat-sub-cast mismatch). -/
noncomputable def deeperFlagUnifConst (a b m M₂ : ℕ) (hmM : m ≤ M₂) (ε c' : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (Cresid (a * b) c')
    * (ENNReal.ofReal (ε ^ (-((a : ℝ) * b)))
      * ∫⁻ X in matBox b M₂ ((M₂ : ℝ) ^ 2),
          ENNReal.ofReal
            ((((Matrix.of X).submatrix id ⇑(Fin.castLEEmb hmM))
                * ((Matrix.of X).submatrix id ⇑(Fin.castLEEmb hmM))ᵀ).det ^ (-(a : ℝ) / 2)))

/-- **The `Z`-uniform per-shell constant is finite** (in the convergent regime `a < m − b + 1`). -/
theorem deeperFlagUnifConst_lt_top (a b m M₂ : ℕ) (hmM : m ≤ M₂) (hbm : b ≤ m)
    (hconv : (a : ℝ) < (m : ℝ) - b + 1) (ε c' : ℝ) :
    deeperFlagUnifConst a b m M₂ hmM ε c' < ⊤ := by
  rw [deeperFlagUnifConst]
  exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top
    (ENNReal.mul_lt_top ENNReal.ofReal_lt_top (strongBlock_unif_const_lt_top hmM hbm hconv))

/-! ## S3 — the `Z`-uniform per-shell interior bound -/

/-- **The `Z`-uniform per-shell interior bound.** `shell_corankOffSector_le` with the constant made
INDEPENDENT of `Z`, `Ccross`, and `w`: on the shell `Z Zᵀ ⪰ ε²·(U_s U_sᵀ)` (`U_sᵀU_s=1`, `b ≤ m ≤ M₂`,
`m ≤ Z.rank`), in the reduced convergent regime `a < m − b + 1` with `ab/2 < c'`,

    ∫_{A_cor ∈ matBox b M₂ 1} ∫_{Γ∈sΓ} (w + frobSq(Ccross + Γ·(A_cor·Z)))^{−c'}
      ≤ Cunif · w^{−(c' − ab/2)}

where `Cunif = ofReal(Cresid(ab)c') · (ofReal(ε^{−ab}) · C_strong_unif)` reads only `ε` and the dims.
The `Z`-uniformity (replacing `shell_corankOffSector_le`'s `Cresid·Wenn(Z)` by the uniform
`shellCorankWeight_le_unif` bound) is what lets the reduced-param `z`-integral in L1 pull the constant
out. Proof: the corner atom `corankBlock_morsePeel_setLE` (`Apiv := 0`) pointwise on the full-row-rank
set, then integrate and bound the corank weight uniformly. -/
theorem shell_corankOffSector_le_unif {a b M₂ m n : ℕ} (Z : Matrix (Fin M₂) (Fin n) ℝ)
    (U_s : Matrix (Fin M₂) (Fin m) ℝ) (hUs : U_sᵀ * U_s = 1) (hbm : b ≤ m) (hmM : m ≤ M₂)
    (hmZ : m ≤ Z.rank) {ε : ℝ} (hε : 0 < ε)
    (hshell : (Z * Zᵀ - (ε ^ 2) • (U_s * U_sᵀ)).PosSemidef)
    (Ccross : Matrix (Fin a) (Fin n) ℝ) (c' : ℝ) (hc' : (a * b : ℝ) / 2 < c')
    (sΓ : Set (Fin a → Fin b → ℝ)) (w : ℝ) (hw : 0 < w) :
    ∫⁻ A_cor in matBox b M₂ 1,
        ∫⁻ Γ in sΓ, ENNReal.ofReal
          ((w + frobSq (Ccross + (Matrix.of Γ) * (Matrix.of A_cor * Z))) ^ (-c'))
      ≤ deeperFlagUnifConst a b m M₂ hmM ε c'
        * ENNReal.ofReal (w ^ (-(c' - (a * b : ℝ) / 2))) := by
  classical
  rw [deeperFlagUnifConst]
  set Wunif : ℝ≥0∞ := ENNReal.ofReal (ε ^ (-((a : ℝ) * b)))
    * ∫⁻ X in matBox b M₂ ((M₂ : ℝ) ^ 2),
        ENNReal.ofReal
          ((((Matrix.of X).submatrix id ⇑(Fin.castLEEmb hmM))
              * ((Matrix.of X).submatrix id ⇑(Fin.castLEEmb hmM))ᵀ).det ^ (-(a : ℝ) / 2)) with hWunif
  set F : (Fin b → Fin M₂ → ℝ) → ℝ≥0∞ := fun A =>
    ∫⁻ Γ in sΓ, ENNReal.ofReal
      ((w + frobSq (Ccross + (Matrix.of Γ) * (Matrix.of A * Z))) ^ (-c')) with hFdef
  have hmeasbox : MeasurableSet (matBox b M₂ 1) := matBox_measurableSet b M₂ 1
  have hbZ : b ≤ Z.rank := le_trans hbm hmZ
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
  calc ∫⁻ A in matBox b M₂ 1, F A
      ≤ ∫⁻ A in matBox b M₂ 1,
          ENNReal.ofReal (Cresid (a * b) c' * w ^ (-(c' - (a * b : ℝ) / 2)))
            * ENNReal.ofReal (((Matrix.of A * Z) * (Matrix.of A * Z)ᵀ).det ^ (-(a : ℝ) / 2)) := by
        refine lintegral_mono_ae ((ae_restrict_iff' hmeasbox).mpr ?_)
        filter_upwards [corank_survival_ae Z hbZ] with A hrank _hAbox
        exact hpt A hrank
    _ = ENNReal.ofReal (Cresid (a * b) c' * w ^ (-(c' - (a * b : ℝ) / 2)))
          * ∫⁻ A in matBox b M₂ 1,
              ENNReal.ofReal (((Matrix.of A * Z) * (Matrix.of A * Z)ᵀ).det ^ (-(a : ℝ) / 2)) :=
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ ≤ ENNReal.ofReal (Cresid (a * b) c' * w ^ (-(c' - (a * b : ℝ) / 2))) * Wunif := by
        exact mul_le_mul_left' (shellCorankWeight_le_unif Z U_s hUs hbm hmM hε hshell) _
    _ = (ENNReal.ofReal (Cresid (a * b) c') * Wunif)
          * ENNReal.ofReal (w ^ (-(c' - (a * b : ℝ) / 2))) := by
        rw [ENNReal.ofReal_mul (Cresid_nonneg (a * b) c')]; ring

/-! ## L1 — the per-shell off-sector-core → comparator domination -/

variable {L : ℕ}

/-- **The off-sector-core integrand at the deeper cut `u`** — L1's LHS and S1's output shape. The
freed-corner core (pivot energy taken to be the comparator loss `(cornerComparator …).decLoss v z`,
S4-definitional), integrated over the reduced params `z ∈ paramsBoxM (redChain u M) 1` and the
exceptional coordinates `v ∈ unitBox d` against the accumulated Jacobian monomial `∏|v_ℓ|^{jc_ℓ}`. Named
so `deeperFlag_spineToCore` (S1) and `deeperFlag_shell_core_le` (L1) reference the identical term. -/
noncomputable def deeperFlagCoreIntegrand {d M₂ n : ℕ} (M : Fin (L + 1 + 1 + 1) → ℕ) (u : ℕ)
    (k jc : Fin d → ℕ)
    (Zf : Params (redChain u M) → Matrix (Fin M₂) (Fin n) ℝ)
    (Ccrossf : Params (redChain u M) → Matrix (Fin (M 0 - u)) (Fin n) ℝ)
    (sΓf : Params (redChain u M) → Set (Fin (M 0 - u) → Fin (M 1 - u) → ℝ))
    (c' : ℝ) : ℝ≥0∞ :=
  ∫⁻ z in paramsBoxM (redChain u M) 1, ∫⁻ v in unitBox d,
    ENNReal.ofReal (∏ ℓ, |v ℓ| ^ (jc ℓ))
      * (∫⁻ A_cor in matBox (M 1 - u) M₂ 1, ∫⁻ Γ in sΓf z,
          ENNReal.ofReal
            (((cornerComparator (redChain u M) k jc).decLoss v z
                + frobSq (Ccrossf z + (Matrix.of Γ) * (Matrix.of A_cor * Zf z))) ^ (-c')))

/-- **L1 — the per-shell off-sector-core domination onto the reduced comparator.** The off-sector-core
integrand — for the reduced comparator `D = cornerComparator (redChain u M) k jc` with its pivot energy
taken to be the comparator loss `w = D.decLoss v z` (S4, DEFINITIONAL) — integrated over the reduced
params `z ∈ paramsBoxM (redChain u M) 1` and the exceptional coordinates `v ∈ unitBox d` against the
accumulated Jacobian monomial `∏|v_ℓ|^{jc_ℓ}`, is bounded by a `z`-uniform finite constant times the
reduced comparator's integral at the shifted exponent `c' − ½·peelCharge M u`:

    ∫_z ∫_v (∏|v_ℓ|^{jc_ℓ}) · [∫_{A_cor}∫_Γ (D.decLoss v z + frobSq(Ccross z + Γ·(A_cor·Z z)))^{−c'}]
      ≤ C · D.integral (c' − ½·peelCharge M u).

The corner dims are `a = M₀−u`, `b = M₁−u`, so `a·b = peelCharge M u` (definitional). Consumes the
`Z`-uniform interior bound `shell_corankOffSector_le_unif` (pointwise in `(z,v)` at `w = D.decLoss v z`,
which is `> 0` a.e. by `hpos` — the `{w=0}`-null side-condition, dischargeable from product-nonvanishing
+ the exceptional monomial), then the reduced-param integration collapses to `D.integral` by unfolding
(`w = decLoss` matched definitionally). The `∃ C < ⊤` form supplies the compose exactly what the decorated
IH needs (comparator finite ⟹ core finite). NO IH used here (pure domination). -/
theorem deeperFlag_shell_core_le {d M₂ m n : ℕ} (M : Fin (L + 1 + 1 + 1) → ℕ) (u : ℕ)
    (k jc : Fin d → ℕ)
    (Zf : Params (redChain u M) → Matrix (Fin M₂) (Fin n) ℝ)
    (Ccrossf : Params (redChain u M) → Matrix (Fin (M 0 - u)) (Fin n) ℝ)
    (U_sf : Params (redChain u M) → Matrix (Fin M₂) (Fin m) ℝ)
    (sΓf : Params (redChain u M) → Set (Fin (M 0 - u) → Fin (M 1 - u) → ℝ))
    {ε : ℝ} (hε : 0 < ε)
    (hUs : ∀ z, (U_sf z)ᵀ * U_sf z = 1) (hbm : M 1 - u ≤ m) (hmM : m ≤ M₂)
    (hmZ : ∀ z, m ≤ (Zf z).rank)
    (hshell : ∀ z, (Zf z * (Zf z)ᵀ - (ε ^ 2) • (U_sf z * (U_sf z)ᵀ)).PosSemidef)
    (c' : ℝ) (hconv : ((M 0 - u : ℕ) : ℝ) < (m : ℝ) - ((M 1 - u : ℕ) : ℝ) + 1)
    (hc' : (((M 0 - u) * (M 1 - u) : ℕ) : ℝ) / 2 < c')
    (hpos : ∀ᵐ z ∂(volume.restrict (paramsBoxM (redChain u M) 1)),
        ∀ᵐ v ∂(volume.restrict (unitBox d)),
          0 < (cornerComparator (redChain u M) k jc).decLoss v z) :
    ∃ C : ℝ≥0∞, C < ⊤ ∧
      deeperFlagCoreIntegrand M u k jc Zf Ccrossf sΓf c'
        ≤ C * (cornerComparator (redChain u M) k jc).integral (c' - (peelCharge M u : ℝ) / 2) := by
  classical
  rw [deeperFlagCoreIntegrand]
  set D := cornerComparator (redChain u M) k jc with hD
  set e : ℝ := c' - (peelCharge M u : ℝ) / 2 with he
  -- the named `Z`-uniform constant
  set C : ℝ≥0∞ := deeperFlagUnifConst (M 0 - u) (M 1 - u) m M₂ hmM ε c' with hC
  have hCfin : C < ⊤ :=
    deeperFlagUnifConst_lt_top (M 0 - u) (M 1 - u) m M₂ hmM hbm hconv ε c'
  refine ⟨C, hCfin, ?_⟩
  -- exponent bookkeeping: `↑a·↑b = a·b(:ℝ) = peelCharge M u(:ℝ)`, so `c' − ↑a·↑b/2 = e`.
  have hc'' : (((M 0 - u : ℕ) : ℝ) * ((M 1 - u : ℕ) : ℝ)) / 2 < c' := by
    rw [← Nat.cast_mul]; exact hc'
  have hexp : c' - ((M 0 - u : ℕ) : ℝ) * ((M 1 - u : ℕ) : ℝ) / 2 = e := by
    rw [he, peelCharge, Nat.cast_mul]
  -- the pointwise-a.e. interior bound, then integrate.
  have hstep : (∫⁻ z in paramsBoxM (redChain u M) 1, ∫⁻ v in unitBox d,
        ENNReal.ofReal (∏ ℓ, |v ℓ| ^ (jc ℓ))
          * (∫⁻ A_cor in matBox (M 1 - u) M₂ 1, ∫⁻ Γ in sΓf z,
              ENNReal.ofReal
                ((D.decLoss v z
                    + frobSq (Ccrossf z + (Matrix.of Γ) * (Matrix.of A_cor * Zf z))) ^ (-c'))))
      ≤ ∫⁻ z in paramsBoxM (redChain u M) 1, ∫⁻ v in unitBox d,
          C * ENNReal.ofReal ((∏ ℓ, |v ℓ| ^ (jc ℓ)) * (D.decLoss v z) ^ (-e)) := by
    refine lintegral_mono_ae ?_
    filter_upwards [hpos] with z hzv
    refine lintegral_mono_ae ?_
    filter_upwards [hzv] with v hvpos
    -- pointwise at `(z, v)`, `w := D.decLoss v z > 0`
    have hbound := shell_corankOffSector_le_unif (Zf z) (U_sf z) (hUs z) hbm hmM (hmZ z) hε
      (hshell z) (Ccrossf z) c' hc'' (sΓf z) (D.decLoss v z) hvpos
    rw [← hC, hexp] at hbound
    calc ENNReal.ofReal (∏ ℓ, |v ℓ| ^ (jc ℓ))
            * (∫⁻ A_cor in matBox (M 1 - u) M₂ 1, ∫⁻ Γ in sΓf z,
                ENNReal.ofReal
                  ((D.decLoss v z
                      + frobSq (Ccrossf z + (Matrix.of Γ) * (Matrix.of A_cor * Zf z))) ^ (-c')))
        ≤ ENNReal.ofReal (∏ ℓ, |v ℓ| ^ (jc ℓ))
            * (C * ENNReal.ofReal ((D.decLoss v z) ^ (-e))) :=
          mul_le_mul_left' hbound _
      _ = C * ENNReal.ofReal ((∏ ℓ, |v ℓ| ^ (jc ℓ)) * (D.decLoss v z) ^ (-e)) := by
          rw [ENNReal.ofReal_mul (Finset.prod_nonneg (fun ℓ _ => by positivity))]
          ring
  refine le_trans hstep ?_
  -- pull `C` out and recognise the comparator integral
  rw [show (∫⁻ z in paramsBoxM (redChain u M) 1, ∫⁻ v in unitBox d,
        C * ENNReal.ofReal ((∏ ℓ, |v ℓ| ^ (jc ℓ)) * (D.decLoss v z) ^ (-e)))
      = C * ∫⁻ z in paramsBoxM (redChain u M) 1, ∫⁻ v in unitBox d,
          ENNReal.ofReal ((∏ ℓ, |v ℓ| ^ (jc ℓ)) * (D.decLoss v z) ^ (-e)) from ?_]
  · exact le_refl _
  · rw [← lintegral_const_mul' C _ hCfin.ne]
    refine lintegral_congr (fun z => ?_)
    rw [← lintegral_const_mul' C _ hCfin.ne]

/-! ## The literal spine integrand + the headline `deeperFlag_shell_le` (S1 ∘ L1) -/

/-- **The literal cut-`u` shell-restricted spine integrand** — the `RouteMSJDecoratedPeelStep`
`innerCorankDescent` freed-Γ triple at cut `u`, with the outer `A'` restricted to the shell
`{A' | prod (tailChain M) A' ∈ singularShell ε r jf}`. This is the T-peel spine's per-shell output. -/
noncomputable def shellSpineIntegrand {L : ℕ} (M : Fin (L + 1 + 1 + 1) → ℕ) (u : ℕ)
    (κ : Fin u ↪ Fin (M 1)) (ε : ℝ) (r : ℕ) (jf : Fin (r + 1)) (c' : ℝ) : ℝ≥0∞ :=
  ∫⁻ A' in paramsBoxM (tailChain M) 1
      ∩ {A' | prod (tailChain M) A' ∈ singularShell ε r jf},
    ∫⁻ x in outerDom u (M 0 - u) (M 1 - u) 1,
      ∫⁻ Γ in {Γ : Fin (M 0 - u) → Fin (M 1 - u) → ℝ |
          Γ + schurShift x ∈ genBox (Fin (M 0 - u)) (Fin (M 1 - u)) 1},
        ENNReal.ofReal
          ((freedSchurLoss x Γ ((prod (tailChain M) A').submatrix (blockSplitEquiv κ) id)) ^ (-c'))

/-- **S1 (the ISOLATED sorry) — the head-split spine→core reduction, at a binding cut on shell `j`.**
For a legal binding cut `t★` (`ht`) and shell index `j ≤ r = min(M₀−t★, M₁−t★)` (`hj`), the cut-`u`
(`u = t★+j`) / shell-`j` spine integrand is bounded by L1's off-sector-core integrand for head-split data
satisfying the L1 + comparator hypotheses (INCLUDING the strict convergence, true here by the binding-cut
fact `a−j < M₂−b+1` — cornershift cert, 0/3161). The binding-cut restriction is LOAD-BEARING: at a
non-binding cut / mismatched shell no convergent head-split exists, so the unconstrained statement would
be FALSE. This is the ~65–75%-genuinely-new decorated-peel head-split change-of-variables
(`RouteMSJDecorated`): Tonelli-factor `∫_{A'}` into leading-layer × deep-tail; the banked `prod_headSplit`
exposes the corank block `Q_b = A_cor·Z_deep`; separate the pivot rows feeding the energy `w = decLoss`;
the per-point strong projection `U_sf` (deliverable B) discharges the shell PSD hypothesis. Statement
CORRECT (the existential asserts the convergent head-split EXISTS — it does, per the certs); proof deferred. -/
theorem deeperFlag_spineToCore {L : ℕ} (M : Fin (L + 1 + 1 + 1) → ℕ) (t j : ℕ)
    (κ : Fin (t + j) ↪ Fin (M 1)) {ε : ℝ} (hε : 0 < ε) (c' : ℝ)
    (ht : t ≤ min (M 0) (M 1)) (hj : j ≤ min (M 0 - t) (M 1 - t))
    (ht1 : 1 ≤ t) (hnd : ∀ i, 1 ≤ M i) :
    ∃ (M₂ m n d : ℕ) (k jc : Fin d → ℕ)
      (Zf : Params (redChain (t + j) M) → Matrix (Fin M₂) (Fin n) ℝ)
      (Ccrossf : Params (redChain (t + j) M) → Matrix (Fin (M 0 - (t + j))) (Fin n) ℝ)
      (U_sf : Params (redChain (t + j) M) → Matrix (Fin M₂) (Fin m) ℝ)
      (sΓf : Params (redChain (t + j) M) → Set (Fin (M 0 - (t + j)) → Fin (M 1 - (t + j)) → ℝ))
      (_i₀ : Fin ((redChain (t + j) M) 0) × Fin ((redChain (t + j) M) (Fin.last (L + 1)))),
      (∀ z, (U_sf z)ᵀ * U_sf z = 1) ∧ (M 1 - (t + j) ≤ m) ∧ (m ≤ M₂) ∧ (∀ z, m ≤ (Zf z).rank)
      ∧ (∀ z, (Zf z * (Zf z)ᵀ - (ε ^ 2) • (U_sf z * (U_sf z)ᵀ)).PosSemidef)
      ∧ (((M 0 - (t + j) : ℕ) : ℝ) < (m : ℝ) - ((M 1 - (t + j) : ℕ) : ℝ) + 1)
      ∧ (∀ᵐ z ∂(volume.restrict (paramsBoxM (redChain (t + j) M) 1)),
          ∀ᵐ v ∂(volume.restrict (unitBox d)),
            0 < (cornerComparator (redChain (t + j) M) k jc).decLoss v z)
      ∧ (1 ≤ d)
      ∧ ((minAdm (redChain (t + j) M) : ℝ≥0∞) / 2 ≤ monomialThreshold d k jc)
      ∧ shellSpineIntegrand M (t + j) κ ε (min (M 0 - t) (M 1 - t)) ⟨j, Nat.lt_succ_of_le hj⟩ c'
          ≤ deeperFlagCoreIntegrand M (t + j) k jc Zf Ccrossf sΓf c' := by
  sorry

/-- **The headline `deeperFlag_shell_le` — the T-Obl3b off-sector shell-stratification mountain (per
shell, corrected deeper-cut route).** At a legal binding cut `t★` and shell `j ≤ r`, the literal cut-`u`
(`u = t★+j`) / shell-`j` spine integrand is dominated by a finite constant times the reduced comparator's
integral at the shifted exponent `c' − ½·peelCharge M u`, with the comparator `adm`-admissible (so the
decorated IH closes it in the compose). Proof = `deeperFlag_spineToCore` (S1, the isolated head-split
sorry) ∘ `deeperFlag_shell_core_le` (L1, the clean analytic core) + `cornerComparator_adm`. The
`c' > ½·peelCharge M u` hypothesis is the freed-corner peel regime (the complementary bounded regime is a
separate, elementary branch). Everything above S1 (L1, the S3 uniform bricks) is sorry-free. -/
theorem deeperFlag_shell_le {L : ℕ} (M : Fin (L + 1 + 1 + 1) → ℕ) (t j : ℕ)
    (κ : Fin (t + j) ↪ Fin (M 1)) {ε : ℝ} (hε : 0 < ε) (c' : ℝ)
    (ht : t ≤ min (M 0) (M 1)) (hj : j ≤ min (M 0 - t) (M 1 - t))
    (ht1 : 1 ≤ t) (hnd : ∀ i, 1 ≤ M i)
    (hc' : (((M 0 - (t + j)) * (M 1 - (t + j)) : ℕ) : ℝ) / 2 < c') :
    ∃ (d : ℕ) (k jc : Fin d → ℕ) (C : ℝ≥0∞), C < ⊤
      ∧ adm (L + 1) (redChain (t + j) M) (cornerComparator (redChain (t + j) M) k jc)
      ∧ shellSpineIntegrand M (t + j) κ ε (min (M 0 - t) (M 1 - t)) ⟨j, Nat.lt_succ_of_le hj⟩ c'
          ≤ C * (cornerComparator (redChain (t + j) M) k jc).integral
              (c' - (peelCharge M (t + j) : ℝ) / 2) := by
  obtain ⟨M₂, m, n, d, k, jc, Zf, Ccrossf, U_sf, sΓf, i₀, hUs, hbm, hmM, hmZ, hshell, hconv, hpos,
    hd, hbeta, hle⟩ := deeperFlag_spineToCore M t j κ hε c' ht hj ht1 hnd
  obtain ⟨C, hCfin, hcore⟩ :=
    deeperFlag_shell_core_le M (t + j) k jc Zf Ccrossf U_sf sΓf hε hUs hbm hmM hmZ hshell c'
      hconv hc' hpos
  exact ⟨d, k, jc, C, hCfin,
    cornerComparator_adm (redChain (t + j) M) k jc hd i₀ hbeta, hle.trans hcore⟩

end DLNFibre.DLN.RLCT
