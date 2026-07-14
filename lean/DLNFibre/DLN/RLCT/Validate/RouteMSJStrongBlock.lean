import DLNFibre.DLN.RLCT.Validate.RouteMSJDeeperFlagShell
import DLNFibre.DLN.RLCT.Validate.RouteMSJOffSectorBPos
import DLNFibre.DLN.RLCT.Validate.RouteMSJOrthoExtend
import DLNFibre.DLN.RLCT.Validate.RouteMSJBlockReindex

set_option linter.style.longLine false

/-!
# `RouteMSJStrongBlock` — OWED-2 of the T-Obl3b mountain: the strong-block reduced weight is finite

**Thread `genm-sj5-domination`, T-Obl3b mountain, OWED-2 (chart cert
`tobl3b-cornershift-chart-cert.md` §5).** The reduced weight that OWED-1 (`uniformWenn_proj_le`)
produces — `∫_{A ∈ box(b'×M₂)} det((A U_s)(A U_s)ᵀ)^{−a'/2}`, `U_s : M₂×m` with orthonormal columns
(`U_sᵀ U_s = 1`) — is finite in the strictly-convergent regime `a' < m − b' + 1`.

## The route (chart cert §5 OWED-2, exact)

1. **`exists_ortho_ext`** (banked, crux) extends `U_s` to an orthogonal `U ∈ O(M₂)` (`Uᵀ U = 1`) whose
   first `m` columns are `U_s`, so `of A · U_s = (of A · U).submatrix id ⇑κ` (`κ = castLEEmb`).
2. **Right-mult CoV `A ↦ A·U`** (banked `lintegral_comp_rightMulₚ`, `|det U| ≠ 0`) via an indicator,
   moving the box to the rotated box `s`, enclosed in `matBox b' M₂ T` (orthogonal ⟹ bounded entries).
3. **Column-Fubini** (`colSplitEquiv`, this file): `matBox b' M₂ T` factors as
   `matBox b' m T ×ˢ matBox b' (M₂−m) T`; the integrand reads only the first `m` columns, so the last
   `M₂−m` columns integrate to a finite volume factor and the first `m` reduce to
   **`detGram_lintegral_box_lt_top`** at `(r,n) = (b', m)`, condition `a' < m − b' + 1`.

Network-free (measure plumbing over banked bricks). Intended axiom footprint
`[propext, Classical.choice, Quot.sound]`.
-/

namespace DLNFibre.DLN.RLCT

open Matrix MeasureTheory
open scoped ENNReal BigOperators

/-! ## The measure-preserving column split -/

/-- **The column split** `(Fin b → Fin M₂ → ℝ) ≃ᵐ (Fin b → Fin m → ℝ) × (Fin b → Fin (M₂ − m) → ℝ)`:
reindex the columns by `blockSplitEquiv κ` (the `κ`-columns first, `arrowCongr'` on the inner index),
split the `Fin m ⊕ Fin (M₂ − m)` column sum (`sumPiEquivProdPi`), then pull the product out of the row
function (`arrowProdEquivProdArrow`). Measure-preserving (each factor is). -/
noncomputable def colSplitEquiv {m M₂ : ℕ} (b : ℕ) (κ : Fin m ↪ Fin M₂) :
    (Fin b → Fin M₂ → ℝ) ≃ᵐ (Fin b → Fin m → ℝ) × (Fin b → Fin (M₂ - m) → ℝ) :=
  (MeasurableEquiv.arrowCongr' (Equiv.refl (Fin b))
      ((MeasurableEquiv.arrowCongr' (blockSplitEquiv κ).symm (MeasurableEquiv.refl ℝ)).trans
        (MeasurableEquiv.sumPiEquivProdPi (fun _ : Fin m ⊕ Fin (M₂ - m) => ℝ)))).trans
    (MeasurableEquiv.arrowProdEquivProdArrow (Fin m → ℝ) (Fin (M₂ - m) → ℝ) (Fin b))

/-- `colSplitEquiv` is measure-preserving. -/
theorem measurePreserving_colSplitEquiv {m M₂ : ℕ} (b : ℕ) (κ : Fin m ↪ Fin M₂) :
    MeasurePreserving (colSplitEquiv b κ) (volume : Measure (Fin b → Fin M₂ → ℝ)) volume := by
  unfold colSplitEquiv
  refine MeasurePreserving.trans ?_
    (volume_measurePreserving_arrowProdEquivProdArrow (Fin m → ℝ) (Fin (M₂ - m) → ℝ) (Fin b))
  refine volume_preserving_arrowCongr' (Equiv.refl (Fin b)) _ ?_
  refine MeasurePreserving.trans ?_
    (volume_measurePreserving_sumPiEquivProdPi (fun _ : Fin m ⊕ Fin (M₂ - m) => ℝ))
  exact volume_preserving_arrowCongr' (blockSplitEquiv κ).symm (MeasurableEquiv.refl ℝ)
    (MeasurePreserving.id volume)

/-- The first block of `colSplitEquiv` reads the `κ`-columns: `(colSplitEquiv b κ Y).1 i k = Y i (κ k)`. -/
theorem colSplitEquiv_fst {m M₂ : ℕ} (b : ℕ) (κ : Fin m ↪ Fin M₂)
    (Y : Fin b → Fin M₂ → ℝ) (i : Fin b) (k : Fin m) :
    (colSplitEquiv b κ Y).1 i k = Y i (κ k) := by
  change Y i (blockSplitEquiv κ (Sum.inl k)) = Y i (κ k)
  rw [blockSplitEquiv_inl]

/-- The second block of `colSplitEquiv` reads the complementary columns. -/
theorem colSplitEquiv_snd {m M₂ : ℕ} (b : ℕ) (κ : Fin m ↪ Fin M₂)
    (Y : Fin b → Fin M₂ → ℝ) (i : Fin b) (k : Fin (M₂ - m)) :
    (colSplitEquiv b κ Y).2 i k = Y i (blockSplitEquiv κ (Sum.inr k)) := rfl

/-- **The box factorization.** `colSplitEquiv ⁻¹' (matBox b m T ×ˢ matBox b (M₂ − m) T) = matBox b M₂ T`:
`blockSplitEquiv κ` is a column bijection, so every column bounded iff both blocks bounded. -/
theorem colSplitEquiv_preimage_box {m M₂ : ℕ} (b : ℕ) (κ : Fin m ↪ Fin M₂) (T : ℝ) :
    colSplitEquiv b κ ⁻¹' (matBox b m T ×ˢ matBox b (M₂ - m) T) = matBox b M₂ T := by
  ext Y
  simp only [Set.mem_preimage, Set.mem_prod, matBox, Set.mem_setOf_eq, colSplitEquiv_fst,
    colSplitEquiv_snd]
  constructor
  · rintro ⟨h1, h2⟩ i j
    obtain ⟨S, rfl⟩ := (blockSplitEquiv κ).surjective j
    cases S with
    | inl k => rw [blockSplitEquiv_inl]; exact h1 i k
    | inr k => exact h2 i k
  · intro h
    exact ⟨fun i k => h i (κ k), fun i k => h i (blockSplitEquiv κ (Sum.inr k))⟩

/-! ## The first-`m`-columns determinant weight is finite -/

/-- **The first-`m`-columns Gram determinant integral is finite on the box.** For a column embedding
`κ : Fin m ↪ Fin M₂`, `b ≤ m`, `a < m − b + 1`, the integral over `matBox b M₂ T` of
`det(X Xᵀ)^{−a/2}` with `X = (of Y).submatrix id ⇑κ` (the `κ`-columns of `Y`) is finite. The column
split factors the box; the integrand reads only the `κ`-columns, so the complementary columns integrate
to `volume (matBox b (M₂−m) T) < ⊤` and the `κ`-columns reduce to `detGram_lintegral_box_lt_top`. -/
theorem detGram_firstCols_lintegral_box_lt_top {b m M₂ : ℕ} (κ : Fin m ↪ Fin M₂)
    (hbm : b ≤ m) {a : ℝ} (ha : a < (m : ℝ) - b + 1) (T : ℝ) :
    (∫⁻ Y in matBox b M₂ T,
      ENNReal.ofReal
        ((((Matrix.of Y).submatrix id ⇑κ) * ((Matrix.of Y).submatrix id ⇑κ)ᵀ).det ^ (-a / 2)))
      < ⊤ := by
  classical
  set E := colSplitEquiv b κ with hEdef
  set G : ((Fin b → Fin m → ℝ) × (Fin b → Fin (M₂ - m) → ℝ)) → ℝ≥0∞ :=
    fun p => ENNReal.ofReal ((Matrix.of p.1 * (Matrix.of p.1)ᵀ).det ^ (-a / 2)) with hGdef
  have hGmeas : Measurable G := (measurable_detGram b m a).comp measurable_fst
  -- the split reads the κ-columns of Y as its first block: `of (E Y).1 = (of Y).submatrix id ⇑κ`
  have hmateq : ∀ Y : Fin b → Fin M₂ → ℝ,
      Matrix.of (E Y).1 = (Matrix.of Y).submatrix id ⇑κ := by
    intro Y; ext i k
    simp only [Matrix.of_apply, Matrix.submatrix_apply, id_eq, hEdef, colSplitEquiv_fst]
  -- integrand equals `G ∘ E`
  have hval : ∀ Y : Fin b → Fin M₂ → ℝ,
      ENNReal.ofReal
          ((((Matrix.of Y).submatrix id ⇑κ) * ((Matrix.of Y).submatrix id ⇑κ)ᵀ).det ^ (-a / 2))
        = G (E Y) := by
    intro Y; rw [hGdef]; simp only [hmateq Y]
  rw [show (∫⁻ Y in matBox b M₂ T,
        ENNReal.ofReal
          ((((Matrix.of Y).submatrix id ⇑κ) * ((Matrix.of Y).submatrix id ⇑κ)ᵀ).det ^ (-a / 2)))
      = ∫⁻ Y in matBox b M₂ T, G (E Y) from
    setLIntegral_congr_fun (matBox_measurableSet b M₂ T) (fun Y _ => hval Y)]
  -- transport through the MP split + box factorization
  have hCoV := (measurePreserving_colSplitEquiv b κ).setLIntegral_comp_preimage_emb
    E.measurableEmbedding G (matBox b m T ×ˢ matBox b (M₂ - m) T)
  rw [colSplitEquiv_preimage_box b κ T] at hCoV
  rw [hCoV]
  -- Tonelli: the complementary block integrates to a finite volume factor
  rw [Measure.volume_eq_prod (Fin b → Fin m → ℝ) (Fin b → Fin (M₂ - m) → ℝ),
    setLIntegral_prod _ hGmeas.aemeasurable]
  have hboxvol : volume (matBox b (M₂ - m) T) < ⊤ := by
    have heq : matBox b (M₂ - m) T
        = Set.univ.pi (fun _ : Fin b => Set.univ.pi (fun _ : Fin (M₂ - m) => Set.Icc (-T) T)) := by
      ext X; simp only [matBox, Set.mem_setOf_eq, Set.mem_pi, Set.mem_univ, true_implies]
    rw [heq]
    exact (isCompact_univ_pi (fun _ => isCompact_univ_pi (fun _ => isCompact_Icc))).measure_lt_top
  have hinner : ∀ x : Fin b → Fin m → ℝ,
      (∫⁻ w in matBox b (M₂ - m) T, G (x, w))
        = ENNReal.ofReal ((Matrix.of x * (Matrix.of x)ᵀ).det ^ (-a / 2))
            * volume (matBox b (M₂ - m) T) := by
    intro x
    calc (∫⁻ w in matBox b (M₂ - m) T, G (x, w))
        = ∫⁻ _w in matBox b (M₂ - m) T,
            ENNReal.ofReal ((Matrix.of x * (Matrix.of x)ᵀ).det ^ (-a / 2)) :=
          lintegral_congr (fun w => by rw [hGdef])
      _ = ENNReal.ofReal ((Matrix.of x * (Matrix.of x)ᵀ).det ^ (-a / 2))
            * volume (matBox b (M₂ - m) T) := setLIntegral_const (matBox b (M₂ - m) T) _
  simp_rw [hinner]
  rw [lintegral_mul_const' _ _ hboxvol.ne]
  exact ENNReal.mul_lt_top (detGram_lintegral_box_lt_top hbm ha T) hboxvol

/-! ## OWED-2 — the strong-block reduced weight is finite -/

/-- **OWED-2 `strongBlock_lintegral_lt_top`** — the strictly-convergent reduced weight at the shrunk
dims. For `U_s : M₂×m` with orthonormal columns (`U_sᵀ U_s = 1`), `b' ≤ m`, and the convergent regime
`a' < m − b' + 1`, the reduced corank weight over `A·U_s` is finite:

    ∫_{A ∈ matBox b' M₂ 1} det((A U_s)(A U_s)ᵀ)^{−a'/2}  <  ⊤.

This closes the RHS of OWED-1 (`uniformWenn_proj_le`). Route (chart cert §5): extend `U_s` to
orthogonal `U` (`exists_ortho_ext`), so `of A · U_s = (of A · U).submatrix id ⇑κ`; the measure-preserving
right-mult `A ↦ A·U` (`lintegral_comp_rightMulₚ`) moves the box to a rotated box enclosed in
`matBox b' M₂ T`; the column-Fubini (`detGram_firstCols_lintegral_box_lt_top`) reduces to
`detGram_lintegral_box_lt_top` at `(b', m)`, condition `a' < m − b' + 1`. NO bordered-Gram. -/
theorem strongBlock_lintegral_lt_top {b' m M₂ : ℕ} (hmM : m ≤ M₂)
    (U_s : Matrix (Fin M₂) (Fin m) ℝ) (hUs : U_sᵀ * U_s = 1) (hbm : b' ≤ m) {a' : ℝ}
    (ha' : a' < (m : ℝ) - b' + 1) :
    (∫⁻ A in matBox b' M₂ 1,
        ENNReal.ofReal (((Matrix.of A * U_s) * (Matrix.of A * U_s)ᵀ).det ^ (-a' / 2))) < ⊤ := by
  classical
  set κ : Fin m ↪ Fin M₂ := Fin.castLEEmb hmM with hκdef
  -- orthogonal extension of `U_s`
  obtain ⟨U, hUU, hUsub⟩ := exists_ortho_ext hmM U_s hUs
  have hUUt : U * Uᵀ = 1 := mul_eq_one_comm.mp hUU
  have hUdet : U.det ≠ 0 := by
    intro h
    have h1 : (Uᵀ * U).det = 1 := by rw [hUU, Matrix.det_one]
    rw [Matrix.det_mul, Matrix.det_transpose, h, mul_zero] at h1
    exact zero_ne_one h1
  have hUsub' : U.submatrix id (⇑κ) = U_s := hUsub
  -- the column-restricted integrand `g`
  set g : (Fin b' → Fin M₂ → ℝ) → ℝ≥0∞ :=
    fun Y => ENNReal.ofReal
      ((((Matrix.of Y).submatrix id (⇑κ)) * ((Matrix.of Y).submatrix id (⇑κ))ᵀ).det ^ (-a' / 2))
    with hgdef
  have hcolmeas : Measurable (fun Y : Fin b' → Fin M₂ → ℝ => (fun i k => Y i (κ k))) :=
    measurable_pi_lambda _ (fun i =>
      measurable_pi_lambda _ (fun k => (measurable_pi_apply (κ k)).comp (measurable_pi_apply i)))
  have hgmeas : Measurable g := (measurable_detGram b' m a').comp hcolmeas
  -- `of (fun i ↦ A i ᵥ* U) = of A * U`
  have hof : ∀ A : Fin b' → Fin M₂ → ℝ, Matrix.of (fun i => A i ᵥ* U) = Matrix.of A * U := by
    intro A; ext i j
    simp only [Matrix.of_apply, Matrix.mul_apply, Matrix.vecMul, dotProduct]
  -- `(of A * U).submatrix id ⇑κ = of A * (U.submatrix id ⇑κ)`
  have hsubmul : ∀ A : Fin b' → Fin M₂ → ℝ,
      (Matrix.of A * U).submatrix id (⇑κ) = Matrix.of A * (U.submatrix id (⇑κ)) := by
    intro A; ext i k
    simp only [Matrix.submatrix_apply, Matrix.mul_apply, id_eq, Matrix.of_apply]
  -- integrand rewrite: `det((A U_s)(A U_s)ᵀ)^… = g (fun i ↦ A i ᵥ* U)`
  have hint : ∀ A : Fin b' → Fin M₂ → ℝ,
      ENNReal.ofReal (((Matrix.of A * U_s) * (Matrix.of A * U_s)ᵀ).det ^ (-a' / 2))
        = g (fun i => A i ᵥ* U) := by
    intro A
    rw [hgdef]
    have hstep : (Matrix.of (fun i => A i ᵥ* U)).submatrix id (⇑κ) = Matrix.of A * U_s := by
      rw [hof A, hsubmul A, hUsub']
    simp only [hstep]
  -- the rotated box preimage
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
  -- the box enclosure `s ⊆ matBox b' M₂ T`
  set T : ℝ := ∑ k : Fin M₂, ∑ j : Fin M₂, |U k j| with hTdef
  have hsub : s ⊆ matBox b' M₂ T := by
    intro Y hY
    simp only [hsdef, Set.mem_setOf_eq, matBox, Set.mem_setOf_eq] at hY ⊢
    intro i j
    rw [Set.mem_Icc]
    have hYrec : (Y i ᵥ* Uᵀ) ᵥ* U = Y i := by
      rw [Matrix.vecMul_vecMul, hUU, Matrix.vecMul_one]
    have hentry : Y i j = ∑ k, (Y i ᵥ* Uᵀ) k * U k j := by
      conv_lhs => rw [← hYrec]
      simp only [Matrix.vecMul, dotProduct]
    have habs : |Y i j| ≤ T := by
      rw [hentry]
      calc |∑ k, (Y i ᵥ* Uᵀ) k * U k j|
          ≤ ∑ k, |(Y i ᵥ* Uᵀ) k * U k j| := Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ k, |U k j| := by
            refine Finset.sum_le_sum (fun k _ => ?_)
            rw [abs_mul]
            have hmb := hY i k
            rw [Set.mem_Icc] at hmb
            have h1 : |(Y i ᵥ* Uᵀ) k| ≤ 1 := abs_le.mpr hmb
            nlinarith [abs_nonneg (U k j), h1]
        _ ≤ T := by
            rw [hTdef]
            exact Finset.sum_le_sum (fun k _ =>
              Finset.single_le_sum (f := fun j' => |U k j'|)
                (fun j' _ => abs_nonneg _) (Finset.mem_univ j))
    exact abs_le.mp habs
  -- assemble: rewrite integrand, indicator-CoV, box enclosure, column-Fubini
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
  refine ENNReal.mul_lt_top ENNReal.ofReal_lt_top ?_
  calc ∫⁻ A in s, g A ≤ ∫⁻ A in matBox b' M₂ T, g A := lintegral_mono_set hsub
    _ < ⊤ := detGram_firstCols_lintegral_box_lt_top κ hbm ha' T

/-! ## OWED-1 ∘ OWED-2 — the shell reduced corank weight is finite (the deeper-cut payoff) -/

/-- **The deeper-cut shell corank weight is finite (Steps 2–3 of the corrected corner-shrink, chart
cert §1/§5).** On the shell `Z Zᵀ ⪰ ε²·(U_s U_sᵀ)` (`U_s : M₂×m`, `U_sᵀ U_s = 1`, `b' ≤ m ≤ M₂`), in
the strictly-convergent reduced regime `a' < m − b' + 1`, the corank weight over `A·Z` is finite:

    ∫_{A ∈ matBox b' M₂ 1} det((A Z)(A Z)ᵀ)^{−a'/2}  <  ⊤.

This is the analytic payoff of the corrected deeper-cut route: OWED-1 (`uniformWenn_proj_le`,
PSD-monotone weak-direction elimination `M₂ → m` with the uniform factor `ε^{−a'b'}`) reduces the
weight to the strong block `A·U_s`, which OWED-2 (`strongBlock_lintegral_lt_top`) shows finite at the
shrunk dims `(b', m)`. NO bordered-Gram. Instantiate at `a' = a−j`, `b' = b−j`, `m = M₂−j` on shell
`S_j`, where `a−j < (M₂−j) − (b−j) + 1 = M₂ − b + 1` is strict at a binding cut. -/
theorem deeperCut_shell_corankWeight_lt_top {a' b' M₂ m n : ℕ} (Z : Matrix (Fin M₂) (Fin n) ℝ)
    (U_s : Matrix (Fin M₂) (Fin m) ℝ) (hUs : U_sᵀ * U_s = 1) (hbm : b' ≤ m) (hmM : m ≤ M₂)
    {ε : ℝ} (hε : 0 < ε)
    (hshell : (Z * Zᵀ - (ε ^ 2) • (U_s * U_sᵀ)).PosSemidef)
    (hconv : (a' : ℝ) < (m : ℝ) - b' + 1) :
    (∫⁻ A in matBox b' M₂ 1,
        ENNReal.ofReal (((Matrix.of A * Z) * (Matrix.of A * Z)ᵀ).det ^ (-(a' : ℝ) / 2))) < ⊤ :=
  lt_of_le_of_lt (uniformWenn_proj_le Z U_s hUs hbm hε hshell)
    (ENNReal.mul_lt_top ENNReal.ofReal_lt_top
      (strongBlock_lintegral_lt_top (a' := (a' : ℝ)) hmM U_s hUs hbm hconv))

/-! ## The per-shell interior bound — freed-corner peel over the corank block on the shell -/

/-- **The per-shell interior corank-integrability bound (Steps 1–3 of the corrected corner-shrink,
chart cert §1).** The shell analog of `corankOffSector_bpos_le`: for a corank block of `b` rows on the
shell `Z Zᵀ ⪰ ε²·(U_s U_sᵀ)` (`U_sᵀ U_s = 1`, `b ≤ m ≤ M₂`, and `m ≤ Z.rank` — which holds on shell
`S_j` at reduced dims `(a,b,m) = (a−j, b−j, M₂−j)`), the freed inner `Γ`-integral (over any domain `sΓ`)
integrated over the free corank block `A_cor ∈ matBox b M₂ 1` is bounded by a finite, `w`-independent
constant times the shifted power of the pivot energy `w`:

    ∫_{A_cor} [ ∫_{Γ∈sΓ} (w + frobSq (Ccross + Γ·(A_cor·Z)))^{−c'} ] dA_cor  ≤  C₁ · w^{−(c'−ab/2)}.

For a.e. `A_cor` the corank block `A_cor·Z` is full row rank `b` (`corank_survival_ae`, `b ≤ Z.rank`), so
the banked corner atom (`corankBlock_morsePeel_setLE`, `Apiv := 0`) drops the core to `w^{−(c'−ab/2)}`
with Gram weight `det((A_cor·Z)(A_cor·Z)ᵀ)^{−a/2}`; the rank-drop locus is null; the shell corank weight
is finite (`deeperCut_shell_corankWeight_lt_top`, the PSD-monotone reduced weight — NOT the full-rank
`corankWeight_bpos_lt_top`). This is the corrected deeper-cut interior leg: the reduced weight converges
via PSD-monotonicity at the `(b, m)` level, NO bordered-Gram.

The constant `C₁ = ofReal(Cresid (a·b) c') · Wenn` is `w`-INDEPENDENT (`Wenn` reads only `Z`), so the
bound is stated in the strong `∃ C₁ < ⊤, ∀ w > 0` form — the `w`-uniform shape the comparator descent
needs (strictly stronger than the banked analog's `∀ w, ∃ C₁`). -/
theorem shell_corankOffSector_le {a b M₂ m n : ℕ} (Z : Matrix (Fin M₂) (Fin n) ℝ)
    (U_s : Matrix (Fin M₂) (Fin m) ℝ) (hUs : U_sᵀ * U_s = 1) (hbm : b ≤ m) (hmM : m ≤ M₂)
    (hmZ : m ≤ Z.rank) {ε : ℝ} (hε : 0 < ε)
    (hshell : (Z * Zᵀ - (ε ^ 2) • (U_s * U_sᵀ)).PosSemidef)
    (Ccross : Matrix (Fin a) (Fin n) ℝ) (c' : ℝ)
    (haM : (a : ℝ) < (m : ℝ) - b + 1) (hc' : (a * b : ℝ) / 2 < c')
    (sΓ : Set (Fin a → Fin b → ℝ)) :
    ∃ C₁ : ℝ≥0∞, C₁ < ⊤ ∧ ∀ w : ℝ, 0 < w →
      ∫⁻ A_cor in matBox b M₂ 1,
          ∫⁻ Γ in sΓ, ENNReal.ofReal
            ((w + frobSq (Ccross + (Matrix.of Γ) * (Matrix.of A_cor * Z))) ^ (-c'))
        ≤ C₁ * ENNReal.ofReal (w ^ (-(c' - (a * b : ℝ) / 2))) := by
  classical
  set Wenn : ℝ≥0∞ := ∫⁻ A in matBox b M₂ 1,
      ENNReal.ofReal (((Matrix.of A * Z) * (Matrix.of A * Z)ᵀ).det ^ (-(a : ℝ) / 2)) with hWdef
  have hWfin : Wenn < ⊤ := deeperCut_shell_corankWeight_lt_top Z U_s hUs hbm hmM hε hshell haM
  refine ⟨ENNReal.ofReal (Cresid (a * b) c') * Wenn,
    ENNReal.mul_lt_top ENNReal.ofReal_lt_top hWfin, ?_⟩
  intro w hw
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
    _ = ENNReal.ofReal (Cresid (a * b) c' * w ^ (-(c' - (a * b : ℝ) / 2))) * Wenn :=
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ = ENNReal.ofReal (Cresid (a * b) c') * Wenn
          * ENNReal.ofReal (w ^ (-(c' - (a * b : ℝ) / 2))) := by
        rw [ENNReal.ofReal_mul (Cresid_nonneg (a * b) c')]; ring

end DLNFibre.DLN.RLCT
