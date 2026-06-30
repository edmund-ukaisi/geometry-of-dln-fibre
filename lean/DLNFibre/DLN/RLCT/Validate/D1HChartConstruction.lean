import DLNFibre.DLN.RLCT.Validate.D1HChartRank

/-!
# `DLNFibre.DLN.RLCT.Validate.D1HChartConstruction` — the concrete D1 chart `Φ`, its derivative
`≃L`, and its smoothness (#230)

The selected-minor chart for the flat, origin-centred DLN loss (`L = 2`). Given the
existentially-chosen invertible `nReg`-minor of the flat Jacobian (`exists_jacFlatL2_minor`, #229) —
selected loss-entry rows `er` and selected flat-coordinate columns `ec` — the chart

    Φ w c = if c ∈ range ec then (the shifted loss entry gⱼ(w) − gⱼ(0)) else w c

(`chartΦ`) carries the selected loss entries onto the `ec`-coordinates and is the identity on the
complement `Wᶜ = (range ec)ᶜ`. Its derivative at `0` is

    DΦ(0) = the `N × N` matrix whose `ec`-rows are the analytic gradients `∇g(0)` (= rows of the
            flat Jacobian) and whose complement-rows are the standard basis covectors,

block-lower-triangular w.r.t. the predicate `c ∈ range ec`: `det DΦ(0) = ±det(minor) · 1 ≠ 0`
(`Matrix.twoBlockTriangular_det`). So `f' := DΦ(0).toContinuousLinearEquivOfDetNeZero` is a genuine
`≃L`, with `HasFDerivAt Φ f' 0` free (the coe is `DΦ(0)` by
`coe_toContinuousLinearEquivOfDetNeZero`).
`Φ` is `ContDiff ℝ 2` (each coordinate is a flat coordinate or an entrywise polynomial loss entry).

**Gate-4 discipline:** the complement `Wᶜ` is the EXISTENTIALLY-CHOSEN complement `(range ec)ᶜ` of
the minor's columns — never a fixed/canonical coordinate complement (a machine-verified `N = 2`
counterexample shows a fixed complement can collapse the determinant). The invertibility of `f'` is
established via `det DΦ(0) ≠ 0` → `toContinuousLinearEquivOfDetNeZero`, NOT via any injection.

STATUS: #230 built sorry-free, axiom-clean. Feeds #231 (wire to `dln_hchart_flat`).
-/

open Matrix Module
open scoped Topology
namespace DLNFibre.DLN.RLCT

variable {H : Fin (2 + 1) → ℕ} {B : Matrix (Fin (H 0)) (Fin (H (Fin.last 2))) ℝ} {v : Params H}
  {m : ℕ} {er : Fin m → Fin (H 0) × Fin (H 2)} {ec : Fin m → Fin (flatDim H)}

/-! ## The chart `Φ`, the shifted loss entries, and the two-branch reduction -/

/-- The shifted loss entry for the `k`-th selected pair: `g_{er k}(w) − g_{er k}(0)`, vanishing at
the flat origin (where `v` is optimal). -/
noncomputable def gShift (H : Fin (2 + 1) → ℕ) (B : Matrix (Fin (H 0)) (Fin (H (Fin.last 2))) ℝ)
    (v : Params H) {m : ℕ} (er : Fin m → Fin (H 0) × Fin (H 2)) (k : Fin m)
    (w : Fin (flatDim H) → ℝ) : ℝ :=
  (prod H (gmapAt H v w) - B) (er k).1 (er k).2
    - (prod H (gmapAt H v 0) - B) (er k).1 (er k).2

/-- **The selected-minor chart** `Φ : ℝ^N → ℝ^N`. A selected coordinate `c = ec k` carries the
shifted loss entry `gShift k`; a complement coordinate is the identity. (The `∑ k, if ec k = c`
indicator form avoids a dependent unique-index inverse; `ec` injective collapses it.) -/
noncomputable def chartΦ (H : Fin (2 + 1) → ℕ)
    (B : Matrix (Fin (H 0)) (Fin (H (Fin.last 2))) ℝ) (v : Params H) {m : ℕ}
    (er : Fin m → Fin (H 0) × Fin (H 2)) (ec : Fin m → Fin (flatDim H))
    (w : Fin (flatDim H) → ℝ) : Fin (flatDim H) → ℝ :=
  fun c => if ∃ k, ec k = c then ∑ k, (if ec k = c then gShift H B v er k w else 0) else w c

/-- On a selected coordinate `ec k₀`, the chart reads the `k₀`-th shifted loss entry. -/
theorem chartΦ_sel (hec : Function.Injective ec) (k₀ : Fin m) (w : Fin (flatDim H) → ℝ) :
    chartΦ H B v er ec w (ec k₀) = gShift H B v er k₀ w := by
  classical
  rw [chartΦ, if_pos ⟨k₀, rfl⟩, Finset.sum_eq_single k₀]
  · rw [if_pos rfl]
  · intro b _ hb; rw [if_neg (fun h => hb (hec h))]
  · intro h; exact absurd (Finset.mem_univ k₀) h

/-- On a complement coordinate, the chart is the identity. -/
theorem chartΦ_compl (c : Fin (flatDim H)) (hc : ¬ ∃ k, ec k = c) (w : Fin (flatDim H) → ℝ) :
    chartΦ H B v er ec w c = w c := by
  rw [chartΦ, if_neg hc]

/-- The chart fixes the origin (`gShift k 0 = 0`, and the complement coords are the identity). -/
theorem chartΦ_zero (hec : Function.Injective ec) :
    chartΦ H B v er ec 0 = 0 := by
  classical
  funext c
  by_cases hc : ∃ k, ec k = c
  · obtain ⟨k, rfl⟩ := hc
    rw [chartΦ_sel hec k, gShift, sub_self]; rfl
  · rw [chartΦ_compl c hc]

/-! ## The per-coordinate derivative and its assembly -/

/-- The per-coordinate derivative CLM of `chartΦ` at `0`: the analytic gradient on a selected
coordinate, the coordinate projection on a complement coordinate. -/
noncomputable def dChartΦcoord (H : Fin (2 + 1) → ℕ)
    (B : Matrix (Fin (H 0)) (Fin (H (Fin.last 2))) ℝ) (v : Params H) {m : ℕ}
    (er : Fin m → Fin (H 0) × Fin (H 2)) (ec : Fin m → Fin (flatDim H))
    (c : Fin (flatDim H)) : (Fin (flatDim H) → ℝ) →L[ℝ] ℝ :=
  if ∃ k, ec k = c then
    ∑ k, (if ec k = c then
        prodAuxEntryDeriv H (gmapAt H v) 0 (fun s a b => gmapDeriv H s a b) 2
          (Nat.lt_succ_self 2) (er k).1 (er k).2
      else 0)
  else ContinuousLinearMap.proj c

/-- The assembled chart derivative CLM `DΦ(0) : ℝ^N →L ℝ^N`. -/
noncomputable def dChartΦ (H : Fin (2 + 1) → ℕ)
    (B : Matrix (Fin (H 0)) (Fin (H (Fin.last 2))) ℝ) (v : Params H) {m : ℕ}
    (er : Fin m → Fin (H 0) × Fin (H 2)) (ec : Fin m → Fin (flatDim H)) :
    (Fin (flatDim H) → ℝ) →L[ℝ] (Fin (flatDim H) → ℝ) :=
  ContinuousLinearMap.pi (dChartΦcoord H B v er ec)

/-- The selected-coordinate derivative is the analytic gradient (the `∑` indicator collapses by
injectivity). -/
theorem dChartΦcoord_sel (hec : Function.Injective ec) (k₀ : Fin m) :
    dChartΦcoord H B v er ec (ec k₀)
      = prodAuxEntryDeriv H (gmapAt H v) 0 (fun s a b => gmapDeriv H s a b) 2
          (Nat.lt_succ_self 2) (er k₀).1 (er k₀).2 := by
  classical
  rw [dChartΦcoord, if_pos ⟨k₀, rfl⟩, Finset.sum_eq_single k₀]
  · rw [if_pos rfl]
  · intro b _ hb; rw [if_neg (fun h => hb (hec h))]
  · intro h; exact absurd (Finset.mem_univ k₀) h

/-- The complement-coordinate derivative is the coordinate projection. -/
theorem dChartΦcoord_compl (c : Fin (flatDim H)) (hc : ¬ ∃ k, ec k = c) :
    dChartΦcoord H B v er ec c = ContinuousLinearMap.proj c := by
  rw [dChartΦcoord, if_neg hc]

/-- **`HasFDerivAt chartΦ dChartΦ 0`** — each coordinate has the named derivative (selected: the
loss-entry gradient `hasStrictFDerivAt_lossEntry`; complement: the coordinate projection), assembled
by `hasFDerivAt_pi`. -/
theorem hasFDerivAt_chartΦ (hec : Function.Injective ec) :
    HasFDerivAt (chartΦ H B v er ec)
      (dChartΦ H B v er ec : (Fin (flatDim H) → ℝ) →L[ℝ] (Fin (flatDim H) → ℝ))
      (0 : Fin (flatDim H) → ℝ) := by
  classical
  rw [dChartΦ, hasFDerivAt_pi]
  intro c
  -- coordinate `c`: `w ↦ chartΦ … w c` has derivative `dChartΦcoord … c`.
  by_cases hc : ∃ k, ec k = c
  · obtain ⟨k₀, rfl⟩ := hc
    rw [dChartΦcoord_sel hec k₀]
    -- the function is `w ↦ chartΦ … w (ec k₀) = gShift k₀ w = (loss entry) − (loss entry at 0)`
    have hfun : (fun w => chartΦ H B v er ec w (ec k₀))
        = fun w => (prod H (gmapAt H v w) - B) (er k₀).1 (er k₀).2
            - (prod H (gmapAt H v 0) - B) (er k₀).1 (er k₀).2 := by
      funext w; rw [chartΦ_sel hec k₀ w]; rfl
    rw [hfun]
    exact (hasStrictFDerivAt_lossEntry H B v 0 (er k₀).1 (er k₀).2).hasFDerivAt.sub_const _
  · rw [dChartΦcoord_compl c hc]
    have hfun : (fun w => chartΦ H B v er ec w c)
        = ⇑(ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin (flatDim H) => ℝ) c) := by
      funext w; rw [chartΦ_compl c hc w, ContinuousLinearMap.proj_apply]
    rw [hfun]
    exact (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin (flatDim H) => ℝ) c).hasFDerivAt

/-! ## The chart derivative matrix and `det ≠ 0` -/

/-- The chart derivative as an `N × N` matrix (`toMatrix'` of `dChartΦ`). -/
noncomputable def dChartΦmat (H : Fin (2 + 1) → ℕ)
    (B : Matrix (Fin (H 0)) (Fin (H (Fin.last 2))) ℝ) (v : Params H) {m : ℕ}
    (er : Fin m → Fin (H 0) × Fin (H 2)) (ec : Fin m → Fin (flatDim H)) :
    Matrix (Fin (flatDim H)) (Fin (flatDim H)) ℝ :=
  LinearMap.toMatrix' (dChartΦ H B v er ec : (Fin (flatDim H) → ℝ) →ₗ[ℝ] (Fin (flatDim H) → ℝ))

/-- A selected row `(ec k₀)` of the chart matrix is the corresponding row of the flat Jacobian. -/
theorem dChartΦmat_sel (hec : Function.Injective ec) (k₀ : Fin m) (c' : Fin (flatDim H)) :
    dChartΦmat H B v er ec (ec k₀) c' = jacFlatL2 H v (er k₀) c' := by
  rw [dChartΦmat, LinearMap.toMatrix'_apply, dChartΦ]
  simp only [ContinuousLinearMap.coe_coe, ContinuousLinearMap.pi_apply]
  rw [dChartΦcoord_sel hec k₀, jacFlatL2_apply_eq_lossEntryDeriv H v (er k₀).1 (er k₀).2 c']

/-- A complement row `c` of the chart matrix is the `c`-th standard basis covector. -/
theorem dChartΦmat_compl (c : Fin (flatDim H)) (hc : ¬ ∃ k, ec k = c) (c' : Fin (flatDim H)) :
    dChartΦmat H B v er ec c c' = (if c = c' then 1 else 0) := by
  rw [dChartΦmat, LinearMap.toMatrix'_apply, dChartΦ]
  simp only [ContinuousLinearMap.coe_coe, ContinuousLinearMap.pi_apply]
  rw [dChartΦcoord_compl c hc, ContinuousLinearMap.proj_apply, Pi.single_apply]

/-- **`det DΦ(0) ≠ 0`.** Block-lower-triangular w.r.t. `p c := c ∈ range ec`
(`Matrix.twoBlockTriangular_det`): the selected block reindexes (via `ec`) to the invertible
`nReg`-minor `jacFlatL2.submatrix er ec`, the complement block is the identity. Hence
`det = ±det(minor) · 1 ≠ 0`. -/
theorem dChartΦmat_det_ne_zero (hec : Function.Injective ec)
    (hminor : ((jacFlatL2 H v).submatrix er ec).det ≠ 0) :
    (dChartΦmat H B v er ec).det ≠ 0 := by
  classical
  set p : Fin (flatDim H) → Prop := fun c => ∃ k, ec k = c with hp
  set M := dChartΦmat H B v er ec with hM
  -- block-lower-triangular
  have hbt : M.det = (M.toSquareBlockProp p).det * (M.toSquareBlockProp (fun c => ¬ p c)).det := by
    apply Matrix.twoBlockTriangular_det M p
    intro i hi j hj
    rw [hM, dChartΦmat_compl i hi, if_neg (fun h => hi (by rw [← h] at hj; exact hj))]
  rw [hbt]
  apply mul_ne_zero
  · -- selected block reindexes (via `ec`) to the invertible minor
    set e : Fin m ≃ {c // p c} :=
      { toFun := fun k => ⟨ec k, ⟨k, rfl⟩⟩
        invFun := fun c => c.2.choose
        left_inv := fun k => hec (Exists.choose_spec (⟨k, rfl⟩ : p (ec k)))
        right_inv := fun c => Subtype.ext c.2.choose_spec } with he
    have key : ((jacFlatL2 H v).submatrix er ec) = (M.toSquareBlockProp p).submatrix e e := by
      ext k l
      simp only [Matrix.submatrix_apply, Matrix.toSquareBlockProp_def, Matrix.of_apply,
        he, Equiv.coe_fn_mk]
      rw [hM, dChartΦmat_sel hec k]
    rw [show (M.toSquareBlockProp p).det = ((jacFlatL2 H v).submatrix er ec).det from by
      rw [key, Matrix.det_submatrix_equiv_self]]
    exact hminor
  · -- complement block = identity
    have heq : M.toSquareBlockProp (fun c => ¬ p c)
        = (1 : Matrix {c // ¬ p c} {c // ¬ p c} ℝ) := by
      ext ⟨a, ha⟩ ⟨b, hb⟩
      rw [Matrix.toSquareBlockProp_def]
      simp only [Matrix.of_apply]
      rw [hM, dChartΦmat_compl a ha b, Matrix.one_apply]
      by_cases h : a = b
      · rw [if_pos h, if_pos (Subtype.ext h)]
      · rw [if_neg h, if_neg (fun he => h (Subtype.ext_iff.mp he))]
    rw [heq, Matrix.det_one]; exact one_ne_zero

/-- `ContinuousLinearMap.det (dChartΦ) ≠ 0` (the CLM determinant ties to the matrix determinant via
`LinearMap.det_toMatrix'`). -/
theorem dChartΦ_det_ne_zero (hec : Function.Injective ec)
    (hminor : ((jacFlatL2 H v).submatrix er ec).det ≠ 0) :
    (dChartΦ H B v er ec).det ≠ 0 := by
  rw [ContinuousLinearMap.det,
    ← LinearMap.det_toMatrix' (dChartΦ H B v er ec : (Fin (flatDim H) → ℝ) →ₗ[ℝ] _)]
  exact dChartΦmat_det_ne_zero hec hminor

/-! ## The chart derivative as a `≃L` -/

/-- **The chart derivative `≃L`** `f' := DΦ(0).toContinuousLinearEquivOfDetNeZero` — a genuine
continuous linear equivalence (from `det DΦ(0) ≠ 0`), whose underlying CLM is definitionally
`dChartΦ`. This is the `f'` the IFT chart-transfer (`dln_hchart_flat`) consumes; the GATE-4
invertible
`f'` comes from the determinant, never from an injection. -/
noncomputable def chartFDerivEquiv (H : Fin (2 + 1) → ℕ)
    (B : Matrix (Fin (H 0)) (Fin (H (Fin.last 2))) ℝ) (v : Params H) {m : ℕ}
    (er : Fin m → Fin (H 0) × Fin (H 2)) (ec : Fin m → Fin (flatDim H))
    (hec : Function.Injective ec) (hminor : ((jacFlatL2 H v).submatrix er ec).det ≠ 0) :
    (Fin (flatDim H) → ℝ) ≃L[ℝ] (Fin (flatDim H) → ℝ) :=
  (dChartΦ H B v er ec).toContinuousLinearEquivOfDetNeZero (dChartΦ_det_ne_zero hec hminor)

/-- The chart `≃L` has underlying CLM `dChartΦ` (definitional via
`coe_toContinuousLinearEquivOfDetNeZero`). -/
theorem chartFDerivEquiv_coe (hec : Function.Injective ec)
    (hminor : ((jacFlatL2 H v).submatrix er ec).det ≠ 0) :
    (chartFDerivEquiv H B v er ec hec hminor : (Fin (flatDim H) → ℝ) →L[ℝ] (Fin (flatDim H) → ℝ))
      = dChartΦ H B v er ec := by
  rw [chartFDerivEquiv, ContinuousLinearMap.coe_toContinuousLinearEquivOfDetNeZero]

/-- **`HasFDerivAt chartΦ (chartFDerivEquiv) 0`** — the chart has the `≃L` `f'` as its derivative at
the origin (the `≃L` coe is `dChartΦ`, the named derivative). -/
theorem hasFDerivAt_chartΦ_equiv (hec : Function.Injective ec)
    (hminor : ((jacFlatL2 H v).submatrix er ec).det ≠ 0) :
    HasFDerivAt (chartΦ H B v er ec)
      (chartFDerivEquiv H B v er ec hec hminor :
        (Fin (flatDim H) → ℝ) →L[ℝ] (Fin (flatDim H) → ℝ))
      (0 : Fin (flatDim H) → ℝ) := by
  rw [chartFDerivEquiv_coe hec hminor]
  exact hasFDerivAt_chartΦ hec

/-! ## Smoothness of the chart -/

/-- **`ContDiff ℝ 2 chartΦ`.** Each coordinate is `C^∞`: a complement coordinate is a coordinate
projection (`contDiff_apply`); a selected coordinate is a finite sum of (loss entry − const), and
the loss entry is entrywise-polynomial (`contDiff_prod_entry`). Assembled by `contDiff_pi`. -/
theorem contDiff_chartΦ :
    ContDiff ℝ 2 (chartΦ H B v er ec) := by
  classical
  rw [contDiff_pi]
  intro c
  -- the loss entries are entrywise `C^∞` (each layer entry is a flat coordinate + const)
  have hprodSmooth : ∀ (i : Fin (H 0)) (j : Fin (H (Fin.last 2))),
      ContDiff ℝ 2 (fun w => prod H (gmapAt H v w) i j) := by
    intro i j
    have hgmap : ∀ (s : Fin 2) (a : Fin (H s.castSucc)) (b : Fin (H s.succ)),
        ContDiff ℝ (⊤ : ℕ∞) (fun w => gmapAt H v w s a b) := by
      intro s a b
      have hcoord : (fun w => gmapAt H v w s a b)
          = fun w : Fin (flatDim H) → ℝ =>
            (w + (paramsEquivFlat H) v) ((Fintype.equivFin (FlatIdx H)) ⟨⟨s, a⟩, b⟩) := by
        funext w; rw [gmapAt]; exact paramsEquivFlat_symm_entry H _ s a b
      rw [hcoord]
      exact (contDiff_apply ℝ _ _).comp (contDiff_id.add contDiff_const)
    refine (contDiff_prod_entry H (gmapAt H v) hgmap i j).of_le ?_
    rw [show (2 : WithTop ℕ∞) = ((2 : ℕ∞) : WithTop ℕ∞) from rfl]
    exact WithTop.coe_le_coe.mpr le_top
  by_cases hc : ∃ k, ec k = c
  · -- selected coordinate: a finite indicator sum of (loss entry − const)
    have hsmooth : ContDiff ℝ 2
        (fun w : Fin (flatDim H) → ℝ =>
          ∑ k, (if ec k = c then gShift H B v er k w else 0)) := by
      apply ContDiff.sum
      intro k _
      by_cases hkc : ec k = c
      · simp only [hkc, if_true]
        -- gShift k = (loss entry)(w) − const, the loss entry is `C^∞`
        have hentry : ContDiff ℝ 2
            (fun w => (prod H (gmapAt H v w) - B) (er k).1 (er k).2) := by
          have hrw : (fun w => (prod H (gmapAt H v w) - B) (er k).1 (er k).2)
              = fun w => prod H (gmapAt H v w) (er k).1 (er k).2
                - B (er k).1 (er k).2 := by
            funext w; rw [Matrix.sub_apply]
          rw [hrw]
          exact (hprodSmooth (er k).1 (er k).2).sub contDiff_const
        exact hentry.sub contDiff_const
      · simp only [hkc, if_false]; exact contDiff_const
    have hfun : (fun w : Fin (flatDim H) → ℝ => chartΦ H B v er ec w c)
        = fun w => ∑ k, (if ec k = c then gShift H B v er k w else 0) := by
      funext w; rw [chartΦ, if_pos hc]
    rw [hfun]; exact hsmooth
  · have hfun : (fun w : Fin (flatDim H) → ℝ => chartΦ H B v er ec w c)
        = fun w : Fin (flatDim H) → ℝ => w c := by
      funext w; exact chartΦ_compl c hc w
    rw [hfun]; exact contDiff_apply ℝ _ c

end DLNFibre.DLN.RLCT
