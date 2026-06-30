import DLNFibre.DLN.RLCT.Validate.D1HChartResidual
import DLNFibre.DLN.RLCT.Validate.D1IFTResidualProducer

/-!
# `DLNFibre.DLN.RLCT.Validate.D1SecondPeelChart` — the D1 SECOND-peel `extraCount` chart producer (L = 2)

The genuinely-open analytic piece of the L = 2 D1 `≥`-leg's TWO-PEEL reduction. The FIRST peel
(`dln_hchart_residual`, banked) charts the DLN loss at a middle-stratum optimal `v` into
`∑_{nReg} s² + ‖q‖²`, leaving the slice residual `R t = ‖q (0,t)‖²` on the complement flat slice
`Y = Fin (flatDim H − nReg) → ℝ`. At a MIDDLE-STRATUM `v` the slice residual `R` still carries
`extra = nReg_v − nReg = extraCount m a b` ADDITIONAL first-order regular directions (the layer ranks
at `v` exceed the deepest rank `r`); the SECOND peel charts THOSE off and lands on the degraded core
`M' = (m−a, m−a−b, m−b)`.

## The verify-first gate VERDICT (2026-06-30, decorrelated Codex xhigh)

The second peel is **BOUNDED at L = 2** — it reuses the SAME bounded selected-minor IFT technique as
the first peel (`dln_hchart_residual`), it does NOT route through `DeepestGaugeChart`'s open #120
gauge-slice wall. The crux (Codex): the SCALAR gradient `∇R(t0)` VANISHES (since `R = ‖h‖²`,
`h(t0) = 0`), so a selected-minor IFT on the scalar `R` is impossible — but the `extra` Morse block of
`R` is exactly FIRST-ORDER rank in `dh(t0)` (`Hess R(t0) = 2·(dh(t0))ᵀ·dh(t0)`). So the bounded route
selects the minor from the residual VECTOR `h = q(0,·)` (a Jacobian-rank condition on the vector), NOT
from the scalar — EXACTLY as the first peel selected its minor from the loss-entry vector `g_{ij}`,
not from the scalar loss `∑ g²`. The `DeepestGaugeChart` #120 wall (rank-`r`-exact pivots,
grouped inter-layer diffeo at the DEEPEST point) feeds the SEPARATE deepest-side gate #44, not this.

## What this module builds (the honest scope)

The abstract, NETWORK-FREE second-peel producer `secondPeel_hchart_residual`: the structural ANALOG of
`dln_hchart_residual`, with the DLN loss-entry vector `g_{ij}` replaced by an abstract `C²` residual
vector `h : Y → EuclideanSpace ℝ (Fin n)` with `h t0 = 0` and a selected invertible `extra`-minor of
its Jacobian at `t0`. It reuses the network-free chart spine of `dln_hchart_residual` (the IFT chart
`Φ`, the right-inverse `Ψsymm`, the split homeomorph, the bump-globalised residual, the RLCT
transfer); only the germ split (`germA`'s analog) is re-derived for the abstract `‖h‖²` loss. Output:
the EXACT `hchart₂` shape `deepest_le_of_optimal_of_iftResidual` consumes.

Scope L = 2 only. The general-L Skeleton sorry `rlctAt_deepest_le_of_optimal` stays #120-walled — NOT
touched. The R1 core value `R1ResolutionInterface` and the germ-nonvanishing `hGne` stay NAMED
hypotheses (this chart enters only `hchart₂`, not the core value).
-/

open Matrix Module MeasureTheory Set Filter
open scoped ENNReal Topology
namespace DLNFibre.DLN.RLCT

/-! ## The abstract second-peel chart producer (network-free, the `dln_hchart_residual` analog)

We chart the slice residual `R = ‖h‖²` of a `C²` residual vector `h : (Fin N → ℝ) → EuclideanSpace ℝ
(Fin n)` vanishing at the basepoint `t0`, with a selected injective `extra`-family of components whose
Jacobian minor at `t0` is invertible. The output is the post-(second-)chart sum-of-squares form. -/

section AbstractChart

variable {N n extra : ℕ}
  (g : (Fin N → ℝ) → EuclideanSpace ℝ (Fin n))
  (eh : Fin extra → Fin n) (ec : Fin extra → Fin N)

/-! ### Sub-build A — the selected-minor chart `Φ` at the ORIGIN (analog of `chartΦ`)

We build the chart for a `C²` map `g` with `g 0 = 0` (the producer pre-translates `h` by `t0` to land
here). The chart carries the `extra` selected components onto the `ec`-coordinates and is the identity
on the complement — EXACTLY the structure of `chartΦ`, centered at the flat origin. -/

/-- The selected residual component for the `k`-th selected pair: `g t (eh k)` (no shift — `g 0 = 0`,
so it vanishes at the origin). -/
def abEntry (k : Fin extra) (t : Fin N → ℝ) : ℝ := g t (eh k)

/-- **The abstract selected-minor chart** `Φ : ℝ^N → ℝ^N`, centered at the origin. A selected
coordinate `c = ec k` carries the selected component `g t (eh k)`; a complement coordinate is the
identity. -/
noncomputable def abChartΦ (t : Fin N → ℝ) : Fin N → ℝ :=
  fun c => if ∃ k, ec k = c then ∑ k, (if ec k = c then abEntry g eh k t else 0) else t c

/-- On a selected coordinate `ec k₀`, the chart reads the `k₀`-th selected component. -/
theorem abChartΦ_sel (hec : Function.Injective ec) (k₀ : Fin extra) (t : Fin N → ℝ) :
    abChartΦ g eh ec t (ec k₀) = abEntry g eh k₀ t := by
  classical
  rw [abChartΦ, if_pos ⟨k₀, rfl⟩, Finset.sum_eq_single k₀]
  · rw [if_pos rfl]
  · intro b _ hb; rw [if_neg (fun hh => hb (hec hh))]
  · intro hmem; exact absurd (Finset.mem_univ k₀) hmem

/-- On a complement coordinate, the chart is the identity. -/
theorem abChartΦ_compl (c : Fin N) (hc : ¬ ∃ k, ec k = c) (t : Fin N → ℝ) :
    abChartΦ g eh ec t c = t c := by
  rw [abChartΦ, if_neg hc]

/-- The chart fixes the origin (`g 0 = 0` ⟹ `abEntry k 0 = 0`; complement coords are the identity). -/
theorem abChartΦ_zero (hec : Function.Injective ec) (hg0 : g 0 = 0) :
    abChartΦ g eh ec 0 = 0 := by
  classical
  funext c
  by_cases hc : ∃ k, ec k = c
  · obtain ⟨k, rfl⟩ := hc
    rw [abChartΦ_sel g eh ec hec k, abEntry, hg0]; rfl
  · rw [abChartΦ_compl g eh ec c hc]

/-! ### Sub-build B — the chart derivative `≃L` at the origin, its `det ≠ 0`, and `C²` smoothness

The chart derivative at `0` is block-lower-triangular w.r.t. `c ∈ range ec`: the selected rows are
the component gradients `D(g·(eh k))(0)`, the complement rows are coordinate projections; the
determinant is `±det(minor)·1 ≠ 0`. Mirrors `dChartΦmat_det_ne_zero` / `chartFDerivEquiv`. -/

/-- The `k`-th selected component `fun t => g t (eh k)` is `C²` (a `proj` of the `C²` `g`). -/
theorem abEntry_contDiff (hgCD : ContDiff ℝ 2 g) (k : Fin extra) :
    ContDiff ℝ 2 (fun t => g t (eh k)) :=
  (contDiff_euclidean.mp hgCD) (eh k)

/-- The `k`-th selected component has the named `fderiv` at every point (from differentiability). -/
theorem hasFDerivAt_abEntry (hgCD : ContDiff ℝ 2 g) (k : Fin extra) (t : Fin N → ℝ) :
    HasFDerivAt (fun t => g t (eh k)) (fderiv ℝ (fun t => g t (eh k)) t) t :=
  ((abEntry_contDiff g eh hgCD k).differentiable (by norm_num)).differentiableAt.hasFDerivAt

/-- The per-coordinate derivative CLM of `abChartΦ` at `0`: the component gradient on a selected
coordinate, the coordinate projection on a complement coordinate. -/
noncomputable def dAbChartΦcoord (c : Fin N) : (Fin N → ℝ) →L[ℝ] ℝ :=
  if ∃ k, ec k = c then
    ∑ k, (if ec k = c then fderiv ℝ (fun t => g t (eh k)) (0 : Fin N → ℝ) else 0)
  else ContinuousLinearMap.proj c

/-- The assembled chart derivative CLM `DΦ(0) : ℝ^N →L ℝ^N`. -/
noncomputable def dAbChartΦ : (Fin N → ℝ) →L[ℝ] (Fin N → ℝ) :=
  ContinuousLinearMap.pi (dAbChartΦcoord g eh ec)

/-- The selected-coordinate derivative is the component gradient (injectivity collapses the sum). -/
theorem dAbChartΦcoord_sel (hec : Function.Injective ec) (k₀ : Fin extra) :
    dAbChartΦcoord g eh ec (ec k₀) = fderiv ℝ (fun t => g t (eh k₀)) (0 : Fin N → ℝ) := by
  classical
  rw [dAbChartΦcoord, if_pos ⟨k₀, rfl⟩, Finset.sum_eq_single k₀]
  · rw [if_pos rfl]
  · intro b _ hb; rw [if_neg (fun hh => hb (hec hh))]
  · intro hmem; exact absurd (Finset.mem_univ k₀) hmem

/-- The complement-coordinate derivative is the coordinate projection. -/
theorem dAbChartΦcoord_compl (c : Fin N) (hc : ¬ ∃ k, ec k = c) :
    dAbChartΦcoord g eh ec c = ContinuousLinearMap.proj c := by
  rw [dAbChartΦcoord, if_neg hc]

/-- **`HasFDerivAt abChartΦ dAbChartΦ 0`** — each coordinate has the named derivative, assembled by
`hasFDerivAt_pi`. -/
theorem hasFDerivAt_abChartΦ (hgCD : ContDiff ℝ 2 g) (hec : Function.Injective ec) :
    HasFDerivAt (abChartΦ g eh ec)
      (dAbChartΦ g eh ec : (Fin N → ℝ) →L[ℝ] (Fin N → ℝ)) (0 : Fin N → ℝ) := by
  classical
  rw [dAbChartΦ, hasFDerivAt_pi]
  intro c
  by_cases hc : ∃ k, ec k = c
  · obtain ⟨k₀, rfl⟩ := hc
    rw [dAbChartΦcoord_sel g eh ec hec k₀]
    have hfun : (fun t => abChartΦ g eh ec t (ec k₀)) = fun t => g t (eh k₀) := by
      funext t; rw [abChartΦ_sel g eh ec hec k₀ t]; rfl
    rw [hfun]; exact hasFDerivAt_abEntry g eh hgCD k₀ 0
  · rw [dAbChartΦcoord_compl g eh ec c hc]
    have hfun : (fun t => abChartΦ g eh ec t c)
        = ⇑(ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin N => ℝ) c) := by
      funext t; rw [abChartΦ_compl g eh ec c hc t, ContinuousLinearMap.proj_apply]
    rw [hfun]
    exact (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin N => ℝ) c).hasFDerivAt

/-- The chart derivative as an `N × N` matrix (`toMatrix'` of `dAbChartΦ`). -/
noncomputable def dAbChartΦmat : Matrix (Fin N) (Fin N) ℝ :=
  LinearMap.toMatrix' (dAbChartΦ g eh ec : (Fin N → ℝ) →ₗ[ℝ] (Fin N → ℝ))

/-- A selected row `(ec k₀)` of the chart matrix is the component gradient at `0`, read coordinatewise
as `(D (g·(eh k₀))(0)) (Pi.single c' 1)` — exactly the `hminor`-minor's row entries. -/
theorem dAbChartΦmat_sel (hec : Function.Injective ec) (k₀ : Fin extra) (c' : Fin N) :
    dAbChartΦmat g eh ec (ec k₀) c'
      = (fderiv ℝ (fun t => g t (eh k₀)) (0 : Fin N → ℝ)) (Pi.single c' 1) := by
  rw [dAbChartΦmat, LinearMap.toMatrix'_apply, dAbChartΦ]
  simp only [ContinuousLinearMap.coe_coe, ContinuousLinearMap.pi_apply]
  rw [dAbChartΦcoord_sel g eh ec hec k₀]

/-- A complement row `c` of the chart matrix is the `c`-th standard basis covector. -/
theorem dAbChartΦmat_compl (c : Fin N) (hc : ¬ ∃ k, ec k = c) (c' : Fin N) :
    dAbChartΦmat g eh ec c c' = (if c = c' then 1 else 0) := by
  rw [dAbChartΦmat, LinearMap.toMatrix'_apply, dAbChartΦ]
  simp only [ContinuousLinearMap.coe_coe, ContinuousLinearMap.pi_apply]
  rw [dAbChartΦcoord_compl g eh ec c hc, ContinuousLinearMap.proj_apply, Pi.single_apply]

/-- **`det DΦ(0) ≠ 0`** from the invertible `extra`-minor. Block-lower-triangular w.r.t. `c ∈ range
ec`: the selected block reindexes (via `ec`) to the minor `of (fun k k' => D(g·(eh k))(0)(single (ec
k') 1))`, the complement block is the identity. -/
theorem dAbChartΦmat_det_ne_zero (hec : Function.Injective ec)
    (hminor : (Matrix.of (fun k k' : Fin extra =>
      (fderiv ℝ (fun t => g t (eh k)) (0 : Fin N → ℝ)) (Pi.single (ec k') 1))).det ≠ 0) :
    (dAbChartΦmat g eh ec).det ≠ 0 := by
  classical
  set p : Fin N → Prop := fun c => ∃ k, ec k = c with hp
  set M := dAbChartΦmat g eh ec with hM
  have hbt : M.det = (M.toSquareBlockProp p).det * (M.toSquareBlockProp (fun c => ¬ p c)).det := by
    apply Matrix.twoBlockTriangular_det M p
    intro i hi j hj
    rw [hM, dAbChartΦmat_compl g eh ec i hi, if_neg (fun hh => hi (by rw [← hh] at hj; exact hj))]
  rw [hbt]
  apply mul_ne_zero
  · set e : Fin extra ≃ {c // p c} :=
      { toFun := fun k => ⟨ec k, ⟨k, rfl⟩⟩
        invFun := fun c => c.2.choose
        left_inv := fun k => hec (Exists.choose_spec (⟨k, rfl⟩ : p (ec k)))
        right_inv := fun c => Subtype.ext c.2.choose_spec } with he
    have key : (Matrix.of (fun k k' : Fin extra =>
        (fderiv ℝ (fun t => g t (eh k)) (0 : Fin N → ℝ)) (Pi.single (ec k') 1)))
        = (M.toSquareBlockProp p).submatrix e e := by
      ext k l
      simp only [Matrix.submatrix_apply, Matrix.toSquareBlockProp_def, Matrix.of_apply,
        he, Equiv.coe_fn_mk]
      rw [hM, dAbChartΦmat_sel g eh ec hec k]
    rw [show (M.toSquareBlockProp p).det = (Matrix.of (fun k k' : Fin extra =>
        (fderiv ℝ (fun t => g t (eh k)) (0 : Fin N → ℝ)) (Pi.single (ec k') 1))).det from by
      rw [key, Matrix.det_submatrix_equiv_self]]
    exact hminor
  · have heq : M.toSquareBlockProp (fun c => ¬ p c)
        = (1 : Matrix {c // ¬ p c} {c // ¬ p c} ℝ) := by
      ext ⟨a, ha⟩ ⟨b, hb⟩
      rw [Matrix.toSquareBlockProp_def]
      simp only [Matrix.of_apply]
      rw [hM, dAbChartΦmat_compl g eh ec a ha b, Matrix.one_apply]
      by_cases hh : a = b
      · rw [if_pos hh, if_pos (Subtype.ext hh)]
      · rw [if_neg hh, if_neg (fun he2 => hh (Subtype.ext_iff.mp he2))]
    rw [heq, Matrix.det_one]; exact one_ne_zero

/-- `ContinuousLinearMap.det (dAbChartΦ) ≠ 0`. -/
theorem dAbChartΦ_det_ne_zero (hec : Function.Injective ec)
    (hminor : (Matrix.of (fun k k' : Fin extra =>
      (fderiv ℝ (fun t => g t (eh k)) (0 : Fin N → ℝ)) (Pi.single (ec k') 1))).det ≠ 0) :
    (dAbChartΦ g eh ec).det ≠ 0 := by
  rw [ContinuousLinearMap.det,
    ← LinearMap.det_toMatrix' (dAbChartΦ g eh ec : (Fin N → ℝ) →ₗ[ℝ] _)]
  exact dAbChartΦmat_det_ne_zero g eh ec hec hminor

/-- **The chart derivative `≃L`** `f' := DΦ(0).toContinuousLinearEquivOfDetNeZero`, coe `= dAbChartΦ`. -/
noncomputable def abChartFDerivEquiv (hec : Function.Injective ec)
    (hminor : (Matrix.of (fun k k' : Fin extra =>
      (fderiv ℝ (fun t => g t (eh k)) (0 : Fin N → ℝ)) (Pi.single (ec k') 1))).det ≠ 0) :
    (Fin N → ℝ) ≃L[ℝ] (Fin N → ℝ) :=
  (dAbChartΦ g eh ec).toContinuousLinearEquivOfDetNeZero (dAbChartΦ_det_ne_zero g eh ec hec hminor)

/-- The chart `≃L` has underlying CLM `dAbChartΦ`. -/
theorem abChartFDerivEquiv_coe (hec : Function.Injective ec)
    (hminor : (Matrix.of (fun k k' : Fin extra =>
      (fderiv ℝ (fun t => g t (eh k)) (0 : Fin N → ℝ)) (Pi.single (ec k') 1))).det ≠ 0) :
    (abChartFDerivEquiv g eh ec hec hminor : (Fin N → ℝ) →L[ℝ] (Fin N → ℝ))
      = dAbChartΦ g eh ec := by
  rw [abChartFDerivEquiv, ContinuousLinearMap.coe_toContinuousLinearEquivOfDetNeZero]

/-- **`HasFDerivAt abChartΦ (abChartFDerivEquiv) 0`** — the chart has the `≃L` as its derivative. -/
theorem hasFDerivAt_abChartΦ_equiv (hgCD : ContDiff ℝ 2 g) (hec : Function.Injective ec)
    (hminor : (Matrix.of (fun k k' : Fin extra =>
      (fderiv ℝ (fun t => g t (eh k)) (0 : Fin N → ℝ)) (Pi.single (ec k') 1))).det ≠ 0) :
    HasFDerivAt (abChartΦ g eh ec)
      (abChartFDerivEquiv g eh ec hec hminor : (Fin N → ℝ) →L[ℝ] (Fin N → ℝ))
      (0 : Fin N → ℝ) := by
  rw [abChartFDerivEquiv_coe g eh ec hec hminor]
  exact hasFDerivAt_abChartΦ g eh ec hgCD hec

/-- **`ContDiff ℝ 2 abChartΦ`.** Each coordinate is `C²`: complement = projection, selected = the
`C²` component `g·(eh k)`. -/
theorem contDiff_abChartΦ (hgCD : ContDiff ℝ 2 g) :
    ContDiff ℝ 2 (abChartΦ g eh ec) := by
  classical
  rw [contDiff_pi]
  intro c
  by_cases hc : ∃ k, ec k = c
  · have hsmooth : ContDiff ℝ 2 (fun t : Fin N → ℝ =>
        ∑ k, (if ec k = c then abEntry g eh k t else 0)) := by
      apply ContDiff.sum
      intro k _
      by_cases hkc : ec k = c
      · simp only [hkc, if_true]; exact abEntry_contDiff g eh hgCD k
      · simp only [hkc, if_false]; exact contDiff_const
    have hfun : (fun t : Fin N → ℝ => abChartΦ g eh ec t c)
        = fun t => ∑ k, (if ec k = c then abEntry g eh k t else 0) := by
      funext t; rw [abChartΦ, if_pos hc]
    rw [hfun]; exact hsmooth
  · have hfun : (fun t : Fin N → ℝ => abChartΦ g eh ec t c) = fun t : Fin N → ℝ => t c := by
      funext t; exact abChartΦ_compl g eh ec c hc t
    rw [hfun]; exact contDiff_apply ℝ _ c

/-! ### Sub-build C — the abstract split homeomorph `ℝ^N ≃ₜ ℝ^extra × ℝ^(N−extra)`

The measure-preserving reindex separating the selected `ec`-columns from the complement. Generic in
the index `Fin N` — the same construction as `splitHomeo`, re-instantiated. -/

/-- The selected-membership predicate on `Fin N` coordinates. -/
def abSelPred (ec : Fin extra → Fin N) : Fin N → Prop := fun c => ∃ k, ec k = c

instance instDecidableAbSelPred (ec : Fin extra → Fin N) : DecidablePred (abSelPred ec) :=
  fun c => Fintype.decidableExistsFintype

/-- `ec` injective reindexes the SELECTED subtype onto `Fin extra`. -/
noncomputable def abSelEquiv (hec : Function.Injective ec) :
    Fin extra ≃ {c : Fin N // abSelPred ec c} where
  toFun k := ⟨ec k, ⟨k, rfl⟩⟩
  invFun c := c.2.choose
  left_inv k := hec (Exists.choose_spec (⟨k, rfl⟩ : abSelPred ec (ec k)))
  right_inv c := Subtype.ext c.2.choose_spec

/-- The COMPLEMENT subtype has cardinality `N − extra`. -/
theorem abCard_complSub (hec : Function.Injective ec) :
    Fintype.card {c : Fin N // ¬ abSelPred ec c} = N - extra := by
  classical
  rw [Fintype.card_subtype_compl]
  have hsel : Fintype.card {c : Fin N // abSelPred ec c} = extra := by
    rw [← Fintype.card_congr (abSelEquiv ec hec), Fintype.card_fin]
  rw [hsel, Fintype.card_fin]

/-- Reindex the COMPLEMENT subtype to `Fin (N − extra)`. -/
noncomputable def abComplEquiv (hec : Function.Injective ec) :
    Fin (N - extra) ≃ {c : Fin N // ¬ abSelPred ec c} :=
  (finCongr (abCard_complSub ec hec).symm).trans (Fintype.equivFin _).symm

/-- **The abstract split homeomorph** `ℝ^N ≃ₜ ℝ^extra × ℝ^(N−extra)`. -/
noncomputable def abSplitHomeo (hec : Function.Injective ec) :
    (Fin N → ℝ) ≃ₜ ((Fin extra → ℝ) × (Fin (N - extra) → ℝ)) :=
  (Homeomorph.piEquivPiSubtypeProd (abSelPred ec) (fun _ => ℝ)).trans
    ((Homeomorph.piCongrLeft (Y := fun _ : {c // abSelPred ec c} => ℝ)
        (abSelEquiv ec hec)).symm.prodCongr
      (Homeomorph.piCongrLeft (Y := fun _ : {c // ¬ abSelPred ec c} => ℝ)
        (abComplEquiv ec hec)).symm)

/-- The selected slot `k` of `abSplitHomeo` reads the `ec k` coordinate. -/
theorem abSplitHomeo_fst_apply (hec : Function.Injective ec) (w : Fin N → ℝ) (k : Fin extra) :
    (abSplitHomeo ec hec w).1 k = w (ec k) := by
  simp only [abSplitHomeo, Homeomorph.trans_apply, Homeomorph.coe_prodCongr, Prod.map_apply,
    Homeomorph.piCongrLeft_symm_apply]
  rfl

/-- `abSplitHomeo` is measure-preserving. -/
theorem abSplitHomeo_mp (hec : Function.Injective ec) :
    MeasurePreserving (abSplitHomeo ec hec) (volume : Measure (Fin N → ℝ)) volume := by
  have hA : MeasurePreserving
      ⇑(MeasurableEquiv.piCongrLeft (fun _ : {c // abSelPred ec c} => ℝ) (abSelEquiv ec hec)).symm
      volume volume :=
    MeasurePreserving.symm _
      (volume_measurePreserving_piCongrLeft (fun _ : {c // abSelPred ec c} => ℝ)
        (abSelEquiv ec hec))
  have hB : MeasurePreserving
      ⇑(MeasurableEquiv.piCongrLeft (fun _ : {c // ¬ abSelPred ec c} => ℝ)
        (abComplEquiv ec hec)).symm volume volume :=
    MeasurePreserving.symm _
      (volume_measurePreserving_piCongrLeft (fun _ : {c // ¬ abSelPred ec c} => ℝ)
        (abComplEquiv ec hec))
  have hpiv := volume_preserving_piEquivPiSubtypeProd (fun _ : Fin N => ℝ) (abSelPred ec)
  exact (hA.prod hB).comp hpiv

/-- `abSplitHomeo` is a measurable embedding. -/
theorem abSplitHomeo_emb (hec : Function.Injective ec) :
    MeasurableEmbedding (abSplitHomeo ec hec) :=
  (abSplitHomeo ec hec).measurableEmbedding

/-- `abSplitHomeo.symm` is `C^∞`. -/
theorem contDiff_abSplitHomeo_symm (hec : Function.Injective ec) :
    ContDiff ℝ (⊤ : ℕ∞) (abSplitHomeo ec hec).symm := by
  classical
  rw [contDiff_pi]
  intro c
  have hfun : (fun p : (Fin extra → ℝ) × (Fin (N - extra) → ℝ) => (abSplitHomeo ec hec).symm p c)
      = fun p => if hc : abSelPred ec c then p.1 ((abSelEquiv ec hec).symm ⟨c, hc⟩)
          else p.2 ((abComplEquiv ec hec).symm ⟨c, hc⟩) := by
    funext p
    simp only [abSplitHomeo, Homeomorph.symm_trans_apply, Homeomorph.prodCongr_symm,
      Homeomorph.symm_symm, Homeomorph.coe_prodCongr,
      Homeomorph.piEquivPiSubtypeProd_symm_apply, Prod.map_fst, Prod.map_snd,
      Homeomorph.piCongrLeft_apply, Equiv.piCongrLeft, Equiv.piCongrLeft'_symm,
      Equiv.symm_symm, Equiv.piCongrLeft'_apply]
  rw [hfun]
  by_cases hc : abSelPred ec c
  · simp only [dif_pos hc]
    exact (contDiff_apply ℝ _ ((abSelEquiv ec hec).symm ⟨c, hc⟩)).comp contDiff_fst
  · simp only [dif_neg hc]
    exact (contDiff_apply ℝ _ ((abComplEquiv ec hec).symm ⟨c, hc⟩)).comp contDiff_snd

/-! ### Sub-build D — the germ split and the residual vector (analog of `germA` / `rawResidVec`)

`R = ∑ g i²` near `0`, pulled back along the chart inverse `Ψsymm`, splits as `∑_k (w(ec k))²` (the
selected components, straightened to coordinates) plus `∑_i (residual i)²` (the rest). -/

/-- The selected-component predicate on `Fin n`: `i` is one of the `eh`-images. -/
def abSelComp (eh : Fin extra → Fin n) : Fin n → Prop := fun i => ∃ k, eh k = i

instance instDecidableAbSelComp (eh : Fin extra → Fin n) : DecidablePred (abSelComp eh) :=
  fun _ => Fintype.decidableExistsFintype

/-- **The selected/residual sum split** (`eh` injective). For any `f`, the full sum splits as the
selected `eh`-components (reindexed by `k`) plus the zeroed-selected residual. -/
theorem abSum_split_selected (heh : Function.Injective eh) (f : Fin n → ℝ) :
    ∑ i : Fin n, f i
      = (∑ k : Fin extra, f (eh k))
        + ∑ i : Fin n, (if abSelComp eh i then 0 else f i) := by
  classical
  set S : Finset (Fin n) := Finset.image eh Finset.univ with hS
  have hsel_mem : ∀ i, i ∈ S ↔ abSelComp eh i := by
    intro i; rw [hS, Finset.mem_image]
    constructor
    · rintro ⟨k, _, rfl⟩; exact ⟨k, rfl⟩
    · rintro ⟨k, rfl⟩; exact ⟨k, Finset.mem_univ k, rfl⟩
  have hsumS : ∑ i ∈ S, f i = ∑ k : Fin extra, f (eh k) := by
    rw [hS, Finset.sum_image (fun a _ b _ hh => heh hh)]
  have hresid : ∑ i : Fin n, (if abSelComp eh i then 0 else f i) = ∑ i ∈ Sᶜ, f i := by
    rw [← Finset.sum_compl_add_sum S (fun i => if abSelComp eh i then 0 else f i)]
    have hSpart : ∑ i ∈ S, (if abSelComp eh i then 0 else f i) = 0 := by
      apply Finset.sum_eq_zero; intro i hi; rw [if_pos ((hsel_mem i).mp hi)]
    rw [hSpart, add_zero]
    apply Finset.sum_congr rfl; intro i hi
    have hnot : ¬ abSelComp eh i := fun hh => (Finset.mem_compl.mp hi) ((hsel_mem i).mpr hh)
    rw [if_neg hnot]
  rw [hresid, ← hsumS, add_comm (∑ i ∈ S, f i) (∑ i ∈ Sᶜ, f i)]
  exact (Finset.sum_compl_add_sum S f).symm

/-- The RAW residual component vector `g ∘ Ψsymm`, ZEROED on the selected `eh`-components. -/
noncomputable def abRawResid (g : (Fin N → ℝ) → EuclideanSpace ℝ (Fin n))
    (eh : Fin extra → Fin n) (Ψsymm : (Fin N → ℝ) → (Fin N → ℝ))
    (w : Fin N → ℝ) (i : Fin n) : ℝ :=
  if abSelComp eh i then 0 else g (Ψsymm w) i

/-- The selected component germ: near `0`, the `k`-th selected component composed with `Ψsymm` reads
the `ec k` coordinate (`g 0 = 0` ⟹ no shift). -/
theorem abSelected_germ (hg0 : g 0 = 0) (hec : Function.Injective ec)
    (Ψsymm : (Fin N → ℝ) → (Fin N → ℝ))
    (hrinv : ∀ᶠ w in 𝓝 (0 : Fin N → ℝ), abChartΦ g eh ec (Ψsymm w) = w) (k : Fin extra) :
    ∀ᶠ w in 𝓝 (0 : Fin N → ℝ), g (Ψsymm w) (eh k) = w (ec k) := by
  filter_upwards [hrinv] with w hw
  have h1 : abChartΦ g eh ec (Ψsymm w) (ec k) = w (ec k) := by rw [hw]
  rwa [abChartΦ_sel g eh ec hec k, abEntry] at h1

/-- **Germ A — the abstract loss decomposition.** Near `0`, `R ∘ Ψsymm = ∑_k (w(ec k))² + ∑_i
(abRawResid w i)²`. -/
theorem abGermA (hg0 : g 0 = 0) (heh : Function.Injective eh) (hec : Function.Injective ec)
    (Ψsymm : (Fin N → ℝ) → (Fin N → ℝ))
    (hrinv : ∀ᶠ w in 𝓝 (0 : Fin N → ℝ), abChartΦ g eh ec (Ψsymm w) = w) :
    (fun w => ∑ i, g (Ψsymm w) i ^ 2) =ᶠ[𝓝 (0 : Fin N → ℝ)]
      fun w => (∑ k : Fin extra, (w (ec k)) ^ 2)
        + ∑ i : Fin n, (abRawResid g eh Ψsymm w i) ^ 2 := by
  classical
  have hsel : ∀ k : Fin extra, ∀ᶠ w in 𝓝 (0 : Fin N → ℝ), g (Ψsymm w) (eh k) = w (ec k) :=
    fun k => abSelected_germ g eh ec hg0 hec Ψsymm hrinv k
  filter_upwards [Filter.eventually_all.2 hsel] with w hw
  rw [abSum_split_selected eh heh (fun i => (g (Ψsymm w) i) ^ 2)]
  congr 1
  · apply Finset.sum_congr rfl; intro k _; rw [hw k]
  · apply Finset.sum_congr rfl; intro i _
    rw [abRawResid]
    by_cases hsr : abSelComp eh i
    · rw [if_pos hsr, if_pos hsr]; norm_num
    · rw [if_neg hsr, if_neg hsr]

/-- The RAW residual as an `EuclideanSpace`-valued vector on `Fin N → ℝ` (selected slots zeroed). -/
noncomputable def abRawResidVec (g : (Fin N → ℝ) → EuclideanSpace ℝ (Fin n))
    (eh : Fin extra → Fin n) (Ψsymm : (Fin N → ℝ) → (Fin N → ℝ))
    (w : Fin N → ℝ) : EuclideanSpace ℝ (Fin n) :=
  WithLp.toLp 2 (fun i => abRawResid g eh Ψsymm w i)

/-- The `i`-th coordinate of `abRawResidVec` is the raw residual at `i`. -/
theorem abRawResidVec_apply (g : (Fin N → ℝ) → EuclideanSpace ℝ (Fin n))
    (eh : Fin extra → Fin n) (Ψsymm : (Fin N → ℝ) → (Fin N → ℝ))
    (w : Fin N → ℝ) (i : Fin n) :
    abRawResidVec g eh Ψsymm w i = abRawResid g eh Ψsymm w i := rfl

/-- On the open set `V` where `Ψsymm` is `C²`, the raw residual vector is `C²`. -/
theorem contDiffOn_abRawResidVec (hgCD : ContDiff ℝ 2 g)
    (Ψsymm : (Fin N → ℝ) → (Fin N → ℝ)) {V : Set (Fin N → ℝ)}
    (hsymmCD : ContDiffOn ℝ 2 Ψsymm V) :
    ContDiffOn ℝ 2 (abRawResidVec g eh Ψsymm) V := by
  classical
  rw [contDiffOn_euclidean]
  intro i
  have hcoord : (fun w => abRawResidVec g eh Ψsymm w i)
      = fun w => if abSelComp eh i then 0 else g (Ψsymm w) i := by
    funext w; rw [abRawResidVec_apply, abRawResid]
  rw [hcoord]
  by_cases hsr : abSelComp eh i
  · simp only [if_pos hsr]; exact contDiffOn_const
  · simp only [if_neg hsr]
    -- `(g · i) ∘ Ψsymm`: outer `C²` (component of `C²` `g`), inner `Ψsymm` `C²` on `V`.
    have houter : ContDiff ℝ 2 (fun w' => g w' i) := (contDiff_euclidean.mp hgCD) i
    exact houter.comp_contDiffOn hsymmCD

end AbstractChart

/-! ### Sub-build E — the centered chart assembly (analog of `dln_hchart_residual`'s body)

The CENTERED case (`g 0 = 0`, chart at the origin). Assembles: the IFT chart `Φ` + right-inverse
`Ψsymm`, the germ split `abGermA`, the bump-globalised residual, and the MP split-homeomorph reindex
— EXACTLY the spine of `dln_hchart_residual`. -/

/-- **The centered abstract second-peel producer.** For a `C²` residual vector `g` with `g 0 = 0` and
a selected invertible `extra`-minor at `0`, the local RLCT of `R = ∑ g i²` at `0` equals the
post-chart `∑ s² + ‖q₂‖²` shape on `ℝ^extra × ℝ^(N−extra)` for a GLOBAL `C¹` residual `q₂`. -/
theorem secondPeel_hchart_residual_zero {N n extra : ℕ}
    (g : (Fin N → ℝ) → EuclideanSpace ℝ (Fin n))
    (hgCD : ContDiff ℝ 2 g) (hg0 : g 0 = 0)
    (eh : Fin extra → Fin n) (ec : Fin extra → Fin N)
    (heh : Function.Injective eh) (hec : Function.Injective ec)
    (hminor : (Matrix.of (fun k k' : Fin extra =>
      (fderiv ℝ (fun t => g t (eh k)) (0 : Fin N → ℝ)) (Pi.single (ec k') 1))).det ≠ 0) :
    ∃ (q₂ : (Fin extra → ℝ) × (Fin (N - extra) → ℝ) → EuclideanSpace ℝ (Fin n))
      (t0₂ : Fin (N - extra) → ℝ),
      ContDiff ℝ 1 q₂ ∧
      rlctAtOn (fun t : Fin N → ℝ => ∑ i, g t i ^ 2) (0 : Fin N → ℝ)
        = rlctAtOn (fun p : (Fin extra → ℝ) × (Fin (N - extra) → ℝ) =>
            (∑ i, p.1 i ^ 2) + (∑ i, q₂ p i ^ 2)) ((0 : Fin extra → ℝ), t0₂) := by
  classical
  -- the concrete chart `Φ`, its `≃L` derivative, smoothness, fix.
  set Φ : (Fin N → ℝ) → (Fin N → ℝ) := abChartΦ g eh ec with hΦdef
  set f' : (Fin N → ℝ) ≃L[ℝ] (Fin N → ℝ) := abChartFDerivEquiv g eh ec hec hminor with hf'def
  have hΦcd : ContDiff ℝ 2 Φ := contDiff_abChartΦ g eh ec hgCD
  have hΦ' : HasFDerivAt Φ (f' : (Fin N → ℝ) →L[ℝ] (Fin N → ℝ)) 0 :=
    hasFDerivAt_abChartΦ_equiv g eh ec hgCD hec hminor
  have hfix : Φ 0 = 0 := abChartΦ_zero g eh ec hec hg0
  -- the right-inverse chart `Ψsymm`, `V` open ∋ 0, `Ψsymm` `C²` on `V`, the germ + RLCT transfer.
  obtain ⟨Ψsymm, V, hVopen, hwV, hsymmCD, hrinv, hrlcttransfer⟩ :=
    rlctAtOn_eq_of_contDiff_chart_rinv (fun t => ∑ i, g t i ^ 2) Φ 0 f' hΦcd hΦ' hfix
  -- the residual vector, `C²` on `V`.
  have hgCDres : ContDiffOn ℝ 2 (abRawResidVec g eh Ψsymm) V :=
    contDiffOn_abRawResidVec g eh hgCD Ψsymm hsymmCD
  -- transport to the product space.
  set U : Set ((Fin extra → ℝ) × (Fin (N - extra) → ℝ)) := abSplitHomeo ec hec '' V with hUdef
  have hUopen : IsOpen U := (abSplitHomeo ec hec).isOpenMap V hVopen
  set w0 : (Fin extra → ℝ) × (Fin (N - extra) → ℝ) := abSplitHomeo ec hec 0 with hw0def
  have hw0U : w0 ∈ U := ⟨0, hwV, rfl⟩
  have hmapsto : Set.MapsTo (abSplitHomeo ec hec).symm U V := by
    rintro p ⟨w, hwV', rfl⟩
    rw [Homeomorph.symm_apply_apply]; exact hwV'
  have hsymmContDiff2 : ContDiff ℝ 2 (abSplitHomeo ec hec).symm := by
    refine (contDiff_abSplitHomeo_symm ec hec).of_le ?_
    rw [show (2 : WithTop ℕ∞) = ((2 : ℕ∞) : WithTop ℕ∞) from rfl]
    exact WithTop.coe_le_coe.mpr le_top
  have hg1CD : ContDiffOn ℝ 2
      (fun p => abRawResidVec g eh Ψsymm ((abSplitHomeo ec hec).symm p)) U :=
    hgCDres.comp (hsymmContDiff2.contDiffOn (s := U)) hmapsto
  -- bump-globalise: `q₂` global `C¹`, `=ᶠ` near `w0`.
  obtain ⟨q₂, hq₂CD, hq₂eq⟩ :=
    exists_contDiff_eventuallyEq_of_contDiffOn (n := 1) hUopen hw0U (hg1CD.of_le (by norm_num))
  refine ⟨q₂, w0.2, hq₂CD, ?_⟩
  -- the engine post-chart loss `F`.
  set F : (Fin extra → ℝ) × (Fin (N - extra) → ℝ) → ℝ :=
    fun p => (∑ i, p.1 i ^ 2) + (∑ i, q₂ p i ^ 2) with hFdef
  -- KEY germ: `F ∘ abSplitHomeo =ᶠ[𝓝 0] R ∘ Ψsymm`.
  have hkey : (fun w => F (abSplitHomeo ec hec w)) =ᶠ[𝓝 (0 : Fin N → ℝ)]
      fun w => ∑ i, g (Ψsymm w) i ^ 2 := by
    have hqpull : (fun w => q₂ (abSplitHomeo ec hec w)) =ᶠ[𝓝 (0 : Fin N → ℝ)]
        fun w => abRawResidVec g eh Ψsymm w := by
      have hcont : ContinuousAt (abSplitHomeo ec hec) 0 :=
        (abSplitHomeo ec hec).continuous.continuousAt
      have := hcont.eventually hq₂eq
      filter_upwards [this] with w hw
      rw [hw, Homeomorph.symm_apply_apply]
    have hgA := abGermA g eh ec hg0 heh hec Ψsymm hrinv
    filter_upwards [hqpull, hgA] with w hwq hwA
    show (∑ i, (abSplitHomeo ec hec w).1 i ^ 2) + (∑ i, q₂ (abSplitHomeo ec hec w) i ^ 2)
      = ∑ i, g (Ψsymm w) i ^ 2
    have hsel : (∑ i, (abSplitHomeo ec hec w).1 i ^ 2) = ∑ k : Fin extra, (w (ec k)) ^ 2 := by
      apply Finset.sum_congr rfl; intro k _; rw [abSplitHomeo_fst_apply ec hec w k]
    have hresid : (∑ i, q₂ (abSplitHomeo ec hec w) i ^ 2)
        = ∑ i : Fin n, (abRawResid g eh Ψsymm w i) ^ 2 := by
      rw [show (fun i => q₂ (abSplitHomeo ec hec w) i ^ 2)
          = fun i => abRawResidVec g eh Ψsymm w i ^ 2 from by rw [hwq]]
      apply Finset.sum_congr rfl; intro i _; rw [abRawResidVec_apply]
    rw [hsel, hresid, ← hwA]
  -- assemble: rinv transfer ▸ germ congr ▸ homeomorph transfer.
  rw [hrlcttransfer]
  rw [← rlctAtOn_congr_germ (fun w => F (abSplitHomeo ec hec w)) (fun w => ∑ i, g (Ψsymm w) i ^ 2)
    0 hkey]
  rw [rlctAtOn_comp_homeomorph (abSplitHomeo ec hec) (abSplitHomeo_mp ec hec)
    (abSplitHomeo_emb ec hec) F 0]
  -- `abSplitHomeo 0 = (0, (abSplitHomeo 0).2)`: the selected block reads `0 (ec k) = 0`.
  have hfst : (abSplitHomeo ec hec (0 : Fin N → ℝ)).1 = (0 : Fin extra → ℝ) := by
    funext k; rw [abSplitHomeo_fst_apply ec hec 0 k]; rfl
  have hsh : abSplitHomeo ec hec (0 : Fin N → ℝ)
      = ((0 : Fin extra → ℝ), (abSplitHomeo ec hec 0).2) := Prod.ext hfst rfl
  rw [hsh]

/-- **The abstract second-peel `hchart₂` producer** (PROVEN). For a `C²` residual vector
`h : (Fin N → ℝ) → EuclideanSpace ℝ (Fin n)` vanishing at the basepoint `t0` (`R = ‖h‖²` the slice
residual), with a selected injective family of `extra` components `eh : Fin extra → Fin n` and
selected coordinates `ec : Fin extra → Fin N` such that the `extra × extra` Jacobian minor
`(D h(t0))[eh, ec]` is invertible (`hminor`), the local RLCT of `R` at `t0` equals the post-chart
`∑ s² + ‖q₂‖²` shape on `ℝ^extra × ℝ^(N−extra)` for a GLOBAL `C¹` residual `q₂` and the reindexed
basepoint `t0₂`:

    rlctAtOn (fun t => ∑ i, h t i ^ 2) t0
      = rlctAtOn (fun p : (Fin extra → ℝ) × (Fin (N − extra) → ℝ) =>
          (∑ i, p.1 i ^ 2) + (∑ i, q₂ p i ^ 2)) ((0 : Fin extra → ℝ), t0₂).

This is the SECOND-peel structural analog of `dln_hchart_residual` (first peel), network-free. -/
theorem secondPeel_hchart_residual {N n extra : ℕ}
    (h : (Fin N → ℝ) → EuclideanSpace ℝ (Fin n)) (t0 : Fin N → ℝ)
    (hhCD : ContDiff ℝ 2 h) (hh0 : h t0 = 0)
    (eh : Fin extra → Fin n) (ec : Fin extra → Fin N)
    (heh : Function.Injective eh) (hec : Function.Injective ec)
    (hminor : (Matrix.of (fun k k' : Fin extra =>
      (fderiv ℝ (fun t => h t (eh k)) t0) (Pi.single (ec k') 1))).det ≠ 0) :
    ∃ (q₂ : (Fin extra → ℝ) × (Fin (N - extra) → ℝ) → EuclideanSpace ℝ (Fin n))
      (t0₂ : Fin (N - extra) → ℝ),
      ContDiff ℝ 1 q₂ ∧
      rlctAtOn (fun t : Fin N → ℝ => ∑ i, h t i ^ 2) t0
        = rlctAtOn (fun p : (Fin extra → ℝ) × (Fin (N - extra) → ℝ) =>
            (∑ i, p.1 i ^ 2) + (∑ i, q₂ p i ^ 2)) ((0 : Fin extra → ℝ), t0₂) := by
  classical
  -- pre-translate to center the basepoint at `0`: `g t := h (t + t0)`, so `g 0 = h t0 = 0`.
  set g : (Fin N → ℝ) → EuclideanSpace ℝ (Fin n) := fun t => h (t + t0) with hgdef
  have hgCD : ContDiff ℝ 2 g := hhCD.comp (contDiff_id.add contDiff_const)
  have hg0 : g 0 = 0 := by rw [hgdef]; simp only [zero_add]; exact hh0
  -- the minor at `0` for `g` equals the minor at `t0` for `h` (chain rule through translation).
  have hminor' : (Matrix.of (fun k k' : Fin extra =>
      (fderiv ℝ (fun t => g t (eh k)) (0 : Fin N → ℝ)) (Pi.single (ec k') 1))).det ≠ 0 := by
    -- per-entry: `fderiv (g·(eh k)) 0 = fderiv (h·(eh k)) t0` by `fderiv_comp_add_right`.
    have hentry : ∀ k : Fin extra, fderiv ℝ (fun t => g t (eh k)) (0 : Fin N → ℝ)
        = fderiv ℝ (fun t => h t (eh k)) t0 := by
      intro k
      have hrw : (fun t => g t (eh k)) = fun t => (fun s => h s (eh k)) (t + t0) := by
        funext t; rw [hgdef]
      rw [hrw, fderiv_comp_add_right (f := fun s => h s (eh k)) (a := t0), zero_add]
    have hmateq : (Matrix.of (fun k k' : Fin extra =>
          (fderiv ℝ (fun t => g t (eh k)) (0 : Fin N → ℝ)) (Pi.single (ec k') 1)))
        = Matrix.of (fun k k' : Fin extra =>
          (fderiv ℝ (fun t => h t (eh k)) t0) (Pi.single (ec k') 1)) := by
      ext k k'; simp only [Matrix.of_apply]; rw [hentry k]
    rw [hmateq]; exact hminor
  -- the centered producer.
  obtain ⟨q₂, t0₂, hq₂CD, hzero⟩ :=
    secondPeel_hchart_residual_zero g hgCD hg0 eh ec heh hec hminor'
  refine ⟨q₂, t0₂, hq₂CD, ?_⟩
  -- translate `rlctAtOn R t0` back to `rlctAtOn (R ∘ (·+t0)) 0 = rlctAtOn (∑ g·²) 0`.
  set τ : (Fin N → ℝ) ≃ₜ (Fin N → ℝ) := Homeomorph.addRight t0 with hτ
  have hτmp : MeasurePreserving τ (volume : Measure (Fin N → ℝ)) volume :=
    measurePreserving_add_right (volume : Measure (Fin N → ℝ)) t0
  have hτemb : MeasurableEmbedding τ := τ.measurableEmbedding
  have hτ0 : τ (0 : Fin N → ℝ) = t0 := by rw [hτ]; simp
  have htrans := rlctAtOn_comp_homeomorph τ hτmp hτemb (fun t : Fin N → ℝ => ∑ i, h t i ^ 2) 0
  rw [hτ0] at htrans
  -- `(fun t => ∑ h t i²) ∘ τ = fun t => ∑ g t i²`.
  have hcomp : (fun w : Fin N → ℝ => (fun t : Fin N → ℝ => ∑ i, h t i ^ 2) (τ w))
      = fun w => ∑ i, g w i ^ 2 := by
    funext w; rw [hgdef]; congr 1
  rw [hcomp] at htrans
  rw [← htrans, hzero]

/-! ## Slot-check — the producer feeds `deepest_le_of_optimal_of_iftResidual`'s `hchart₂`

A durable contract confirming the abstract producer's output IS the `hchart₂` hypothesis shape. The
use site instantiates the first peel's slice complement `Y = Fin (flatDim H − nReg) → ℝ` and the
slice residual vector `h t = q (0,t)`; the producer's `t0₂`/`q₂`/equality slot directly. -/

/-- **Slot-check (durable contract).** Given the first-peel `C¹` slice residual vector `q` on
`(Fin (nRegL2 H r) → ℝ) × (Fin N → ℝ)`, the SECOND-peel producer's output has EXACTLY the `hchart₂`
shape of `deepest_le_of_optimal_of_iftResidual` (with `Y = Fin N → ℝ`, `Y₂ = Fin (N − extra) → ℝ`,
`n₂ = n`). This `example` typechecks the producer ⟹ `hchart₂` wiring, pinning the interface; it does
NOT re-prove the producer. -/
example {N n extra : ℕ} (H : Fin (2 + 1) → ℕ) (r : ℕ)
    (q : (Fin (nRegL2 H r) → ℝ) × (Fin N → ℝ) → EuclideanSpace ℝ (Fin n))
    (t0 : Fin N → ℝ)
    (hslice : ContDiff ℝ 2 (fun t : Fin N → ℝ => q ((0 : Fin (nRegL2 H r) → ℝ), t)))
    (hslice0 : (fun t : Fin N → ℝ => q ((0 : Fin (nRegL2 H r) → ℝ), t)) t0 = 0)
    (eh : Fin extra → Fin n) (ec : Fin extra → Fin N)
    (heh : Function.Injective eh) (hec : Function.Injective ec)
    (hminor : (Matrix.of (fun k k' : Fin extra =>
      (fderiv ℝ (fun t => q ((0 : Fin (nRegL2 H r) → ℝ), t) (eh k)) t0)
        (Pi.single (ec k') 1))).det ≠ 0) :
    ∃ (q₂ : (Fin extra → ℝ) × (Fin (N - extra) → ℝ) → EuclideanSpace ℝ (Fin n))
      (t0₂ : Fin (N - extra) → ℝ),
      ContDiff ℝ 1 q₂ ∧
      rlctAtOn (fun t : Fin N → ℝ => ∑ i, q ((0 : Fin (nRegL2 H r) → ℝ), t) i ^ 2) t0
        = rlctAtOn (fun p : (Fin extra → ℝ) × (Fin (N - extra) → ℝ) =>
            (∑ i, p.1 i ^ 2) + (∑ i, q₂ p i ^ 2)) ((0 : Fin extra → ℝ), t0₂) :=
  secondPeel_hchart_residual (fun t => q ((0 : Fin (nRegL2 H r) → ℝ), t)) t0 hslice hslice0
    eh ec heh hec hminor

end DLNFibre.DLN.RLCT
