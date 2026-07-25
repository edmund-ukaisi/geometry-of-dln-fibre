import DLNFibre.DLN.Aoyagi.Corank2GWrapDecomp
import DLNFibre.DLN.Aoyagi.GeneralGeoAtlas
import DLNFibre.DLN.Aoyagi.LeafChartWire

/-!
# `DLN.Aoyagi.Corank2ChartJac` — #112 rung 5b, STAGE 2+3: the chart Jacobian + `Chart` L6 fields

Builds ON routeP-p1's STAGE 1 (`Corank2GWrapDecomp`: `gWrap = sigmaPiv ∘ shearH ∘ permP ∘ bbA0 ∘ bbA1`,
`gFaithful_decomp`/`gWrap_decomp`, the atom defs). Delivers:

- **STAGE 2 — the Jacobian.** `|jacDet gWrap u| = |u₀|⁷·|u₁|³·|u₂₀|⁸`, via `jacDet_comp` over the banked
  per-atom Jacobians (`jacDet_blockBlowupMap` (O9) for `bbA1`/`bbA0`/`sigmaPiv`; `jacDet_blockShear`
  (shear-pin) for `shearH`; `det_permutation` for `permP`) — **NO 21×21 determinant**.
- **STAGE 3 — the `Chart` L6 fields.** `hjac` (unit ≡ 1, `jac = [0↦7, 1↦3, 20↦8]`), `hg_analytic`,
  `hg_inj` (a.e.-injective off `excepWrap`), `hexcep` (null + measurable).

The banked two-sided `hideal` (`Corank2CoreGenWrap.hideal_coreGen_*`) is UNCHANGED — stated for the same
`gWrap`; the decomposition feeds only the Jacobian. NO crux re-proof.

`shearH` (routeP-p1's raw if-chain) is bridged to `blockShear shearPhiH` (`shearH_eq`) so the GENERAL
shear-pin `jacDet_blockShear` (which handles a NONLINEAR φ) gives `jacDet shearH ≡ 1` directly. The
reusable atom `abs_jacDet_permCoord` (a coordinate permutation has `|jacDet| = 1`, general `Fin D`) is
kept local pending a second use.
-/

open MeasureTheory Set Equiv Matrix
open DLNFibre.Core.Aoyagi DLNFibre.Core.Aoyagi.Corank2FaithfulComposite
open DLNFibre.DLN.Aoyagi.Corank2CoreGenWrap DLNFibre.DLN.Aoyagi.GeneralGeoAtlas
open DLNFibre.DLN.Aoyagi.Corank2GWrapDecomp

namespace DLNFibre.DLN.Aoyagi.Corank2ChartJac

/-! ## §0 — a reusable atom: the coordinate-permutation Jacobian is `±1` -/

/-- **The Jacobian determinant of a coordinate permutation is `±1`, so its absolute value is `1`**
(general `Fin D`). `w ↦ w ∘ σ` is linear; its Jacobian matrix is the permutation matrix `σ.permMatrix`,
whose determinant is `Perm.sign σ` (`det_permutation`), a unit of `ℤ` (`±1`). Reusable engine material
(the inter-node coordinate relabelling of any decomposed general-`d` leaf chart). -/
theorem abs_jacDet_permCoord {D : ℕ} (σ : Equiv.Perm (Fin D)) (u : Fin D → ℝ) :
    |jacDet (fun w i ↦ w (σ i)) u| = 1 := by
  set L : (Fin D → ℝ) →L[ℝ] (Fin D → ℝ) :=
    ContinuousLinearMap.pi (fun i ↦ ContinuousLinearMap.proj (σ i)) with hL
  have hfun : (fun w : Fin D → ℝ ↦ fun i ↦ w (σ i)) = L := by
    funext w i; simp [hL]
  have hfd : fderiv ℝ (fun w : Fin D → ℝ ↦ fun i ↦ w (σ i)) u = L := by
    rw [hfun]; exact L.hasFDerivAt.fderiv
  unfold jacDet
  rw [hfd, ← LinearMap.det_toMatrix' L.toLinearMap]
  have hmat : LinearMap.toMatrix' L.toLinearMap = σ.permMatrix ℝ := by
    ext i j
    rw [LinearMap.toMatrix'_apply]
    change L (Pi.single j 1) i = _
    rw [Equiv.Perm.permMatrix, PEquiv.toMatrix_toPEquiv_apply]
    simp [hL, Pi.single_apply, eq_comm]
  rw [hmat, Matrix.det_permutation]
  rcases Int.units_eq_one_or (Perm.sign σ) with h | h <;> rw [h] <;> simp

/-! ## §1 — the shear as a `blockShear` (bridge to routeP-p1's raw `shearH`) -/

/-- The shear displacement `shearPhiH` (`shearH = id + shearPhiH`): the bilinear corrections in slots
`4..11`, reading only the kept coordinates `{0,1,2,3,12..19}`; `0` elsewhere. -/
def shearPhiH (w : Fin 21 → ℝ) : Fin 21 → ℝ := fun i ↦
  if i = 4 then w 0 * w 2
  else if i = 5 then w 1 * w 2
  else if i = 6 then w 0 * w 3
  else if i = 7 then w 1 * w 3
  else if i = 8 then - (w 0 * w 12) - w 1 * w 16
  else if i = 9 then - (w 0 * w 13) - w 1 * w 17
  else if i = 10 then - (w 0 * w 14) - w 1 * w 18
  else if i = 11 then - (w 0 * w 15) - w 1 * w 19
  else 0

/-- The kept coordinates (fixed + read by the shear): `{0,1,2,3} ∪ {12,…,20}` = complement of `{4..11}`. -/
def shearKeepH : Fin 21 → Prop := fun i ↦ i.val < 4 ∨ 12 ≤ i.val

/-- **The bridge**: routeP-p1's raw `shearH` (an if-chain) IS the unipotent block-shear
`blockShear shearPhiH`. Lets the general shear-pin `jacDet_blockShear` apply. -/
theorem shearH_eq : shearH = blockShear shearPhiH := by
  funext w k
  fin_cases k <;>
    simp only [shearH, blockShear, shearPhiH, Pi.add_apply, Fin.reduceFinMk, Fin.reduceEq,
      if_true, if_false] <;>
    ring

/-- `shearPhiH` vanishes on the kept coordinates. -/
theorem shearPhiH_keep (u : Fin 21 → ℝ) (i : Fin 21) (hi : shearKeepH i) : shearPhiH u i = 0 := by
  fin_cases i <;>
    first
    | rfl
    | (exfalso; rcases hi with h | h <;> exact absurd h (by decide))

/-- `shearPhiH` reads only the kept coordinates. -/
theorem shearPhiH_read (u v : Fin 21 → ℝ) (h : ∀ i, shearKeepH i → u i = v i) :
    shearPhiH u = shearPhiH v := by
  have e : ∀ j : Fin 21, shearKeepH j → u j = v j := h
  funext i
  simp only [shearPhiH]
  rw [e 0 (Or.inl (by decide)), e 1 (Or.inl (by decide)), e 2 (Or.inl (by decide)),
    e 3 (Or.inl (by decide)), e 12 (Or.inr (by decide)), e 13 (Or.inr (by decide)),
    e 14 (Or.inr (by decide)), e 15 (Or.inr (by decide)), e 16 (Or.inr (by decide)),
    e 17 (Or.inr (by decide)), e 18 (Or.inr (by decide)), e 19 (Or.inr (by decide))]

/-- `shearPhiH` is differentiable (a polynomial map). -/
theorem differentiable_shearPhiH : Differentiable ℝ shearPhiH := by
  refine differentiable_pi.2 (fun i ↦ ?_)
  fin_cases i <;>
    (simp only [shearPhiH, Fin.reduceFinMk, Fin.reduceEq, if_true, if_false] <;> fun_prop)

/-- **The shear's Jacobian is exactly `1`** (shear-pin, `jacDet_blockShear` — GENERAL in the nonlinear
`shearPhiH`). -/
theorem jacDet_shearH (u : Fin 21 → ℝ) : jacDet shearH u = 1 := by
  rw [shearH_eq]
  exact jacDet_blockShear shearPhiH shearKeepH differentiable_shearPhiH
    (fun u i hi ↦ shearPhiH_keep u i hi) (fun u v h ↦ shearPhiH_read u v h) u

/-- `shearH` is injective (unipotent — a polynomial automorphism). -/
theorem injective_shearH : Function.Injective shearH := by
  rw [shearH_eq]
  exact injective_blockShear shearPhiH shearKeepH (fun u i hi ↦ shearPhiH_keep u i hi)
    (fun u v h ↦ shearPhiH_read u v h)

/-- `shearH` is differentiable. -/
theorem differentiable_shearH : Differentiable ℝ shearH := by
  rw [shearH_eq]
  exact differentiable_id.add differentiable_shearPhiH

/-! ## §2 — the permutation `permP`: `|jacDet| = 1` + differentiability -/

/-- `permIdx` is injective (checked by kernel `decide`). -/
theorem permIdx_injective : Function.Injective permIdx := by decide

/-- `permIdx` as an `Equiv.Perm (Fin 21)` (injective + finite ⟹ bijective). -/
noncomputable def permSigma : Equiv.Perm (Fin 21) :=
  Equiv.ofBijective permIdx ((Finite.injective_iff_bijective).mp permIdx_injective)

/-- **The permutation's Jacobian is `±1`** (`abs_jacDet_permCoord`, via `permSigma`). -/
theorem abs_jacDet_permP (u : Fin 21 → ℝ) : |jacDet permP u| = 1 := by
  have h : permP = fun w i ↦ w (permSigma i) := rfl
  rw [h]; exact abs_jacDet_permCoord permSigma u

/-- `permP` as a continuous linear map (`w ↦ w ∘ permIdx`). -/
def permCLM : (Fin 21 → ℝ) →L[ℝ] (Fin 21 → ℝ) :=
  ContinuousLinearMap.pi (fun i ↦ ContinuousLinearMap.proj (permIdx i))

theorem permP_eq_permCLM : permP = permCLM := by funext w i; simp [permP, permCLM]

/-- `permP` is differentiable (a linear map). -/
theorem differentiable_permP : Differentiable ℝ permP := by
  rw [permP_eq_permCLM]; exact permCLM.differentiable

/-- `permP` is analytic (a linear map). -/
theorem analyticOnNhd_permP : AnalyticOnNhd ℝ permP Set.univ := by
  rw [permP_eq_permCLM]; exact permCLM.analyticOnNhd _

/-- `permP` is injective (a bijection: `permIdx` is bijective). -/
theorem injective_permP : Function.Injective permP := by
  intro a b hab
  funext j
  obtain ⟨i, rfl⟩ := (Finite.injective_iff_surjective.mp permIdx_injective) j
  exact congrFun hab i

/-! ## §3 — atom differentiability -/

theorem differentiable_bbA1 : Differentiable ℝ bbA1 := differentiable_blockBlowupMap _ _
theorem differentiable_bbA0 : Differentiable ℝ bbA0 := differentiable_blockBlowupMap _ _
theorem differentiable_sigmaPiv : Differentiable ℝ sigmaPiv := differentiable_blockBlowupMap _ _

/-- `bbA1` fixes coordinate `0` — needed to place `bbA0`'s pivot factor. -/
theorem bbA1_apply_0 (u : Fin 21 → ℝ) : bbA1 u 0 = u 0 :=
  blockBlowupMap_offCenter_eq _ _ _ (by decide)

/-- `gFaithful` is differentiable (the composite of the differentiable atoms). -/
theorem differentiable_gFaithful : Differentiable ℝ gFaithful := by
  rw [gFaithful_decomp]
  exact (differentiable_shearH.comp differentiable_permP).comp
    (differentiable_bbA0.comp differentiable_bbA1)

/-! ## §4 — the composite Jacobian (`|jacDet gWrap| = |u₀|⁷·|u₁|³·|u₂₀|⁸`) -/

/-- **`|jacDet gFaithful u| = |u₀|⁷·|u₁|³`** — the composite of `shearH ∘ permP` (`|jacDet| = 1`) with
`bbA0 ∘ bbA1` (`|jacDet| = |u₀|⁷·|u₁|³`), by the chain rule over the atoms. NO 21×21 det. -/
theorem abs_jacDet_gFaithful (u : Fin 21 → ℝ) :
    |jacDet gFaithful u| = |u 0| ^ 7 * |u 1| ^ 3 := by
  have hK : Differentiable ℝ (shearH ∘ permP) := differentiable_shearH.comp differentiable_permP
  have hB : Differentiable ℝ (bbA0 ∘ bbA1) := differentiable_bbA0.comp differentiable_bbA1
  have hdecomp : gFaithful = (shearH ∘ permP) ∘ (bbA0 ∘ bbA1) := gFaithful_decomp
  rw [hdecomp, jacDet_comp u (hK _) (hB u), abs_mul]
  have hKjac : ∀ w, |jacDet (shearH ∘ permP) w| = 1 := by
    intro w
    rw [jacDet_comp w (differentiable_shearH _) (differentiable_permP w), jacDet_shearH, one_mul,
      abs_jacDet_permP]
  have hBjac : |jacDet (bbA0 ∘ bbA1) u| = |u 0| ^ 7 * |u 1| ^ 3 := by
    rw [jacDet_comp u (differentiable_bbA0 _) (differentiable_bbA1 u), abs_mul,
      show bbA0 = blockBlowupMap ({0, 1, 2, 3, 4, 5, 6, 7} : Finset (Fin 21)) 0 from rfl,
      jacDet_blockBlowupMap (by decide), abs_pow, bbA1_apply_0,
      show bbA1 = blockBlowupMap ({1, 5, 6, 7} : Finset (Fin 21)) 1 from rfl,
      jacDet_blockBlowupMap (by decide), abs_pow,
      show ({0, 1, 2, 3, 4, 5, 6, 7} : Finset (Fin 21)).card - 1 = 7 from by decide,
      show ({1, 5, 6, 7} : Finset (Fin 21)).card - 1 = 3 from by decide]
  rw [hKjac, hBjac, one_mul]

/-- **THE L6 JACOBIAN (`-- map: #112-5b-hjac`).** `|jacDet gWrap u| = |u₀|⁷·|u₁|³·|u₂₀|⁸` — the full
(3,3,4) chart Jacobian, `gWrap = sigmaPiv ∘ gFaithful`, from `sigmaPiv`'s pivot-`20` monomial
(`|(gFaithful u)₂₀|⁸ = |u₂₀|⁸`, `gFaithful_apply_20`) times `abs_jacDet_gFaithful`. -/
theorem abs_jacDet_gWrap (u : Fin 21 → ℝ) :
    |jacDet gWrap u| = |u 0| ^ 7 * |u 1| ^ 3 * |u 20| ^ 8 := by
  have hg : gWrap = sigmaPiv ∘ gFaithful := rfl
  rw [hg, jacDet_comp u (differentiable_sigmaPiv _) (differentiable_gFaithful u), abs_mul,
    show sigmaPiv = blockBlowupMap ({0, 1, 2, 3, 4, 5, 6, 7, 20} : Finset (Fin 21)) 20 from rfl,
    jacDet_blockBlowupMap (by decide), abs_pow, gFaithful_apply_20, abs_jacDet_gFaithful,
    show ({0, 1, 2, 3, 4, 5, 6, 7, 20} : Finset (Fin 21)).card - 1 = 8 from by decide]
  ring

/-! ## §5 — the `Chart` L6 fields: `jac`, `hjac` (unit ≡ 1), `hg_analytic`, `hg_inj`, `hexcep` -/

/-- The Jacobian monomial exponent vector `jacWrap = [0↦7, 1↦3, 20↦8]` (the paper's `M_{s,k}−1`). -/
def jacWrap : Fin 21 → ℕ :=
  fun d ↦ if d = 0 then 7 else if d = 1 then 3 else if d = 20 then 8 else 0

/-- `jacWeight jacWrap u = |u₀|⁷·|u₁|³·|u₂₀|⁸`. -/
theorem jacWeight_jacWrap (u : Fin 21 → ℝ) :
    jacWeight jacWrap u = |u 0| ^ 7 * |u 1| ^ 3 * |u 20| ^ 8 := by
  rw [jacWeight,
    ← Finset.prod_subset (Finset.subset_univ ({0, 1, 20} : Finset (Fin 21)))
      (fun d _ hd ↦ by
        have hz : jacWrap d = 0 := by
          simp only [jacWrap]
          rw [if_neg (fun h ↦ hd (by simp [h])), if_neg (fun h ↦ hd (by simp [h])),
            if_neg (fun h ↦ hd (by simp [h]))]
        rw [hz, pow_zero])]
  rw [Finset.prod_insert (by decide), Finset.prod_insert (by decide), Finset.prod_singleton]
  simp only [jacWrap, Fin.reduceEq, if_true, if_false]
  ring

/-- **The L6 `hjac` field, unit ≡ 1.** `|jacDet gWrap u| = jacWeight jacWrap u · |1|` for ALL `u` —
the exact `Chart.hjac` shape with `unit := fun _ ↦ 1`. -/
theorem gWrap_hjac (u : Fin 21 → ℝ) :
    |jacDet gWrap u| = jacWeight jacWrap u * |(1 : ℝ)| := by
  rw [abs_jacDet_gWrap, jacWeight_jacWrap, abs_one, mul_one]

/-- `shearPhiH` is analytic (each coordinate is a polynomial in the projections). -/
theorem analyticOnNhd_shearPhiH : AnalyticOnNhd ℝ shearPhiH Set.univ := by
  have hproj : ∀ k : Fin 21, AnalyticOnNhd ℝ (fun w : Fin 21 → ℝ ↦ w k) Set.univ := fun k ↦
    (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 21 ↦ ℝ) k).analyticOnNhd _
  refine AnalyticOnNhd.pi (fun i ↦ ?_)
  fin_cases i <;>
    simp only [shearPhiH, Fin.reduceFinMk, Fin.reduceEq, if_true, if_false] <;>
    first
      | exact analyticOnNhd_const
      | exact (hproj _).mul (hproj _)
      | exact ((hproj _).mul (hproj _)).neg.sub ((hproj _).mul (hproj _))

/-- `shearH` is analytic. -/
theorem analyticOnNhd_shearH : AnalyticOnNhd ℝ shearH Set.univ := by
  rw [shearH_eq]; exact analyticOnNhd_blockShear shearPhiH analyticOnNhd_shearPhiH

/-- `gFaithful` is analytic (the composite of the analytic atoms). -/
theorem analyticOnNhd_gFaithful : AnalyticOnNhd ℝ gFaithful Set.univ := by
  rw [gFaithful_decomp]
  exact (analyticOnNhd_shearH.comp analyticOnNhd_permP (Set.mapsTo_univ _ _)).comp
    ((analyticOnNhd_blockBlowupMap _ _).comp (analyticOnNhd_blockBlowupMap _ _)
      (Set.mapsTo_univ _ _)) (Set.mapsTo_univ _ _)

/-- **The `hg_analytic` field.** `gWrap` is analytic on the whole space (a polynomial map). -/
theorem analyticOnNhd_gWrap : AnalyticOnNhd ℝ gWrap Set.univ :=
  (analyticOnNhd_blockBlowupMap _ _).comp analyticOnNhd_gFaithful (Set.mapsTo_univ _ _)

/-- The exceptional locus `{u | jacWeight jacWrap u = 0} = {u₀ = 0} ∪ {u₁ = 0} ∪ {u₂₀ = 0}`. -/
def excepWrap : Set (Fin 21 → ℝ) := {u | jacWeight jacWrap u = 0}

/-- **The `hexcep_meas` field.** `excepWrap` is a measurable (closed) set. -/
theorem measurableSet_excepWrap : MeasurableSet excepWrap :=
  (isClosed_eq (continuous_jacWeight jacWrap) continuous_const).measurableSet

/-- **The `hexcep_null` field.** `excepWrap` is null (`volume_jacWeight_zeroSet`). -/
theorem volume_excepWrap : volume excepWrap = 0 :=
  volume_jacWeight_zeroSet jacWrap

/-- **The `hg_inj` field.** `gWrap` is a.e.-injective: injective off `excepWrap`. Composition of the
globally-injective `shearH ∘ permP` with the blow-ups `bbA0`/`bbA1`/`sigmaPiv`, each injective off
its pivot hyperplane; on `{u₀≠0 ∧ u₁≠0 ∧ u₂₀≠0}` all pivots survive. -/
theorem injOn_gWrap : Set.InjOn gWrap (Set.univ \ excepWrap) := by
  have hmem : ∀ x ∈ Set.univ \ excepWrap, x 0 ≠ 0 ∧ x 1 ≠ 0 ∧ x 20 ≠ 0 := by
    intro x hx
    have hj : jacWeight jacWrap x ≠ 0 := hx.2
    rw [jacWeight_jacWrap] at hj
    refine ⟨?_, ?_, ?_⟩ <;> intro h <;> apply hj <;> simp [h]
  intro x hx y hy hxy
  obtain ⟨hx0, hx1, hx20⟩ := hmem x hx
  obtain ⟨hy0, hy1, hy20⟩ := hmem y hy
  -- peel `sigmaPiv` (pivot 20): `(gFaithful ·) 20 = ·₂₀ ≠ 0`
  have hgfx20 : gFaithful x 20 ≠ 0 := by rw [gFaithful_apply_20]; exact hx20
  have hgfy20 : gFaithful y 20 ≠ 0 := by rw [gFaithful_apply_20]; exact hy20
  have hgf : gFaithful x = gFaithful y :=
    injOn_blockBlowupMap (S := ({0, 1, 2, 3, 4, 5, 6, 7, 20} : Finset (Fin 21))) (p := 20) (by decide)
      ⟨Set.mem_univ _, by simpa using hgfx20⟩ ⟨Set.mem_univ _, by simpa using hgfy20⟩ hxy
  -- peel `shearH ∘ permP` (global injections) → `(bbA0 ∘ bbA1) x = (bbA0 ∘ bbA1) y`
  rw [gFaithful_decomp] at hgf
  have hB : (bbA0 ∘ bbA1) x = (bbA0 ∘ bbA1) y :=
    injective_permP (injective_shearH hgf)
  -- peel `bbA0` (pivot 0): `(bbA1 ·) 0 = ·₀ ≠ 0`
  have hbx0 : bbA1 x 0 ≠ 0 := by rw [bbA1_apply_0]; exact hx0
  have hby0 : bbA1 y 0 ≠ 0 := by rw [bbA1_apply_0]; exact hy0
  have hb1 : bbA1 x = bbA1 y :=
    injOn_blockBlowupMap (S := ({0, 1, 2, 3, 4, 5, 6, 7} : Finset (Fin 21))) (p := 0) (by decide)
      ⟨Set.mem_univ _, by simpa using hbx0⟩ ⟨Set.mem_univ _, by simpa using hby0⟩ hB
  -- peel `bbA1` (pivot 1)
  exact injOn_blockBlowupMap (S := ({1, 5, 6, 7} : Finset (Fin 21))) (p := 1) (by decide)
    ⟨Set.mem_univ _, by simpa using hx1⟩ ⟨Set.mem_univ _, by simpa using hy1⟩ hb1

end DLNFibre.DLN.Aoyagi.Corank2ChartJac
