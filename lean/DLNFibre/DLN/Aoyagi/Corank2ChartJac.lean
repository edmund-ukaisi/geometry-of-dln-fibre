import DLNFibre.DLN.Aoyagi.Corank2CoreGenWrap
import DLNFibre.DLN.Aoyagi.GeneralGeoAtlas
import DLNFibre.DLN.Aoyagi.LeafChartWire

/-!
# `DLN.Aoyagi.Corank2ChartJac` — #112 rung 5b (L6): the DECOMPOSED (3,3,4) chart Jacobian

The (3,3,4) resolution chart `gWrap = sigmaPiv ∘ gFaithful` is presented as the banked-atom composite
(chart-architecture fork #138, verdict (B) DECOMPOSED), and its `Chart` L6 fields
(`hjac`/`jac`/`hg_analytic`/`hg_inj`/`hexcep`) are read off the per-atom Jacobians — with **NO 21×21
determinant** and **NO crux re-proof**. The banked two-sided `hideal`
(`Corank2CoreGenWrap.hideal_coreGen_*`) is unchanged: it is stated for the SAME `gWrap`.

## The decomposition (sympy-exact, `verify_B_decomp.py` + `decomp_check.py`; verified here numerically)

`gFaithful = shearH ∘ permP ∘ blowA0 ∘ blowA1`, so `gWrap = sigmaPiv ∘ shearH ∘ permP ∘ blowA0 ∘ blowA1`:

| atom | what | `|jacDet|` | banked as |
|---|---|---|---|
| `blowA1` | `blockBlowupMap {1,5,6,7} 1` | `|u₁|³` | `jacDet_blockBlowupMap` (O9) |
| `blowA0` | `blockBlowupMap {0,…,7} 0` | `|u₀|⁷` | `jacDet_blockBlowupMap` (O9) |
| `permP` | coordinate permutation `[8,9,10,11,1,5,6,7,0,2,3,4]` (fixed `12..20`) | `1` | `det_permutation` (`|±1|`) |
| `shearH` | unipotent block-shear (reads kept `{0,1,2,3,12..19}`, writes `4..11`) | `1` | `jacDet_blockShear` (shear-pin) |
| `sigmaPiv` | `blockBlowupMap {0..7,20} 20` | `|u₂₀|⁸` | `jacDet_blockBlowupMap` (O9) |

So `|jacDet gWrap u| = |u₀|⁷·|u₁|³·|u₂₀|⁸` (`jacWrap = [0↦7, 1↦3, 20↦8]`, unit ≡ 1). The permutation `permP`
is kept **explicit** (the load-bearing caveat, fork #138): omitting it / reversing the composition
order breaks the extensional identity `gFaithful_decomp`, which is the self-gate.

`abs_jacDet_permCoord` (a coordinate-permutation `|jacDet| = 1`, general `Fin D`) is reusable engine
material; kept local pending a second use.
-/

open MeasureTheory Set Equiv Matrix
open DLNFibre.Core.Aoyagi DLNFibre.Core.Aoyagi.Corank2FaithfulComposite
open DLNFibre.DLN.Aoyagi.Corank2CoreGenWrap DLNFibre.DLN.Aoyagi.GeneralGeoAtlas

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

/-! ## §1 — the five atoms -/

/-- `blowA1 = blockBlowupMap {1,5,6,7} 1` (`|jacDet| = |u₁|³`). -/
noncomputable def blowA1 : (Fin 21 → ℝ) → (Fin 21 → ℝ) :=
  blockBlowupMap ({1, 5, 6, 7} : Finset (Fin 21)) 1

/-- `blowA0 = blockBlowupMap {0,…,7} 0` (`|jacDet| = |u₀|⁷`). -/
noncomputable def blowA0 : (Fin 21 → ℝ) → (Fin 21 → ℝ) :=
  blockBlowupMap ({0, 1, 2, 3, 4, 5, 6, 7} : Finset (Fin 21)) 0

/-- The coordinate-permutation table `[8,9,10,11,1,5,6,7,0,2,3,4]` on `{0..11}`, identity on `{12..20}`
(the pull convention `z i = w (permFun i)`). -/
def permFun : Fin 21 → Fin 21 :=
  ![8, 9, 10, 11, 1, 5, 6, 7, 0, 2, 3, 4, 12, 13, 14, 15, 16, 17, 18, 19, 20]

/-- `permFun` is injective (checked by kernel `decide`). -/
theorem permFun_injective : Function.Injective permFun := by decide

/-- The permutation `permFun` as an `Equiv.Perm (Fin 21)` (injective + finite ⟹ bijective). -/
noncomputable def permSigma : Equiv.Perm (Fin 21) :=
  Equiv.ofBijective permFun ((Finite.injective_iff_bijective).mp permFun_injective)

/-- The coordinate permutation `permP w = w ∘ permFun`. -/
def permP : (Fin 21 → ℝ) → (Fin 21 → ℝ) := fun w i ↦ w (permFun i)

/-- The unipotent shear displacement: writes the bilinear corrections to slots `4..11`, reading only
the kept coordinates `{0,1,2,3,12..19}`; `0` elsewhere. -/
def shearPhi (w : Fin 21 → ℝ) : Fin 21 → ℝ := fun i ↦
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
def shearKeep : Fin 21 → Prop := fun i ↦ i.val < 4 ∨ 12 ≤ i.val

/-- The unipotent block-shear `shearH = id + shearPhi` (the recoord-cancelling shear of fork #138). -/
def shearH : (Fin 21 → ℝ) → (Fin 21 → ℝ) := blockShear shearPhi

/-! ## §2 — the shear's structural facts (`hkeep`/`hread`/differentiability/`jacDet = 1`) -/

/-- `shearPhi` vanishes on the kept coordinates. -/
theorem shearPhi_keep (u : Fin 21 → ℝ) (i : Fin 21) (hi : shearKeep i) : shearPhi u i = 0 := by
  fin_cases i <;>
    first
    | rfl
    | (exfalso; rcases hi with h | h <;> exact absurd h (by decide))

/-- `shearPhi` reads only the kept coordinates. -/
theorem shearPhi_read (u v : Fin 21 → ℝ) (h : ∀ i, shearKeep i → u i = v i) :
    shearPhi u = shearPhi v := by
  have e : ∀ j : Fin 21, shearKeep j → u j = v j := h
  funext i
  simp only [shearPhi]
  rw [e 0 (Or.inl (by decide)), e 1 (Or.inl (by decide)), e 2 (Or.inl (by decide)),
    e 3 (Or.inl (by decide)), e 12 (Or.inr (by decide)), e 13 (Or.inr (by decide)),
    e 14 (Or.inr (by decide)), e 15 (Or.inr (by decide)), e 16 (Or.inr (by decide)),
    e 17 (Or.inr (by decide)), e 18 (Or.inr (by decide)), e 19 (Or.inr (by decide))]

/-- `shearPhi` is differentiable (a polynomial map). -/
theorem differentiable_shearPhi : Differentiable ℝ shearPhi := by
  refine differentiable_pi.2 (fun i ↦ ?_)
  fin_cases i <;>
    (simp only [shearPhi, Fin.reduceFinMk, Fin.reduceEq, if_true, if_false] <;> fun_prop)

/-- `shearH` is differentiable. -/
theorem differentiable_shearH : Differentiable ℝ shearH := by
  change Differentiable ℝ (fun u ↦ u + shearPhi u)
  exact differentiable_id.add differentiable_shearPhi

/-- **The shear's Jacobian is exactly `1`** (shear-pin, `jacDet_blockShear`). -/
theorem jacDet_shearH (u : Fin 21 → ℝ) : jacDet shearH u = 1 :=
  jacDet_blockShear shearPhi shearKeep differentiable_shearPhi
    (fun u i hi ↦ shearPhi_keep u i hi) (fun u v h ↦ shearPhi_read u v h) u

/-- `shearH` is injective (unipotent — a polynomial automorphism). -/
theorem injective_shearH : Function.Injective shearH :=
  injective_blockShear shearPhi shearKeep (fun u i hi ↦ shearPhi_keep u i hi)
    (fun u v h ↦ shearPhi_read u v h)

/-! ## §3 — the extensional decomposition identity (the self-gate) -/

/-- **THE DECOMPOSITION (`-- map: #112-5b-decomp`).** The folded faithful chart `gFaithful` IS the
banked-atom composite `shearH ∘ permP ∘ blowA0 ∘ blowA1` — proven extensionally on all 21 coordinates
(`fin_cases` + `ring`). This is the self-gate: were the recipe (esp. the explicit permutation `permP`)
wrong, this identity would not close. Sympy-exact + verified numerically before formalising. -/
theorem gFaithful_decomp : gFaithful = shearH ∘ permP ∘ blowA0 ∘ blowA1 := by
  funext u k
  fin_cases k <;>
    simp only [Function.comp_apply, shearH, blockShear, Pi.add_apply, permP, shearPhi, permFun,
      blowA0, blowA1, blockBlowupMap, Matrix.cons_val, gFaithful, Fin.reduceFinMk, Fin.reduceEq,
      Finset.mem_insert, Finset.mem_singleton, if_true, if_false] <;>
    norm_num [Fin.ext_iff] <;> ring

/-- **The full (3,3,4) resolution chart as the 5-atom decomposed composite.** `gWrap = sigmaPiv ∘
gFaithful` (its def) `= sigmaPiv ∘ shearH ∘ permP ∘ blowA0 ∘ blowA1` — the general-`d` GeoStep-chart
template shape. The banked `hideal` (`Corank2CoreGenWrap.hideal_coreGen_*`) holds verbatim for THIS
presentation: it is stated for the same `gWrap`; this identity only exposes the atom spine. -/
theorem gWrap_decomp : gWrap = sigmaPiv ∘ shearH ∘ permP ∘ blowA0 ∘ blowA1 := by
  have h : gWrap = sigmaPiv ∘ gFaithful := rfl
  rw [h, gFaithful_decomp]

/-! ## §4 — the composite Jacobian (`|jacDet gWrap| = |u₀|⁷·|u₁|³·|u₂₀|⁸`) -/

theorem differentiable_blowA1 : Differentiable ℝ blowA1 := differentiable_blockBlowupMap _ _
theorem differentiable_blowA0 : Differentiable ℝ blowA0 := differentiable_blockBlowupMap _ _
theorem differentiable_sigmaPiv : Differentiable ℝ sigmaPiv := differentiable_blockBlowupMap _ _

/-- `permP` as a continuous linear map (`w ↦ w ∘ permFun`). -/
def permCLM : (Fin 21 → ℝ) →L[ℝ] (Fin 21 → ℝ) :=
  ContinuousLinearMap.pi (fun i ↦ ContinuousLinearMap.proj (permFun i))

theorem permP_eq_permCLM : permP = permCLM := by funext w i; simp [permP, permCLM]

/-- `permP` is differentiable (a linear map). -/
theorem differentiable_permP : Differentiable ℝ permP := by
  rw [permP_eq_permCLM]; exact permCLM.differentiable

/-- `permP` is injective (a bijection: `permFun` is bijective). -/
theorem injective_permP : Function.Injective permP := by
  intro a b h
  funext j
  obtain ⟨i, rfl⟩ := (Finite.injective_iff_surjective.mp permFun_injective) j
  exact congrFun h i

/-- `gFaithful` is differentiable (the composite of the differentiable atoms). -/
theorem differentiable_gFaithful : Differentiable ℝ gFaithful := by
  rw [gFaithful_decomp]
  exact (differentiable_shearH.comp differentiable_permP).comp
    (differentiable_blowA0.comp differentiable_blowA1)

/-- `permFun` fixes coordinate `0` — needed to place `blowA1`'s pivot factor. -/
theorem blowA1_apply_0 (u : Fin 21 → ℝ) : blowA1 u 0 = u 0 :=
  blockBlowupMap_offCenter_eq _ _ _ (by decide)

/-- **The permutation's Jacobian is `±1`** (`abs_jacDet_permCoord`, via `permSigma`). -/
theorem abs_jacDet_permP (u : Fin 21 → ℝ) : |jacDet permP u| = 1 :=
  abs_jacDet_permCoord permSigma u

/-- **`|jacDet gFaithful u| = |u₀|⁷·|u₁|³`** — the composite of `shearH ∘ permP` (`|jacDet| = 1`) with
`blowA0 ∘ blowA1` (`|jacDet| = |u₀|⁷·|u₁|³`), by the chain rule over the atoms. NO 21×21 det. -/
theorem abs_jacDet_gFaithful (u : Fin 21 → ℝ) :
    |jacDet gFaithful u| = |u 0| ^ 7 * |u 1| ^ 3 := by
  have hK : Differentiable ℝ (shearH ∘ permP) := differentiable_shearH.comp differentiable_permP
  have hB : Differentiable ℝ (blowA0 ∘ blowA1) := differentiable_blowA0.comp differentiable_blowA1
  have hdecomp : gFaithful = (shearH ∘ permP) ∘ (blowA0 ∘ blowA1) := gFaithful_decomp
  rw [hdecomp, jacDet_comp u (hK _) (hB u), abs_mul]
  -- `|jacDet (shearH ∘ permP) (B u)| = 1`
  have hKjac : ∀ w, |jacDet (shearH ∘ permP) w| = 1 := by
    intro w
    rw [jacDet_comp w (differentiable_shearH _) (differentiable_permP w), jacDet_shearH, one_mul,
      abs_jacDet_permP]
  -- `|jacDet (blowA0 ∘ blowA1) u| = |u₀|⁷·|u₁|³`
  have hBjac : |jacDet (blowA0 ∘ blowA1) u| = |u 0| ^ 7 * |u 1| ^ 3 := by
    rw [jacDet_comp u (differentiable_blowA0 _) (differentiable_blowA1 u), abs_mul,
      show blowA0 = blockBlowupMap ({0, 1, 2, 3, 4, 5, 6, 7} : Finset (Fin 21)) 0 from rfl,
      jacDet_blockBlowupMap (by decide), abs_pow, blowA1_apply_0,
      show blowA1 = blockBlowupMap ({1, 5, 6, 7} : Finset (Fin 21)) 1 from rfl,
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
  rw [hg, jacDet_comp u (differentiable_sigmaPiv _) (differentiable_gFaithful u), abs_mul]
  rw [show sigmaPiv = blockBlowupMap ({0, 1, 2, 3, 4, 5, 6, 7, 20} : Finset (Fin 21)) 20 from rfl,
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

/-- `permP` is analytic (a linear map). -/
theorem analyticOnNhd_permP : AnalyticOnNhd ℝ permP Set.univ := by
  rw [permP_eq_permCLM]; exact permCLM.analyticOnNhd _

/-- `shearPhi` is analytic (each coordinate is a polynomial in the projections). -/
theorem analyticOnNhd_shearPhi : AnalyticOnNhd ℝ shearPhi Set.univ := by
  have hproj : ∀ k : Fin 21, AnalyticOnNhd ℝ (fun w : Fin 21 → ℝ ↦ w k) Set.univ := fun k ↦
    (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 21 ↦ ℝ) k).analyticOnNhd _
  refine AnalyticOnNhd.pi (fun i ↦ ?_)
  fin_cases i <;>
    simp only [shearPhi, Fin.reduceFinMk, Fin.reduceEq, if_true, if_false] <;>
    first
      | exact analyticOnNhd_const
      | exact (hproj _).mul (hproj _)
      | exact ((hproj _).mul (hproj _)).neg.sub ((hproj _).mul (hproj _))

/-- `shearH` is analytic. -/
theorem analyticOnNhd_shearH : AnalyticOnNhd ℝ shearH Set.univ :=
  analyticOnNhd_blockShear shearPhi analyticOnNhd_shearPhi

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
globally-injective `shearH ∘ permP` with the blow-ups `blowA0`/`blowA1`/`sigmaPiv`, each injective
off its pivot hyperplane; on `{u₀≠0 ∧ u₁≠0 ∧ u₂₀≠0}` all pivots survive. -/
theorem injOn_gWrap : Set.InjOn gWrap (Set.univ \ excepWrap) := by
  -- membership in `univ \ excepWrap` gives the three pivots nonzero.
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
    injOn_blockBlowupMap (S := ({0,1,2,3,4,5,6,7,20} : Finset (Fin 21))) (p := 20) (by decide)
      ⟨Set.mem_univ _, by simpa using hgfx20⟩ ⟨Set.mem_univ _, by simpa using hgfy20⟩ hxy
  -- peel `shearH ∘ permP` (global injections) → `(blowA0 ∘ blowA1) x = (blowA0 ∘ blowA1) y`
  rw [gFaithful_decomp] at hgf
  have hB : (blowA0 ∘ blowA1) x = (blowA0 ∘ blowA1) y :=
    injective_permP (injective_shearH hgf)
  -- peel `blowA0` (pivot 0): `(blowA1 ·) 0 = ·₀ ≠ 0`
  have hbx0 : blowA1 x 0 ≠ 0 := by rw [blowA1_apply_0]; exact hx0
  have hby0 : blowA1 y 0 ≠ 0 := by rw [blowA1_apply_0]; exact hy0
  have hb1 : blowA1 x = blowA1 y :=
    injOn_blockBlowupMap (S := ({0,1,2,3,4,5,6,7} : Finset (Fin 21))) (p := 0) (by decide)
      ⟨Set.mem_univ _, by simpa using hbx0⟩ ⟨Set.mem_univ _, by simpa using hby0⟩ hB
  -- peel `blowA1` (pivot 1)
  exact injOn_blockBlowupMap (S := ({1,5,6,7} : Finset (Fin 21))) (p := 1) (by decide)
    ⟨Set.mem_univ _, by simpa using hx1⟩ ⟨Set.mem_univ _, by simpa using hy1⟩ hb1

end DLNFibre.DLN.Aoyagi.Corank2ChartJac
