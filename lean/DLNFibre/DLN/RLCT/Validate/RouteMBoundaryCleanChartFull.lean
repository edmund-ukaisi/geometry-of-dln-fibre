import DLNFibre.DLN.RLCT.Validate.RouteMBoundaryCleanU
import DLNFibre.DLN.RLCT.Validate.RouteM4422

/-!
# `RouteMBoundaryCleanChartFull` — the ∀M BOUNDARY-CLEAN `NodeAchieverChart` + the atom discharge

The full clean achiever chart bundle for clean-boundary `M` (`NoInteriorBothDrop M`, `deepRank = deepRows`,
all widths positive), and the discharge of the achiever box-divergence atom for that class. Built on the
banked legs:

* the RATE `routeMCore (cleanPhi u) = (u p)²·U` (`RouteMBoundaryCleanRate`),
* the unit `U ≢ 0` a.e. + measurability + box-bound (`RouteMBoundaryCleanU`),
* the GENERIC `pivotBlowupOn` det/cov/injOn (`S1G5Charts`) at `active.card = minAdm`
  (`deepestCoords_card_eq_minAdm`).

The chart is `cleanPhi = pivotBlowupOn (deepestCoords M hL) (deepestPivot M hL hne)` — a SINGLE radial
blow-up of the deepest factor (no Schur shear), so the determinant `|det Dφ| = |u_p|^{minAdm−1}` and the
cov are DIRECTLY the generic lemmas (the POLYNOMIAL-radial branch: no rational pole, no null-slice split).
-/

open scoped BigOperators ENNReal
open Matrix MeasureTheory

namespace DLNFibre.DLN.RLCT

variable {L : ℕ}

/-! ## The clean leaf Jacobian exponents -/

/-- The clean leaf Jacobian exponents: `minAdm M − 1` on the pivot (the radial blow-up determinant
`|u_p|^{minAdm−1}`), `0` on the spectator axes (a PURE radial blow-up has no spectator monomial). -/
noncomputable def cleanLeafH (M : Fin (L + 1) → ℕ) (hL : 0 < L)
    (hne : (deepestCoords M hL).Nonempty) : Fin (routeMAmbient M) → ℕ :=
  fun j => if j = deepestPivot M hL hne then minAdm M - 1 else 0

/-- `cleanLeafH (deepestPivot) = minAdm M − 1`. -/
theorem cleanLeafH_pivot (M : Fin (L + 1) → ℕ) (hL : 0 < L)
    (hne : (deepestCoords M hL).Nonempty) :
    cleanLeafH M hL hne (deepestPivot M hL hne) = minAdm M - 1 := by
  rw [cleanLeafH, if_pos rfl]

/-- The Jacobian weight `∏_j |u_j|^{cleanLeafH j} = |u_p|^{minAdm−1}` (the pivot exceptional divisor;
spectators `|·|⁰ = 1`). -/
theorem cleanLeafH_prod_eq (M : Fin (L + 1) → ℕ) (hL : 0 < L)
    (hne : (deepestCoords M hL).Nonempty) (u : Fin (routeMAmbient M) → ℝ) :
    (∏ j, |u j| ^ (cleanLeafH M hL hne j)) = |u (deepestPivot M hL hne)| ^ (minAdm M - 1) := by
  rw [Finset.prod_eq_single (deepestPivot M hL hne)]
  · rw [cleanLeafH_pivot]
  · intro j _ hj; rw [cleanLeafH, if_neg hj, pow_zero]
  · intro h; exact absurd (Finset.mem_univ _) h

/-! ## The chart fderiv + determinant (GENERIC `pivotBlowupOn`) -/

/-- **`cleanPhi` has fderiv `pivotBlowupOnDeriv`** (the generic node C¹). -/
theorem cleanPhi_hasFDerivAt (M : Fin (L + 1) → ℕ) (hL : 0 < L)
    (hne : (deepestCoords M hL).Nonempty) (u : Fin (routeMAmbient M) → ℝ) :
    HasFDerivAt (cleanPhi M hL hne)
      (pivotBlowupOnDeriv (deepestCoords M hL) (deepestPivot M hL hne) u) u :=
  hasFDerivWithinAt_univ.mp (pivotBlowupOn_hasFDerivWithinAt _ _ Set.univ u)

/-- **The chart Jacobian determinant** `|det Dφ| = |u_p|^{minAdm−1}` — the generic radial-blow-up det
(`pivotBlowupOn_abs_det` at `active.card = minAdm`, the clean `deepestCoords_card_eq_minAdm`). -/
theorem cleanPhi_abs_det (M : Fin (L + 1) → ℕ) (hL : 0 < L)
    (hne : (deepestCoords M hL).Nonempty) (hNo : NoInteriorBothDrop M)
    (hclean : deepRank M = deepRows M) (u : Fin (routeMAmbient M) → ℝ) :
    |(pivotBlowupOnDeriv (deepestCoords M hL) (deepestPivot M hL hne) u).det|
      = |u (deepestPivot M hL hne)| ^ (minAdm M - 1) := by
  rw [pivotBlowupOn_abs_det _ _ (deepestPivot_mem M hL hne),
    deepestCoords_card_eq_minAdm M hL hNo hclean]

/-! ## Continuity / image containment -/

/-- **`cleanPhi` is continuous** (a polynomial map: each output coord is a projection or a product). -/
theorem continuous_cleanPhi (M : Fin (L + 1) → ℕ) (hL : 0 < L)
    (hne : (deepestCoords M hL).Nonempty) : Continuous (cleanPhi M hL hne) := by
  rw [cleanPhi]
  apply continuous_pi
  intro i
  unfold pivotBlowupOn
  by_cases hi : i = deepestPivot M hL hne
  · simp only [if_pos hi]; exact continuous_apply _
  · simp only [if_neg hi]
    by_cases ha : i ∈ deepestCoords M hL
    · simp only [if_pos ha]; exact (continuous_apply _).mul (continuous_apply _)
    · simp only [if_neg ha]; exact continuous_apply _

/-- **`cleanPhi 0 = 0`** (every output coord is a monomial in the inputs, vanishing at `0`). -/
theorem cleanPhi_zero (M : Fin (L + 1) → ℕ) (hL : 0 < L)
    (hne : (deepestCoords M hL).Nonempty) :
    cleanPhi M hL hne (0 : Fin (routeMAmbient M) → ℝ) = 0 := by
  funext i
  rw [cleanPhi]
  unfold pivotBlowupOn
  by_cases hi : i = deepestPivot M hL hne
  · simp [if_pos hi]
  · by_cases ha : i ∈ deepestCoords M hL <;> simp [if_neg hi, ha]

/-- **Image containment**: a small source box `[0,δ]^N` maps into `cubeBox N ε` (continuity + `phi 0 = 0`,
exactly the `phi4422_image_subset_cubeBox` pattern). -/
theorem cleanPhi_image_subset_cubeBox (M : Fin (L + 1) → ℕ) (hL : 0 < L)
    (hne : (deepestCoords M hL).Nonempty) (ε : ℝ) (hε : 0 < ε) :
    ∃ δ > 0, cleanPhi M hL hne ''
        (Set.univ.pi (fun _ : Fin (routeMAmbient M) => Set.Icc (0 : ℝ) δ))
      ⊆ cubeBox (routeMAmbient M) ε := by
  have hopen : IsOpen (Set.univ.pi (fun _ : Fin (routeMAmbient M) => Set.Ioo (-ε) ε)) :=
    isOpen_set_pi Set.finite_univ (fun _ _ => isOpen_Ioo)
  have hmem : (0 : Fin (routeMAmbient M) → ℝ)
      ∈ cleanPhi M hL hne ⁻¹' (Set.univ.pi (fun _ : Fin (routeMAmbient M) => Set.Ioo (-ε) ε)) := by
    simp only [Set.mem_preimage, cleanPhi_zero, Set.mem_pi, Set.mem_univ, true_implies,
      Set.mem_Ioo, Pi.zero_apply]
    exact fun i => ⟨by linarith, hε⟩
  obtain ⟨δ, hδ, hsub⟩ :=
    cubeBox_subset_of_isOpen (hopen.preimage (continuous_cleanPhi M hL hne)) hmem
  refine ⟨δ, hδ, ?_⟩
  rintro y ⟨x, hx, rfl⟩
  have hxcube : x ∈ cubeBox (routeMAmbient M) δ := by
    simp only [cubeBox, Set.mem_pi, Set.mem_univ, true_implies, Set.mem_Icc] at hx ⊢
    intro i; exact ⟨le_trans (by linarith [hδ]) (hx i).1, (hx i).2⟩
  have hxmem : cleanPhi M hL hne x ∈ Set.univ.pi (fun _ : Fin (routeMAmbient M) => Set.Ioo (-ε) ε) :=
    Set.mem_preimage.mp (hsub hxcube)
  refine Set.mem_pi.mpr (fun i _ => ?_)
  have hi := (Set.mem_pi.mp hxmem) i (Set.mem_univ i)
  rw [Set.mem_Ioo] at hi
  rw [Set.mem_Icc]
  exact ⟨hi.1.le, hi.2.le⟩

/-! ## The leaf-integrand identity + the genuine change-of-variables -/

/-- **The leaf-integrand identity**: `(∏_j |u_j|^{leafH j})·|routeMCore (cleanPhi u)|^{−c} =
monomialIntegrand · U^{−c}` (the radial Jacobian `|u_p|^{minAdm−1}` against the loss power, via the rate
`F∘φ = u_p²·U`). The M-agnostic `leaf_integrand334`/`leaf_integrand4422` analog. -/
theorem cleanLeaf_integrand (M : Fin (L + 1) → ℕ) (hL : 0 < L)
    (hne : (deepestCoords M hL).Nonempty) (c : ℝ) (u : Fin (routeMAmbient M) → ℝ) :
    (∏ j, |u j| ^ (cleanLeafH M hL hne j)) * |routeMCore M (cleanPhi M hL hne u)| ^ (-c)
      = monomialIntegrand (routeMAmbient M)
          (nodeLeafK (routeMAmbient M) (deepestPivot M hL hne)) (cleanLeafH M hL hne) c u
        * (cleanUfun M hL hne u) ^ (-c) := by
  set p := deepestPivot M hL hne with hp
  -- evaluate the monomial integrand: loss base `|u_p|²` (k=1 at p) × radial Jacobian `|u_p|^{minAdm−1}`
  have hmono : monomialIntegrand (routeMAmbient M) (nodeLeafK (routeMAmbient M) p)
      (cleanLeafH M hL hne) c u
        = (|u p| ^ (minAdm M - 1)) * (|u p| ^ 2) ^ (-c) := by
    unfold monomialIntegrand
    rw [cleanLeafH_prod_eq]
    congr 1
    rw [Finset.prod_eq_single p]
    · simp [nodeLeafK]
    · intro j _ hj; simp [nodeLeafK, hj]
    · intro h; exact absurd (Finset.mem_univ p) h
  rw [hmono, cleanLeafH_prod_eq, routeMCore_cleanPhi,
    show dlnLoss M 0 (unblownParams M hL hne u) = cleanUfun M hL hne u from rfl]
  have hUnn : (0 : ℝ) ≤ cleanUfun M hL hne u := cleanUfun_nonneg M hL hne u
  rw [abs_of_nonneg (mul_nonneg (sq_nonneg _) hUnn),
    Real.mul_rpow (sq_nonneg _) hUnn, ← sq_abs (u p)]
  ring

/-- **The genuine change-of-variables for `cleanPhi`** (the `cov` field): `cleanPhi` is `InjOn` off
`{u_p = 0}` (generic `pivotBlowupOn_injOn`), C¹ (`cleanPhi_hasFDerivAt`), with structural det
`|u_p|^{minAdm−1}` (`cleanPhi_abs_det`). PURE radial blow-up: NO second null-slice. -/
theorem cleanPhi_cov (M : Fin (L + 1) → ℕ) (hL : 0 < L) (hne : (deepestCoords M hL).Nonempty)
    (hNo : NoInteriorBothDrop M) (hclean : deepRank M = deepRows M)
    (V : Set (Fin (routeMAmbient M) → ℝ)) (hV : MeasurableSet V)
    (g : (Fin (routeMAmbient M) → ℝ) → ℝ≥0∞) :
    ∫⁻ x in cleanPhi M hL hne '' (V \ {x | x (deepestPivot M hL hne) = 0}), g x
      = ∫⁻ u in V \ {x | x (deepestPivot M hL hne) = 0},
          ENNReal.ofReal (∏ j, |u j| ^ (cleanLeafH M hL hne j)) * g (cleanPhi M hL hne u) := by
  set p := deepestPivot M hL hne with hp
  set S := V \ {x : Fin (routeMAmbient M) → ℝ | x p = 0} with hS
  have hSmeas : MeasurableSet S :=
    hV.diff (measurableSet_eq_fun (measurable_pi_apply p) measurable_const)
  have hcov : ∫⁻ x in cleanPhi M hL hne '' S, g x
      = ∫⁻ u in S, ENNReal.ofReal
          |(pivotBlowupOnDeriv (deepestCoords M hL) p u).det| * g (cleanPhi M hL hne u) := by
    refine lintegral_image_eq_lintegral_abs_det_fderiv_mul volume hSmeas
      (fun x _ => (cleanPhi_hasFDerivAt M hL hne x).hasFDerivWithinAt) ?_ g
    -- `InjOn` off `{u_p = 0}` (generic `pivotBlowupOn_injOn`)
    intro x hx y hy hxy
    exact pivotBlowupOn_injOn (deepestCoords M hL) p V ⟨hx.1, hx.2⟩ ⟨hy.1, hy.2⟩ hxy
  rw [hcov]
  refine setLIntegral_congr_fun hSmeas (fun u _ => ?_)
  rw [cleanPhi_abs_det M hL hne hNo hclean, cleanLeafH_prod_eq]

/-! ## The `NodeAchieverChart M` instance + the atom discharge -/

/-- **The clean-boundary achiever chart bundle** for `M` with `NoInteriorBothDrop M`, the clean
equality `deepRank = deepRows`, all widths positive, and a nonempty deepest block.

`phi = cleanPhi` (the pure radial blow-up of the deepest factor), binding axis `deepestPivot`, unit
`cleanUfun`, the radial Jacobian `|u_p|^{minAdm−1}`. All fields are banked sorry-free: the rate
`F∘φ = u_p²·U` (`routeMCore_cleanPhi`), the threshold via `leafH_pivot`, the leaf-integrand
(`cleanLeaf_integrand`), the `U > 0` a.e. (`cleanUbound`, the polynomial null-zero-set route), the image
containment (`cleanPhi_image_subset_cubeBox`), and the genuine c-o-v (`cleanPhi_cov`, det `|u_p|^{minAdm−1}`
= `pivotBlowupOn_abs_det` at `active.card = minAdm`). -/
noncomputable def cleanNodeChart (M : Fin (L + 1) → ℕ) (hL : 0 < L)
    (hne : (deepestCoords M hL).Nonempty) (hNo : NoInteriorBothDrop M)
    (hclean : deepRank M = deepRows M) (hpos : 1 ≤ minAdm M) (hMpos : ∀ s, 0 < M s) :
    NodeAchieverChart M where
  hpos := hpos
  phi := cleanPhi M hL hne
  p := deepestPivot M hL hne
  leafH := cleanLeafH M hL hne
  leafH_pivot := cleanLeafH_pivot M hL hne
  Ufun := cleanUfun M hL hne
  Ubound := cleanUbound M hL hne hMpos
  Umeas := measurable_cleanUfun M hL hne
  -- a.e. core (option-i generalization): the pointwise clean rate ⟹ the a.e. field via `Eventually.of_forall`.
  leaf_integrand := fun c => Filter.Eventually.of_forall (cleanLeaf_integrand M hL hne c)
  cov := cleanPhi_cov M hL hne hNo hclean
  image_subset := cleanPhi_image_subset_cubeBox M hL hne

/-- **The achiever box-divergence atom, discharged for the clean class.** For `M` satisfying
`NoInteriorBothDrop` (+ the clean equality, all widths positive, nonempty deepest block),
`∫⁻_{cubeBox N ε} |routeMCore M|^{−c'} = ⊤` for `c'` at-or-above `½·minAdm M`, every `ε > 0`. The clean
`NodeAchieverChart` fed through the M-agnostic assembly `routeMCore_box_diverges_of_nodeChart`. This is
the WALL-2 deliverable: the achiever atom (`routeMCore_box_diverges_achiever`) discharged for the
POLYNOMIAL-radial (clean) branch. -/
theorem routeMCore_box_diverges_clean (M : Fin (L + 1) → ℕ) (hL : 0 < L)
    (hne : (deepestCoords M hL).Nonempty) (hNo : NoInteriorBothDrop M)
    (hclean : deepRank M = deepRows M) (hpos : 1 ≤ minAdm M) (hMpos : ∀ s, 0 < M s)
    (c' : NNReal) (hc' : (minAdm M : ℝ≥0∞) / 2 ≤ (c' : ℝ≥0∞)) (ε : ℝ) (hε : 0 < ε) :
    ∫⁻ x in cubeBox (routeMAmbient M) ε,
      ENNReal.ofReal (|routeMCore M x| ^ (-(c' : ℝ))) = ⊤ :=
  routeMCore_box_diverges_of_nodeChart M
    (cleanNodeChart M hL hne hNo hclean hpos hMpos) c' hc' ε hε

end DLNFibre.DLN.RLCT
