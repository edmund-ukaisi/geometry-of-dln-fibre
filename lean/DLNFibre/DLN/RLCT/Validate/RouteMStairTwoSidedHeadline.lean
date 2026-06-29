import DLNFibre.DLN.RLCT.Validate.RouteMStairTwoSided
import DLNFibre.DLN.RLCT.Validate.RouteMInteriorDetHeadline

/-!
# `RouteMStairTwoSidedHeadline` — the interior-det headline via the two-sided staircase conjugacy

The two-equivalence analogue of `RouteMStairHeadline.interiorDet_headline_of_stairConj`: the SAME
interior-det headline output formula

  `|det D| = |u_p|^{minAdm−1} · ∏_s ( |det K_s|^{r_s+c_s} · ∏_i |q_{s,i}|^{2(t_s−1−i)} )`,

now consumed from the rectangular-partition two-sided conjugacy `eOut ∘ D ∘ eIn.symm = stairMap`
(plus the regauge `eOut.symm ∘ eIn` abs-det-`1`) rather than the artificial single-`e` form. This is
the wrapper the genuine opaque-`M` construction feeds: the input/output partitions of the real chart
differ (`RouteMGradingObstruction`), so the natural decomposition produces `eIn ≠ eOut`.

* `interiorDet_headline_of_twoStairConj` — the HEADLINE from the two-sided conjugacy + regauge
  det-`1` + the radial/boundary engine block-det identifications. Output formula identical to
  `interiorDet_headline_of_blockTri` and `interiorDet_headline_of_stairConj`.

Axiom-clean `[propext, Classical.choice, Quot.sound]` (determinant + finite products; no analysis).
-/

open scoped BigOperators

noncomputable section

namespace DLNFibre.DLN.RLCT

universe u

variable {L : ℕ}

/-- **The interior-det HEADLINE via the two-sided staircase conjugacy.** Given the flat Jacobian
`D : E →ₗ E` with the two-sided staircase `eOut ∘ D ∘ eIn.symm = stairMap V (L+1) f c` (for
layer-collecting equivs `eIn eOut : E ≃ₗ StairProd V (L+1)`), the regauge factor `eOut.symm ∘ eIn`
abs-det-`1`, the radial layer-`0` block-det `|det (f 0)| = |u_p|^{minAdm−1}`, and each boundary
layer-`s+1` block-det the Schur⊗LDU engine value, the interior Jacobian determinant factorizes
uniformly. The two-sided generalization of `interiorDet_headline_of_stairConj`. -/
theorem interiorDet_headline_of_twoStairConj
    {E : Type u} [AddCommGroup E] [Module ℝ E] [FiniteDimensional ℝ E]
    (V : ℕ → Type u) [∀ k, AddCommGroup (V k)] [∀ k, Module ℝ (V k)]
    [∀ k, FiniteDimensional ℝ (V k)]
    (M : Fin (L + 1) → ℕ) (f : (s : ℕ) → V s →ₗ[ℝ] V s) (c : StairCoupling V (L + 1))
    (eIn eOut : E ≃ₗ[ℝ] StairProd V (L + 1)) (D : E →ₗ[ℝ] E)
    (hD : (eOut : E →ₗ[ℝ] StairProd V (L + 1)) ∘ₗ D ∘ₗ (eIn.symm : StairProd V (L + 1) →ₗ[ℝ] E)
        = stairMap V (L + 1) f c)
    (hreg : |LinearMap.det ((eOut.symm : StairProd V (L + 1) →ₗ[ℝ] E)
        ∘ₗ (eIn : E →ₗ[ℝ] StairProd V (L + 1)))| = 1)
    (up : ℝ) (t : Fin L → ℕ) (rc : Fin L → ℕ) (Kdet : Fin L → ℝ) (q : (s : Fin L) → Fin (t s) → ℝ)
    (hR : |LinearMap.det (f 0)| = |up| ^ (minAdm M - 1))
    (hB : ∀ s : Fin L, |LinearMap.det (f (s.val + 1))|
      = |Kdet s| ^ (rc s) * ∏ i : Fin (t s), |q s i| ^ (2 * ((t s : ℕ) - 1 - (i : ℕ)))) :
    |LinearMap.det D|
      = |up| ^ (minAdm M - 1)
        * ∏ s : Fin L,
            (|Kdet s| ^ (rc s) * ∏ i : Fin (t s), |q s i| ^ (2 * ((t s : ℕ) - 1 - (i : ℕ)))) := by
  rw [stairMap_abs_det_twoConj V (L + 1) f c eIn eOut D hD hreg, Fin.prod_univ_succ,
    Fin.val_zero, hR]
  congr 1
  refine Finset.prod_congr rfl (fun s _ => ?_)
  rw [Fin.val_succ]
  exact hB s

/-! ## Non-vacuity: the two-sided headline fires on a concrete frame with `eIn ≠ eOut`

The headline's hypotheses are simultaneously satisfiable with distinct input/output equivs, and
`hR`/`hB` discharge from real data — the conditional is not hollow nor secretly single-`e`. -/

/-- **Non-vacuity (`L = 1`, scalar layers, distinct equivs via a det-`1` swap).** On
`E = StairProd (fun _ => ℝ) 2` with `eOut = refl` and `eIn` a det-`±1` reflection, the staircase
`eOut ∘ D ∘ eIn.symm = stairMap` (i.e. `D = stairMap ∘ eIn`) fires the headline. The regauge
`eOut.symm ∘ eIn = eIn` is abs-det-`1`, so the two-sided form accommodates `eIn ≠ eOut`. -/
example (up k : ℝ) (M : Fin 2 → ℕ) (hM : minAdm M = 2)
    (c : StairCoupling (fun _ : ℕ => ℝ) 2)
    (eIn : StairProd (fun _ : ℕ => ℝ) 2 ≃ₗ[ℝ] StairProd (fun _ : ℕ => ℝ) 2)
    (hreg : |LinearMap.det (eIn : StairProd (fun _ : ℕ => ℝ) 2 →ₗ[ℝ] StairProd (fun _ : ℕ => ℝ) 2)|
        = 1) :
    |LinearMap.det
        (stairMap (fun _ : ℕ => ℝ) 2
            (fun s => if s = 0 then LinearMap.mulRight ℝ up else LinearMap.mulRight ℝ k) c
          ∘ₗ (eIn : StairProd (fun _ : ℕ => ℝ) 2 →ₗ[ℝ] StairProd (fun _ : ℕ => ℝ) 2))|
      = |up| ^ (minAdm M - 1)
        * ∏ _s : Fin 1, (|k| ^ (1 : ℕ)
            * ∏ i : Fin 0, |(0 : Fin 0 → ℝ) i| ^ (2 * ((0 : ℕ) - 1 - (i : ℕ)))) := by
  refine interiorDet_headline_of_twoStairConj (L := 1) (fun _ : ℕ => ℝ) M
    (fun s => if s = 0 then LinearMap.mulRight ℝ up else LinearMap.mulRight ℝ k) c
    eIn (LinearEquiv.refl ℝ _) _ ?_ ?_ up (fun _ => 0) (fun _ => 1) (fun _ => k)
    (fun _ => (0 : Fin 0 → ℝ)) ?_ ?_
  · -- the conjugacy: `refl ∘ (stairMap ∘ eIn) ∘ eIn.symm = stairMap`
    ext x
    simp only [LinearMap.comp_apply, LinearEquiv.refl_apply, LinearEquiv.coe_coe,
      LinearEquiv.apply_symm_apply]
  · -- the regauge `refl.symm ∘ eIn = eIn` is abs-det-`1` by `hreg`
    rw [show (LinearEquiv.refl ℝ (StairProd (fun _ : ℕ => ℝ) 2)).symm.toLinearMap
        ∘ₗ (eIn : StairProd (fun _ : ℕ => ℝ) 2 →ₗ[ℝ] StairProd (fun _ : ℕ => ℝ) 2)
        = (eIn : StairProd (fun _ : ℕ => ℝ) 2 →ₗ[ℝ] StairProd (fun _ : ℕ => ℝ) 2) from by
      ext x; simp]
    exact hreg
  · simp only [↓reduceIte]
    rw [LinearMap.det_ring, hM]
    norm_num
  · intro s
    fin_cases s
    simp only [show (0 : ℕ) + 1 = 1 from rfl, if_neg (by decide : ¬((1 : ℕ) = 0)),
      LinearMap.det_ring]
    norm_num

end DLNFibre.DLN.RLCT

end
