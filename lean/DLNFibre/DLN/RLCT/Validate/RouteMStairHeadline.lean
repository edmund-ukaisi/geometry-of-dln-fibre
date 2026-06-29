import DLNFibre.DLN.RLCT.Validate.RouteMStairFold
import DLNFibre.DLN.RLCT.Validate.RouteMInteriorDetHeadline

/-!
# `RouteMStairHeadline` — the interior-det HEADLINE via the staircase conjugacy (the sound route-2 form)

The SOUND restatement of `RouteMInteriorDetHeadline.interiorDet_headline_of_blockTri` for the direction-2
staircase route. The single-grading `Matrix.BlockTriangular` form is BLOCKED (the input/output partitions
genuinely differ, `RouteMGradingObstruction`); the determinant must be read at the LINEAR-MAP level via
the conjugation-to-a-staircase bridge `RouteMStairFold.stairMap_abs_det_conj`. This module composes that
bridge with the radial/boundary split (`Fin.prod_univ_succ`) to land the EXACT SAME headline formula

  `|det Dφ| = |u_p|^{minAdm−1} · ∏_s ( |det K_s|^{r_s+c_s} · ∏_i |q_{s,i}|^{2(t_s−1−i)} )`,

now conditional on the route-2 obligations (the staircase conjugacy + the per-layer engine-det
identifications) rather than on the refuted `BlockTriangular`. The staircase has `L+1` layers: layer `0`
is the radial blow-up (det `|u_p|^{minAdm−1}`), layers `s+1` are the per-boundary Schur⊗LDU blocks
(det `|det K_s|^{r_s+c_s}·∏_i|q_{s,i}|^{2(t_s−1−i)}`).

* `interiorDet_headline_of_stairConj` — the HEADLINE, given (i) the flat Jacobian `D` conjugate to a
  staircase `stairMap V (L+1) f c` (any layer-collecting `LinearEquiv e`), (ii) the radial block-det
  `|det (f 0)| = |u_p|^{minAdm−1}`, (iii) the boundary block-dets `|det (f (s+1))| = engine value`.

Axiom-clean `[propext, Classical.choice, Quot.sound]` (determinant + finite products; no analysis).
-/

open scoped BigOperators

noncomputable section

namespace DLNFibre.DLN.RLCT

universe u

variable {L : ℕ}

/-- **The interior-det HEADLINE via the staircase conjugacy.** Given the flat Jacobian `D : E →ₗ E`
conjugate (through a layer-collecting `LinearEquiv e : E ≃ₗ StairProd V (L+1)`) to the staircase
`stairMap V (L+1) f c`, with the radial layer-`0` block-det `|det (f 0)| = |u_p|^{minAdm−1}` and each
boundary layer-`s+1` block-det equal to the Schur⊗LDU engine value, the interior Jacobian determinant
factorizes uniformly:

  `|det D| = |u_p|^{minAdm−1} · ∏_s ( |det K_s|^{r_s+c_s} · ∏_i |q_{s,i}|^{2(t_s−1−i)} )`.

The radial/boundary identifications are exactly the engine values (`radial_abs_det_minAdm`,
`schurFrame_abs_det` × `lduCoreDeriv_abs_det`); the conjugacy is the route-2 staircase decomposition of the
real frame — the sound replacement for the refuted single-grading `BlockTriangular`. -/
theorem interiorDet_headline_of_stairConj
    {E : Type u} [AddCommGroup E] [Module ℝ E] [FiniteDimensional ℝ E]
    (V : ℕ → Type u) [∀ k, AddCommGroup (V k)] [∀ k, Module ℝ (V k)]
    [∀ k, FiniteDimensional ℝ (V k)]
    (M : Fin (L + 1) → ℕ) (f : (s : ℕ) → V s →ₗ[ℝ] V s) (c : StairCoupling V (L + 1))
    (e : E ≃ₗ[ℝ] StairProd V (L + 1)) (D : E →ₗ[ℝ] E)
    (hD : D = (e.symm : StairProd V (L + 1) →ₗ[ℝ] E) ∘ₗ stairMap V (L + 1) f c
        ∘ₗ (e : E →ₗ[ℝ] StairProd V (L + 1)))
    (up : ℝ) (t : Fin L → ℕ) (rc : Fin L → ℕ) (Kdet : Fin L → ℝ) (q : (s : Fin L) → Fin (t s) → ℝ)
    (hR : |LinearMap.det (f 0)| = |up| ^ (minAdm M - 1))
    (hB : ∀ s : Fin L, |LinearMap.det (f (s.val + 1))|
      = |Kdet s| ^ (rc s) * ∏ i : Fin (t s), |q s i| ^ (2 * ((t s : ℕ) - 1 - (i : ℕ)))) :
    |LinearMap.det D|
      = |up| ^ (minAdm M - 1)
        * ∏ s : Fin L,
            (|Kdet s| ^ (rc s) * ∏ i : Fin (t s), |q s i| ^ (2 * ((t s : ℕ) - 1 - (i : ℕ)))) := by
  rw [stairMap_abs_det_conj V (L + 1) f c e D hD, Fin.prod_univ_succ, Fin.val_zero, hR]
  congr 1
  refine Finset.prod_congr rfl (fun s _ => ?_)
  rw [Fin.val_succ]
  exact hB s

/-! ## Non-vacuity: the headline fires on a concrete staircase frame

The headline's conjugacy hypothesis IS satisfiable on a real frame, and `hR`/`hB` discharge from genuine
data — the conditional is not hollow. -/

/-- **Non-vacuity (`L = 1`, scalar layers).** On `E = StairProd (fun _ => ℝ) 2` with `e = refl`, the
staircase `D = stairMap` with radial block `mulRight up` and boundary block `mulRight k` fires the
headline: `|det D| = |up|^{minAdm−1} · (|k|^1 · empty)`. The conjugacy holds (`e = refl`, `D = stairMap`),
`hR`/`hB` from `LinearMap.det_ring`. Confirms the route-2 headline is a genuine conditional. -/
example (up k : ℝ) (M : Fin 2 → ℕ) (hM : minAdm M = 2)
    (c : StairCoupling (fun _ : ℕ => ℝ) 2) :
    |LinearMap.det
        (stairMap (fun _ : ℕ => ℝ) 2
          (fun s => if s = 0 then LinearMap.mulRight ℝ up else LinearMap.mulRight ℝ k) c)|
      = |up| ^ (minAdm M - 1)
        * ∏ _s : Fin 1, (|k| ^ (1 : ℕ)
            * ∏ i : Fin 0, |(0 : Fin 0 → ℝ) i| ^ (2 * ((0 : ℕ) - 1 - (i : ℕ)))) := by
  refine interiorDet_headline_of_stairConj (L := 1) (fun _ : ℕ => ℝ) M
    (fun s => if s = 0 then LinearMap.mulRight ℝ up else LinearMap.mulRight ℝ k) c
    (LinearEquiv.refl ℝ _) _ ?_ up (fun _ => 0) (fun _ => 1) (fun _ => k)
    (fun _ => (0 : Fin 0 → ℝ)) ?_ ?_
  · rfl
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
