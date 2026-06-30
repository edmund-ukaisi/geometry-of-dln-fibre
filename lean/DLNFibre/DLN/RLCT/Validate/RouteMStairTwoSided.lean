import DLNFibre.DLN.RLCT.Validate.RouteMStairFold

/-!
# `RouteMStairTwoSided` — the two-equivalence staircase det wrapper (the rectangular-partition form)

The single-`e` conjugacy `D = e.symm ∘ stairMap ∘ e` (`RouteMStairFold.stairMap_det_conj`) forces
ONE equivalence to serve as both the input and output regrouping of the flat Jacobian. The real
chart's Jacobian has two GENUINELY DIFFERENT natural partitions (`RouteMGradingObstruction`: at
`(2,2,2)` the output `FlatIdx` layer sizes `(4,4)` differ from the input `ChartIdx` boundary sizes
`(6,2)`), so a single `e` is artificial. This module banks the Codex-endorsed two-equivalence form
(decorrelated consult `threads/80-genM-nodechart/codex/detfderiv-route-answer.md`): a SEPARATE input
regrouping `eIn` and output regrouping `eOut`, the staircase `eOut ∘ D ∘ eIn.symm = stairMap`, the
det conclusion via `det_conj` + `det_comp` once the regauge factor `eOut.symm ∘ eIn` is shown
det-`±1` (abs-det `1`).

* `stairMap_abs_det_twoConj` — `|det D| = ∏_s |det (f s)|` from `eOut ∘ D ∘ eIn.symm = stairMap`
  plus `|det (eOut.symm ∘ eIn)| = 1` (the input/output regauge is abs-det-`1`).

The single-`e` form is the special case `eIn = eOut` (regauge `= id`, det `1`); this generalizes it
to the rectangular-partition layout without re-deriving a new headline — `stairMap_abs_det_twoConj`
feeds the same `Fin.prod_univ_succ` radial/boundary split as `interiorDet_headline_of_stairConj`.

Axiom-clean `[propext, Classical.choice, Quot.sound]` (determinant; no analysis).
-/

open scoped BigOperators

noncomputable section

namespace DLNFibre.DLN.RLCT

universe u

/-- **The staircase det via a two-sided conjugacy (plain).** If `D : E →ₗ E` is an endomorphism, and
two layer-collecting equivs `eIn eOut : E ≃ₗ StairProd V n` express `D`'s staircase as
`eOut ∘ D ∘ eIn.symm = stairMap V n f c`, then `det D = det (eOut.symm ∘ eIn) · ∏_s (f s).det`. The
"regauge" factor `eOut.symm ∘ eIn : E →ₗ E` carries the input/output partition mismatch; when
`eIn = eOut` it is the identity (det `1`) and this reduces to `stairMap_det_conj`. -/
theorem stairMap_det_twoConj {E : Type u} [AddCommGroup E] [Module ℝ E] [FiniteDimensional ℝ E]
    (V : ℕ → Type u) [∀ k, AddCommGroup (V k)] [∀ k, Module ℝ (V k)]
    [∀ k, FiniteDimensional ℝ (V k)] (n : ℕ) (f : (s : ℕ) → V s →ₗ[ℝ] V s) (c : StairCoupling V n)
    (eIn eOut : E ≃ₗ[ℝ] StairProd V n) (D : E →ₗ[ℝ] E)
    (hD : (eOut : E →ₗ[ℝ] StairProd V n) ∘ₗ D ∘ₗ (eIn.symm : StairProd V n →ₗ[ℝ] E)
        = stairMap V n f c) :
    LinearMap.det D
      = LinearMap.det ((eOut.symm : StairProd V n →ₗ[ℝ] E) ∘ₗ (eIn : E →ₗ[ℝ] StairProd V n))
        * ∏ s : Fin n, (f s).det := by
  -- `det` is only defined for ENDOmorphisms; `eOut.symm ∘ stairMap ∘ eIn` mixes types. Rewrite `D`
  -- as a product of two endomorphisms of `E`: the conjugate `eOut.symm ∘ stairMap ∘ eOut`
  -- (det = det stairMap by `det_conj`) and the regauge `eOut.symm ∘ eIn`.
  have hDexpand : D = ((eOut.symm : StairProd V n →ₗ[ℝ] E) ∘ₗ stairMap V n f c
      ∘ₗ (eOut : E →ₗ[ℝ] StairProd V n))
      ∘ₗ ((eOut.symm : StairProd V n →ₗ[ℝ] E) ∘ₗ (eIn : E →ₗ[ℝ] StairProd V n)) := by
    rw [← hD]
    ext x
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply,
      LinearEquiv.symm_apply_apply]
  rw [hDexpand, LinearMap.det_comp]
  -- the conjugate factor's det is `det stairMap` (`det_conj` with `e = eOut.symm`)
  have hconj := LinearMap.det_conj (stairMap V n f c) eOut.symm
  rw [LinearEquiv.symm_symm] at hconj
  rw [hconj, stairMap_det]
  ring

/-- **The staircase abs-det via a two-sided conjugacy.** The `|·|` form, the shape the interior-det
headline consumes. Given the staircase `eOut ∘ D ∘ eIn.symm = stairMap V n f c` and the regauge
factor `eOut.symm ∘ eIn` abs-det-`1` (the partition mismatch is volume-preserving), then
`|det D| = ∏_s |(f s).det|`. -/
theorem stairMap_abs_det_twoConj {E : Type u} [AddCommGroup E] [Module ℝ E] [FiniteDimensional ℝ E]
    (V : ℕ → Type u) [∀ k, AddCommGroup (V k)] [∀ k, Module ℝ (V k)]
    [∀ k, FiniteDimensional ℝ (V k)] (n : ℕ) (f : (s : ℕ) → V s →ₗ[ℝ] V s) (c : StairCoupling V n)
    (eIn eOut : E ≃ₗ[ℝ] StairProd V n) (D : E →ₗ[ℝ] E)
    (hD : (eOut : E →ₗ[ℝ] StairProd V n) ∘ₗ D ∘ₗ (eIn.symm : StairProd V n →ₗ[ℝ] E)
        = stairMap V n f c)
    (hreg : |LinearMap.det ((eOut.symm : StairProd V n →ₗ[ℝ] E) ∘ₗ (eIn : E →ₗ[ℝ] StairProd V n))|
        = 1) :
    |LinearMap.det D| = ∏ s : Fin n, |(f s).det| := by
  rw [stairMap_det_twoConj V n f c eIn eOut D hD, abs_mul, hreg, one_mul, Finset.abs_prod]

/-- **Non-vacuity (single-`e` special case).** When `eIn = eOut = e`, the regauge `e.symm ∘ e`
is the identity (det `1`), so `stairMap_abs_det_twoConj` reduces to the single-`e`
`stairMap_abs_det_conj`. Confirms the two-sided form generalizes the banked single-`e` one. -/
example {E : Type u} [AddCommGroup E] [Module ℝ E] [FiniteDimensional ℝ E]
    (V : ℕ → Type u) [∀ k, AddCommGroup (V k)] [∀ k, Module ℝ (V k)]
    [∀ k, FiniteDimensional ℝ (V k)] (n : ℕ) (f : (s : ℕ) → V s →ₗ[ℝ] V s) (c : StairCoupling V n)
    (e : E ≃ₗ[ℝ] StairProd V n) (D : E →ₗ[ℝ] E)
    (hD : (e : E →ₗ[ℝ] StairProd V n) ∘ₗ D ∘ₗ (e.symm : StairProd V n →ₗ[ℝ] E)
        = stairMap V n f c) :
    |LinearMap.det D| = ∏ s : Fin n, |(f s).det| := by
  refine stairMap_abs_det_twoConj V n f c e e D hD ?_
  rw [show (e.symm : StairProd V n →ₗ[ℝ] E) ∘ₗ (e : E →ₗ[ℝ] StairProd V n)
      = LinearMap.id from by ext x; simp]
  rw [LinearMap.det_id, abs_one]

end DLNFibre.DLN.RLCT

end
