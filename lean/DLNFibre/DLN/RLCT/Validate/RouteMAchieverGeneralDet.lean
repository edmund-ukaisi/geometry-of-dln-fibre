import Mathlib.LinearAlgebra.Determinant
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Algebra.Order.Ring.Abs

/-!
# `RouteMAchieverGeneralDet` — the general composed-determinant telescoping (R1 general achiever)

The det engine for the general-`M` achiever chart `φ_M` (the lone general-`M` `sorry` of the R1 LOWER
leg, `routeMCore_box_diverges_achiever`). The general `φ_M` is assembled as a `List.prod` of
**full-ambient** continuous endomorphisms of the fixed flat space `(Fin N → ℝ)` — one Schur/shear/LDU
factor per boundary level plus a radial blow-up. Its determinant telescopes via the **det monoid-hom**
with NO dependent `Fin (r−j)`-to-`Fin (r−j')` casts:

  `|det Dφ_M| = ∏_s (per-factor abs-det)`.

`LinearMap.det : (M →ₗ[A] M) →* A` is literally a `MonoidHom`, and the endomorphism monoid product is
`comp` (def-eq). So `MonoidHom.map_list_prod` discharges the telescoping directly; the CLM analog adds
only the CLM→LinearMap `RingHom` coercion (`toLinearMapRingHom`). This is the promoted, committed form
of the banked feasibility spike (`DLNFibre/Spike/GeneralComposedDet.lean`).

The deliverables (all PROVEN sorry-free, axiom-clean `[propext, Classical.choice, Quot.sound]`):

* `listProd_det` / `listProd_abs_det` — the plain / abs telescoping over a `List` of `LinearMap` endos.
* `listProd_clm_abs_det` — the CLM analog (the shape the DLN charts produce, `→L[ℝ]`).
* `general_composed_abs_det` / `general_composed_clm_abs_det` — the consumer contract: given the
  per-factor abs-det list `m`, `|det φDeriv| = m.prod` in one `rw`.

The variable-length composition is discharged with no induction-on-`L` cast fight; the residual
per-level work (full-ambient embeddings + per-factor block-triangular dets) is the same per-block
computation the `(3,3,3,3)` anchor (`RouteM3333Atom`) already does, now indexed by a `List`.
-/

namespace DLNFibre.DLN.RLCT

open scoped BigOperators

/-! ## The telescoping lemmas (`LinearMap` endos) -/

/-- **The telescoping lemma (plain `det`).** For a `List` of full-ambient endomorphisms of the FIXED
space `Fin N → ℝ`, the determinant of the list-product is the product of the per-factor determinants.
`LinearMap.det` is a `MonoidHom`, so this is `MonoidHom.map_list_prod` — NO dependent `Fin`-cast, NO
induction-on-length `det_comp` chain. -/
theorem listProd_det (N : ℕ) (fs : List ((Fin N → ℝ) →ₗ[ℝ] (Fin N → ℝ))) :
    (fs.prod).det = (fs.map LinearMap.det).prod :=
  LinearMap.det.map_list_prod fs

/-- **The telescoping lemma (abs `|det|`).** Composing `listProd_det` with `absHom` (the
`MonoidWithZeroHom` `|·|`): the absolute value of the list-product determinant is the product of the
per-factor absolute determinants. This is the shape the achiever box-divergence atom consumes
(`|det Dφ_M| = ∏_s m_s`). -/
theorem listProd_abs_det (N : ℕ) (fs : List ((Fin N → ℝ) →ₗ[ℝ] (Fin N → ℝ))) :
    |(fs.prod).det| = (fs.map (fun f ↦ |LinearMap.det f|)).prod := by
  rw [listProd_det]
  rw [show (fun f : (Fin N → ℝ) →ₗ[ℝ] (Fin N → ℝ) ↦ |LinearMap.det f|)
        = (fun a : ℝ ↦ |a|) ∘ LinearMap.det from rfl, ← List.map_map]
  exact map_list_prod absHom (fs.map LinearMap.det)

/-! ## The CLM analog (the DLN charts are `→L[ℝ]`)

The DLN charts are CLMs (`Q3333CLM`, `T3333Deriv`, &c. are `→L[ℝ]`). The CLM coercion to a plain
`LinearMap` is a `RingHom` (`ContinuousLinearMap.toLinearMapRingHom`), hence a `MonoidHom`, so the
list-product coercion commutes and the telescoping transports. In Mathlib's c-o-v API the determinant
of a CLM `f` is written `LinearMap.det (f : E →ₗ[ℝ] E)` (no separate `ContinuousLinearMap.det` at this
pin); we state the analog in that form. -/

/-- **The CLM telescoping lemma (abs).** For a `List` of full-ambient CONTINUOUS endomorphisms, the
abs determinant (read through the LinearMap coercion, as the Mathlib c-o-v API does) telescopes. The
CLM→LinearMap coercion respects `List.prod` (a `RingHom`), so this reduces to `listProd_abs_det` with
no new casts. -/
theorem listProd_clm_abs_det (N : ℕ)
    (fs : List ((Fin N → ℝ) →L[ℝ] (Fin N → ℝ))) :
    |LinearMap.det (fs.prod).toLinearMap|
      = (fs.map (fun f ↦ |LinearMap.det f.toLinearMap|)).prod := by
  let Φ : ((Fin N → ℝ) →L[ℝ] (Fin N → ℝ)) →* ℝ :=
    (absHom : ℝ →*₀ ℝ).toMonoidHom.comp
      (LinearMap.det.comp
        (ContinuousLinearMap.toLinearMapRingHom :
            ((Fin N → ℝ) →L[ℝ] (Fin N → ℝ)) →+* _).toMonoidHom)
  have h := Φ.map_list_prod fs
  rw [show (fun f : (Fin N → ℝ) →L[ℝ] (Fin N → ℝ) ↦ |LinearMap.det f.toLinearMap|) = ⇑Φ from rfl]
  exact h

/-! ## The consumer contract (variable-length composition discharged in one `rw`) -/

/-- **General composed-det contract.** `φDeriv = List.prod fs` with `fs` full-ambient endomorphisms of
`Fin N → ℝ`; if each factor has abs-det `m s` (indexed by the factor list position), then
`|det φDeriv| = ∏ m`. The `hfac` hypothesis packages the per-factor dets; the conclusion is the
telescoped product. The general-`M`, variable-length analog of `phi3333_abs_det`. -/
theorem general_composed_abs_det
    (N : ℕ) (fs : List ((Fin N → ℝ) →ₗ[ℝ] (Fin N → ℝ))) (m : List ℝ)
    (hfac : fs.map (fun f ↦ |LinearMap.det f|) = m) :
    |(fs.prod).det| = m.prod := by
  rw [listProd_abs_det, hfac]

/-- **General composed-det contract (CLM form).** Same, for a `φDeriv` given as a `List.prod` of
full-ambient CLMs (the shape the DLN charts produce). The per-factor abs-dets `m` are supplied by
the per-level embedding lemmas; telescoping is `listProd_clm_abs_det`. -/
theorem general_composed_clm_abs_det
    (N : ℕ) (fs : List ((Fin N → ℝ) →L[ℝ] (Fin N → ℝ))) (m : List ℝ)
    (hfac : fs.map (fun f ↦ |LinearMap.det f.toLinearMap|) = m) :
    |LinearMap.det (fs.prod).toLinearMap| = m.prod := by
  rw [listProd_clm_abs_det, hfac]

/-! ## Non-vacuity: a worked variable-length instance

A length-3 product of full-ambient `2×2` factors (a diagonal scaling, a shear, another scaling)
telescopes to the product of per-factor abs-dets. The shape the per-level factors take; the
determinant step needs no per-instance work. -/

/-- Variable-length non-vacuous check: a length-3 product of `2×2` full-ambient factors telescopes
to the product of per-factor abs-dets. -/
example (a d : ℝ) :
    |((([Matrix.toLin' !![a, 0; 0, 1],
        Matrix.toLin' !![1, (3 : ℝ); 0, 1],
        Matrix.toLin' !![1, 0; 0, d]] :
          List ((Fin 2 → ℝ) →ₗ[ℝ] (Fin 2 → ℝ))).prod).det)|
      = |a| * (|(1 : ℝ)| * |d|) := by
  rw [listProd_abs_det]
  simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one,
    LinearMap.det_toLin']
  rw [Matrix.det_fin_two_of, Matrix.det_fin_two_of, Matrix.det_fin_two_of]
  ring_nf

end DLNFibre.DLN.RLCT
