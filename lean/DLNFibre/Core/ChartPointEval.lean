/-
Copyright (c) 2026. Released under Apache 2.0; see LICENSE.
-/
import DLNFibre.Core.ChartPsiReconstruct
import DLNFibre.Core.ChartBijection

/-!
# `DLNFibre.Core.ChartPointEval` — the target-side evaluation maps (Ψ descent, seam A)

Seam A of the route-β Ψ descent (thread 31): the target-side evaluation maps that turn the abstract
`Localization.Away gF` target of the Ψ comorphism into a `k`-point, so that the point-realization
argument can be run. Codex route-3.

A `k`-point of the schur-side polynomial ring `P = MvPolynomial SchurVar O(F)` is a pair
`(s : SchurVar → k, B ∈ fibre E)`: the fibre point `B` evaluates the `O(F)`-coefficients
(`evalF B`), and the Schur assignment `s` evaluates the `SchurVar` generators (`evalP s B`).

When `eval s detSchurS ≠ 0` the localizing element `gF` evaluates to a unit, so `evalP s B` lifts
across the away-localization to `evalAway s B : Localization.Away gF →ₐ[k] k`.

## Main results
- `evalF` — the fibre-point evaluation `O(F) →ₐ[k] k`.
- `evalP` — the chart-point evaluation `P →ₐ[k] k`.
- `evalP_gF` — `evalP s B gF = eval s detSchurS` (the localizing element's value).
- `evalAway` — the localized chart-point evaluation `Localization.Away gF →ₐ[k] k`.

**Dependency rule:** `Core` only — never import `DLNFibre.DLN`.
-/

namespace DLNFibre.Core

open MvPolynomial Matrix

universe u

variable {k : Type u} [Field k] {N : ℕ}

variable (k) in
/-- **The fibre-point evaluation** `evalF B hB : O(F) →ₐ[k] k`: for a fibre point `B ∈ fibre E`,
the `Ideal.Quotient.liftₐ` of `aeval (canonicalCoord d B)`, which kills `vanishingIdeal F` because
`canonicalCoord d B ∈ F`. Reads the `O(F)`-coefficient class at the point `B`. -/
noncomputable def evalF (d : Fin (N + 2) → ℕ) (r : ℕ)
    (hp : r ≤ d (Fin.last (N + 1))) (hq : r ≤ d 0)
    (B : Tuple (k := k) d) (hB : B ∈ fibre d (normalForm (d (Fin.last (N + 1))) (d 0) r hp hq)) :
    sweepFibreRing k d r hp hq →ₐ[k] k :=
  Ideal.Quotient.liftₐ (vanishingIdeal k (sweepFibre k d r hp hq))
    (aeval (canonicalCoord d B))
    (fun a ha ↦ by
      have : canonicalCoord d B ∈ sweepFibre k d r hp hq := ⟨B, hB, rfl⟩
      exact (mem_vanishingIdeal_iff.mp ha) _ this)

/-- `evalF B` reads the class of a coordinate `X x` as the entry `B x.1 x.2.1 x.2.2`. -/
@[simp] theorem evalF_mk_X (d : Fin (N + 2) → ℕ) (r : ℕ)
    (hp : r ≤ d (Fin.last (N + 1))) (hq : r ≤ d 0)
    (B : Tuple (k := k) d) (hB : B ∈ fibre d (normalForm (d (Fin.last (N + 1))) (d 0) r hp hq))
    (x : RepCoord d) :
    evalF k d r hp hq B hB (Ideal.Quotient.mk (vanishingIdeal k (sweepFibre k d r hp hq)) (X x))
      = B x.1 x.2.1 x.2.2 := by
  rw [evalF, Ideal.Quotient.liftₐ_apply, Ideal.Quotient.lift_mk]
  simp only [RingHom.coe_coe, aeval_X, canonicalCoord_apply]

variable (k) in
/-- **The chart-point evaluation** `evalP s B hB : P = MvPolynomial SchurVar O(F) →ₐ[k] k`: the
`aevalTower` of the fibre-point evaluation `evalF B` on `O(F)`-coefficients and the Schur assignment
`s` on `SchurVar` generators. The `k`-point of the chart corresponding to `(s, B)`. -/
noncomputable def evalP (d : Fin (N + 2) → ℕ) (r : ℕ)
    (hp : r ≤ d (Fin.last (N + 1))) (hq : r ≤ d 0)
    (s : SchurVar (d 0) (d (Fin.last (N + 1))) r → k)
    (B : Tuple (k := k) d) (hB : B ∈ fibre d (normalForm (d (Fin.last (N + 1))) (d 0) r hp hq)) :
    MvPolynomial (SchurVar (d 0) (d (Fin.last (N + 1))) r) (sweepFibreRing k d r hp hq) →ₐ[k] k :=
  MvPolynomial.aevalTower (evalF k d r hp hq B hB) s

/-- **The localizing element's value.** `evalP s B gF = eval s detSchurS`: the schur-side localizing
element `gF = map (algebraMap k O(F)) detSchurS` evaluates, under the chart-point evaluation, to the
schur determinant at the assignment `s`. The bridge to the unit hypothesis for the away-lift. -/
theorem evalP_gF (d : Fin (N + 2) → ℕ) (r : ℕ)
    (hp : r ≤ d (Fin.last (N + 1))) (hq : r ≤ d 0)
    (s : SchurVar (d 0) (d (Fin.last (N + 1))) r → k)
    (B : Tuple (k := k) d) (hB : B ∈ fibre d (normalForm (d (Fin.last (N + 1))) (d 0) r hp hq)) :
    evalP k d r hp hq s B hB (chartGfib k d r hp hq)
      = eval s (detSchurS (d 0) (d (Fin.last (N + 1))) r) := by
  rw [chartGfib, evalP]
  -- `aevalTower (evalF B) s = eval₂Hom (evalF B) s` as a ring hom; push through `map`.
  change MvPolynomial.eval₂Hom (evalF k d r hp hq B hB).toRingHom s
      (MvPolynomial.map (algebraMap k (sweepFibreRing k d r hp hq))
        (detSchurS (d 0) (d (Fin.last (N + 1))) r)) = _
  rw [MvPolynomial.eval₂Hom_map_hom]
  -- now `eval₂Hom ((evalF B).comp (algebraMap k O(F))) s detSchurS`; the comp is `id` on `k`.
  have hcomp : (evalF k d r hp hq B hB).toRingHom.comp (algebraMap k (sweepFibreRing k d r hp hq))
      = RingHom.id k := by
    ext x
    simp
  rw [hcomp]
  rfl

variable (k) in
/-- **The localized chart-point evaluation** `evalAway s B hs : Localization.Away gF →ₐ[k] k`: when
the schur determinant is nonzero at `s` (`eval s detSchurS ≠ 0`), the localizing element `gF` maps
to a unit (`evalP_gF` + field), so `evalP s B` lifts across the away-localization via
`IsLocalization.liftAlgHom`. The `k`-point of the principal open `D(gF)` for `(s, B)`. -/
noncomputable def evalAway (d : Fin (N + 2) → ℕ) (r : ℕ)
    (hp : r ≤ d (Fin.last (N + 1))) (hq : r ≤ d 0)
    (s : SchurVar (d 0) (d (Fin.last (N + 1))) r → k)
    (B : Tuple (k := k) d) (hB : B ∈ fibre d (normalForm (d (Fin.last (N + 1))) (d 0) r hp hq))
    (hs : eval s (detSchurS (d 0) (d (Fin.last (N + 1))) r) ≠ 0) :
    Localization.Away (chartGfib k d r hp hq) →ₐ[k] k :=
  IsLocalization.liftAlgHom (M := Submonoid.powers (chartGfib k d r hp hq))
    (f := evalP k d r hp hq s B hB)
    (by
      rintro ⟨y, n, rfl⟩
      rw [map_pow]
      refine (?_ : IsUnit (evalP k d r hp hq s B hB (chartGfib k d r hp hq))).pow n
      rw [evalP_gF]
      exact (isUnit_iff_ne_zero).mpr hs)

/-- `evalAway` agrees with `evalP` on `P`-classes (the away-lift fixes the structure map). -/
@[simp] theorem evalAway_algebraMap (d : Fin (N + 2) → ℕ) (r : ℕ)
    (hp : r ≤ d (Fin.last (N + 1))) (hq : r ≤ d 0)
    (s : SchurVar (d 0) (d (Fin.last (N + 1))) r → k)
    (B : Tuple (k := k) d) (hB : B ∈ fibre d (normalForm (d (Fin.last (N + 1))) (d 0) r hp hq))
    (hs : eval s (detSchurS (d 0) (d (Fin.last (N + 1))) r) ≠ 0)
    (a : MvPolynomial (SchurVar (d 0) (d (Fin.last (N + 1))) r) (sweepFibreRing k d r hp hq)) :
    evalAway k d r hp hq s B hB hs
        (algebraMap _ (Localization.Away (chartGfib k d r hp hq)) a)
      = evalP k d r hp hq s B hB a := by
  rw [evalAway, IsLocalization.liftAlgHom_apply, IsLocalization.lift_eq]
  rfl

end DLNFibre.Core
