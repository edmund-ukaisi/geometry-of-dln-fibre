/-
Copyright (c) 2026. Released under Apache 2.0; see LICENSE.
-/
import DLNFibre.Core.ChartRoundTripH1

/-!
# `DLNFibre.Core.ChartLocalizedAlgEquiv` — the localized chart `AlgEquiv` `e` (seam E)

Glues `chartPsiLoc` and `chartPhiLoc` into the chart `AlgEquiv`
`e : Localization.Away dsig ≃ₐ[k] Localization.Away gF` via `AlgEquiv.ofAlgHom`, with the two
round-trips.

**Dependency rule:** `Core` only — never import `DLNFibre.DLN`.
-/

namespace DLNFibre.Core

open MvPolynomial Matrix

universe u

variable {k : Type u} [Field k] {N : ℕ}

variable (k) in
/-- **Round-trip h2** `chartPhiLoc ∘ chartPsiLoc = id` on `Away dsig`. By `Localization.algHom_ext` +
`Ideal.Quotient` + `MvPolynomial.algHom_ext` it reduces to: for each `x : RepCoord d`,
`chartPhiLoc (chartPsiSub x) = sigmaCoordT x`. The composite `chartPhiLoc ∘ chartPsiTower =
aevalTower schurToDsig chartPhiFibSub` (`chartPhiLoc_comp_chartPsiTower`), so the value is the nested
`aevalTower` of gauges `eg⁻¹` (Ψ) and `eg` (Φ), collapsing by the gauge group law
`aevalTower_gaugeSub_gaugeSub` at `eg⁻¹ * eg = 1` to `sigmaCoordT x`. -/
theorem chartPhiLoc_comp_chartPsiLoc [Infinite k] (d : Fin (N + 2) → ℕ) (r : ℕ)
    (hp : r ≤ d (Fin.last (N + 1))) (hq : r ≤ d 0) :
    (chartPhiLoc k d r hp hq).comp (chartPsiLoc k d r hp hq)
      = AlgHom.id k (Localization.Away (chartDsig k d r hp hq)) := by
  -- reduce to `O(Σ)`-classes (`Localization.algHom_ext`), then to `RepCoord` generators.
  apply Localization.algHom_ext (Submonoid.powers (chartDsig k d r hp hq))
  apply Ideal.Quotient.algHom_ext
  apply MvPolynomial.algHom_ext
  intro x
  -- flatten the nested `.comp`s; both sides apply to the `O(Σ)`-class of `X x`.
  simp only [AlgHom.comp_apply, AlgHom.id_apply, Ideal.Quotient.mkₐ_eq_mk]
  -- the per-generator identity `chartPhiLoc (chartPsiSub x) = sigmaCoordT x` (`chartPhiLoc_chartPsiSub`).
  show chartPhiLoc k d r hp hq (chartPsiLoc k d r hp hq
      (algebraMap (sweepSigmaRing k d r) (Localization.Away (chartDsig k d r hp hq))
        (Ideal.Quotient.mk (vanishingIdeal k (sweepSigma k d r)) (X x))))
    = algebraMap (sweepSigmaRing k d r) (Localization.Away (chartDsig k d r hp hq))
        (Ideal.Quotient.mk (vanishingIdeal k (sweepSigma k d r)) (X x))
  -- `chartPsiLoc (algebraMap (mk (X x))) = chartPsiSub x`.
  rw [show chartPsiLoc k d r hp hq
        (algebraMap (sweepSigmaRing k d r) (Localization.Away (chartDsig k d r hp hq))
          (Ideal.Quotient.mk (vanishingIdeal k (sweepSigma k d r)) (X x)))
      = chartPsiSub k d r hp hq x from by
    rw [chartPsiLoc, IsLocalization.liftAlgHom_apply, IsLocalization.lift_eq]
    show chartPsiQuot k d r hp hq
        (Ideal.Quotient.mk (vanishingIdeal k (sweepSigma k d r)) (X x)) = _
    rw [chartPsiQuot, Ideal.Quotient.liftₐ_apply, Ideal.Quotient.lift_mk, RingHom.coe_coe,
      chartPsiAeval, aeval_X]]
  rw [chartPhiLoc_chartPsiSub]
  rfl

variable (k) in
/-- **Round-trip h1** `chartPsiLoc ∘ chartPhiLoc = id` on `Away gF`. By `Localization.algHom_ext`
(over `P = MvPolynomial SchurVar O(F)`) it reduces, via `chartPhiLoc_algebraMap`, to
`chartPsiLoc ∘ chartPhiAeval = algebraMap P (Away gF)` — the LANDED
`chartPsiLoc_comp_chartPhiAeval` (the `SchurVar` var leg + the `O(F)` coeff leg). -/
theorem chartPsiLoc_comp_chartPhiLoc [Infinite k] (d : Fin (N + 2) → ℕ) (r : ℕ)
    (hp : r ≤ d (Fin.last (N + 1))) (hq : r ≤ d 0) :
    (chartPsiLoc k d r hp hq).comp (chartPhiLoc k d r hp hq)
      = AlgHom.id k (Localization.Away (chartGfib k d r hp hq)) := by
  -- reduce to `P`-classes (`Localization.algHom_ext`); `chartPhiLoc (algebraMap p) = chartPhiAeval p`.
  apply Localization.algHom_ext (Submonoid.powers (chartGfib k d r hp hq))
  refine AlgHom.ext (fun p ↦ ?_)
  -- both sides applied to `algebraMap P (Away gF) p`; LHS = `chartPsiLoc (chartPhiAeval p)`.
  show chartPsiLoc k d r hp hq (chartPhiLoc k d r hp hq
      (algebraMap (MvPolynomial (SchurVar (d 0) (d (Fin.last (N + 1))) r)
        (sweepFibreRing k d r hp hq)) (Localization.Away (chartGfib k d r hp hq)) p))
    = algebraMap (MvPolynomial (SchurVar (d 0) (d (Fin.last (N + 1))) r)
        (sweepFibreRing k d r hp hq)) (Localization.Away (chartGfib k d r hp hq)) p
  rw [chartPhiLoc_algebraMap]
  -- `chartPsiLoc (chartPhiAeval p) = algebraMap P (Away gF) p` (the LANDED composite identity).
  have hp' := AlgHom.congr_fun (chartPsiLoc_comp_chartPhiAeval k d r hp hq) p
  rw [AlgHom.comp_apply] at hp'
  rw [hp']
  rfl

variable (k) in
/-- **The localized chart `AlgEquiv`** `e : Localization.Away dsig ≃ₐ[k] Localization.Away gF`. -/
noncomputable def chartLocalizedAlgEquiv [Infinite k] (d : Fin (N + 2) → ℕ) (r : ℕ)
    (hp : r ≤ d (Fin.last (N + 1))) (hq : r ≤ d 0) :
    Localization.Away (chartDsig k d r hp hq) ≃ₐ[k] Localization.Away (chartGfib k d r hp hq) :=
  AlgEquiv.ofAlgHom (chartPsiLoc k d r hp hq) (chartPhiLoc k d r hp hq)
    (chartPsiLoc_comp_chartPhiLoc k d r hp hq) (chartPhiLoc_comp_chartPsiLoc k d r hp hq)

end DLNFibre.Core
