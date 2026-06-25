/-
Copyright (c) 2026. Released under Apache 2.0; see LICENSE.
-/
import DLNFibre.Core.ChartPhiDescent

/-!
# `DLNFibre.Core.ChartPhiLoc` — the localized Φ comorphism (seam D capstone)

The Φ-direction mirror of seam C's `chartPsiLoc`. The Φ comorphism `chartPhiAeval : MvPolynomial
SchurVar O(F) →ₐ[k] Away dsig` carries the schur-side localizing element `gF = map (algebraMap k O(F))
detSchurS` to a **unit** of `Localization.Away dsig` (its value is `algebraMap dsig`, the inverted
element of the source localization), so it lifts across the `gF`-localization to

> `chartPhiLoc : Localization.Away gF →ₐ[k] Localization.Away dsig`.

The value: `chartPhiAeval gF = chartPhiSchurAeval detSchurS = algebraMap dsig` — the `O(F)`-coefficients
of `gF` are `k`-constants (`map (algebraMap k O(F))`), fixed by the coeff leg, so `chartPhiAeval`
reduces to the `chartPhiSchurAeval` of `detSchurS` (`ChartPhiSubstitution.chartPhiSchurAeval_detSchurS`).

## Main results
- `chartPhiAeval_chartGfib` — `chartPhiAeval gF = algebraMap dsig` (the unit value).
- `chartPhi_gF_isUnit` — `chartPhiAeval gF` is a unit.
- `chartPhiLoc` — the localized Φ comorphism `Away gF →ₐ[k] Away dsig`.

**Dependency rule:** `Core` only — never import `DLNFibre.DLN`.
-/

namespace DLNFibre.Core

open MvPolynomial Matrix

universe u

variable {k : Type u} [Field k] {N : ℕ}

variable (k) in
/-- **The Φ comorphism on a `map (algebraMap k O(F))`-lifted `k`-polynomial is `chartPhiSchurAeval`.**
`chartPhiAeval (map (algebraMap k O(F)) p) = chartPhiSchurAeval p`: the `O(F)`-coefficients of the
lift are `k`-constants, fixed by the coeff leg `chartPhiCoeff` (whose composite with `algebraMap k
O(F)` is `algebraMap k (Away dsig)`), and the `SchurVar` generators go through `chartPhiVarSub` both
sides. Ring-hom extensionality on the two composite homs `MvPolynomial SchurVar k →+* Away dsig`. -/
theorem chartPhiAeval_map_algebraMap (d : Fin (N + 2) → ℕ) (r : ℕ)
    (hp : r ≤ d (Fin.last (N + 1))) (hq : r ≤ d 0)
    (p : MvPolynomial (SchurVar (d 0) (d (Fin.last (N + 1))) r) k) :
    chartPhiAeval k d r hp hq
        (MvPolynomial.map (algebraMap k (sweepFibreRing k d r hp hq)) p)
      = chartPhiSchurAeval k d r hp hq p := by
  -- compare the two composite ring homs `MvPolynomial SchurVar k →+* Away dsig`, applied to `p`.
  have hext : (chartPhiAeval k d r hp hq).toRingHom.comp
        (MvPolynomial.map (algebraMap k (sweepFibreRing k d r hp hq)))
      = (chartPhiSchurAeval k d r hp hq).toRingHom := by
    refine MvPolynomial.ringHom_ext ?_ ?_
    · intro a
      -- constants: both sides are `algebraMap k (Away dsig) a`.
      rw [RingHom.comp_apply, MvPolynomial.map_C]
      change chartPhiAeval k d r hp hq
          (C (algebraMap k (sweepFibreRing k d r hp hq) a)) = chartPhiSchurAeval k d r hp hq (C a)
      rw [chartPhiAeval, MvPolynomial.aevalTower_C,
        AlgHom.commutes (chartPhiCoeff k d r hp hq) a]
      rw [show (C a : MvPolynomial (SchurVar (d 0) (d (Fin.last (N + 1))) r) k)
          = algebraMap k _ a from rfl, AlgHom.commutes]
    · intro s
      -- generators: `chartPhiAeval (X s) = chartPhiVarSub s = chartPhiSchurAeval (X s)`.
      rw [RingHom.comp_apply, MvPolynomial.map_X]
      change chartPhiAeval k d r hp hq (X s) = chartPhiSchurAeval k d r hp hq (X s)
      rw [chartPhiAeval, MvPolynomial.aevalTower_X, chartPhiSchurAeval, aeval_X]
  have := DFunLike.congr_fun hext p
  rw [RingHom.comp_apply] at this
  exact this

variable (k) in
/-- **The Φ comorphism carries `gF` to the inverted element `dsig`.** `chartPhiAeval gF = algebraMap
dsig`, a unit: `gF = map (algebraMap k O(F)) detSchurS`, so `chartPhiAeval gF = chartPhiSchurAeval
detSchurS` (`chartPhiAeval_map_algebraMap`), which is `algebraMap dsig`
(`chartPhiSchurAeval_detSchurS`). -/
theorem chartPhiAeval_chartGfib (d : Fin (N + 2) → ℕ) (r : ℕ)
    (hp : r ≤ d (Fin.last (N + 1))) (hq : r ≤ d 0) :
    chartPhiAeval k d r hp hq (chartGfib k d r hp hq)
      = algebraMap (sweepSigmaRing k d r) (Localization.Away (chartDsig k d r hp hq))
          (chartDsig k d r hp hq) := by
  rw [chartGfib, chartPhiAeval_map_algebraMap, chartPhiSchurAeval_detSchurS]

variable (k) in
/-- **The schur-side localizing element maps to a unit.** `chartPhiAeval gF` is a unit of
`Localization.Away dsig`: its value is `algebraMap dsig` (`chartPhiAeval_chartGfib`), the inverted
element of the source localization (`isUnit_algebraMap_chartDsig`). -/
theorem chartPhi_gF_isUnit (d : Fin (N + 2) → ℕ) (r : ℕ)
    (hp : r ≤ d (Fin.last (N + 1))) (hq : r ≤ d 0) :
    IsUnit (chartPhiAeval k d r hp hq (chartGfib k d r hp hq)) := by
  rw [chartPhiAeval_chartGfib]
  exact isUnit_algebraMap_chartDsig d r hp hq

variable (k) in
/-- **The localized Φ comorphism** `chartPhiLoc : Localization.Away gF →ₐ[k] Away dsig`: the
`IsLocalization.liftAlgHom` lift of `chartPhiAeval`, which inverts the localizing element `gF`
because `chartPhi_gF_isUnit` makes its image a unit (the powers of `gF` are then all units). The
Φ-direction half of the chart `AlgEquiv` `e`. -/
noncomputable def chartPhiLoc (d : Fin (N + 2) → ℕ) (r : ℕ)
    (hp : r ≤ d (Fin.last (N + 1))) (hq : r ≤ d 0) :
    Localization.Away (chartGfib k d r hp hq) →ₐ[k] Localization.Away (chartDsig k d r hp hq) :=
  IsLocalization.liftAlgHom (M := Submonoid.powers (chartGfib k d r hp hq))
    (f := chartPhiAeval k d r hp hq)
    (by
      rintro ⟨y, n, rfl⟩
      rw [map_pow]
      exact (chartPhi_gF_isUnit k d r hp hq).pow n)

end DLNFibre.Core
