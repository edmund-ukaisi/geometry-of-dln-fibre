/-
Copyright (c) 2026. Released under Apache 2.0; see LICENSE.
-/
import DLNFibre.Core.EndpointNormalization

/-!
# `DLNFibre.Core.ChartGaugeTower` — the gauge group law at the `aevalTower` level (seam E)

The tower-level version of the gauge group law `aeval_gaugeSub_gaugeSub` (LANDED,
`EndpointNormalization`), used for the seam-E round-trips: for a coefficient hom
`χ : SchurLoc →ₐ[k] T` and a variable assignment `v : RepCoord d → T`, the nested `aevalTower`
substitution of two gauges `P`, `Q` collapses to a single `aevalTower` at the product gauge `Q * P`:

> `aevalTower χ (fun y ↦ aevalTower χ v (gaugeSub d P y)) (gaugeSub d Q x)
>     = aevalTower χ v (gaugeSub d (Q * P) x)`.

Specialized to `Q * P = 1` (e.g. `Q = P⁻¹`) the RHS is `v x` (`gaugeSub d 1 x = X x`,
`aevalTower_X`). The cross-ring round-trip `chartPhiLoc ∘ chartPsiLoc` (and its mirror) reduces to
this after the tower-composition lemmas isolate the coefficient/variable legs.

The proof rides `MvPolynomial.map_aeval` (push `aevalTower χ (aevalTower χ v ∘ gaugeSub P)` through
the inner `aeval` at the ring-hom level, sidestepping the `k`-vs-`SchurLoc` scalar mismatch) + the
LANDED `aeval_gaugeSub_gaugeSub`.

## Main results
- `aevalTower_gaugeSub_gaugeSub` — the gauge group law at the `aevalTower` level.

**Dependency rule:** `Core` only — never import `DLNFibre.DLN`.
-/

namespace DLNFibre.Core

open MvPolynomial Matrix

universe u

variable {R : Type u} [CommRing R] {N : ℕ}

/-- **The gauge group law at the `aevalTower` level.** For a coefficient `R`-algebra hom
`χ : MvPolynomial (RepCoord d) R`'s coefficient ring `R →ₐ[S] T` (here `S = k`, `R = SchurLoc`) — more
precisely for `χ : R →ₐ[S] T` and a variable assignment `v : RepCoord d → T` — the nested `aevalTower`
substitution `aevalTower χ (aevalTower χ v ∘ gaugeSub P) (gaugeSub Q x)` collapses to
`aevalTower χ v (gaugeSub (Q * P) x)`. Via `MvPolynomial.map_aeval` (the inner `aeval (gaugeSub P)` is
pushed through `aevalTower χ v` at the ring-hom level) + the LANDED `aeval_gaugeSub_gaugeSub`. -/
theorem aevalTower_gaugeSub_gaugeSub {S T : Type*} [CommSemiring S] [CommRing T]
    [Algebra S R] [Algebra S T] (χ : R →ₐ[S] T)
    (d : Fin (N + 1) → ℕ) (v : RepCoord d → T) (P Q : BaseChangeGroup (k := R) d) (x : RepCoord d) :
    MvPolynomial.aevalTower χ (fun y ↦ MvPolynomial.aevalTower χ v (gaugeSub d P y))
        (gaugeSub d Q x)
      = MvPolynomial.aevalTower χ v (gaugeSub d (Q * P) x) := by
  -- `aevalTower χ (aevalTower χ v ∘ gaugeSub P)` = `aevalTower χ v ∘ aeval (gaugeSub P)` (ring-hom
  -- level): push the `aeval (gaugeSub P)` through via `map_aeval`.
  have key : (MvPolynomial.aevalTower χ
        (fun y ↦ MvPolynomial.aevalTower χ v (gaugeSub d P y))).toRingHom
      = (MvPolynomial.aevalTower χ v).toRingHom.comp
          (MvPolynomial.aeval (R := R) (gaugeSub d P)).toRingHom := by
    refine MvPolynomial.ringHom_ext ?_ ?_
    · intro a
      rw [RingHom.comp_apply]
      change MvPolynomial.aevalTower χ
          (fun y ↦ MvPolynomial.aevalTower χ v (gaugeSub d P y)) (C a)
        = MvPolynomial.aevalTower χ v (MvPolynomial.aeval (R := R) (gaugeSub d P) (C a))
      rw [MvPolynomial.aevalTower_C, MvPolynomial.aeval_C, MvPolynomial.aevalTower_algebraMap]
    · intro y
      rw [RingHom.comp_apply]
      change MvPolynomial.aevalTower χ
          (fun z ↦ MvPolynomial.aevalTower χ v (gaugeSub d P z)) (X y)
        = MvPolynomial.aevalTower χ v (MvPolynomial.aeval (R := R) (gaugeSub d P) (X y))
      rw [MvPolynomial.aevalTower_X, MvPolynomial.aeval_X]
  have hkey := DFunLike.congr_fun key (gaugeSub d Q x)
  rw [RingHom.comp_apply] at hkey
  -- LHS = `aevalTower χ v (aeval (gaugeSub P) (gaugeSub Q x))`; the inner `aeval` collapses to
  -- `gaugeSub (Q * P) x` by the LANDED `aeval_gaugeSub_gaugeSub` (its `baseChange` RHS is `gaugeSub`).
  rw [show MvPolynomial.aevalTower χ (fun y ↦ MvPolynomial.aevalTower χ v (gaugeSub d P y))
        (gaugeSub d Q x)
      = MvPolynomial.aevalTower χ v
          (MvPolynomial.aeval (R := R) (gaugeSub d P) (gaugeSub d Q x)) from hkey]
  rw [aeval_gaugeSub_gaugeSub d P Q x]
  rfl

end DLNFibre.Core
