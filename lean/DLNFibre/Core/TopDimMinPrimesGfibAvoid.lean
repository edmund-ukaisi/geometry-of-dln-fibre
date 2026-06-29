/-
Copyright (c) 2026. Released under Apache 2.0; see LICENSE.
-/
import DLNFibre.Core.SchurSideNoDrop
import DLNFibre.Core.ChartLocalizedCoordinates

/-!
# `DLNFibre.Core.TopDimMinPrimesGfibAvoid` — the W2 avoidance: `gF ∉ map C q`

The avoidance half of the W2 localization-survival step of the fibre-`θ` count transport (expedition
`theta-components`, thread 08). The Schur-side localizing element `gF = chartGfib = map (algebraMap
k O(F)) detSchurS` avoids **every** extended prime `Ideal.map C q` of `O(F)[SchurVar] = MvPolynomial
SchurVar (sweepFibreRing k d r)` (for `q` any prime of `O(F)`):

> **`chartGfib_not_mem_map_C`** — `chartGfib ∉ Ideal.map C q`, any prime `q`.

After the polynomial descent (`Core.MinimalPrime.Polynomial`), every top-dimensional minimal prime of
`O(F)[SchurVar]` is `Ideal.map C q` for a top prime `q` of `O(F)`; so this lemma is exactly the
`havoid` input of the reusable survival lemma `Core.MinimalPrime.Localization` for the W2 step.

The argument (the standalone form of the avoidance buried inside
`Core.SchurSideNoDrop.ringKrullDim_localizationAway_eq_of_schurSide`): the reduction `map (mk q) :
MvPolynomial SchurVar O(F) → MvPolynomial SchurVar (O(F) ⧸ q)` kills `map C q` (each `C a`, `a ∈ q`,
maps to `C (mk q a) = 0`), and sends `gF` to `map (algebraMap k (O(F) ⧸ q)) detSchurS`, which is
nonzero because `detSchurS ≠ 0` survives the coefficient injection `k ↪ O(F) ⧸ q`. So `gF` is not in
the kernel, hence not in `map C q`.

**Dependency rule:** `Core` only — never import `DLNFibre.DLN`.
-/

namespace DLNFibre.Core

open MvPolynomial

universe u

variable {k : Type u} [Field k] {N : ℕ}

/-- **The W2 avoidance certificate.** The Schur-side localizing element `chartGfib = map (algebraMap
k O(F)) detSchurS` avoids every extended prime `Ideal.map C q` of `O(F)[SchurVar]`, for `q` any
prime of `O(F) = sweepFibreRing`. The reduction `map (mk q)` kills `map C q` but sends `chartGfib`
to the nonzero polynomial `map (algebraMap k (O(F) ⧸ q)) detSchurS` (`detSchurS ≠ 0` survives the
field coefficient injection). The `havoid` input of the reusable survival lemma at the W2 step. -/
theorem chartGfib_not_mem_map_C (d : Fin (N + 2) → ℕ) (r : ℕ)
    (hp : r ≤ d (Fin.last (N + 1))) (hq : r ≤ d 0)
    (q : Ideal (sweepFibreRing k d r hp hq)) [q.IsPrime] :
    chartGfib k d r hp hq ∉ Ideal.map (C : sweepFibreRing k d r hp hq →+* _) q := by
  set A := sweepFibreRing k d r hp hq
  set g₀ := detSchurS (k := k) (d 0) (d (Fin.last (N + 1))) r
  set gfib : MvPolynomial (SchurVar (d 0) (d (Fin.last (N + 1))) r) A :=
    MvPolynomial.map (algebraMap k A) g₀ with hgfib
  have hchart : chartGfib k d r hp hq = gfib := rfl
  rw [hchart]
  -- the reduction `red = map (mk q)` kills `map C q` and keeps `gfib` nonzero.
  set red : MvPolynomial (SchurVar (d 0) (d (Fin.last (N + 1))) r) A
      →+* MvPolynomial (SchurVar (d 0) (d (Fin.last (N + 1))) r) (A ⧸ q) :=
    MvPolynomial.map (Ideal.Quotient.mk q) with hred
  have hple : Ideal.map (C : A →+* _) q ≤ RingHom.ker red := by
    rw [Ideal.map_le_iff_le_comap]
    intro a ha
    rw [Ideal.mem_comap, RingHom.mem_ker, hred, MvPolynomial.map_C,
      Ideal.Quotient.eq_zero_iff_mem.mpr ha, map_zero]
  have hcomp : (Ideal.Quotient.mk q).comp (algebraMap k A) = algebraMap k (A ⧸ q) :=
    (IsScalarTower.algebraMap_eq k A (A ⧸ q)).symm
  have hredgfib : red gfib = MvPolynomial.map (algebraMap k (A ⧸ q)) g₀ := by
    rw [hred, hgfib, MvPolynomial.map_map, hcomp]
  have hredne : red gfib ≠ 0 := by
    rw [hredgfib, Ne, ← map_zero (MvPolynomial.map (algebraMap k (A ⧸ q)))]
    exact fun h ↦ (detSchurS_ne_zero _ _ _)
      (MvPolynomial.map_injective _ (algebraMap k (A ⧸ q)).injective h)
  exact fun h ↦ hredne (RingHom.mem_ker.mp (hple h))

end DLNFibre.Core
