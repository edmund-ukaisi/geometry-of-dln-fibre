/-
Copyright (c) 2026. Released under Apache 2.0; see LICENSE.
-/
import DLNFibre.Core.ChartLocalizedPolyDim
import DLNFibre.Core.DeterminantalBaseElimination
import DLNFibre.Core.ChartSection
import DLNFibre.Core.NullstellensatzCodim

/-!
# `DLNFibre.Core.ChartSweepWiring` — `ringKrullDim` chart identity → `varietyDim` sweep

The mechanical bridge from the route-3 dimension wrapper
(`ChartLocalizedPolyDim.ringKrullDim_eq_of_localized_polyExtensionAlgEquiv`) to the **`varietyDim`
form of the homogeneous-sweep identity** `hSweep` that `Core.RouteCAssembly` consumes. The wrapper
produces a `ringKrullDim` equality between the chart-closure coordinate ring `O(Σ^r)` and the fibre
coordinate ring `O(F)` shifted by `card SchurVar = δ`; this module converts that into the
`varietyDim` shape

> `varietyDim (Σ^r) = δ + varietyDim (F)`   (`δ = r·(p + q − r)`, `card SchurVar`).

via the definition `varietyDim Z = (ringKrullDim (MvPolynomial (RepCoord d) k ⧸ vanishingIdeal Z))
.unbotD 0` and the `card_SchurVar` arithmetic. Both `O(Σ^r)` and `O(F)` are finite-type `k`-algebras
(`RepCoord d` finite), so the Krull dims are genuine (not `⊥`) once the loci are nonempty, and the
`unbotD 0` wrapper commutes with the `+δ`.

This is the **conditional-bank skeleton**: the two genuinely-hard inputs — the localized chart
`AlgEquiv` `e` (route-β) and the source avoidance no-drop `hsig` (the pp-nodrop cert) — enter as
explicit named hypotheses, with the schur-side no-drop `hP` discharged from
`Core.SchurSideNoDrop`. Everything *around* them is machine-checked here. Nothing in this module
claims `e` or `hsig`.

## Main results
- `varietyDim_eq_shift_of_ringKrullDim_eq` — the `ringKrullDim → varietyDim` shift, abstract.
- `sweep_of_localizedChartAlgEquiv` — `hSweep` (`varietyDim` form) from the chart `AlgEquiv` + the two
  no-drops, packaged for `RouteCAssembly`.

**Dependency rule:** `Core` only — never import `DLNFibre.DLN`.
-/

namespace DLNFibre.Core

open MvPolynomial Matrix

universe u

variable {k : Type u} [Field k] {N : ℕ}

/-- **`varietyDim` shift from a `ringKrullDim` chart identity.** Given two sets `Z ⊆ (σ → k)`,
`F ⊆ (σ → k)` whose coordinate rings satisfy
`ringKrullDim O(Z) = ringKrullDim O(F) + (m : ℕ∞)`, with `O(F)` nontrivial (`vanishingIdeal F ≠ ⊤`)
and `σ` finite, the `varietyDim`s satisfy `varietyDim Z = (m : ℕ∞) + varietyDim F`. The `unbotD 0`
wrappers are matched because `O(F)` is a nontrivial finite-type `k`-algebra (Krull dim `≠ ⊥`), so
both sides read off genuine `ℕ∞` values. -/
theorem varietyDim_eq_shift_of_ringKrullDim_eq {σ : Type*} [Finite σ]
    {Z F : Set (σ → k)} (m : ℕ)
    (hF : (vanishingIdeal k F : Ideal (MvPolynomial σ k)) ≠ ⊤)
    (hdim : ringKrullDim (MvPolynomial σ k ⧸ vanishingIdeal k Z)
        = ringKrullDim (MvPolynomial σ k ⧸ vanishingIdeal k F) + (m : ℕ∞)) :
    varietyDim Z = (m : ℕ∞) + varietyDim F := by
  -- `O(F)` is a nontrivial Noetherian `k`-algebra, so its Krull dim is a genuine `↑a : WithBot ℕ∞`.
  haveI : Nontrivial (MvPolynomial σ k ⧸ vanishingIdeal k F) :=
    Ideal.Quotient.nontrivial_iff.mpr hF
  have hAne : ringKrullDim (MvPolynomial σ k ⧸ vanishingIdeal k F) ≠ ⊥ :=
    fun h ↦ by simpa [h] using
      ringKrullDim_nonneg_of_nontrivial (R := MvPolynomial σ k ⧸ vanishingIdeal k F)
  obtain ⟨a, ha⟩ := WithBot.ne_bot_iff_exists.mp hAne
  have hvF : varietyDim F = a := by rw [varietyDim, ← ha, WithBot.unbotD_coe]
  -- `ringKrullDim O(Z) = ↑(a + m)`, so `varietyDim Z = a + m`.
  have hvZ : varietyDim Z = a + (m : ℕ∞) := by
    have hZdim : ringKrullDim (MvPolynomial σ k ⧸ vanishingIdeal k Z)
        = (((a + (m : ℕ∞)) : ℕ∞) : WithBot ℕ∞) := by
      rw [hdim, ← ha]; push_cast; ring
    rw [varietyDim, hZdim, WithBot.unbotD_coe]
  rw [hvZ, hvF, add_comm]

section Wiring

variable (k)
variable (d : Fin (N + 2) → ℕ) (r : ℕ) (hp : r ≤ d (Fin.last (N + 1))) (hq : r ≤ d 0)

/-- The chart-closure locus `Σ^r` (rank-exactly-`r` product locus), as a coordinate set. -/
abbrev sweepSigma : Set (RepCoord d → k) := canonicalCoord d '' productRankLocus (k := k) d r

/-- The fibre `F` over the rank-`r` normal form `E`, as a coordinate set. -/
abbrev sweepFibre : Set (RepCoord d → k) :=
  canonicalCoord d '' fibre d (normalForm (d (Fin.last (N + 1))) (d 0) r hp hq)

/-- The chart-closure coordinate ring `O(Σ^r)`. -/
abbrev sweepSigmaRing : Type u :=
  MvPolynomial (RepCoord d) k ⧸ vanishingIdeal k (sweepSigma k d r)

/-- The fibre coordinate ring `O(F)`. -/
abbrev sweepFibreRing : Type u :=
  MvPolynomial (RepCoord d) k ⧸ vanishingIdeal k (sweepFibre k d r hp hq)

/-- **The homogeneous-sweep identity from the localized chart `AlgEquiv` (the conditional-bank
skeleton).** Carrying:
- `e` — the localized chart `AlgEquiv`
  `Localization.Away dsig ≃ₐ[k] Localization.Away gF` (route-β, the hard rung);
- `hsig` — the source no-drop `ringKrullDim (O(Σ^r)[1/dsig]) = ringKrullDim O(Σ^r)` (the pp-nodrop cert);
- `hP` — the schur-side no-drop (discharged from `SchurSideNoDrop`);
- `hF` — `O(F)` nontrivial;

the wrapper `ringKrullDim_eq_of_localized_polyExtensionAlgEquiv` gives
`ringKrullDim O(Σ^r) = ringKrullDim O(F) + δ`, which `varietyDim_eq_shift_of_ringKrullDim_eq` converts
into the `RouteCAssembly`-shaped `hSweep`: `varietyDim Σ^r = δ + varietyDim F`. -/
theorem sweep_of_localizedChartAlgEquiv
    (dsig : sweepSigmaRing k d r)
    (gF : MvPolynomial (SchurVar (d 0) (d (Fin.last (N + 1))) r) (sweepFibreRing k d r hp hq))
    (e : Localization.Away dsig ≃ₐ[k] Localization.Away gF)
    (hsig : ringKrullDim (Localization.Away dsig) = ringKrullDim (sweepSigmaRing k d r))
    (hP : ringKrullDim (Localization.Away gF)
        = ringKrullDim (MvPolynomial (SchurVar (d 0) (d (Fin.last (N + 1))) r)
            (sweepFibreRing k d r hp hq)))
    (hF : (vanishingIdeal k (sweepFibre k d r hp hq) :
        Ideal (MvPolynomial (RepCoord d) k)) ≠ ⊤) :
    varietyDim (sweepSigma k d r)
      = ((r * (d (Fin.last (N + 1)) + d 0 - r) : ℕ) : ℕ∞)
        + varietyDim (sweepFibre k d r hp hq) := by
  -- the wrapper output: `ringKrullDim O(Σ^r) = ringKrullDim O(F) + card SchurVar`.
  have hwrap := ringKrullDim_eq_of_localized_polyExtensionAlgEquiv (k := k)
    (ι := SchurVar (d 0) (d (Fin.last (N + 1))) r)
    (sweepSigmaRing k d r) (sweepFibreRing k d r hp hq) dsig gF e hsig hP
  -- `card SchurVar = δ`.
  have hcard : (Nat.card (SchurVar (d 0) (d (Fin.last (N + 1))) r) : ℕ∞)
      = ((r * (d (Fin.last (N + 1)) + d 0 - r) : ℕ) : ℕ∞) := by
    rw [card_SchurVar (d 0) (d (Fin.last (N + 1))) r hp hq]
  rw [hcard] at hwrap
  exact varietyDim_eq_shift_of_ringKrullDim_eq (σ := RepCoord d)
    (Z := sweepSigma k d r) (F := sweepFibre k d r hp hq)
    (r * (d (Fin.last (N + 1)) + d 0 - r)) hF hwrap

end Wiring

end DLNFibre.Core
