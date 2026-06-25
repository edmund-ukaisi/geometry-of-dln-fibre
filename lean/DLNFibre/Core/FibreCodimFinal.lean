/-
Copyright (c) 2026. Released under Apache 2.0; see LICENSE.
-/
import DLNFibre.Core.SourceNoDrop
import DLNFibre.Core.SchurSideNoDrop
import DLNFibre.Core.DeterminantalBaseElimination
import DLNFibre.Core.ChartLocalizedAlgEquiv

/-!
# `DLNFibre.Core.FibreCodimFinal` — the final assembly: `codim (fibre d B) = C + δ`

The expedition's central result. Feeds the four discharged route-β inputs into the localized-chart
sweep wiring (`Core.ChartSweepWiring.sweep_of_localizedChartAlgEquiv`) and then the route-c assembly
(`Core.ClosureBridge.codimRepCanonical_fibre_eq_cCodim_add_shift_of_sweep_closure`):

- the localized chart `AlgEquiv` `e = chartLocalizedAlgEquiv` (LANDED, `ChartLocalizedAlgEquiv`);
- the source no-drop `hsig = ringKrullDim_localizationAway_chartDsig_eq` (LANDED, `SourceNoDrop`);
- the schur-side no-drop `hP` (discharged here from `Core.SchurSideNoDrop` at a top prime of the
  fibre ring with the unit-`k`-coefficient `detSchurS ≠ 0`);
- `hF` (the fibre is nonempty — the realizer base-changes onto the normal form).

These give the homogeneous-sweep identity `hSweep` (`varietyDim Σ^r = δ + varietyDim F`), which the
route-c assembly turns into the unconditional

> `codimRepCanonical (fibre d B) = (cCodim d r).toNat + r·(d_N + d_0 − r)`   (rank-`r` `B`, `N≥1`).

**Dependency rule:** `Core` only — never import `DLNFibre.DLN`.
-/

namespace DLNFibre.Core

open Matrix MvPolynomial Ideal

variable {k : Type} [Field k] {N : ℕ}

/-! ## `hF` — the fibre over the normal form is nonempty -/

/-- **The fibre over the rank-`r` normal form is nonempty.** The realizer `M₀` of a minimising
Kostant partition has `rank (mult M₀) = r = rank (normalForm)`, so an end-factor base change
(`exists_baseChange_of_rank_eq`, `N ≥ 1`) carries `mult M₀` onto `normalForm`; the base-changed
tuple `P • M₀` lies in `fibre d (normalForm)`. -/
theorem fibre_normalForm_nonempty [Infinite k]
    (d : Fin (N + 2) → ℕ) (r : ℕ)
    (hp : r ≤ d (Fin.last (N + 1))) (hq : r ≤ d 0)
    (hN : (0 : Fin (N + 2)) ≠ Fin.last (N + 1))
    (h : (kostantPartitions d r).Nonempty) :
    (fibre d (normalForm (k := k) (d (Fin.last (N + 1))) (d 0) r hp hq)).Nonempty := by
  obtain ⟨m₀, hm₀, _⟩ :=
    Finset.exists_mem_eq_inf' h (fun m ↦ codimForm (N + 1) (extendℤ m))
  set M₀ := realizerD (k := k) hm₀ with hM₀
  have hrankM₀ : (mult d M₀).rank = r := rank_mult_realizerD hm₀
  set E : Matrix (Fin (d (Fin.last (N + 1)))) (Fin (d 0)) k :=
    normalForm (d (Fin.last (N + 1))) (d 0) r hp hq with hE
  have hrankE : E.rank = r := rank_normalForm _ _ _ hp hq
  obtain ⟨P, hP⟩ := exists_baseChange_of_rank_eq d hN (mult d M₀) E (hrankM₀.trans hrankE.symm)
  exact ⟨P • M₀, by rw [mem_fibre, mult_smul, ← hP]⟩

/-- **`hF`: the fibre vanishing ideal is proper.** `vanishingIdeal (sweepFibre) ≠ ⊤`, from the
fibre's nonemptiness (`fibre_normalForm_nonempty`). -/
theorem vanishingIdeal_sweepFibre_ne_top [Infinite k]
    (d : Fin (N + 2) → ℕ) (r : ℕ)
    (hp : r ≤ d (Fin.last (N + 1))) (hq : r ≤ d 0)
    (hN : (0 : Fin (N + 2)) ≠ Fin.last (N + 1))
    (h : (kostantPartitions d r).Nonempty) :
    (vanishingIdeal k (sweepFibre k d r hp hq) :
        Ideal (MvPolynomial (RepCoord d) k)) ≠ ⊤ :=
  vanishingIdeal_ne_top_of_nonempty
    ((fibre_normalForm_nonempty d r hp hq hN h).image (canonicalCoord d))

/-! ## `hP` — the schur-side no-drop for `chartGfib` -/

/-- **`hP`: the schur-side no-drop for `chartGfib`.** Inverting `gF = chartGfib` over
`MvPolynomial (SchurVar …) (sweepFibreRing …)` does not drop the dimension. Discharged from
`Core.SchurSideNoDrop.ringKrullDim_localizationAway_eq_of_schurSide` at a top-dimensional prime of
the fibre coordinate ring `O(F) = sweepFibreRing`, with the unit-`k`-coefficient witness
`detSchurS ≠ 0`. -/
theorem ringKrullDim_localizationAway_chartGfib_eq [IsAlgClosed k] [CharZero k]
    (d : Fin (N + 2) → ℕ) (r : ℕ)
    (hp : r ≤ d (Fin.last (N + 1))) (hq : r ≤ d 0)
    (hN : (0 : Fin (N + 2)) ≠ Fin.last (N + 1))
    (h : (kostantPartitions d r).Nonempty) :
    ringKrullDim (Localization.Away (chartGfib k d r hp hq))
      = ringKrullDim (MvPolynomial (SchurVar (d 0) (d (Fin.last (N + 1))) r)
          (sweepFibreRing k d r hp hq)) := by
  -- `IF = vanishingIdeal (sweepFibre)`, the (proper) defining ideal of the fibre ring `O(F)`.
  set IF : Ideal (MvPolynomial (RepCoord d) k) := vanishingIdeal k (sweepFibre k d r hp hq) with hIF
  have hIFne : IF ≠ ⊤ := vanishingIdeal_sweepFibre_ne_top d r hp hq hN h
  -- a top-dimensional minimal prime `PF` of `IF`: `dim (MvPoly ⧸ IF) = dim (MvPoly ⧸ PF)`.
  obtain ⟨PF, hPFmem, hPFge⟩ :=
    exists_minimalPrime_ringKrullDim_quotient_ge IF hIFne
  haveI hPFprime : PF.IsPrime := Ideal.minimalPrimes_isPrime hPFmem
  have hIFle : IF ≤ PF := hPFmem.1.2
  -- the reverse `dim (MvPoly ⧸ PF) ≤ dim (MvPoly ⧸ IF)` (quotient surjection `IF ≤ PF`).
  have hPFdimeq : ringKrullDim (MvPolynomial (RepCoord d) k ⧸ PF)
      = ringKrullDim (MvPolynomial (RepCoord d) k ⧸ IF) :=
    le_antisymm (ringKrullDim_le_of_surjective _ (Ideal.Quotient.factor_surjective hIFle)) hPFge
  -- the top prime `q₀ = PF / IF` of `O(F) = sweepFibreRing`; prime, full-dimensional.
  set q₀ : Ideal (sweepFibreRing k d r hp hq) := PF.map (Ideal.Quotient.mk IF) with hq₀
  haveI hq₀prime : q₀.IsPrime :=
    Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective
      (by rw [Ideal.mk_ker]; exact hIFle)
  have htopq : ringKrullDim (sweepFibreRing k d r hp hq ⧸ q₀)
      = ringKrullDim (sweepFibreRing k d r hp hq) := by
    rw [ringKrullDim_eq_of_ringEquiv (DoubleQuot.quotQuotEquivQuotOfLE hIFle),
      (rfl : ringKrullDim (sweepFibreRing k d r hp hq)
        = ringKrullDim (MvPolynomial (RepCoord d) k ⧸ IF)), hPFdimeq]
  -- apply the schur-side no-drop with `g₀ = detSchurS` (a unit-`k`-coefficient polynomial, ≠ 0).
  exact ringKrullDim_localizationAway_eq_of_schurSide (k := k)
    (ι := SchurVar (d 0) (d (Fin.last (N + 1))) r) (A := sweepFibreRing k d r hp hq)
    q₀ htopq (detSchurS (d 0) (d (Fin.last (N + 1))) r) (detSchurS_ne_zero _ _ _)

/-! ## `hSweep` — the homogeneous-sweep dimension identity -/

/-- **`hSweep`: the homogeneous-sweep dimension identity** `varietyDim Σ^r = δ + varietyDim F`.
Feeds the four discharged route-β inputs (`e`, `hsig`, `hP`, `hF`) into
`Core.ChartSweepWiring.sweep_of_localizedChartAlgEquiv`. The expedition's penultimate rung. -/
theorem varietyDim_sweepSigma_eq_shift [IsAlgClosed k] [CharZero k]
    (d : Fin (N + 2) → ℕ) (r : ℕ)
    (hp : r ≤ d (Fin.last (N + 1))) (hq : r ≤ d 0)
    (hN : (0 : Fin (N + 2)) ≠ Fin.last (N + 1))
    (h : (kostantPartitions d r).Nonempty) :
    varietyDim (sweepSigma k d r)
      = ((r * (d (Fin.last (N + 1)) + d 0 - r) : ℕ) : ℕ∞)
        + varietyDim (sweepFibre k d r hp hq) :=
  sweep_of_localizedChartAlgEquiv k d r hp hq
    (chartDsig k d r hp hq) (chartGfib k d r hp hq) (chartLocalizedAlgEquiv k d r hp hq)
    (ringKrullDim_localizationAway_chartDsig_eq d r hp hq hN h)
    (ringKrullDim_localizationAway_chartGfib_eq d r hp hq hN h)
    (vanishingIdeal_sweepFibre_ne_top d r hp hq hN h)

/-! ## The central result: `codim (fibre d B) = C + δ` -/

/-- **The fibre over the normal form has codimension `C + δ`.** Wiring `hSweep`
(`varietyDim_sweepSigma_eq_shift`) into the route-c assembly
(`ClosureBridge.codimRepCanonical_fibre_eq_cCodim_add_shift_of_sweep_closure`, which carries the
in-repo closure bridge `hClosure` and the reducible-locus catenary): for the rank-`r` normal form
`E = normalForm`, `codimRepCanonical (fibre d E) = C + δ`, `C = cCodim d r`,
`δ = r·(d_N + d_0 − r)`. -/
theorem codimRepCanonical_fibre_normalForm_eq_cCodim_add_shift [IsAlgClosed k] [CharZero k]
    (d : Fin (N + 2) → ℕ) (r : ℕ)
    (hp : r ≤ d (Fin.last (N + 1))) (hq : r ≤ d 0)
    (hN : (0 : Fin (N + 2)) ≠ Fin.last (N + 1))
    (h : (kostantPartitions d r).Nonempty) :
    codimRepCanonical (fibre d (normalForm (k := k) (d (Fin.last (N + 1))) (d 0) r hp hq))
      = ((cCodim d r h).toNat : ℕ∞)
        + ((r * (d (Fin.last (N + 1)) + d 0 - r) : ℕ) : ℕ∞) :=
  codimRepCanonical_fibre_eq_cCodim_add_shift_of_sweep_closure d r h
    (normalForm (k := k) (d (Fin.last (N + 1))) (d 0) r hp hq) (rank_normalForm _ _ _ hp hq)
    ((fibre_normalForm_nonempty d r hp hq hN h).image (canonicalCoord d))
    (nonempty_image_productRankLocus d r h |>.mono
      (Set.image_mono (productRankLocus_subset_productRankLocusLE d r)))
    (varietyDim_sweepSigma_eq_shift d r hp hq hN h)

/-- **The central result: `codim (fibre d B) = C + δ` for any rank-`r` target.** For a rank-`r`
matrix `B` (`N ≥ 1`, algebraically closed char-`0` field), the geometric codimension of the
multiplication-map fibre `mult⁻¹(B)` is the combinatorial codimension `C = cCodim d r` plus the
matrix-stratum shift `δ = r·(d_N + d_0 − r)`:

> `codimRepCanonical (fibre d B) = (cCodim d r).toNat + r·(d_N + d_0 − r)`.

Lifted from the normal-form fibre (`codimRepCanonical_fibre_normalForm_eq_cCodim_add_shift`) by the
same-rank fibre-codimension invariance `FibreNormalForm.codimRepCanonical_fibre_eq_of_rank_eq`. This
is the expedition's central geometric result — the new content underneath the (Cited) RLCT
`= ½·codim` reading. -/
theorem codimRepCanonical_fibre_eq_cCodim_add_shift [IsAlgClosed k] [CharZero k]
    (d : Fin (N + 2) → ℕ) (r : ℕ)
    (hp : r ≤ d (Fin.last (N + 1))) (hq : r ≤ d 0)
    (hN : (0 : Fin (N + 2)) ≠ Fin.last (N + 1))
    (h : (kostantPartitions d r).Nonempty)
    (B : Matrix (Fin (d (Fin.last (N + 1)))) (Fin (d 0)) k) (hB : B.rank = r) :
    codimRepCanonical (fibre d B)
      = ((cCodim d r h).toNat : ℕ∞)
        + ((r * (d (Fin.last (N + 1)) + d 0 - r) : ℕ) : ℕ∞) := by
  rw [codimRepCanonical_fibre_eq_of_rank_eq d hN B
      (normalForm (k := k) (d (Fin.last (N + 1))) (d 0) r hp hq)
      (hB.trans (rank_normalForm _ _ _ hp hq).symm),
    codimRepCanonical_fibre_normalForm_eq_cCodim_add_shift d r hp hq hN h]

end DLNFibre.Core
