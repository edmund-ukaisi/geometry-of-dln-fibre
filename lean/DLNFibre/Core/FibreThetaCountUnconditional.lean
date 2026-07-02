/-
Copyright (c) 2026. Released under Apache 2.0; see LICENSE.
-/
import DLNFibre.Core.FibreThetaCountArbitrary
import DLNFibre.Core.CThetaSortClosedForm

/-!
# `DLNFibre.Core.FibreThetaCountUnconditional` — the fibre-`θ` headline WITHOUT `Monotone d`

`Core.FibreThetaCount.ncard_topDimMinPrimes_fibre_eq_cTheta_dminus` counts the top-dimensional
irreducible components of the fibre `mult⁻¹(E_r)` as the *closed combinatorial form*
`cTheta (d − r)`. That closed form reads the **order-sensitive** prefix data of `d`, so the headline
is gated on `hd : Monotone d`. This module drops that gate.

The `Monotone d` hypothesis enters the seven-rung count chain at EXACTLY one place: the E0 rung's
`numTop d r = cTheta (d − r)` step (`Core.CThetaShiftCount.numTop_eq_cTheta_dminus`, the closed-form
evaluation). The other six rungs (W3←radical, poly, W2, chartE, W1, W0) and the
`topComponents ↔ TopDimMinPrimes` bijection are all `Monotone`-free. So **stopping the headline at
the combinatorial minimiser count `numTop d r`** — rather than the closed form `cTheta (d − r)` —
removes the gate entirely:

> for an **arbitrary** dimension vector `d` (no monotonicity), the number of top-dimensional
> irreducible components of the fibre over the rank-`r` normal form equals `numTop d r`.

The E0 rung's `Monotone`-free geometric half is
`Core.TopComponentsTopDim.ncard_topDimMinPrimes_sigma_eq_numTop` (bijection + the unconditional
`Core.CCodimZeroStrict.numTop_eq_ncard_topComponents`). Under `Monotone d`, `numTop d r`
re-evaluates to `cTheta (d − r)` via `numTop_eq_cTheta_dminus`, recovering
`ncard_topDimMinPrimes_fibre_eq_cTheta_dminus` exactly — so no content is lost, only the gate.

The arbitrary-`B` transport (same-rank component-count invariance) is the LANDED, already
`Monotone`-free `Core.FibreThetaCountArbitrary.ncard_topDimMinPrimes_fibre_eq_of_rank_eq`; we
compose it with the `numTop`-endpoint model headline to get the arbitrary-`B`, arbitrary-`d` count.

**Closed form for arbitrary `d`.** `numTop d r` is the honest floor, but relates two geometric
counts without computing either. The computable closed form for non-monotone `d` follows from the
LANDED permutation invariance of `(C, θ)`: `numTop d r = cTheta ((d ∘ Tuple.sort d) − r)`
(`Core.CThetaSortClosedForm.numTop_eq_cTheta_dminus_sort` — sort to the monotone representative,
then the `Monotone` closed form). Composing gives the fibre count as `cTheta` of the sorted shift,
for any `d`; this carries `hr : ∀ i, r ≤ d i` (which perm invariance needs) but NOT `Monotone d`.

**Dependency rule:** `Core` only — never import `DLNFibre.DLN`.
-/

namespace DLNFibre.Core

open Ideal (TopDimMinPrimes topDimMinPrimes_ncard_eq_of_ringEquiv
  topDimMinPrimes_mvPolynomial_ncard_eq topDimMinPrimes_quotient_radical_ncard_eq)

open MvPolynomial Matrix

/-! ## The `Monotone`-free model headline (at `Type 0`)

The W2 rung `Core.TopDimMinPrimesW2.ncard_topDimMinPrimes_away_chartGfib_eq` is stated at `Type`, so
the headline lands at `Type 0` (the other rungs specialise to `u = 0` freely). `Type 0` carries the
operative fields (`AlgebraicClosure ℚ`, `ℂ`). -/

section UnivZero

variable {k : Type} [Field k] {N : ℕ}

/-- **The fibre-`θ` headline, `Monotone d`-FREE (normal-form target).** For an arbitrary dimension
vector `d` — no monotonicity — the number of top-dimensional irreducible components of the fibre
`mult⁻¹(E_r)` over the rank-`r` normal form `E_r = diag(I_r, 0)` equals the combinatorial minimiser
count `numTop d r`. Composes the six `Monotone`-free fibre rungs (W3←radical, poly, W2, chartE, W1,
W0) with the `Monotone`-free geometric E0 rung
`Core.TopComponentsTopDim.ncard_topDimMinPrimes_sigma_eq_numTop`. Only `(kostantPartitions d r)`
nonempty (the fibre is nonempty), `hp/hq` (`r` bounded by the endpoint dimensions) and `hN`
(distinct endpoints, automatic for the `Fin (N + 2)` indexing) are needed — the closed-form step's
`Monotone d`, `∀ i, r ≤ d i`, and shifted-nonemptiness `h₀` all DROP. Under `Monotone d`,
`numTop d r` re-evaluates to `cTheta (d − r)`, recovering
`ncard_topDimMinPrimes_fibre_eq_cTheta_dminus`. -/
theorem ncard_topDimMinPrimes_fibre_eq_numTop [IsAlgClosed k] [CharZero k]
    (d : Fin (N + 2) → ℕ) (r : ℕ) (hp : r ≤ d (Fin.last (N + 1))) (hq : r ≤ d 0)
    (hN : (0 : Fin (N + 2)) ≠ Fin.last (N + 1))
    (h : (kostantPartitions d r).Nonempty) :
    (TopDimMinPrimes (MvPolynomial (RepCoord d) k
        ⧸ fibreGenIdeal d (normalForm (k := k) (d (Fin.last (N + 1))) (d 0) r hp hq))).ncard
      = numTop d r h := by
  -- Pin the doubly-nested base `CommRing` so the W2 rung `hW2` and the `Away` calc steps elaborate.
  letI : CommRing (MvPolynomial (SchurVar (d 0) (d (Fin.last (N + 1))) r)
    (sweepFibreRing k d r hp hq)) := inferInstance
  have hW2 := ncard_topDimMinPrimes_away_chartGfib_eq (k := k) d r hp hq hN h
  set E : Matrix (Fin (d (Fin.last (N + 1)))) (Fin (d 0)) k :=
    normalForm (d (Fin.last (N + 1))) (d 0) r hp hq with hE
  have hrad : vanishingIdeal k (sweepFibre k d r hp hq) = (fibreGenIdeal d E).radical := by
    rw [hE]; exact vanishingIdeal_image_fibre_eq_radical d _
  have hW3 : (TopDimMinPrimes (MvPolynomial (RepCoord d) k ⧸ fibreGenIdeal d E)).ncard
      = (TopDimMinPrimes (sweepFibreRing k d r hp hq)).ncard := by
    rw [topDimMinPrimes_quotient_radical_ncard_eq (fibreGenIdeal d E), ← hrad]
  have hpoly : (TopDimMinPrimes (MvPolynomial (SchurVar (d 0) (d (Fin.last (N + 1))) r)
        (sweepFibreRing k d r hp hq))).ncard
      = (TopDimMinPrimes (sweepFibreRing k d r hp hq)).ncard :=
    topDimMinPrimes_mvPolynomial_ncard_eq
  have hchart := ncard_topDimMinPrimes_chartE_eq (k := k) d r hp hq
  have hW1 := ncard_topDimMinPrimes_away_chartDsig_eq (k := k) d r hp hq hN h
  have hW0 := ncard_topDimMinPrimes_sigma_eq_sweepSigma (k := k) (N := N + 1) d r h
  -- E0 (geometric half only): `(TopDimMinPrimes O(Σ̄^r)).ncard = numTop d r`, `Monotone`-free.
  have hE0 := ncard_topDimMinPrimes_sigma_eq_numTop (k := k) (N := N + 1) (d := d) (r := r) h
  calc (TopDimMinPrimes (MvPolynomial (RepCoord d) k ⧸ fibreGenIdeal d E)).ncard
      = (TopDimMinPrimes (sweepFibreRing k d r hp hq)).ncard := hW3
    _ = (TopDimMinPrimes (MvPolynomial (SchurVar (d 0) (d (Fin.last (N + 1))) r)
          (sweepFibreRing k d r hp hq))).ncard := hpoly.symm
    _ = (TopDimMinPrimes (Localization.Away (chartGfib k d r hp hq))).ncard := hW2.symm
    _ = (TopDimMinPrimes (Localization.Away (chartDsig k d r hp hq))).ncard := hchart.symm
    _ = (TopDimMinPrimes (sweepSigmaRing k d r)).ncard := hW1
    _ = (TopDimMinPrimes (MvPolynomial (RepCoord d) k ⧸ sigmaIdeal (k := k) d r)).ncard := hW0.symm
    _ = numTop d r h := hE0

/-- **The fibre-`θ` headline for an ARBITRARY rank-`r` target `B`, `Monotone d`-FREE.** For any `B`
of rank `r` and an arbitrary dimension vector `d` (no monotonicity), the number of top-dimensional
irreducible components of the fibre `mult⁻¹ B` equals the combinatorial minimiser count
`numTop d r`. Transports the normal-form headline `ncard_topDimMinPrimes_fibre_eq_numTop` along the
LANDED, `Monotone`-free same-rank component-count invariance
`Core.FibreThetaCountArbitrary.ncard_topDimMinPrimes_fibre_eq_of_rank_eq` (`B` and the normal form
`E_r = diag(I_r, 0)` have equal rank). This no longer references the chart normal form and carries
no order hypothesis on `d`. -/
theorem ncard_topDimMinPrimes_fibre_eq_numTop_of_rank [IsAlgClosed k] [CharZero k]
    (d : Fin (N + 2) → ℕ) (r : ℕ) (hp : r ≤ d (Fin.last (N + 1))) (hq : r ≤ d 0)
    (hN : (0 : Fin (N + 2)) ≠ Fin.last (N + 1))
    (h : (kostantPartitions d r).Nonempty)
    (B : Matrix (Fin (d (Fin.last (N + 1)))) (Fin (d 0)) k) (hB : B.rank = r) :
    (TopDimMinPrimes (MvPolynomial (RepCoord d) k ⧸ fibreGenIdeal d B)).ncard
      = numTop d r h := by
  have hrankE : (normalForm (k := k) (d (Fin.last (N + 1))) (d 0) r hp hq).rank = r :=
    rank_normalForm _ _ _ hp hq
  exact (ncard_topDimMinPrimes_fibre_eq_of_rank_eq d hN B
      (normalForm (k := k) (d (Fin.last (N + 1))) (d 0) r hp hq) (hB.trans hrankE.symm)).trans
    (ncard_topDimMinPrimes_fibre_eq_numTop d r hp hq hN h)

/-! ## The closed form `cTheta` for arbitrary `d` (via LANDED permutation invariance)

These upgrade the `numTop d r` floor to the *computable* closed form
`cTheta ((d ∘ Tuple.sort d) − r)` for an arbitrary (non-monotone) `d`, composing the
`numTop`-endpoint headlines with
`Core.CThetaSortClosedForm.numTop_eq_cTheta_dminus_sort`. They add `hr : ∀ i, r ≤ d i` (which the
permutation-invariance lever needs) but still carry NO monotonicity on `d`. The `1 ≤ N`
side-condition of `numTop_eq_cTheta_dminus_sort` is automatic here: `numTop`'s index is `N + 1`, so
`1 ≤ N + 1` (`Nat.succ_pos`). -/

/-- **Fibre-`θ` closed form, arbitrary `d`, normal-form target.** For an arbitrary dimension vector
`d` with `r ≤ d i` everywhere, the top-dimensional-component count of the fibre `mult⁻¹(E_r)` over
the rank-`r` normal form equals `cTheta` of the *sorted* shift: `cTheta ((d ∘ Tuple.sort d) − r)`.
Composes `ncard_topDimMinPrimes_fibre_eq_numTop` with the permutation-invariance closed form
`Core.CThetaSortClosedForm.numTop_eq_cTheta_dminus_sort`. No `Monotone d`; for monotone `d` the sort
is the identity so this recovers `ncard_topDimMinPrimes_fibre_eq_cTheta_dminus`. -/
theorem ncard_topDimMinPrimes_fibre_eq_cTheta_dminus_sort [IsAlgClosed k] [CharZero k]
    (d : Fin (N + 2) → ℕ) (r : ℕ) (hp : r ≤ d (Fin.last (N + 1))) (hq : r ≤ d 0)
    (hN : (0 : Fin (N + 2)) ≠ Fin.last (N + 1)) (hr : ∀ i, r ≤ d i)
    (h : (kostantPartitions d r).Nonempty) :
    (TopDimMinPrimes (MvPolynomial (RepCoord d) k
        ⧸ fibreGenIdeal d (normalForm (k := k) (d (Fin.last (N + 1))) (d 0) r hp hq))).ncard
      = cTheta (dminus (d ∘ _root_.Tuple.sort d) r) := by
  rw [ncard_topDimMinPrimes_fibre_eq_numTop d r hp hq hN h,
    numTop_eq_cTheta_dminus_sort d r (Nat.succ_pos N) hr h]

/-- **Fibre-`θ` closed form, arbitrary `d`, arbitrary target `B`.** For any `B` of rank `r` and an
arbitrary `d` with `r ≤ d i` everywhere, the top-dimensional-component count of `mult⁻¹ B` equals
`cTheta ((d ∘ Tuple.sort d) − r)`. Composes the arbitrary-`B` `numTop` headline
`ncard_topDimMinPrimes_fibre_eq_numTop_of_rank` with the sorted closed form. No `Monotone d`. -/
theorem ncard_topDimMinPrimes_fibre_eq_cTheta_dminus_sort_of_rank [IsAlgClosed k] [CharZero k]
    (d : Fin (N + 2) → ℕ) (r : ℕ) (hp : r ≤ d (Fin.last (N + 1))) (hq : r ≤ d 0)
    (hN : (0 : Fin (N + 2)) ≠ Fin.last (N + 1)) (hr : ∀ i, r ≤ d i)
    (h : (kostantPartitions d r).Nonempty)
    (B : Matrix (Fin (d (Fin.last (N + 1)))) (Fin (d 0)) k) (hB : B.rank = r) :
    (TopDimMinPrimes (MvPolynomial (RepCoord d) k ⧸ fibreGenIdeal d B)).ncard
      = cTheta (dminus (d ∘ _root_.Tuple.sort d) r) := by
  rw [ncard_topDimMinPrimes_fibre_eq_numTop_of_rank d r hp hq hN h B hB,
    numTop_eq_cTheta_dminus_sort d r (Nat.succ_pos N) hr h]

/-! ## Non-vacuity: the headline fires on a genuinely NON-monotone `d`

The whole point of dropping `Monotone d` is that the count is now stated for dimension vectors the
`cTheta`-gated headline could not even mention. The witness `dNonMono = ![1, 2, 1]` (`N = 1`, so
`Fin (N + 2) = Fin 3`) is non-monotone (`1 < 2 > 1`), yet `kostantPartitions dNonMono 0` is nonempty
(4 elements), so `ncard_topDimMinPrimes_fibre_eq_numTop` instantiates at it — impossible under the
old `Monotone`-gated headline. -/

/-- A non-monotone dimension vector `d : Fin 3 → ℕ` (`1 < 2 > 1`). -/
def dNonMono : Fin 3 → ℕ := ![1, 2, 1]

/-- `dNonMono` is NOT monotone (`d 1 = 2 > 1 = d 2`). -/
theorem not_monotone_dNonMono : ¬ Monotone dNonMono := by decide

/-- `kostantPartitions dNonMono 0` is nonempty — the fibre-`θ` headline's only real hypothesis holds
for this non-monotone vector, `Monotone`-free (a `decide` witness). -/
theorem kostantPartitions_dNonMono_zero_nonempty :
    (kostantPartitions dNonMono 0).Nonempty := by decide

/-- **Non-vacuity witness.** The `Monotone`-free fibre-`θ` headline
`ncard_topDimMinPrimes_fibre_eq_numTop` fires on the NON-monotone `dNonMono = ![1, 2, 1]` at rank
`0`: the top-dimensional-component count of the fibre over the normal form equals
`numTop dNonMono 0`.
The old `cTheta`-gated headline `ncard_topDimMinPrimes_fibre_eq_cTheta_dminus` cannot even be stated
here (`hd : Monotone dNonMono` is false, `not_monotone_dNonMono`). -/
theorem ncard_topDimMinPrimes_fibre_dNonMono_eq_numTop :
    (Ideal.TopDimMinPrimes (MvPolynomial (RepCoord dNonMono) (AlgebraicClosure ℚ)
        ⧸ fibreGenIdeal dNonMono (normalForm (k := AlgebraicClosure ℚ)
            (dNonMono (Fin.last 2)) (dNonMono 0) 0 (by decide) (by decide)))).ncard
      = numTop dNonMono 0 kostantPartitions_dNonMono_zero_nonempty :=
  ncard_topDimMinPrimes_fibre_eq_numTop dNonMono 0 (by decide) (by decide) (by decide)
    kostantPartitions_dNonMono_zero_nonempty

/-- **Non-vacuity witness (closed form).** The arbitrary-`d` CLOSED-form corollary
`ncard_topDimMinPrimes_fibre_eq_cTheta_dminus_sort` also fires on the NON-monotone
`dNonMono = ![1, 2, 1]` at rank `0`: the fibre component count equals `cTheta` of the sorted shift
`(dNonMono ∘ Tuple.sort dNonMono) − 0` (`Tuple.sort` rearranges `![1, 2, 1]` to `![1, 1, 2]`). So
the count is the computable closed form, not merely `numTop`, for a genuinely non-monotone `d`. -/
theorem ncard_topDimMinPrimes_fibre_dNonMono_eq_cTheta_sort :
    (Ideal.TopDimMinPrimes (MvPolynomial (RepCoord dNonMono) (AlgebraicClosure ℚ)
        ⧸ fibreGenIdeal dNonMono (normalForm (k := AlgebraicClosure ℚ)
            (dNonMono (Fin.last 2)) (dNonMono 0) 0 (by decide) (by decide)))).ncard
      = cTheta (dminus (dNonMono ∘ _root_.Tuple.sort dNonMono) 0) :=
  ncard_topDimMinPrimes_fibre_eq_cTheta_dminus_sort dNonMono 0 (by decide) (by decide) (by decide)
    (fun _ ↦ Nat.zero_le _) kostantPartitions_dNonMono_zero_nonempty

end UnivZero

end DLNFibre.Core
