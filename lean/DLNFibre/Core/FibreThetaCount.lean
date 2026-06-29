/-
Copyright (c) 2026. Released under Apache 2.0; see LICENSE.
-/
import DLNFibre.Core.TopComponentsTopDim
import DLNFibre.Core.TopDimMinPrimesW0
import DLNFibre.Core.TopDimMinPrimesW1W2
import DLNFibre.Core.TopDimMinPrimesW2
import DLNFibre.Core.TopDimMinPrimesChartE
import DLNFibre.Core.TopDimMinPrimesPoly
import DLNFibre.Core.TopDimMinPrimesRadical
import DLNFibre.Core.MultComorphism

/-!
# `DLNFibre.Core.FibreThetaCount` — the fibre-`θ` headline `numTop(fibre) = cTheta(d − r)`

The expedition `theta-components` headline (thread 09): the number of **top-dimensional irreducible
components of the fibre** `mult⁻¹(E_r)` over the rank-`r` normal form `E_r = diag(I_r, 0)` equals
the closed combinatorial form `cTheta (d − r) = C(m, |δ|)`. The composition of the count chain whose
rungs were landed across threads 06–09:

```
cTheta (d − r)
  =[E0]      (TopDimMinPrimes (O(Σ̄^r))).ncard          -- TopComponentsTopDim
  =[W0]      (TopDimMinPrimes (O(Σ^r))).ncard           -- TopDimMinPrimesW0
  =[W1]      (TopDimMinPrimes (O(Σ^r)[1/dsig])).ncard   -- TopDimMinPrimesW1W2 (keystone)
  =[chart e] (TopDimMinPrimes ((O(F)[Schur])[1/gF])).ncard  -- TopDimMinPrimesChartE
  =[W2]      (TopDimMinPrimes (O(F)[Schur])).ncard      -- TopDimMinPrimesW2 (keystone, flat route)
  =[poly]    (TopDimMinPrimes (O(F))).ncard             -- TopDimMinPrimesPoly
  =[W3]      (TopDimMinPrimes (O(fibre))).ncard         -- TopDimMinPrimesRadical + Nullstellensatz
```

`O(fibre) = MvPolynomial (RepCoord d) k ⧸ fibreGenIdeal d E_r` is the fibre coordinate ring (the
explicit generator ideal). Stated over the chart indexing `Fin (N + 2)` (the chart machinery needs
an interior vertex, `hN : (0 : Fin (N + 2)) ≠ Fin.last (N + 1)`); the `Σ̄^r` endpoint `E0` and W0
are instantiated at the matching `Fin ((N + 1) + 1)`.

The W2 rung enters as the explicit hypothesis `hW2` here (the diamond-routed proof
`Core.TopDimMinPrimesW2.ncard_topDimMinPrimes_away_chartGfib_eq` discharges it — wired in the
unconditional headline `numTop_fibre_eq_cTheta_dminus`).

**Dependency rule:** `Core` only — never import `DLNFibre.DLN`.
-/

namespace DLNFibre.Core

open Ideal (TopDimMinPrimes mem_topDimMinPrimes isPrime_of_mem_topDimMinPrimes
  comap_mem_topDimMinPrimes bijOn_comap_topDimMinPrimes topDimMinPrimes_ncard_eq_of_ringEquiv)

open MvPolynomial Matrix

universe u

variable {k : Type u} [Field k] {N : ℕ}

/-- **The fibre-`θ` headline, with the W2 rung supplied.** Given the W2 keystone equality `hW2`
(`(TopDimMinPrimes (Away gF)).ncard = (TopDimMinPrimes (O(F)[Schur])).ncard`), the number of
top-dimensional minimal primes of the fibre coordinate ring `O(fibre) = R ⧸ fibreGenIdeal d E_r`
equals `cTheta (d − r)`. Composes the seven landed rungs of the count chain. -/
theorem ncard_topDimMinPrimes_fibre_eq_cTheta_dminus_of [IsAlgClosed k] [CharZero k]
    (d : Fin (N + 2) → ℕ) (r : ℕ) (hp : r ≤ d (Fin.last (N + 1))) (hq : r ≤ d 0)
    (hN : (0 : Fin (N + 2)) ≠ Fin.last (N + 1))
    (hd : Monotone d) (hr : ∀ i, r ≤ d i)
    (h₀ : (kostantPartitions (dminus d r) 0).Nonempty)
    (h : (kostantPartitions d r).Nonempty)
    (hW2 : letI : CommRing (MvPolynomial (SchurVar (d 0) (d (Fin.last (N + 1))) r)
          (sweepFibreRing k d r hp hq)) := inferInstance
      (TopDimMinPrimes (Localization.Away (chartGfib k d r hp hq))).ncard
        = (TopDimMinPrimes (MvPolynomial (SchurVar (d 0) (d (Fin.last (N + 1))) r)
            (sweepFibreRing k d r hp hq))).ncard) :
    (TopDimMinPrimes (MvPolynomial (RepCoord d) k
        ⧸ fibreGenIdeal d (normalForm (k := k) (d (Fin.last (N + 1))) (d 0) r hp hq))).ncard
      = cTheta (dminus d r) := by
  -- pin the doubly-nested base `CommRing` so the `Away (chartGfib)` calc steps elaborate.
  letI : CommRing (MvPolynomial (SchurVar (d 0) (d (Fin.last (N + 1))) r)
    (sweepFibreRing k d r hp hq)) := inferInstance
  -- the rank-`r` normal form `E`.
  set E : Matrix (Fin (d (Fin.last (N + 1)))) (Fin (d 0)) k :=
    normalForm (d (Fin.last (N + 1))) (d 0) r hp hq with hE
  -- W3: `vanishingIdeal (sweepFibre) = radical (fibreGenIdeal E)`, so `O(fibre)` (generator) and
  -- `O(F)` (radical / `sweepFibreRing`) carry the same count.
  have hrad : vanishingIdeal k (sweepFibre k d r hp hq) = (fibreGenIdeal d E).radical := by
    rw [hE]; exact vanishingIdeal_image_fibre_eq_radical d _
  have hW3 : (TopDimMinPrimes (MvPolynomial (RepCoord d) k ⧸ fibreGenIdeal d E)).ncard
      = (TopDimMinPrimes (sweepFibreRing k d r hp hq)).ncard := by
    rw [topDimMinPrimes_quotient_radical_ncard_eq (fibreGenIdeal d E), ← hrad]
  -- poly descent: strip the Schur polynomial extension off `O(F)`.
  have hpoly : (TopDimMinPrimes (MvPolynomial (SchurVar (d 0) (d (Fin.last (N + 1))) r)
        (sweepFibreRing k d r hp hq))).ncard
      = (TopDimMinPrimes (sweepFibreRing k d r hp hq)).ncard :=
    topDimMinPrimes_mvPolynomial_ncard_eq
  -- chart `e`.
  have hchart := ncard_topDimMinPrimes_chartE_eq (k := k) d r hp hq
  -- W1.
  have hW1 := ncard_topDimMinPrimes_away_chartDsig_eq (k := k) d r hp hq hN h
  -- W0: closed `O(Σ̄^r)` and exact `O(Σ^r) = sweepSigmaRing`, at `Fin ((N + 1) + 1) = Fin (N + 2)`.
  have hW0 := ncard_topDimMinPrimes_sigma_eq_sweepSigma (k := k) (N := N + 1) d r h
  -- E0: `O(Σ̄^r)` count is `cTheta (d − r)`.
  have hE0 := ncard_topDimMinPrimes_sigma_eq_cTheta_dminus (k := k) (N := N + 1)
    (d := d) (r := r) hd hr h₀ h
  -- chain everything (telescope the seven rungs).
  calc (TopDimMinPrimes (MvPolynomial (RepCoord d) k ⧸ fibreGenIdeal d E)).ncard
      = (TopDimMinPrimes (sweepFibreRing k d r hp hq)).ncard := hW3
    _ = (TopDimMinPrimes (MvPolynomial (SchurVar (d 0) (d (Fin.last (N + 1))) r)
          (sweepFibreRing k d r hp hq))).ncard := hpoly.symm
    _ = (TopDimMinPrimes (Localization.Away (chartGfib k d r hp hq))).ncard := hW2.symm
    _ = (TopDimMinPrimes (Localization.Away (chartDsig k d r hp hq))).ncard := hchart.symm
    _ = (TopDimMinPrimes (sweepSigmaRing k d r)).ncard := hW1
    _ = (TopDimMinPrimes (MvPolynomial (RepCoord d) k ⧸ sigmaIdeal (k := k) d r)).ncard := hW0.symm
    _ = cTheta (dminus d r) := hE0

/-! ## The unconditional headline (at `Type 0`)

The W2 rung `Core.TopDimMinPrimesW2.ncard_topDimMinPrimes_away_chartGfib_eq` is stated at `Type` (not
`Type u`), so the unconditional headline lands at `Type 0` (the universe-polymorphic rungs E0/W0/W1/
chartE/poly/W3 specialise to `u = 0` freely). `Type 0` carries the operative fields
(`AlgebraicClosure ℚ`, `ℂ`). -/

section UnivZero

variable {k : Type} [Field k]

/-- **The fibre-`θ` headline, UNCONDITIONAL.** The number of top-dimensional irreducible components of
the fibre `mult⁻¹(E_r)` over the rank-`r` normal form `E_r = diag(I_r, 0)` equals the closed
combinatorial form `cTheta (d − r) = C(m, |δ|)`. Discharges the `_of` form's W2 rung with the LANDED
flat-route keystone application `Core.TopDimMinPrimesW2.ncard_topDimMinPrimes_away_chartGfib_eq`. This
is the expedition `theta-components` headline: the fibre top-component count `θ` is the shifted
component count, closing the count chain end-to-end. -/
theorem ncard_topDimMinPrimes_fibre_eq_cTheta_dminus [IsAlgClosed k] [CharZero k]
    (d : Fin (N + 2) → ℕ) (r : ℕ) (hp : r ≤ d (Fin.last (N + 1))) (hq : r ≤ d 0)
    (hN : (0 : Fin (N + 2)) ≠ Fin.last (N + 1))
    (hd : Monotone d) (hr : ∀ i, r ≤ d i)
    (h₀ : (kostantPartitions (dminus d r) 0).Nonempty)
    (h : (kostantPartitions d r).Nonempty) :
    (TopDimMinPrimes (MvPolynomial (RepCoord d) k
        ⧸ fibreGenIdeal d (normalForm (k := k) (d (Fin.last (N + 1))) (d 0) r hp hq))).ncard
      = cTheta (dminus d r) := by
  -- Inline the chain (rather than applying the `_of` form, whose `hW2` binder type would force an
  -- `isDefEq` across the `MvPolynomial`-over-quotient instance diamond at the application boundary).
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
  have hE0 := ncard_topDimMinPrimes_sigma_eq_cTheta_dminus (k := k) (N := N + 1)
    (d := d) (r := r) hd hr h₀ h
  calc (TopDimMinPrimes (MvPolynomial (RepCoord d) k ⧸ fibreGenIdeal d E)).ncard
      = (TopDimMinPrimes (sweepFibreRing k d r hp hq)).ncard := hW3
    _ = (TopDimMinPrimes (MvPolynomial (SchurVar (d 0) (d (Fin.last (N + 1))) r)
          (sweepFibreRing k d r hp hq))).ncard := hpoly.symm
    _ = (TopDimMinPrimes (Localization.Away (chartGfib k d r hp hq))).ncard := hW2.symm
    _ = (TopDimMinPrimes (Localization.Away (chartDsig k d r hp hq))).ncard := hchart.symm
    _ = (TopDimMinPrimes (sweepSigmaRing k d r)).ncard := hW1
    _ = (TopDimMinPrimes (MvPolynomial (RepCoord d) k ⧸ sigmaIdeal (k := k) d r)).ncard := hW0.symm
    _ = cTheta (dminus d r) := hE0

end UnivZero

end DLNFibre.Core
