/-
Copyright (c) 2026. Released under Apache 2.0; see LICENSE.
-/
import DLNFibre.Core.FibreSmoothBlock

/-!
# `DLNFibre.Core.FibreSmoothBlockExists` — closing the top-component residual of the smooth block

`FibreSmoothBlock.exists_smoothBlock_certificate` still takes a top-dimensional component
`I ∈ TopDimMinPrimes (sweepFibreRing …)` and `hI` as **hypotheses**. This module closes that
residual by witnessing that the set of top-dimensional minimal primes is **nonempty** under the same
gate, and composing.

## Main results

* `topDimMinPrimes_nonempty` — **generic engine**: for a nontrivial Noetherian ring,
  `TopDimMinPrimes A` is nonempty (a minimal prime realises the full Krull dimension). Pure
  commutative algebra, reusable — no finite-dimensionality hypothesis.
* `topDimMinPrimes_sweepFibreRing_nonempty` — the gate-specialised nonemptiness for the fibre ring.
* `exists_topComponent_smoothBlock_certificate` — **THE closed deliverable**: under the gate only
  (NO `I, hI`), there EXIST a top component `I`, a smooth closed point `m`, with `Ω[A_m⁄k]` free of
  finrank `n` and `n + codimRepCanonical (fibre d B) = Nat.card (RepCoord d)`.

**Dependency rule:** `Core` only — never import `DLNFibre.DLN`.
-/

namespace DLNFibre.Core

open Ideal (TopDimMinPrimes mem_topDimMinPrimes isPrime_of_mem_topDimMinPrimes
  comap_mem_topDimMinPrimes bijOn_comap_topDimMinPrimes topDimMinPrimes_ncard_eq_of_ringEquiv)

open Algebra MvPolynomial Matrix TensorProduct Dimension

/-! ## The generic engine — `TopDimMinPrimes` nonempty for a nontrivial Noetherian ring -/

/-- **A top-dimensional minimal prime exists.** For a nontrivial Noetherian ring `A`, the set
`TopDimMinPrimes A` (minimal primes whose quotient realises the full Krull dimension) is
**nonempty**. No finite-dimensionality hypothesis: `minimalPrimes A` is finite (Noetherian) and
nonempty (`⊥ ≠ ⊤`), so `q ↦ ringKrullDim (A ⧸ q)` attains a maximum at some minimal prime `p`; that
maximum is `ringKrullDim A`, because every prime `x` dominates a minimal prime `q ≤ x` with
`coheight x ≤ coheight q = ringKrullDim (A ⧸ q) ≤ ringKrullDim (A ⧸ p)`, so the dimension `=
⨆ coheight ≤ ringKrullDim (A ⧸ p)`; the reverse `ringKrullDim (A ⧸ p) ≤ ringKrullDim A` is the
quotient bound. -/
theorem topDimMinPrimes_nonempty (A : Type*) [CommRing A] [IsNoetherianRing A] [Nontrivial A] :
    (TopDimMinPrimes A).Nonempty := by
  -- `minimalPrimes A` is finite (Noetherian) and nonempty (`⊥ ≠ ⊤`).
  have hfin : (minimalPrimes A).Finite := minimalPrimes.finite_of_isNoetherianRing A
  have hne : (minimalPrimes A).Nonempty := by
    obtain ⟨p, hp⟩ := Ideal.nonempty_minimalPrimes (I := (⊥ : Ideal A)) bot_ne_top
    exact ⟨p, hp⟩
  -- pick a minimal prime `p` maximising the quotient Krull dimension.
  obtain ⟨p, hpmin, hpmax⟩ :=
    Set.exists_max_image (minimalPrimes A) (fun q ↦ ringKrullDim (A ⧸ q)) hfin hne
  haveI : p.IsPrime := Ideal.minimalPrimes_isPrime hpmin
  refine ⟨p, hpmin, le_antisymm (ringKrullDim_quotient_le p) ?_⟩
  -- `ringKrullDim A = ⨆ x, coheight x ≤ ringKrullDim (A ⧸ p)`.
  have hsup : ringKrullDim A = ⨆ x : PrimeSpectrum A, (Order.coheight x : WithBot ℕ∞) := by
    rw [ringKrullDim, Order.krullDim_eq_iSup_coheight]
  rw [hsup]
  refine iSup_le fun x ↦ ?_
  -- the prime `x` dominates a minimal prime `q ≤ x`.
  obtain ⟨q, hqmin, hqle⟩ :=
    Ideal.exists_minimalPrimes_le (I := (⊥ : Ideal A)) (J := x.asIdeal) bot_le
  haveI : q.IsPrime := Ideal.minimalPrimes_isPrime hqmin
  have hqx : (⟨q, ‹_›⟩ : PrimeSpectrum A) ≤ x :=
    (PrimeSpectrum.asIdeal_le_asIdeal _ _).mp hqle
  calc ((Order.coheight x : ℕ∞) : WithBot ℕ∞)
      ≤ ((Order.coheight (⟨q, ‹_›⟩ : PrimeSpectrum A) : ℕ∞) : WithBot ℕ∞) :=
        WithBot.coe_le_coe.mpr (Order.coheight_anti hqx)
    _ = ringKrullDim (A ⧸ q) :=
        (ringKrullDim_quotient_eq_coheight (⟨q, ‹_›⟩ : PrimeSpectrum A)).symm
    _ ≤ ringKrullDim (A ⧸ p) := hpmax q hqmin

/-! ## The gate-specialised nonemptiness for the fibre ring -/

section FibreCertificate

variable {k : Type} [Field k] {N : ℕ}

/-- **The fibre coordinate ring has a top-dimensional component, under the kostant gate.** Over an
infinite field, with `N ≥ 1` (`hN`) and a nonempty Kostant gate, the model fibre is nonempty
(`fibre_normalForm_nonempty`), so its vanishing ideal is proper (`vanishingIdeal_sweepFibre_ne_top`)
and `sweepFibreRing` is a nontrivial Noetherian ring — hence `TopDimMinPrimes (sweepFibreRing …)` is
nonempty (`topDimMinPrimes_nonempty`). This discharges the `I ∈ TopDimMinPrimes` hypothesis of the
smooth-block certificate. -/
theorem topDimMinPrimes_sweepFibreRing_nonempty [Infinite k]
    (d : Fin (N + 2) → ℕ) (r : ℕ) (hp : r ≤ d (Fin.last (N + 1))) (hq : r ≤ d 0)
    (hN : (0 : Fin (N + 2)) ≠ Fin.last (N + 1)) (h : (kostantPartitions d r).Nonempty) :
    (TopDimMinPrimes (sweepFibreRing k d r hp hq)).Nonempty := by
  haveI : Nontrivial (sweepFibreRing k d r hp hq) :=
    Ideal.Quotient.nontrivial_iff.mpr (vanishingIdeal_sweepFibre_ne_top d r hp hq hN h)
  exact topDimMinPrimes_nonempty (sweepFibreRing k d r hp hq)

/-- **THE SMOOTH-BLOCK CERTIFICATE, closed over the top-component input.** For a rank-`r` target `B`
over an algebraically closed char-`0` field, under the kostant gate only (NO `I, hI`), there
**exist** a top-dimensional component `I` of the reduced fibre ring, a smooth closed point `m` of
the component ring `A := sweepFibreRing … ⧸ I`, and a natural number `n` such that the local Kähler
module `Ω[A_m⁄k]` is **free** of finrank `n` with

> `n + codimRepCanonical (fibre d B) = Nat.card (RepCoord d)`,

i.e. `rank(Ω) = ambient − codim`, the free rank pinned to the **proved** fibre codimension `C + δ`
(`FibreCodimFinal`). Composes `topDimMinPrimes_sweepFibreRing_nonempty` (a top component exists)
with `exists_smoothBlock_certificate` (the per-component smooth-block certificate). This is the
closed form of the smooth-block deliverable: the top-dimensional component is produced, not assumed.

⚠ The closed point `m` is *some* point of the dense smooth open of the produced top component, not a
prescribed (θ-generic) geometric point — full component-incidence is a separate residual (as for
`exists_smoothBlock_certificate`). The free rank is the **relative dimension** `ambient − codim`,
**not** `codim` (that would be the conormal `I/I²`, a different module). -/
theorem exists_topComponent_smoothBlock_certificate [IsAlgClosed k] [CharZero k]
    (d : Fin (N + 2) → ℕ) (r : ℕ) (hp : r ≤ d (Fin.last (N + 1))) (hq : r ≤ d 0)
    (h : (kostantPartitions d r).Nonempty)
    (B : Matrix (Fin (d (Fin.last (N + 1)))) (Fin (d 0)) k) (hB : B.rank = r) :
    ∃ (I : Ideal (sweepFibreRing k d r hp hq))
      (_ : I ∈ TopDimMinPrimes (sweepFibreRing k d r hp hq))
      (m : Ideal (sweepFibreRing k d r hp hq ⧸ I)) (_ : m.IsMaximal),
      Algebra.IsSmoothAt k m ∧
      Module.Free (Localization.AtPrime m) (Ω[Localization.AtPrime m⁄k]) ∧
      ∃ n : ℕ,
        Module.finrank (Localization.AtPrime m) (Ω[Localization.AtPrime m⁄k]) = n ∧
          (n : ℕ∞) + codimRepCanonical (fibre d B) = (Nat.card (RepCoord d) : ℕ∞) := by
  have hN : (0 : Fin (N + 2)) ≠ Fin.last (N + 1) := fun he ↦ by
    simp [Fin.ext_iff, Fin.val_last] at he
  obtain ⟨I, hI⟩ := topDimMinPrimes_sweepFibreRing_nonempty (k := k) d r hp hq hN h
  exact ⟨I, hI, exists_smoothBlock_certificate d r hp hq h B hB I hI⟩

end FibreCertificate

end DLNFibre.Core
