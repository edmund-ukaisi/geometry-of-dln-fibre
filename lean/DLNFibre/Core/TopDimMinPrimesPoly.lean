/-
Copyright (c) 2026. Released under Apache 2.0; see LICENSE.
-/
import DLNFibre.Core.TopDimMinPrimes
import DLNFibre.Core.SchurSideNoDrop

/-!
# `DLNFibre.Core.TopDimMinPrimesPoly` — `TopDimMinPrimes` descends a polynomial extension

The polynomial-extension descent for the fibre-`θ` count transport (expedition
`theta-components`, thread 06). For a Noetherian ring `A` and a *finite* index set `ι`, the
constant-embedding `C : A → MvPolynomial ι A` induces a bijection of **minimal primes** —
`q ↦ Ideal.map C q`, with inverse `P ↦ Ideal.comap C P` — and it carries **top-dimensional**
minimal primes to top-dimensional minimal primes (both `ringKrullDim A` and `ringKrullDim (A ⧸ q)`
gain `Nat.card ι`). So the count is preserved:

> **`topDimMinPrimes_mvPolynomial_ncard_eq`** — `(TopDimMinPrimes (MvPolynomial ι A)).ncard =
> (TopDimMinPrimes A).ncard`.

This is the cleanest isolated, reusable rung of the chart transport: the fibre side of the chart
`e` carries an extra `|δ| = card SchurVar`-variable polynomial extension, and this descent strips
it off without touching the count. Pure commutative algebra — no DLN content.

The minimal-prime correspondence is hand-built (no packaged Mathlib lemma): `Ideal.map C q` is
prime (`Core.SchurSideNoDrop.isPrime_map_C_of_isPrime`), the contraction
`Ideal.comap C (Ideal.map C q) = q` holds (the reduction `map (mk q)` kills `map C q` and `C` is
injective into the domain `A ⧸ q`), and minimality transports both ways through the order-reversing
adjunction `map C ⊣ comap C`.

**Dependency rule:** `Core` only — never import `DLNFibre.DLN`.
-/

namespace DLNFibre.Core

open MvPolynomial

variable {A : Type*} [CommRing A] {ι : Type*}

/-! ## The contraction `comap C (map C q) = q` -/

/-- **The constant-coefficient contraction.** For a prime `q` of `A`, the extension `Ideal.map C q`
contracts back to `q`: `Ideal.comap C (Ideal.map C q) = q`. The reduction
`map (mk q) : MvPolynomial ι A → MvPolynomial ι (A ⧸ q)` kills `map C q` (each `C a`, `a ∈ q`,
maps to `C (mk q a) = 0`), so `C a ∈ map C q` forces `mk q a = 0` (`C` injective into the domain),
i.e. `a ∈ q`; the reverse inclusion is `Ideal.le_comap_map`. -/
theorem comap_map_C_eq (q : Ideal A) [q.IsPrime] :
    (Ideal.map (C : A →+* MvPolynomial ι A) q).comap (C : A →+* MvPolynomial ι A) = q := by
  apply le_antisymm
  · intro a ha
    rw [Ideal.mem_comap] at ha
    have hker : Ideal.map (C : A →+* MvPolynomial ι A) q
        ≤ RingHom.ker (MvPolynomial.map (Ideal.Quotient.mk q)) := by
      rw [Ideal.map_le_iff_le_comap]
      intro x hx
      rw [Ideal.mem_comap, RingHom.mem_ker, MvPolynomial.map_C,
        Ideal.Quotient.eq_zero_iff_mem.mpr hx, map_zero]
    have h2 := hker ha
    rw [RingHom.mem_ker, MvPolynomial.map_C] at h2
    have : (Ideal.Quotient.mk q) a = 0 := MvPolynomial.C_injective ι (A ⧸ q) (by simpa using h2)
    exact Ideal.Quotient.eq_zero_iff_mem.mp this
  · exact Ideal.le_comap_map

/-! ## The minimal-prime correspondence -/

/-- **`map C` carries minimal primes to minimal primes.** For `q ∈ minimalPrimes A`, the extension
`Ideal.map C q` is a minimal prime of `MvPolynomial ι A`: it is prime
(`isPrime_map_C_of_isPrime`), and any prime `P ≤ map C q` contracts to `comap C P ≤ q`, so by
minimality of `q` we get `q ≤ comap C P`, hence `map C q ≤ map C (comap C P) ≤ P`. -/
theorem map_C_mem_minimalPrimes (q : Ideal A) (hq : q ∈ minimalPrimes A) :
    Ideal.map (C : A →+* MvPolynomial ι A) q ∈ minimalPrimes (MvPolynomial ι A) := by
  haveI : q.IsPrime := hq.1.1
  haveI : (Ideal.map (C : A →+* MvPolynomial ι A) q).IsPrime := isPrime_map_C_of_isPrime q
  refine ⟨⟨inferInstance, bot_le⟩, ?_⟩
  rintro P ⟨hPp, -⟩ hPle
  haveI := hPp
  have hcomple : P.comap (C : A →+* MvPolynomial ι A) ≤ q := by
    rw [← comap_map_C_eq (ι := ι) q]; exact Ideal.comap_mono hPle
  have hcomp_min := hq.2 ⟨Ideal.IsPrime.comap _, bot_le⟩ hcomple
  calc Ideal.map (C : A →+* MvPolynomial ι A) q
      ≤ Ideal.map (C : A →+* MvPolynomial ι A) (P.comap (C : A →+* MvPolynomial ι A)) :=
        Ideal.map_mono hcomp_min
    _ ≤ P := Ideal.map_comap_le

/-- **`comap C` carries minimal primes to minimal primes.** For `P ∈ minimalPrimes (MvPolynomial ι
A)`, the contraction `Ideal.comap C P` is a minimal prime of `A`: any prime `q ≤ comap C P` lifts
to `map C q ≤ P` (a prime), and minimality of `P` forces `P = map C q`, so
`comap C P = comap C (map C q) = q`. -/
theorem comap_C_mem_minimalPrimes (P : Ideal (MvPolynomial ι A))
    (hP : P ∈ minimalPrimes (MvPolynomial ι A)) :
    P.comap (C : A →+* MvPolynomial ι A) ∈ minimalPrimes A := by
  haveI : P.IsPrime := hP.1.1
  refine ⟨⟨Ideal.IsPrime.comap _, bot_le⟩, ?_⟩
  rintro q ⟨hqp, -⟩ hqle
  haveI := hqp
  have hmaple : Ideal.map (C : A →+* MvPolynomial ι A) q ≤ P :=
    (Ideal.map_mono hqle).trans Ideal.map_comap_le
  haveI : (Ideal.map (C : A →+* MvPolynomial ι A) q).IsPrime := isPrime_map_C_of_isPrime q
  have hPeq : P ≤ Ideal.map (C : A →+* MvPolynomial ι A) q := hP.2 ⟨inferInstance, bot_le⟩ hmaple
  have hcomple : P.comap (C : A →+* MvPolynomial ι A)
      ≤ (Ideal.map (C : A →+* MvPolynomial ι A) q).comap (C : A →+* MvPolynomial ι A) :=
    Ideal.comap_mono hPeq
  rwa [comap_map_C_eq (ι := ι) q] at hcomple

/-- **Every minimal prime of `MvPolynomial ι A` is extended from `A`.** For `P ∈ minimalPrimes`,
`Ideal.map C (Ideal.comap C P) = P`: `map C (comap C P)` is a minimal prime (`comap C P` is one,
then `map C`), it sits `≤ P` (`map_comap_le`), and `P` is minimal, so they coincide. -/
theorem map_comap_C_of_mem_minimalPrimes (P : Ideal (MvPolynomial ι A))
    (hP : P ∈ minimalPrimes (MvPolynomial ι A)) :
    Ideal.map (C : A →+* MvPolynomial ι A) (P.comap (C : A →+* MvPolynomial ι A)) = P := by
  haveI : P.IsPrime := hP.1.1
  have hqmin := comap_C_mem_minimalPrimes P hP
  have hmapmin := map_C_mem_minimalPrimes (ι := ι) (P.comap (C : A →+* MvPolynomial ι A)) hqmin
  have hle : Ideal.map (C : A →+* MvPolynomial ι A) (P.comap (C : A →+* MvPolynomial ι A)) ≤ P :=
    Ideal.map_comap_le
  haveI : (Ideal.map (C : A →+* MvPolynomial ι A)
      (P.comap (C : A →+* MvPolynomial ι A))).IsPrime := hmapmin.1.1
  exact le_antisymm hle (hP.2 ⟨inferInstance, bot_le⟩ hle)

/-! ## The dimension shift on quotients -/

/-- **The quotient by `map C q` adds `card ι` to the Krull dimension.** Via the algebra equivalence
`MvPolynomial ι (A ⧸ q) ≃ (MvPolynomial ι A) ⧸ map C q` (`quotientEquivQuotientMvPolynomial`) and
`MvPolynomial.ringKrullDim_of_isNoetherianRing`. Needs `A ⧸ q` Noetherian (from `A` Noetherian). -/
theorem ringKrullDim_quotient_map_C [IsNoetherianRing A] [Finite ι] (q : Ideal A) [q.IsPrime] :
    ringKrullDim (MvPolynomial ι A ⧸ Ideal.map (C : A →+* MvPolynomial ι A) q)
      = ringKrullDim (A ⧸ q) + Nat.card ι := by
  haveI : IsNoetherianRing (A ⧸ q) := inferInstance
  rw [← ringKrullDim_eq_of_ringEquiv
      (MvPolynomial.quotientEquivQuotientMvPolynomial (σ := ι) (R := A) q).toRingEquiv,
    MvPolynomial.ringKrullDim_of_isNoetherianRing]

/-! ## Top-dimensionality transports -/

/-- **`map C` carries top-dimensional minimal primes to top-dimensional ones.** For
`q ∈ TopDimMinPrimes A`, the extension `Ideal.map C q ∈ TopDimMinPrimes (MvPolynomial ι A)`:
minimality is `map_C_mem_minimalPrimes`, and the top-dimensional equality shifts by `card ι` on
both numerator (`ringKrullDim_quotient_map_C`) and ambient
(`MvPolynomial.ringKrullDim_of_isNoetherianRing`). -/
theorem map_C_mem_topDimMinPrimes [IsNoetherianRing A] [Finite ι] (q : Ideal A)
    (hq : q ∈ TopDimMinPrimes A) :
    Ideal.map (C : A →+* MvPolynomial ι A) q ∈ TopDimMinPrimes (MvPolynomial ι A) := by
  haveI : q.IsPrime := hq.1.1.1
  refine ⟨map_C_mem_minimalPrimes q hq.1, ?_⟩
  rw [ringKrullDim_quotient_map_C (ι := ι) q, hq.2, MvPolynomial.ringKrullDim_of_isNoetherianRing]

/-- **`comap C` carries top-dimensional minimal primes to top-dimensional ones.** The inverse
direction: for `P ∈ TopDimMinPrimes (MvPolynomial ι A)`, `Ideal.comap C P ∈ TopDimMinPrimes A`.
Minimality is `comap_C_mem_minimalPrimes`; the dimension equality is recovered by cancelling the
`card ι` shift (`ringKrullDim_quotient_map_C` applied to `P = map C (comap C P)`). -/
theorem comap_C_mem_topDimMinPrimes [IsNoetherianRing A] [Finite ι]
    (P : Ideal (MvPolynomial ι A)) (hP : P ∈ TopDimMinPrimes (MvPolynomial ι A)) :
    P.comap (C : A →+* MvPolynomial ι A) ∈ TopDimMinPrimes A := by
  have hPmin := hP.1
  have hqmin := comap_C_mem_minimalPrimes P hPmin
  haveI : (P.comap (C : A →+* MvPolynomial ι A)).IsPrime := hqmin.1.1
  refine ⟨hqmin, ?_⟩
  -- `dim (A ⧸ comap C P) + card ι = dim (B ⧸ map C (comap C P)) = dim (B ⧸ P) = dim B
  --   = dim A + card ι`, so cancel `card ι`.
  have hmap := map_comap_C_of_mem_minimalPrimes P hPmin
  have key : ringKrullDim (A ⧸ P.comap (C : A →+* MvPolynomial ι A)) + (Nat.card ι : WithBot ℕ∞)
      = ringKrullDim A + (Nat.card ι : WithBot ℕ∞) := by
    rw [← ringKrullDim_quotient_map_C (ι := ι) (P.comap (C : A →+* MvPolynomial ι A)), hmap, hP.2,
      MvPolynomial.ringKrullDim_of_isNoetherianRing]
  rwa [ENat.WithBot.add_natCast_cancel] at key

/-! ## The count is preserved -/

/-- **`comap C` is a bijection `TopDimMinPrimes (MvPolynomial ι A) → TopDimMinPrimes A`.**
Injectivity: a minimal prime equals `map C (comap C P)` (`map_comap_C_of_mem_minimalPrimes`), so
`comap C` determines it. Surjectivity: `q = comap C (map C q)` (`comap_map_C_eq`) with
`map C q` top-dimensional (`map_C_mem_topDimMinPrimes`). -/
theorem bijOn_comap_C_topDimMinPrimes [IsNoetherianRing A] [Finite ι] :
    Set.BijOn (Ideal.comap (C : A →+* MvPolynomial ι A))
      (TopDimMinPrimes (MvPolynomial ι A)) (TopDimMinPrimes A) := by
  refine ⟨fun P hP ↦ comap_C_mem_topDimMinPrimes P hP, ?_, ?_⟩
  · -- InjOn
    intro P hP P' hP' hPP'
    rw [← map_comap_C_of_mem_minimalPrimes P hP.1, ← map_comap_C_of_mem_minimalPrimes P' hP'.1,
      hPP']
  · -- SurjOn
    intro q hq
    haveI : q.IsPrime := hq.1.1.1
    exact ⟨Ideal.map (C : A →+* MvPolynomial ι A) q, map_C_mem_topDimMinPrimes (ι := ι) q hq,
      comap_map_C_eq (ι := ι) q⟩

/-- **The polynomial extension preserves the top-dimensional minimal-prime count.** For a
Noetherian ring `A` and finite `ι`,
`(TopDimMinPrimes (MvPolynomial ι A)).ncard = (TopDimMinPrimes A).ncard`. The cleanest isolated
rung of the fibre-`θ` chart transport: it strips the `|δ|`-variable Schur polynomial extension off
the count. -/
theorem topDimMinPrimes_mvPolynomial_ncard_eq [IsNoetherianRing A] [Finite ι] :
    (TopDimMinPrimes (MvPolynomial ι A)).ncard = (TopDimMinPrimes A).ncard :=
  (bijOn_comap_C_topDimMinPrimes (A := A) (ι := ι)).ncard_eq

end DLNFibre.Core
