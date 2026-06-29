import Mathlib.RingTheory.Ideal.MinimalPrime.Basic
import Mathlib.RingTheory.Ideal.Operations

/-!
# `DLNFibre.Core.MinimalPrime.Finite` — minimal primes of the `sInf` of a finite prime family

For a **finite family of prime ideals** `s` in a commutative (semi)ring, the minimal primes of its
intersection `sInf s` are exactly the **inclusion-minimal members** of `s`. This is the
finite-family packaging of the minimal-primes calculus: Mathlib has the radical form
`Ideal.sInf_minimalPrimes` (`sInf I.minimalPrimes = I.radical`) but not this characterisation of the
minimal primes *of* a finite `sInf` directly in terms of the family, so it is a genuine small gap.

The proof is prime avoidance (`Ideal.IsPrime.inf_le'`): a prime `P ⊇ sInf s` contains some member of
`s`, since `sInf s` is the finite `Finset.inf` of the family. Both inclusions follow:

* `⊆` — a minimal prime `q ⊇ sInf s` contains some `p ∈ s`; minimality of `q` over `sInf s` and
  `sInf s ≤ p` force `q = p`, and `q` is then inclusion-minimal in `s`.
* `⊇` — an inclusion-minimal `p ∈ s` is a prime above `sInf s`; any prime `r` between `sInf s` and
  `p` contains some `p' ∈ s` (avoidance), and inclusion-minimality of `p` forces `p ≤ p' ≤ r`.

This file lives in namespace `Ideal` and mirrors the Mathlib home
`Mathlib.RingTheory.Ideal.MinimalPrime` (a plausible `…/MinimalPrime/Finite.lean`), so an upstream
move is a file-move with no namespace surgery.

**Dependency rule:** `Core` only — never import `DLNFibre.DLN`.
-/

namespace Ideal

/-- The minimal primes of the intersection of a **finite family of prime ideals** `s` are exactly
the **inclusion-minimal members** of `s`. The `⊆` direction is prime avoidance
(`Ideal.IsPrime.inf_le'`): a minimal prime `q ⊇ sInf s` contains some `p ∈ s`, and minimality forces
`q = p`; the `⊇` direction is the same avoidance for any prime below an inclusion-minimal member. -/
theorem minimalPrimes_sInf_of_finite_of_isPrime {R : Type*} [CommSemiring R]
    (s : Set (Ideal R)) (hfin : s.Finite) (hs : ∀ p ∈ s, p.IsPrime) :
    (sInf s).minimalPrimes = {p | p ∈ s ∧ ∀ q ∈ s, q ≤ p → p ≤ q} := by
  classical
  -- avoidance: a prime `P ⊇ sInf s` contains some member of `s`.
  have avoid : ∀ {P : Ideal R}, P.IsPrime → sInf s ≤ P → ∃ p ∈ s, p ≤ P := by
    intro P hP hle
    rw [← hfin.coe_toFinset, ← Finset.inf_id_eq_sInf, hP.inf_le'] at hle
    obtain ⟨p, hp, hpP⟩ := hle
    exact ⟨p, hfin.mem_toFinset.mp hp, by simpa using hpP⟩
  ext q
  constructor
  · rintro ⟨⟨hqp, hle⟩, hmin⟩
    obtain ⟨p, hps, hpq⟩ := avoid hqp hle
    have hp_le : sInf s ≤ p := sInf_le hps
    have : q ≤ p := hmin ⟨hs p hps, hp_le⟩ hpq
    have hqeqp : q = p := le_antisymm this hpq
    subst hqeqp
    exact ⟨hps, fun r hrs hrq ↦ hmin ⟨hs r hrs, sInf_le hrs⟩ hrq⟩
  · rintro ⟨hqs, hqmin⟩
    refine ⟨⟨hs q hqs, sInf_le hqs⟩, ?_⟩
    rintro r ⟨hr_prime, hr_le⟩ hrq
    obtain ⟨p, hps, hpr⟩ := avoid hr_prime hr_le
    exact (hqmin p hps (hpr.trans hrq)).trans hpr

end Ideal
