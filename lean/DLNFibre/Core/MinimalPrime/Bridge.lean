/-
Copyright (c) 2026. Released under Apache 2.0; see LICENSE.
-/
import DLNFibre.Core.MinimalPrime.TopDimensional
import DLNFibre.Core.Dimension.Codimension

/-!
# `DLNFibre.Core.MinimalPrime.Bridge` — height-`= I.height` ↔ `TopDimMinPrimes` (polynomial ring)

Connects the **height-based** "top-dimensional component" reading of a minimal prime
(`p.height = I.height`) to the **dimension-based** `Ideal.TopDimMinPrimes` (see
`…/MinimalPrime/TopDimensional`) used for the count transport. On a polynomial ring
`R = MvPolynomial σ k` (`k` a field, `σ` finite) the two notions select the **same** minimal primes,
because the ring is catenary: for a minimal prime `p ⊇ I` of a proper ideal `I`,

> `ringKrullDim (R ⧸ p) = ringKrullDim (R ⧸ I)  ↔  p.height = I.height`

(both `dim (R ⧸ ·) = card − height ·`, and `I.height` is the minimal component height). With the
quotient minimal-prime bijection `Ideal.minimalPrimes_eq_comap`, this gives a bijection between
`{p ∈ I.minimalPrimes | p.height = I.height}` and `TopDimMinPrimes (R ⧸ I)`, hence equal counts
(the count consequence is a downstream wire; this module proves the per-prime biconditional and the
`card − height` quotient-dimension identities it rides on).

Pure commutative algebra over a field — no DLN content. It lives in namespace `Ideal` and mirrors
the Mathlib home `Mathlib.RingTheory.Ideal.MinimalPrime`, so an upstream move is a file-move with no
namespace surgery.

**Dependency rule:** `Core` only — never import `DLNFibre.DLN`.
-/

namespace Ideal

open MvPolynomial DLNFibre.Core.Dimension

variable {k : Type*} [Field k] {σ : Type*} [Finite σ]

/-! ## The quotient dimension as `card − height` -/

/-- **The height of a prime in `MvPolynomial σ k` is finite** (`≤ Nat.card σ`): the ring has
finite Krull dimension `Nat.card σ`. -/
theorem height_prime_le_card (p : Ideal (MvPolynomial σ k)) [p.IsPrime] :
    p.height ≤ (Nat.card σ : ℕ∞) := by
  have h := Ideal.height_le_ringKrullDim_of_ne_top (I := p) (Ideal.IsPrime.ne_top inferInstance)
  rw [ringKrullDim_mvPolynomial_finite] at h
  exact_mod_cast h

/-- The height of a prime in `MvPolynomial σ k` is `≠ ⊤`. -/
theorem height_prime_ne_top (p : Ideal (MvPolynomial σ k)) [p.IsPrime] : p.height ≠ ⊤ :=
  ne_top_of_le_ne_top (ENat.coe_ne_top _) (height_prime_le_card p)

/-- **The quotient dimension of a prime is `card − height` (`ℕ∞`).** For `R = MvPolynomial σ k` and
a prime `p`, `ringKrullDim (R ⧸ p) = Nat.card σ − p.height`. From the per-prime catenary
`height p + dim (R ⧸ p) = card` (`Core.Dimension.Codimension`) by `ℕ∞`-subtraction (lossless,
`height p ≤ card`). -/
theorem ringKrullDim_quotient_prime_eq (p : Ideal (MvPolynomial σ k)) [p.IsPrime] :
    ringKrullDim (MvPolynomial σ k ⧸ p) = ((Nat.card σ : ℕ∞) - p.height : ℕ∞) := by
  have hcat := height_add_ringKrullDim_quotient_eq_card (k := k) (σ := σ) p
  haveI : Nontrivial (MvPolynomial σ k ⧸ p) :=
    Ideal.Quotient.nontrivial_iff.mpr (Ideal.IsPrime.ne_top inferInstance)
  have hne : ringKrullDim (MvPolynomial σ k ⧸ p) ≠ ⊥ :=
    fun h ↦ by simpa [h] using ringKrullDim_nonneg_of_nontrivial (R := MvPolynomial σ k ⧸ p)
  obtain ⟨m, hm⟩ := WithBot.ne_bot_iff_exists.mp hne
  rw [← hm] at hcat ⊢
  have hcat' : m + p.height = (Nat.card σ : ℕ∞) := by rw [add_comm]; exact_mod_cast hcat
  rw [WithBot.coe_eq_coe]
  exact (ENat.addLECancellable_of_ne_top (height_prime_ne_top p)).eq_tsub_of_add_eq hcat'

/-- **The quotient dimension of a proper ideal is `card − height` (`ℕ∞`).** The any-proper-ideal
catenary `height I + dim (R ⧸ I) = card` (`Core.Dimension.Codimension`) in subtraction form. -/
theorem ringKrullDim_quotient_eq_of_ne_top (I : Ideal (MvPolynomial σ k)) (hIne : I ≠ ⊤) :
    ringKrullDim (MvPolynomial σ k ⧸ I) = ((Nat.card σ : ℕ∞) - I.height : ℕ∞) := by
  have hcat := height_add_ringKrullDim_quotient_eq_card_of_ne_top (k := k) (σ := σ) I hIne
  haveI : Nontrivial (MvPolynomial σ k ⧸ I) := Ideal.Quotient.nontrivial_iff.mpr hIne
  have hne : ringKrullDim (MvPolynomial σ k ⧸ I) ≠ ⊥ :=
    fun h ↦ by simpa [h] using ringKrullDim_nonneg_of_nontrivial (R := MvPolynomial σ k ⧸ I)
  obtain ⟨m, hm⟩ := WithBot.ne_bot_iff_exists.mp hne
  rw [← hm] at hcat ⊢
  have hcat' : m + I.height = (Nat.card σ : ℕ∞) := by rw [add_comm]; exact_mod_cast hcat
  have hIne' : I.height ≠ ⊤ := by
    intro h; rw [h, add_top] at hcat'; exact (ENat.coe_ne_top _) hcat'.symm
  rw [WithBot.coe_eq_coe]
  exact (ENat.addLECancellable_of_ne_top hIne').eq_tsub_of_add_eq hcat'

/-! ## The height ↔ dimension biconditional on minimal primes -/

/-- The `ℕ∞` truncated subtraction from a finite bound is injective on the values below it. -/
private theorem enat_sub_left_cancel {c a b : ℕ∞} (ha : a ≤ c) (hb : b ≤ c) (hc : c ≠ ⊤)
    (hane : a ≠ ⊤) (hbne : b ≠ ⊤) : c - a = c - b ↔ a = b := by
  lift c to ℕ using hc; lift a to ℕ using hane; lift b to ℕ using hbne
  rw [← ENat.coe_sub, ← ENat.coe_sub, Nat.cast_inj, Nat.cast_inj]
  have ha' : a ≤ c := by exact_mod_cast ha
  have hb' : b ≤ c := by exact_mod_cast hb
  omega

/-- **Top-dimensional ⟺ minimal-height, on a minimal prime.** For a minimal prime `p` of a proper
ideal `I` of `R = MvPolynomial σ k`, the quotient `R ⧸ p` carries the full dimension `R ⧸ I` exactly
when `p` has the minimal component height `I.height`. Both quotient dims are `card − (·)`, and the
subtraction from the finite `card` is injective on the finite heights (`p.height`, `I.height ≤
card`). -/
theorem ringKrullDim_quotient_eq_iff_height_eq (I : Ideal (MvPolynomial σ k)) (hIne : I ≠ ⊤)
    {p : Ideal (MvPolynomial σ k)} (hp : p ∈ I.minimalPrimes) :
    ringKrullDim (MvPolynomial σ k ⧸ p) = ringKrullDim (MvPolynomial σ k ⧸ I)
      ↔ p.height = I.height := by
  haveI : p.IsPrime := Ideal.minimalPrimes_isPrime hp
  have hIle : I.height ≤ p.height := Ideal.height_mono hp.1.2
  have hpne := height_prime_ne_top (k := k) (σ := σ) p
  have hIne' : I.height ≠ ⊤ := ne_top_of_le_ne_top hpne hIle
  rw [ringKrullDim_quotient_prime_eq (k := k) (σ := σ) p,
    ringKrullDim_quotient_eq_of_ne_top (k := k) (σ := σ) I hIne, WithBot.coe_eq_coe]
  exact enat_sub_left_cancel (height_prime_le_card p)
    (hIle.trans (height_prime_le_card p)) (ENat.coe_ne_top _) hpne hIne'

end Ideal
