/-
Copyright (c) 2026. Released under Apache 2.0; see LICENSE.
-/
import DLNFibre.Core.MinimalPrime.TopDimensional
import Mathlib.RingTheory.KrullDimension.NonZeroDivisors
import Mathlib.RingTheory.Ideal.Quotient.Operations

/-!
# `DLNFibre.Core.MinimalPrime.Radical` — `TopDimMinPrimes` count is radical-insensitive

The top-dimensional minimal-prime count (`Ideal.TopDimMinPrimes`, see
`…/MinimalPrime/TopDimensional`) of a quotient `R ⧸ J` depends only on the **radical** of `J`. So
two ideals with the same radical
carry the **same** count, with no radicality of the smaller ideal needed.

The mechanism (pure commutative algebra, two facts):

* `Ideal.minimalPrimes` is radical-insensitive (`Ideal.radical_minimalPrimes`), so two ideals with
  equal minimal primes give the same `R`-side minimal-prime set;
* `ringKrullDim (R ⧸ J) = Order.krullDim (zeroLocus J)` (`ringKrullDim_quotient`), and `zeroLocus`
  is radical-insensitive (`PrimeSpectrum.zeroLocus_radical`), so the ambient dimension agrees.

Both `TopDimMinPrimes (R ⧸ I)` and `TopDimMinPrimes (R ⧸ J)` map (`comap (Quotient.mk ·)`,
injectively) onto the **same** `R`-side set `{q ∈ minimalPrimes · | ringKrullDim (R ⧸ q) =
ringKrullDim (R ⧸ ·)}` when `minimalPrimes I = minimalPrimes J` and `ringKrullDim (R ⧸ I) =
ringKrullDim (R ⧸ J)` — so the counts coincide.

> **`topDimMinPrimes_quotient_ncard_eq_of_minimalPrimes_eq`** — abstract: equal minimal primes +
> equal quotient dim ⟹ equal count.
> **`topDimMinPrimes_quotient_radical_ncard_eq`** — the `J` / `radical J` instance.

Also re-homed here is the general third-isomorphism-theorem dimension identity
`ringKrullDim_doubleQuot_eq` (any `[CommRing R]`, any ideal `I`, any prime `P` of `R ⧸ I`), the
double-quotient transport this radical-insensitivity rides on. Pure commutative algebra — no DLN
content. It lives in namespace `Ideal` and mirrors the Mathlib home
`Mathlib.RingTheory.Ideal.MinimalPrime`, so an upstream move is a file-move with no namespace
surgery.

**Dependency rule:** `Core` only — never import `DLNFibre.DLN`.
-/

namespace Ideal

universe u

variable {R : Type u} [CommRing R]

/-! ## The double-quotient dimension transport (third isomorphism theorem) -/

/-- **The third isomorphism theorem at `ringKrullDim`.** For a prime `P` of `R ⧸ I`,
`ringKrullDim ((R ⧸ I) ⧸ P) = ringKrullDim (R ⧸ Ideal.comap (Quotient.mk I) P)` via
`DoubleQuot.quotQuotEquivQuotOfLE` (`P = (comap P).map (mk I)`, `I ≤ comap P`). -/
theorem ringKrullDim_doubleQuot_eq (I : Ideal R) (P : Ideal (R ⧸ I)) :
    ringKrullDim ((R ⧸ I) ⧸ P) = ringKrullDim (R ⧸ (P.comap (Ideal.Quotient.mk I))) := by
  have hle : I ≤ P.comap (Ideal.Quotient.mk I) := by
    intro x hx
    rw [Ideal.mem_comap, Ideal.Quotient.eq_zero_iff_mem.mpr hx]
    exact zero_mem P
  have hmapeq : (P.comap (Ideal.Quotient.mk I)).map (Ideal.Quotient.mk I) = P :=
    Ideal.map_comap_of_surjective _ Ideal.Quotient.mk_surjective P
  have key := ringKrullDim_eq_of_ringEquiv (DoubleQuot.quotQuotEquivQuotOfLE hle)
  rw [hmapeq] at key
  exact key

/-! ## The `R`-side top-dimensional minimal-prime set of a quotient -/

/-- **The `R`-side top-dimensional minimal-prime set of a quotient.** `{q ∈ I.minimalPrimes |
ringKrullDim (R ⧸ q) = ringKrullDim (R ⧸ I)}` — the comap-image of `TopDimMinPrimes (R ⧸ I)` under
`Quotient.mk I`. Reading the dimension-based top components on the ambient `R`. -/
def quotTopDimSet (I : Ideal R) : Set (Ideal R) :=
  {q | q ∈ I.minimalPrimes ∧ ringKrullDim (R ⧸ q) = ringKrullDim (R ⧸ I)}

/-- **`comap (Quotient.mk I)` is a `Set.BijOn` `TopDimMinPrimes (R ⧸ I) → quotTopDimSet I`.**
Minimality transports through `Ideal.minimalPrimes_eq_comap`; the dimension equality through the
third isomorphism theorem `ringKrullDim_doubleQuot_eq`. -/
theorem bijOn_comap_quotTopDimSet (I : Ideal R) :
    Set.BijOn (Ideal.comap (Ideal.Quotient.mk I)) (TopDimMinPrimes (R ⧸ I)) (quotTopDimSet I) := by
  refine ⟨?_, ?_, ?_⟩
  · -- MapsTo
    rintro P ⟨hPmin, hPdim⟩
    refine ⟨?_, ?_⟩
    · rw [Ideal.minimalPrimes_eq_comap]; exact ⟨P, hPmin, rfl⟩
    · rw [← ringKrullDim_doubleQuot_eq I P, hPdim]
  · -- InjOn
    intro P _ P' _ hPP'
    exact Ideal.comap_injective_of_surjective _ Ideal.Quotient.mk_surjective hPP'
  · -- SurjOn
    rintro q ⟨hqmin, hqdim⟩
    have hmem : q ∈ Ideal.comap (Ideal.Quotient.mk I) '' minimalPrimes (R ⧸ I) := by
      rw [← Ideal.minimalPrimes_eq_comap]; exact hqmin
    obtain ⟨P, hPmin, hPq⟩ := hmem
    refine ⟨P, ⟨hPmin, ?_⟩, hPq⟩
    rw [ringKrullDim_doubleQuot_eq I P, hPq, hqdim]

/-- **The top-dimensional minimal-prime count of `R ⧸ I` is `(quotTopDimSet I).ncard`.** -/
theorem ncard_topDimMinPrimes_quotient_eq (I : Ideal R) :
    (TopDimMinPrimes (R ⧸ I)).ncard = (quotTopDimSet I).ncard :=
  (bijOn_comap_quotTopDimSet I).ncard_eq

/-! ## The count from equal minimal primes / radical-insensitivity -/

/-- **Equal minimal primes + equal quotient dimension ⟹ equal top-dimensional count.** Both
quotients' counts equal `(quotTopDimSet ·).ncard`, and `quotTopDimSet I = quotTopDimSet J` when
`I.minimalPrimes = J.minimalPrimes` and `ringKrullDim (R ⧸ I) = ringKrullDim (R ⧸ J)`. -/
theorem topDimMinPrimes_quotient_ncard_eq_of_minimalPrimes_eq (I J : Ideal R)
    (hmin : I.minimalPrimes = J.minimalPrimes)
    (hdim : ringKrullDim (R ⧸ I) = ringKrullDim (R ⧸ J)) :
    (TopDimMinPrimes (R ⧸ I)).ncard = (TopDimMinPrimes (R ⧸ J)).ncard := by
  rw [ncard_topDimMinPrimes_quotient_eq, ncard_topDimMinPrimes_quotient_eq]
  congr 1
  unfold quotTopDimSet
  rw [hmin]
  ext q
  simp only [Set.mem_setOf_eq, hdim]

/-- **The count is radical-insensitive.** `(TopDimMinPrimes (R ⧸ J)).ncard = (TopDimMinPrimes (R ⧸
radical J)).ncard`: `J` and `radical J` share their minimal primes (`Ideal.radical_minimalPrimes`)
and their quotient Krull dimension (`ringKrullDim_quotient` + `PrimeSpectrum.zeroLocus_radical`).
Passing between an explicit generator ideal and its radical does not change the top-dimensional
component count. -/
theorem topDimMinPrimes_quotient_radical_ncard_eq (J : Ideal R) :
    (TopDimMinPrimes (R ⧸ J)).ncard = (TopDimMinPrimes (R ⧸ J.radical)).ncard := by
  refine topDimMinPrimes_quotient_ncard_eq_of_minimalPrimes_eq J J.radical ?_ ?_
  · exact (Ideal.radical_minimalPrimes (I := J)).symm
  · rw [ringKrullDim_quotient, ringKrullDim_quotient, PrimeSpectrum.zeroLocus_radical]

end Ideal
