/-
Copyright (c) 2026. Released under Apache 2.0; see LICENSE.
-/
import DLNFibre.Core.FibreThetaCount
import DLNFibre.Core.FibreNormalForm

/-!
# `DLNFibre.Core.FibreThetaCountArbitrary` — the fibre-`θ` headline for an ARBITRARY rank-`r` target

`Core.FibreThetaCount.ncard_topDimMinPrimes_fibre_eq_cTheta_dminus` counts the top-dimensional
irreducible components of the fibre over the **normal form** `E_r = diag(I_r, 0)`. This module
transports that count to an **arbitrary** rank-`r` target `B`: for `B.rank = r`,

> `numTop(mult⁻¹ B) = numTop(mult⁻¹ E_r) = cTheta (d − r)`.

The transport is a **same-rank component-count invariance**: two matrices of the same rank are
`GL × GL`-equivalent (`exists_baseChange_of_rank_eq`), and the base change `A ↦ P • A` is a *linear*
automorphism of the representation space carrying `mult⁻¹ B` onto `mult⁻¹ E_r`
(`reducedFibre_baseChangeHomogeneous`), so the two fibre coordinate rings are isomorphic varieties
and carry the **same** top-dimensional minimal-prime count.

## The mechanism (all rungs LANDED, pure commutative-algebra glue)

The count `numTop(mult⁻¹ B) = (TopDimMinPrimes (R ⧸ fibreGenIdeal d B)).ncard`,
`R = MvPolynomial (RepCoord d) k`. The chain:

* `topDimMinPrimes_quotient_radical_ncard_eq` — the count is **radical-insensitive**, so it suffices
  to compare `R ⧸ radical (fibreGenIdeal d B)` with `R ⧸ radical (fibreGenIdeal d E_r)`;
* `vanishingIdeal_image_fibre_eq_radical` — `radical (fibreGenIdeal d B) = vanishingIdeal(fibre B)`,
  the Nullstellensatz reading of the generator ideal;
* `vanishingIdeal_image_smul` — the vanishing ideal of the base-change-shifted fibre is the `comap`
  of the model fibre's vanishing ideal along the coordinate-ring automorphism `baseChangeAlgEquiv P`
  (a `RingEquiv`);
* `Ideal.quotientEquiv` + `topDimMinPrimes_ncard_eq_of_ringEquiv` — `R ⧸ comap φ J ≃+* R ⧸ J` for a
  ring equiv `φ`, and **any** ring iso preserves the top-dimensional minimal-prime count.

So the count chain composing on top of the model headline gives the genuinely-arbitrary-`B`
statement `numTop_fibre_eq_cTheta_dminus_of_rank`.

Carries `hN : (0 : Fin (N + 2)) ≠ Fin.last (N + 1)` (distinct endpoints — the base-change must act on
the two ends independently). NB with the `Fin (N + 2)` indexing there are always ≥ 2 nodes, so this is
automatically satisfiable for every `N ≥ 0` (`0 ≠ N + 1` in `Fin (N + 2)`); it is passed explicitly
rather than discharged. (The earlier "constant map at `N = 0`" caveat was inherited from the older
`Fin (N + 1)` normal-form API and does NOT apply to this `Fin (N + 2)` module.)

**Dependency rule:** `Core` only — never import `DLNFibre.DLN`.
-/

namespace DLNFibre.Core

open MvPolynomial Matrix

universe u

variable {k : Type u} [Field k] {N : ℕ}

/-- **Same-rank component-count invariance (the C3 transport).** For two matrices `B, B'` of equal
rank, the fibre coordinate rings carry the same top-dimensional minimal-prime count:
`numTop(R ⧸ fibreGenIdeal d B) = numTop(R ⧸ fibreGenIdeal d B')`. The base change `A ↦ P • A`
(`exists_baseChange_of_rank_eq`, `N ≥ 1`) is a linear automorphism of `RepCoord d` carrying one
fibre onto the other; its coordinate-ring `RingEquiv` `baseChangeAlgEquiv P` identifies the two
radical-quotient rings (`vanishingIdeal_image_smul` + `Ideal.quotientEquiv`), and the count is a
ring-iso invariant (`topDimMinPrimes_ncard_eq_of_ringEquiv`) and radical-insensitive
(`topDimMinPrimes_quotient_radical_ncard_eq`). -/
theorem ncard_topDimMinPrimes_fibre_eq_of_rank_eq [IsAlgClosed k]
    (d : Fin (N + 2) → ℕ) (hN : (0 : Fin (N + 2)) ≠ Fin.last (N + 1))
    (B B' : Matrix (Fin (d (Fin.last (N + 1)))) (Fin (d 0)) k) (hrank : B.rank = B'.rank) :
    (TopDimMinPrimes (MvPolynomial (RepCoord d) k ⧸ fibreGenIdeal d B)).ncard
      = (TopDimMinPrimes (MvPolynomial (RepCoord d) k ⧸ fibreGenIdeal d B')).ncard := by
  -- a base change `P` carries `B` to `B'`: `B' = P_N · B · P_0⁻¹`, so `(P•·)'' fibre B = fibre B'`.
  obtain ⟨P, hP⟩ := exists_baseChange_of_rank_eq d hN B B' hrank
  set φ : MvPolynomial (RepCoord d) k ≃+* MvPolynomial (RepCoord d) k :=
    (baseChangeAlgEquiv P).toRingEquiv with hφ
  -- the radicals are related by the coordinate-ring `comap` of `φ`.
  have he : (baseChangePullback P :
        MvPolynomial (RepCoord d) k →+* MvPolynomial (RepCoord d) k)
      = (φ : MvPolynomial (RepCoord d) k →+* MvPolynomial (RepCoord d) k) := rfl
  have hcomap : (fibreGenIdeal d B').radical
      = (fibreGenIdeal d B).radical.comap
          (φ : MvPolynomial (RepCoord d) k →+* MvPolynomial (RepCoord d) k) := by
    rw [← vanishingIdeal_image_fibre_eq_radical d B', ← vanishingIdeal_image_fibre_eq_radical d B,
      hP, ← image_smul_fibre, vanishingIdeal_image_smul, he]
  -- `radical J_B = map φ (radical J_{B'})` (apply `map φ` to `hcomap` and cancel `map ∘ comap`).
  have hmapJ : (fibreGenIdeal d B).radical
      = (fibreGenIdeal d B').radical.map
          (φ : MvPolynomial (RepCoord d) k →+* MvPolynomial (RepCoord d) k) := by
    rw [hcomap, Ideal.map_comap_of_surjective
      (φ : MvPolynomial (RepCoord d) k →+* MvPolynomial (RepCoord d) k) φ.surjective]
  -- `R ⧸ radical J_{B'} ≃+* R ⧸ radical J_B` (ring equiv `φ`), so the radical counts agree.
  have hquot : (TopDimMinPrimes (MvPolynomial (RepCoord d) k ⧸ (fibreGenIdeal d B').radical)).ncard
      = (TopDimMinPrimes (MvPolynomial (RepCoord d) k ⧸ (fibreGenIdeal d B).radical)).ncard :=
    topDimMinPrimes_ncard_eq_of_ringEquiv
      (Ideal.quotientEquiv (fibreGenIdeal d B').radical (fibreGenIdeal d B).radical φ hmapJ)
  -- strip the radicals on both sides (the count is radical-insensitive).
  rw [topDimMinPrimes_quotient_radical_ncard_eq (fibreGenIdeal d B),
    topDimMinPrimes_quotient_radical_ncard_eq (fibreGenIdeal d B'), hquot]

/-! ## The arbitrary-`B` headline (at `Type 0`)

The model count `ncard_topDimMinPrimes_fibre_eq_cTheta_dminus` is stated at `Type` (its W2 rung is),
so the arbitrary-`B` headline that composes with it also lands at `Type 0`. The same-rank transport
`ncard_topDimMinPrimes_fibre_eq_of_rank_eq` above is universe-polymorphic and specialises freely. -/

section UnivZero

variable {k : Type} [Field k]

/-- **The fibre-`θ` headline for an ARBITRARY rank-`r` target.** For any `B` of rank `r` (and the
model hypotheses of `ncard_topDimMinPrimes_fibre_eq_cTheta_dminus`), the number of top-dimensional
irreducible components of the fibre `mult⁻¹ B` equals the closed combinatorial form
`cTheta (d − r) = C(m, |δ|)`. Transports the normal-form headline along the same-rank invariance
`ncard_topDimMinPrimes_fibre_eq_of_rank_eq` (`B` and `E_r = diag(I_r, 0)` have equal rank). This is
the genuinely-arbitrary-`B` `θ`-count: it no longer references the chart normal form. -/
theorem ncard_topDimMinPrimes_fibre_eq_cTheta_dminus_of_rank [IsAlgClosed k] [CharZero k]
    (d : Fin (N + 2) → ℕ) (r : ℕ) (hp : r ≤ d (Fin.last (N + 1))) (hq : r ≤ d 0)
    (hN : (0 : Fin (N + 2)) ≠ Fin.last (N + 1))
    (hd : Monotone d) (hr : ∀ i, r ≤ d i)
    (h₀ : (kostantPartitions (dminus d r) 0).Nonempty)
    (h : (kostantPartitions d r).Nonempty)
    (B : Matrix (Fin (d (Fin.last (N + 1)))) (Fin (d 0)) k) (hB : B.rank = r) :
    (TopDimMinPrimes (MvPolynomial (RepCoord d) k ⧸ fibreGenIdeal d B)).ncard
      = cTheta (dminus d r) := by
  -- `B` and the normal form `E_r` have equal rank `r`.
  have hrankE : (normalForm (k := k) (d (Fin.last (N + 1))) (d 0) r hp hq).rank = r :=
    rank_normalForm _ _ _ hp hq
  -- transport the count from `B` to `E_r` (same-rank invariance), then chain the model headline.
  exact (ncard_topDimMinPrimes_fibre_eq_of_rank_eq d hN B
      (normalForm (k := k) (d (Fin.last (N + 1))) (d 0) r hp hq) (hB.trans hrankE.symm)).trans
    (ncard_topDimMinPrimes_fibre_eq_cTheta_dminus d r hp hq hN hd hr h₀ h)

end UnivZero

end DLNFibre.Core
