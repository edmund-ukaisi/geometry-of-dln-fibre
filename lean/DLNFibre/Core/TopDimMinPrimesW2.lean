/-
Copyright (c) 2026. Released under Apache 2.0; see LICENSE.
-/
import DLNFibre.Core.TopDimMinPrimesW1W2

/-!
# `DLNFibre.Core.TopDimMinPrimesW2` — the W2 keystone application (diamond-free, Option A)

The W2 rung of the fibre-`θ` count transport (expedition `theta-components`, thread 09, sub-task
W2-Option-A): inverting the Schur-side localizing element `chartGfib` over the *nested* ring
`A = MvPolynomial SchurVar O(F)` preserves the top-dimensional minimal-prime count.

> **`ncard_topDimMinPrimes_away_chartGfib_eq`** — `(TopDimMinPrimes (Away chartGfib)).ncard =
> (TopDimMinPrimes (MvPolynomial SchurVar O(F))).ncard`.

## Why Option A (the flat-ring transport)

`A = MvPolynomial SchurVar O(F)` is `MvPolynomial` over a *quotient* `O(F) = R ⧸ I`
(`R = MvPolynomial (RepCoord d) k`, `I = vanishingIdeal(F)`) — a doubly-nested `CommRing`. Applying
the abstract away-survival wrapper `topDimMinPrimes_ncard_away_eq_of_fgDomain` DIRECTLY to this `A`
triggers a non-terminating `isDefEq` at the conclusion-unification (the nested-quotient `whnf`
blowup). Fuel does not fix it.

The fix transports across the flat iso
`e : MvPolynomial SchurVar (R ⧸ I) ≃ₐ[R] MvPolynomial SchurVar R ⧸ map C I`
(`MvPolynomial.quotientEquivQuotientMvPolynomial`). The codomain `B` is a *single* quotient of a
flat polynomial ring, on which the wrapper applies cleanly. Each hypothesis of the keystone is moved
from `A` to `B` (or its `Away`) by `e`:

* the count `(TopDimMinPrimes A).ncard = (TopDimMinPrimes B).ncard` and the `Away` count are
  ring-iso transports (`topDimMinPrimes_ncard_eq_of_ringEquiv`);
* `hdim_B` chains the LANDED nested `ringKrullDim_localizationAway_chartGfib_eq` through the two
  iso transports;
* `havoid_B` transports the LANDED nested `chartGfib_not_mem_of_mem_topDimMinPrimes` along
  `comap e`.

The wrapper on the flat `B` then gives the `Away`-count = `B`-count, and the chain closes.

**Dependency rule:** `Core` only — never import `DLNFibre.DLN`.
-/

namespace DLNFibre.Core

open MvPolynomial

variable {k : Type} [Field k] {N : ℕ}

/-- **W2 keystone application (Option A).** Inverting `chartGfib` over the nested ring
`A = MvPolynomial SchurVar O(F)` preserves the top-dimensional minimal-prime count:

> `(TopDimMinPrimes (Away chartGfib)).ncard = (TopDimMinPrimes (MvPolynomial SchurVar O(F))).ncard`.

Proved diamond-free by transporting across the flat iso `quotientEquivQuotientMvPolynomial`. -/
theorem ncard_topDimMinPrimes_away_chartGfib_eq [IsAlgClosed k] [CharZero k]
    (d : Fin (N + 2) → ℕ) (r : ℕ) (hp : r ≤ d (Fin.last (N + 1))) (hq : r ≤ d 0)
    (hN : (0 : Fin (N + 2)) ≠ Fin.last (N + 1)) (h : (kostantPartitions d r).Nonempty) :
    letI : CommRing (MvPolynomial (SchurVar (d 0) (d (Fin.last (N + 1))) r)
      (sweepFibreRing k d r hp hq)) := inferInstance
    (TopDimMinPrimes (Localization.Away (chartGfib k d r hp hq))).ncard
      = (TopDimMinPrimes (MvPolynomial (SchurVar (d 0) (d (Fin.last (N + 1))) r)
          (sweepFibreRing k d r hp hq))).ncard := by
  -- `R = MvPolynomial (RepCoord d) k`, `I = vanishingIdeal(F)`, `ι = SchurVar`; the nested
  -- `A = MvPolynomial ι (R ⧸ I) = MvPolynomial ι O(F)`, the flat `B = MvPolynomial ι R ⧸ map C I`.
  -- We pin `e`'s DOMAIN type to the `sweepFibreRing` form (via ascription) so the
  -- `MvPolynomial`-CommRing instance matches the goal's instance path.
  set R := MvPolynomial (RepCoord d) k with hR
  set I : Ideal R := vanishingIdeal k (sweepFibre k d r hp hq) with hI
  set ι := SchurVar (d 0) (d (Fin.last (N + 1))) r with hι
  -- The flat iso `A ≃ₐ[R] B`, with domain forced to `MvPolynomial ι (sweepFibreRing ..)`.
  let e : MvPolynomial ι (sweepFibreRing k d r hp hq)
      ≃ₐ[R] MvPolynomial ι R ⧸ Ideal.map (C : R →+* MvPolynomial ι R) I :=
    MvPolynomial.quotientEquivQuotientMvPolynomial I
  set gA := chartGfib k d r hp hq with hgA
  let gB := e gA
  -- Step 1: the count `A → B` is a ring-iso transport.
  have hBase : (TopDimMinPrimes (MvPolynomial ι (sweepFibreRing k d r hp hq))).ncard
      = (TopDimMinPrimes (MvPolynomial ι R ⧸ Ideal.map (C : R →+* MvPolynomial ι R) I)).ncard :=
    topDimMinPrimes_ncard_eq_of_ringEquiv e.toRingEquiv
  -- Step 2: the `Away` iso, transporting `e` through the localizations (`gB = e gA`).
  let eAway : Localization.Away gA ≃+* Localization.Away gB :=
    IsLocalization.ringEquivOfRingEquiv (Localization.Away gA) (Localization.Away gB)
      e.toRingEquiv (Submonoid.map_powers e.toRingEquiv gA)
  have hAway : (TopDimMinPrimes (Localization.Away gA)).ncard
      = (TopDimMinPrimes (Localization.Away gB)).ncard :=
    topDimMinPrimes_ncard_eq_of_ringEquiv eAway
  -- Step 3: `hdim_B` — chain the LANDED nested hdim through the two iso transports.
  have hdim_B : ringKrullDim (Localization.Away gB)
      = ringKrullDim (MvPolynomial ι R ⧸ Ideal.map (C : R →+* MvPolynomial ι R) I) := by
    rw [← ringKrullDim_eq_of_ringEquiv eAway,
      ringKrullDim_localizationAway_chartGfib_eq d r hp hq hN h,
      ringKrullDim_eq_of_ringEquiv e.toRingEquiv]
  -- Step 4: `havoid_B` — transport the LANDED nested no-mem along `comap e`.
  have havoid_B : ∀ p ∈ TopDimMinPrimes
      (MvPolynomial ι R ⧸ Ideal.map (C : R →+* MvPolynomial ι R) I), gB ∉ p := by
    intro p hpB hmem
    -- `comap e p ∈ TopDimMinPrimes A`; the nested no-mem says `gA ∉ comap e p`.
    have hpA : p.comap (e : MvPolynomial ι (sweepFibreRing k d r hp hq) →+* _)
        ∈ TopDimMinPrimes (MvPolynomial ι (sweepFibreRing k d r hp hq)) :=
      comap_mem_topDimMinPrimes e.toRingEquiv hpB
    -- `gB = e gA ∈ p ↔ gA ∈ comap e p`.
    have hgAmem : gA ∈ p.comap (e : MvPolynomial ι (sweepFibreRing k d r hp hq) →+* _) :=
      Ideal.mem_comap.mpr hmem
    exact chartGfib_not_mem_of_mem_topDimMinPrimes d r hp hq hpA hgAmem
  -- Step 5: the wrapper on the FLAT `B` (confirmed clean — single quotient of a flat poly ring).
  have hFlat : (TopDimMinPrimes (Localization.Away gB)).ncard
      = (TopDimMinPrimes (MvPolynomial ι R ⧸ Ideal.map (C : R →+* MvPolynomial ι R) I)).ncard :=
    topDimMinPrimes_ncard_away_eq_of_fgDomain (k := k) gB hdim_B havoid_B
  -- Step 6: chain `Away gA → Away gB → B → A`.
  calc (TopDimMinPrimes (Localization.Away gA)).ncard
      = (TopDimMinPrimes (Localization.Away gB)).ncard := hAway
    _ = (TopDimMinPrimes (MvPolynomial ι R ⧸ Ideal.map (C : R →+* MvPolynomial ι R) I)).ncard :=
        hFlat
    _ = (TopDimMinPrimes (MvPolynomial ι (sweepFibreRing k d r hp hq))).ncard := hBase.symm

end DLNFibre.Core
