/-
Copyright (c) 2026. Released under Apache 2.0; see LICENSE.
-/
import DLNFibre.Core.MinimalPrime.TopDimensional
import DLNFibre.Core.Dimension.Localization
import Mathlib.RingTheory.Localization.Away.Basic

/-!
# `DLNFibre.Core.TopDimMinPrimesLocalization` — `TopDimMinPrimes` survives an away-localization

The **reusable** localization-survival rung of the fibre-`θ` count transport (expedition
`theta-components`, thread 08). The keystone for the two non-unit localization steps W1 (`detΔ` on
`O(Σ^r)`) and W2 (`detSchurS` on `O(F)[SchurVar]`): inverting a *single* element `f` of a ring `A`
preserves the **top-dimensional minimal-prime count**, given two inputs phrased entirely on `A`:

* **avoidance** `havoid : ∀ p ∈ TopDimMinPrimes A, f ∉ p` — every top-dimensional component survives
  the localization (a component carried by a prime containing `f` would disappear);
* **the componentwise no-drop** `hper : ∀ p ∈ TopDimMinPrimes A,
  ringKrullDim (Localization.Away (Ideal.Quotient.mk p f)) = ringKrullDim (A ⧸ p)` — localizing
  each surviving top component's domain `A ⧸ p` at the image of `f` does not drop its dimension.

The `hper` input is a **required lemma**, NOT inferable from an ambient no-drop: a domain localized
at a non-unit can drop dimension (a DVR at a uniformizer). It must be invoked **per top prime**; it
holds in the applications because `A ⧸ p` is an f.g. `k`-domain and `f̄ ≠ 0`, via
`Core.Dimension.ringKrullDim_localizationAway_eq_of_fg_domain`. (Reviewer + Codex,
decorrelated: the per-prime / *componentwise* no-drop does NOT fold out of the global no-drop +
avoidance.)

The bridge between `hper` (A-side) and the `S`-side quotient dimension is the helper
`ringKrullDim_quotient_map_localizationAway_eq`: `S ⧸ map φ p ≅ Localization.Away (mk p f)` over
`A ⧸ p` (the away-localization of the quotient is the quotient of the away-localization), built by
hand from `Localization.awayMap (Ideal.Quotient.mk p) f` (surjective) and its kernel
(`IsLocalization.ker_map` + `Submonoid.map_powers`).

> **`bijOn_comap_topDimMinPrimes_away`** — `comap (algebraMap A S)` is a `Set.BijOn` from
> `TopDimMinPrimes S` onto `TopDimMinPrimes A`;
> **`topDimMinPrimes_ncard_away_eq`** — `(TopDimMinPrimes S).ncard = (TopDimMinPrimes A).ncard`.

Pure commutative algebra — no DLN content; reusable for any single-element localization survival.

**Dependency rule:** `Core` only — never import `DLNFibre.DLN`.
-/

namespace DLNFibre.Core

open Ideal (TopDimMinPrimes mem_topDimMinPrimes isPrime_of_mem_topDimMinPrimes
  comap_mem_topDimMinPrimes bijOn_comap_topDimMinPrimes topDimMinPrimes_ncard_eq_of_ringEquiv)

open IsLocalization Localization Dimension

universe u

variable {A : Type u} [CommRing A]

/-! ## The quotient ↔ localization bridge (away-localization of a quotient) -/

/-- **The quotient of the away-localization by `map φ p` is the away-localization of the quotient by
`p`.** `ringKrullDim (S ⧸ Ideal.map (algebraMap A S) p) = ringKrullDim (Away (mk p f))`,
for `S = Localization.Away f`. Built from the ring iso `S ⧸ map φ p ≃+* Localization.Away (mk p f)`:
the away-map `Localization.awayMap (mk p) f : S → Localization.Away (mk p f)` is surjective (the
quotient map `mk p` is) with kernel `map φ p` (`IsLocalization.ker_map` + `Submonoid.map_powers`,
`Ideal.mk_ker`), so `RingHom.quotientKerEquivOfSurjective` gives the iso. The A-side / S-side dim
bridge feeding the count survival. -/
theorem ringKrullDim_quotient_map_localizationAway_eq (f : A) (S : Type u) [CommRing S]
    [Algebra A S] [IsLocalization.Away f S] (p : Ideal A) :
    ringKrullDim (S ⧸ Ideal.map (algebraMap A S) p)
      = ringKrullDim (Localization.Away (Ideal.Quotient.mk p f)) := by
  -- the away-map `S → Localization.Away (mk p f)` of the quotient map `mk p`.
  set g : S →+* Localization.Away (Ideal.Quotient.mk p f) :=
    IsLocalization.Away.map S (Localization.Away (Ideal.Quotient.mk p f)) (Ideal.Quotient.mk p) f
    with hgdef
  -- it is surjective (the quotient map `mk p` is).
  have hsurj : Function.Surjective g := by
    rw [hgdef, IsLocalization.Away.map_surjective_iff]
    intro a
    obtain ⟨c, rfl⟩ := Ideal.Quotient.mk_surjective a
    exact ⟨c, 0, by simp⟩
  -- its kernel is `map φ p` (via `ker_map`, `Submonoid.map (mk p) (powers f) = powers (mk p f)`).
  have hmap : Submonoid.map (Ideal.Quotient.mk p) (Submonoid.powers f)
      = Submonoid.powers (Ideal.Quotient.mk p f) := Submonoid.map_powers _ _
  have hker : RingHom.ker g = Ideal.map (algebraMap A S) p := by
    rw [hgdef]
    have hk := IsLocalization.ker_map (R := A) (S := S)
      (P := A ⧸ p) (Q := Localization.Away (Ideal.Quotient.mk p f))
      (M := Submonoid.powers f) (T := Submonoid.powers (Ideal.Quotient.mk p f))
      (Ideal.Quotient.mk p) hmap
    rwa [Ideal.mk_ker] at hk
  have hiso : (S ⧸ Ideal.map (algebraMap A S) p)
      ≃+* Localization.Away (Ideal.Quotient.mk p f) := by
    rw [← hker]; exact RingHom.quotientKerEquivOfSurjective hsurj
  exact ringKrullDim_eq_of_ringEquiv hiso

/-! ## The minimal-prime correspondence (`f ∉ comap`) -/

/-- **The away-localization minimal primes are the `f`-avoiding minimal primes of `A`, pulled
back.** `IsLocalization.minimalPrimes_map` at `⊥` (with `Ideal.map_bot`) says `minimalPrimes S =
comap (algebraMap A S) ⁻¹' minimalPrimes A`; so `comap P ∈ minimalPrimes A` for `P ∈ minimalPrimes
S`. -/
theorem comap_mem_minimalPrimes_of_away (f : A) (S : Type u) [CommRing S] [Algebra A S]
    [IsLocalization.Away f S] {P : Ideal S} (hP : P ∈ minimalPrimes S) :
    P.comap (algebraMap A S) ∈ minimalPrimes A := by
  have hmap := IsLocalization.minimalPrimes_map (Submonoid.powers f) S (⊥ : Ideal A)
  rw [Ideal.map_bot] at hmap
  have hset : minimalPrimes S = Ideal.comap (algebraMap A S) ⁻¹' minimalPrimes A := hmap
  rw [hset] at hP
  exact hP

/-- **Top-dimensional minimal primes of `A` avoid `f`, so `powers f` is disjoint from them.** A
top-dimensional minimal prime `p` is prime and `f ∉ p` (`havoid`); a power `f ^ n ∈ p` would force
`f ∈ p` (prime). -/
theorem disjoint_powers_of_mem_topDimMinPrimes {f : A} {p : Ideal A}
    (hp : p ∈ TopDimMinPrimes A) (havoid : f ∉ p) :
    Disjoint (Submonoid.powers f : Set A) (p : Set A) := by
  haveI : p.IsPrime := isPrime_of_mem_topDimMinPrimes hp
  rw [Set.disjoint_left]
  rintro x ⟨n, rfl⟩ hxp
  exact havoid (‹p.IsPrime›.mem_of_pow_mem n hxp)

/-! ## `comap` carries `TopDimMinPrimes S` into `TopDimMinPrimes A` -/

/-- **`comap` of a top-dim minimal prime of `S` is one of `A`.** Minimality is
`comap_mem_minimalPrimes_of_away`. Top-dimensionality by a squeeze that needs no `hper` here: with
`p = comap P`, the round-trip `P = map φ p` (`IsLocalization.map_comap`) gives `S ⧸ P ≅
Localization.Away (mk p f)` (the helper), a localization of `A ⧸ p`, so `dim A = dim S = dim (S ⧸ P)
= dim (Localization.Away (mk p f)) ≤ dim (A ⧸ p) ≤ dim A` — forcing `dim (A ⧸ p) = dim A`. -/
theorem comap_mem_topDimMinPrimes_of_away (f : A) (S : Type u) [CommRing S] [Algebra A S]
    [IsLocalization.Away f S] (hdim : ringKrullDim S = ringKrullDim A)
    {P : Ideal S} (hP : P ∈ TopDimMinPrimes S) :
    P.comap (algebraMap A S) ∈ TopDimMinPrimes A := by
  set p := P.comap (algebraMap A S) with hpdef
  have hpmin : p ∈ minimalPrimes A := comap_mem_minimalPrimes_of_away f S hP.1
  haveI : p.IsPrime := hpmin.1.1
  -- `P = map φ (comap φ P) = map φ p` (the localization round-trip on a prime disjoint from `M`).
  have hPeq : P = Ideal.map (algebraMap A S) p :=
    (IsLocalization.map_comap (Submonoid.powers f) S P).symm
  refine ⟨hpmin, ?_⟩
  -- `dim (A ⧸ p) ≥ dim (S ⧸ P)`: `S ⧸ P ≅ Localization.Away (mk p f)`, a localization of `A ⧸ p`.
  have hquoteq : ringKrullDim (S ⧸ P)
      = ringKrullDim (Localization.Away (Ideal.Quotient.mk p f)) := by
    rw [hPeq]; exact ringKrullDim_quotient_map_localizationAway_eq f S p
  have hle1 : ringKrullDim (Localization.Away (Ideal.Quotient.mk p f)) ≤ ringKrullDim (A ⧸ p) :=
    ringKrullDim_localization_le (Submonoid.powers (Ideal.Quotient.mk p f)) _
  have hle2 : ringKrullDim (A ⧸ p) ≤ ringKrullDim A :=
    ringKrullDim_le_of_surjective (Ideal.Quotient.mk p) Ideal.Quotient.mk_surjective
  -- `dim A = dim S = dim (S ⧸ P) = dim (Away (mk p f)) ≤ dim (A ⧸ p) ≤ dim A`, so all equal.
  have hchain : ringKrullDim A ≤ ringKrullDim (A ⧸ p) := by
    calc ringKrullDim A = ringKrullDim S := hdim.symm
      _ = ringKrullDim (S ⧸ P) := hP.2.symm
      _ = ringKrullDim (Localization.Away (Ideal.Quotient.mk p f)) := hquoteq
      _ ≤ ringKrullDim (A ⧸ p) := hle1
  exact le_antisymm hle2 hchain

/-! ## `map` (the inverse) carries `TopDimMinPrimes A` into `TopDimMinPrimes S` -/

/-- **The extension of an `f`-avoiding top-dim minimal prime contracts back to itself.** For
`p ∈ TopDimMinPrimes A` with `f ∉ p`, `(Ideal.map (algebraMap A S) p).comap (algebraMap A S) = p`
(`IsLocalization.comap_map_of_isPrime_disjoint` + the avoidance disjointness). The round-trip that
makes `map p` the `comap`-preimage of `p`, used for the bijection's surjectivity. -/
theorem map_comap_eq_of_mem_topDimMinPrimes (f : A) (S : Type u) [CommRing S] [Algebra A S]
    [IsLocalization.Away f S] {p : Ideal A} (hp : p ∈ TopDimMinPrimes A) (havoid : f ∉ p) :
    (Ideal.map (algebraMap A S) p).comap (algebraMap A S) = p := by
  haveI : p.IsPrime := isPrime_of_mem_topDimMinPrimes hp
  exact IsLocalization.comap_map_of_isPrime_disjoint (Submonoid.powers f) S ‹p.IsPrime›
    (disjoint_powers_of_mem_topDimMinPrimes hp havoid)

/-- **`map p` is a minimal prime of `S`** for `p ∈ TopDimMinPrimes A` avoiding `f`. Via
`IsLocalization.minimalPrimes_map`: `minimalPrimes S = comap ⁻¹' minimalPrimes A`, and
`comap (map p) = p ∈ minimalPrimes A` (`map_comap_eq_of_mem_topDimMinPrimes` + `hp.1`). -/
theorem map_mem_minimalPrimes_of_avoid (f : A) (S : Type u) [CommRing S] [Algebra A S]
    [IsLocalization.Away f S] {p : Ideal A} (hp : p ∈ TopDimMinPrimes A) (havoid : f ∉ p) :
    Ideal.map (algebraMap A S) p ∈ minimalPrimes S := by
  have hmap := IsLocalization.minimalPrimes_map (Submonoid.powers f) S (⊥ : Ideal A)
  rw [Ideal.map_bot] at hmap
  have hset : minimalPrimes S = Ideal.comap (algebraMap A S) ⁻¹' minimalPrimes A := hmap
  rw [hset, Set.mem_preimage, map_comap_eq_of_mem_topDimMinPrimes f S hp havoid]
  exact hp.1

/-- **`map` of an `f`-avoiding top-dim minimal prime of `A` is one of `S`.** Minimality is
`map_mem_minimalPrimes_of_avoid`; the dimension equality is `dim (S ⧸ map φ p) = dim (Away (mk p f))
= dim (A ⧸ p) = dim A = dim S` (the helper, then `hper`, then `hp.2`, then `hdim`). -/
theorem map_mem_topDimMinPrimes_of_avoid (f : A) (S : Type u) [CommRing S] [Algebra A S]
    [IsLocalization.Away f S] (hdim : ringKrullDim S = ringKrullDim A)
    (hper : ∀ p ∈ TopDimMinPrimes A,
      ringKrullDim (Localization.Away (Ideal.Quotient.mk p f)) = ringKrullDim (A ⧸ p))
    {p : Ideal A} (hp : p ∈ TopDimMinPrimes A) (havoid : f ∉ p) :
    Ideal.map (algebraMap A S) p ∈ TopDimMinPrimes S := by
  refine ⟨map_mem_minimalPrimes_of_avoid f S hp havoid, ?_⟩
  rw [ringKrullDim_quotient_map_localizationAway_eq f S p, hper p hp, hp.2, hdim]

/-! ## The bijection and the count -/

/-- **`comap` is a `Set.BijOn` `TopDimMinPrimes S → TopDimMinPrimes A`.** Maps-to:
`comap_mem_topDimMinPrimes_of_away`. Injective: `comap (algebraMap A S)` is injective on `Ideal S`
(left-inverse `map`, `IsLocalization.map_comap`). Surjective onto: for `p ∈ TopDimMinPrimes A`, the
extension `map p` is in `TopDimMinPrimes S` (`map_mem_topDimMinPrimes_of_avoid`) with `comap (map p)
= p` (`map_comap_eq_of_mem_topDimMinPrimes`). The `havoid`/`hper` inputs feed the `map`-side. -/
theorem bijOn_comap_topDimMinPrimes_away (f : A) (S : Type u) [CommRing S] [Algebra A S]
    [IsLocalization.Away f S] (hdim : ringKrullDim S = ringKrullDim A)
    (havoid : ∀ p ∈ TopDimMinPrimes A, f ∉ p)
    (hper : ∀ p ∈ TopDimMinPrimes A,
      ringKrullDim (Localization.Away (Ideal.Quotient.mk p f)) = ringKrullDim (A ⧸ p)) :
    Set.BijOn (Ideal.comap (algebraMap A S)) (TopDimMinPrimes S) (TopDimMinPrimes A) := by
  refine ⟨fun P hP ↦ comap_mem_topDimMinPrimes_of_away f S hdim hP, ?_, ?_⟩
  · -- InjOn: `comap` is globally injective for a localization (left inverse `map`).
    intro P _ Q _ hPQ
    exact Function.LeftInverse.injective (IsLocalization.map_comap (Submonoid.powers f) S) hPQ
  · -- SurjOn: `p ↦ map p`.
    intro p hp
    exact ⟨Ideal.map (algebraMap A S) p,
      map_mem_topDimMinPrimes_of_avoid f S hdim hper hp (havoid p hp),
      map_comap_eq_of_mem_topDimMinPrimes f S hp (havoid p hp)⟩

/-- **Away-localization preserves the top-dimensional minimal-prime count.** The headline reusable
survival lemma: inverting a single element `f` of `A` keeps `(TopDimMinPrimes ·).ncard` fixed, given
avoidance `havoid` and the componentwise no-drop `hper`. The two non-unit localization steps W1
(`detΔ`) and W2 (`detSchurS`) of the fibre-`θ` chart transport are instances. -/
theorem topDimMinPrimes_ncard_away_eq (f : A) (S : Type u) [CommRing S] [Algebra A S]
    [IsLocalization.Away f S] (hdim : ringKrullDim S = ringKrullDim A)
    (havoid : ∀ p ∈ TopDimMinPrimes A, f ∉ p)
    (hper : ∀ p ∈ TopDimMinPrimes A,
      ringKrullDim (Localization.Away (Ideal.Quotient.mk p f)) = ringKrullDim (A ⧸ p)) :
    (TopDimMinPrimes S).ncard = (TopDimMinPrimes A).ncard :=
  (bijOn_comap_topDimMinPrimes_away f S hdim havoid hper).ncard_eq

end DLNFibre.Core
