/-
Copyright (c) 2026. Released under Apache 2.0; see LICENSE.
-/
import Mathlib.RingTheory.Localization.Away.Basic

/-!
# `Localization` — the transition cocycle on principal-open overlaps

For a commutative ring `R` and elements `f g h : R`, the basic opens `D(f)`, `D(g)`, `D(h)` of
`Spec R` overlap in `D(f) ∩ D(g)` (coordinate ring `Away (f * g)`) and `D(f) ∩ D(g) ∩ D(h)`
(coordinate ring `Away (f * g * h)`). This file packages the **canonical transition data** of such a
principal-open cover — the iterated double/triple `Away`-localizations, the canonical `R`-algebra
transition `AlgEquiv`s between the two/three iterated presentations of an overlap, and the cocycle
identities they satisfy — entirely at the level of an arbitrary `CommRing R`.

## What is built

Over `R`, each iterated localization
> `awayOverlap f g := Away (algebraMap R (Away f) g)`   (localize at `f`, then at `g`)
is, by `IsLocalization.Away.mul'`, the localization of `R` at `f * g` — the coordinate ring of the
overlap `D(f) ∩ D(g)`. The canonical `R`-algebra **transition** between the two presentations
`awayOverlap f g` and `awayOverlap g f` (localizing in the opposite order) is
`awayOverlapTransition` (= `IsLocalization.algEquiv` at `powers (f * g)`), and it satisfies the
cocycle laws:

- **base normalization** `awayOverlapTransition_commutes`: the transition fixes the image of `R`
  (it is an `R`-algebra map);
- **symmetry** `awayOverlapTransition_symm`: `(awayOverlapTransition f g).symm =
  awayOverlapTransition g f` (the two presentations of `D(f) ∩ D(g)` swap);
- **round-trip identity** `awayOverlapTransition_trans_symm`: `(f, g)` then `(g, f)` is `id`;
- **triple-overlap cocycle** `awayTriple_cocycle`: the three pairwise transitions on
  `D(f) ∩ D(g) ∩ D(h)` compose, around the cycle, to the identity — the genuine cocycle condition
  `g_{fg} ∘ g_{gh} ∘ g_{hf} = 1`;
- **single-chart restriction** `awayOverlapTransition_restrict_left`: restricting the transition
  along the chart-`f` localization map `Away f → awayOverlap f g` gives the canonical chart-`f` map
  `chartToSwappedOverlap` into the swapped overlap `awayOverlap g f` — the genuine overlap-LOCAL
  statement that the transition identifies the two single-chart presentations *on the overlap* (not
  merely through a common target).

All of these hold because the localization is initial among `R`-algebras inverting the relevant
denominators, so any two `R`-algebra maps out of it agree (`IsLocalization.algHom_subsingleton`).

These are general localization combinators — the eventual home is
`Mathlib.RingTheory.Localization.*`, so they live in the bare `Localization` namespace (L7
Mathlib-mirror), network-free over arbitrary `R`.
-/

namespace Localization

/-! ## The abstract transition cocycle for a principal-open cover of `Spec R` -/

section Abstract

variable {R : Type*} [CommRing R]

/-- **The overlap double-localization, chart-`f`-first.** `Away (algebraMap R (Away f) g)`: localize
`R` at `f`, then localize that at the image of `g`. By `IsLocalization.Away.mul'` this is the
localization of `R` at `f * g` — the coordinate ring of the overlap `D(f) ∩ D(g)`. -/
abbrev awayOverlap (f g : R) : Type _ :=
  Localization.Away (algebraMap R (Localization.Away f) g)

/-- **The transition `AlgEquiv` on the overlap `D(f) ∩ D(g)`.** Both `awayOverlap f g` and
`awayOverlap g f` are localizations of `R` at the submonoid `powers (f * g)` (the `.mul'` / `.mul`
instances), so `IsLocalization.algEquiv` supplies the canonical `R`-algebra iso between them — the
genuine transition datum of the principal-open cover. -/
noncomputable def awayOverlapTransition (f g : R) :
    awayOverlap f g ≃ₐ[R] awayOverlap g f :=
  IsLocalization.algEquiv (Submonoid.powers (f * g)) (awayOverlap f g) (awayOverlap g f)

/-- **Cocycle: the transition agrees with the base structure map.** The transition `AlgEquiv` sends
`algebraMap R (awayOverlap f g) x` to `algebraMap R (awayOverlap g f) x` — it is an `R`-algebra map,
so it fixes the image of `R`. (This is `AlgEquiv.commutes`; the cocycle's normalization.) -/
theorem awayOverlapTransition_commutes (f g : R) (x : R) :
    awayOverlapTransition f g (algebraMap R (awayOverlap f g) x)
      = algebraMap R (awayOverlap g f) x :=
  (awayOverlapTransition f g).commutes x

/-- **Cocycle: symmetry.** The inverse of the `(f, g)` transition is the `(g, f)` transition (the
two presentations of `D(f) ∩ D(g)` swap), as `R`-algebra isos
`awayOverlap g f ≃ₐ[R] awayOverlap f g`. Both are `R`-algebra maps out of the localization
`awayOverlap g f`, so they agree by the universal property (`IsLocalization.algHom_subsingleton` at
the submonoid `powers (g * f)`). -/
theorem awayOverlapTransition_symm (f g : R) :
    (awayOverlapTransition f g).symm = awayOverlapTransition g f :=
  have : Subsingleton (awayOverlap g f →ₐ[R] awayOverlap f g) :=
    IsLocalization.algHom_subsingleton (Submonoid.powers (g * f))
  AlgEquiv.coe_algHom_injective (Subsingleton.elim _ _)

/-- **Cocycle: identity normalization.** The pairwise round trip `(g, f) ∘ (f, g)` is the identity
on `awayOverlap f g` — a localization, so the only `R`-algebra endomorphism is the identity
(`IsLocalization.algHom_subsingleton` at `powers (f * g)`). -/
theorem awayOverlapTransition_trans_symm (f g : R) :
    (awayOverlapTransition f g).trans (awayOverlapTransition g f) = AlgEquiv.refl :=
  have : Subsingleton (awayOverlap f g →ₐ[R] awayOverlap f g) :=
    IsLocalization.algHom_subsingleton (Submonoid.powers (f * g))
  AlgEquiv.coe_algHom_injective (Subsingleton.elim _ _)

/-! ### The overlap restriction of the single chart (the genuine overlap-local content) -/

/-- **The chart-`f` denominator `f` is a unit in the swapped overlap `awayOverlap g f`.** Each power
`f ^ n` maps to a unit: `awayOverlap g f = Away (algebraMap R (Away g) f)`, so the image of `f`
(through the scalar tower `R → Away g → awayOverlap g f`) is the localizing element, made a unit by
`IsLocalization.Away.algebraMap_isUnit`. -/
theorem isUnit_ofId_powers_awayOverlap (f g : R) (y : Submonoid.powers f) :
    IsUnit ((Algebra.ofId R (awayOverlap g f)) (y : R)) := by
  obtain ⟨_, n, rfl⟩ := y
  rw [Algebra.ofId_apply, map_pow]
  refine IsUnit.pow n ?_
  rw [IsScalarTower.algebraMap_apply R (Localization.Away g) (awayOverlap g f)]
  exact IsLocalization.Away.algebraMap_isUnit (algebraMap R (Localization.Away g) f)

/-- **The canonical `R`-algebra map from the single chart `Away f` into the swapped overlap.** Since
`f` is a unit in `awayOverlap g f` (`isUnit_ofId_powers_awayOverlap`), the localization universal
property (`IsLocalization.liftAlgHom`) gives a unique `R`-algebra map
`Localization.Away f →ₐ[R] awayOverlap g f` — the structure map presenting the overlap as a further
localization of chart `f`. -/
noncomputable def chartToSwappedOverlap (f g : R) :
    Localization.Away f →ₐ[R] awayOverlap g f :=
  IsLocalization.liftAlgHom (A := R) (M := Submonoid.powers f)
    (S := Localization.Away f) (P := awayOverlap g f)
    (f := Algebra.ofId R (awayOverlap g f)) (isUnit_ofId_powers_awayOverlap f g)

/-- **The overlap transition restricts to the single chart compatibly (the genuine overlap-local
cocycle content).** On the double overlap `D(f) ∩ D(g)`, restricting the transition
`awayOverlapTransition f g` along the chart-`f` localization map `Away f → awayOverlap f g` gives
the canonical chart-`f` map into the swapped overlap `awayOverlap g f` — i.e. the transition
genuinely identifies the two single-chart presentations *on the overlap*, not merely through a
common target. Both composites are `R`-algebra maps out of the localization `Away f`, so they agree
by the universal property (`IsLocalization.algHom_subsingleton` at `powers f`). -/
theorem awayOverlapTransition_restrict_left (f g : R) :
    (awayOverlapTransition f g).toAlgHom.comp
        (IsScalarTower.toAlgHom R (Localization.Away f) (awayOverlap f g))
      = chartToSwappedOverlap f g :=
  have : Subsingleton (Localization.Away f →ₐ[R] awayOverlap g f) :=
    IsLocalization.algHom_subsingleton (Submonoid.powers f)
  Subsingleton.elim _ _

end Abstract

/-! ## The triple-overlap cocycle condition -/

section TripleOverlap

variable {R : Type*} [CommRing R]

/-- The overlap ring of three charts `D(f) ∩ D(g) ∩ D(h)`: localize `R` at the chart-`(f, g)`
overlap, then at `h`. By the iterated `IsLocalization.Away.mul'` instances this is the localization
of `R` at `(f * g) * h` — the coordinate ring of the triple overlap. -/
abbrev awayTriple (f g h : R) : Type _ :=
  Localization.Away (algebraMap R (awayOverlap f g) h)

/-- The triple overlap ring `awayTriple a b c` is the localization of `R` at **any** element `x`
equal to `a * b * c` — in particular at `f * g * h` for any cyclic reordering. (Instance-wise it is
`IsLocalization.Away ((a * b) * c)`; `IsLocalization.Away.of_associated` realigns the product to
`x`.) This is the explicit instance the `algEquiv` cocycle below consumes — all three cyclic
presentations localize at the same submonoid `powers (f * g * h)`. -/
theorem isLocalization_awayTriple {a b c x : R} (hx : x = a * b * c) :
    IsLocalization (Submonoid.powers x) (awayTriple a b c) := by
  haveI : IsLocalization.Away ((a * b) * c) (awayTriple a b c) := inferInstance
  -- `a * b * c` parses as `(a * b) * c`, so `hx` makes the goal element the instance's element.
  have hassoc : Associated ((a * b) * c) x := by rw [hx]
  exact IsLocalization.Away.of_associated (S := awayTriple a b c) hassoc

/-- **The triple-overlap cocycle identity.** On `D(f) ∩ D(g) ∩ D(h)`, the three iterated
localization presentations `awayTriple f g h`, `awayTriple g h f`, `awayTriple h f g` are all
localizations of `R` at the same submonoid `powers (f * g * h)` (`isLocalization_awayTriple`, up to
the `Associated` reordering of the product). The canonical `R`-algebra transitions between them
(`IsLocalization.algEquiv`) compose, around the cycle, to the **identity** —
`g_{fg} ∘ g_{gh} ∘ g_{hf} = 1`.

This cocycle identity is **automatic by localization initiality**, not a compatibility checked on
independently-built maps: the cyclic composite is an `R`-algebra endomorphism of the localization
`awayTriple f g h`, and the localization is initial among `R`-algebras inverting the denominators,
so its only `R`-algebra endomorphism is the identity (`IsLocalization.algHom_subsingleton`). (For
canonical localization isos at one monoid the diagram commutes for free — the content is that the
three iterated presentations of the same triple overlap are coherently identified.) -/
theorem awayTriple_cocycle (f g h : R) :
    haveI := isLocalization_awayTriple (a := f) (b := g) (c := h) rfl
    haveI := isLocalization_awayTriple (a := g) (b := h) (c := f) (x := f * g * h) (by ring)
    haveI := isLocalization_awayTriple (a := h) (b := f) (c := g) (x := f * g * h) (by ring)
    (((IsLocalization.algEquiv (Submonoid.powers (f * g * h))
          (awayTriple f g h) (awayTriple g h f)).trans
        (IsLocalization.algEquiv (Submonoid.powers (f * g * h))
          (awayTriple g h f) (awayTriple h f g))).trans
      (IsLocalization.algEquiv (Submonoid.powers (f * g * h))
        (awayTriple h f g) (awayTriple f g h)))
      = AlgEquiv.refl := by
  haveI := isLocalization_awayTriple (a := f) (b := g) (c := h) (x := f * g * h) rfl
  have : Subsingleton (awayTriple f g h →ₐ[R] awayTriple f g h) :=
    IsLocalization.algHom_subsingleton (Submonoid.powers (f * g * h))
  exact AlgEquiv.coe_algHom_injective (Subsingleton.elim _ _)

end TripleOverlap

end Localization
