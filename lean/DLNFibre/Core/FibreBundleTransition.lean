/-
Copyright (c) 2026. Released under Apache 2.0; see LICENSE.
-/
import DLNFibre.Core.RankMinorCover
import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.LinearAlgebra.Matrix.MvPolynomial

/-!
# `DLNFibre.Core.FibreBundleTransition` — the transition cocycle on chart overlaps (B3-3)

Thread 18 (`Core.FibreBundlePerMinor`) built the genuine per-minor open cover of `Mat^{=r}` plus the
per-minor `GL_r × Mat × Mat` chart family, but explicitly did **not** build the **transition
coherence** on chart overlaps — so it stopped short of `locallyTrivial`.

This module supplies the missing rung at the level the brief specifies — a **genuine cocycle datum
at the ring/localization level**, not the existential `GL × GL` base-change transport.

## What is built (honest scope)

Over the coordinate ring `R = MvPolynomial (Fin p × Fin q) k` of the ambient matrix space, each
per-minor chart `minorChart s t = {M | the (s,t) minor is invertible}` is the **principal open**
`D(detMinorPoly s t)` cut by the minor-determinant polynomial `detMinorPoly s t` (its evaluation at
a point `M` is `(M.submatrix s t).det`, `eval_detMinorPoly`). On the overlap `D(f) ∩ D(g)` of two
charts (`f = detMinorPoly s t`, `g = detMinorPoly s' t'`), the two iterated localizations

> `Away (algebraMap R (Away f) g)`   (localize at chart `f`, then at `g`)
> `Away (algebraMap R (Away g) f)`   (localize at chart `g`, then at `f`)

are **both** `IsLocalization.Away (f * g) R` (`IsLocalization.Away.mul'` / `.mul`, available as
Mathlib instances), i.e. localizations of `R` at the **same** submonoid `powers (f * g)`. The
canonical `R`-algebra **transition `AlgEquiv`** between them is `awayOverlapTransition`
(= `IsLocalization.algEquiv`), and it satisfies the genuine cocycle laws:

- **base normalization** `awayOverlapTransition_commutes`: the transition fixes the image of `R`
  (it is an `R`-algebra map);
- **symmetry** `awayOverlapTransition_symm`: `(awayOverlapTransition f g).symm =
  awayOverlapTransition g f` (the two presentations of the overlap swap);
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

## What is NOT built (disclaimed — the deeper rung)

This is the cocycle on the **ambient affine-space** principal-open cover (`R = O(Mat)`). It does
**not** identify these ambient overlap transitions with the **deep Schur-chart** localized
`AlgEquiv` `Core.chartLocalizedAlgEquiv` (`e_β : Away chartDsig ≃ₐ[k] Away chartGfib`), which lives
in localized *chart* coordinates and is built (~250 LoC) only at the top-left pivot of a single
`(d, r)`. Connecting the two — a per-pivot transport identifying each `e_{s,t}` with the ambient
principal-open presentation — is the remaining work, and re-deriving `e_β` per pivot is a separate
multi-module build. Accordingly the bundle is **not** named `locallyTrivial`: this is the genuine
base-space transition cocycle, with the Schur-chart comparison honestly deferred.

**Dependency rule:** `Core` only — never import `DLNFibre.DLN`.
-/

namespace DLNFibre.Core

open MvPolynomial Matrix

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

/-! ## Instantiation at the per-minor charts of `Mat^{=r}` -/

section MinorChart

variable {k : Type} [Field k] {p q r : ℕ}

/-- **The minor-determinant polynomial** `detMinorPoly s t : MvPolynomial (Fin p × Fin q) k`: the
determinant of the `(s, t)` minor of the **generic matrix** `Matrix.mvPolynomialX` (entries the
coordinate variables `X (i, j)`). Its evaluation at a point `M` is `(M.submatrix s t).det`
(`eval_detMinorPoly`), so the per-minor chart `minorChart s t` (the `(s, t)` minor invertible) is
the principal open `D(detMinorPoly s t)` of the matrix coordinate ring. -/
noncomputable def detMinorPoly (s : Fin r → Fin p) (t : Fin r → Fin q) :
    MvPolynomial (Fin p × Fin q) k :=
  ((Matrix.mvPolynomialX (Fin p) (Fin q) k).submatrix s t).det

/-- **The minor polynomial evaluates to the minor determinant.** Evaluating `detMinorPoly s t` at
the point `M` (the assignment `X (i, j) ↦ M i j`) gives `(M.submatrix s t).det`. So membership
`M ∈ minorChart s t` (the `(s, t)` minor invertible) is equivalent to
`MvPolynomial.eval (fun ij ↦ M ij.1 ij.2) (detMinorPoly s t)` being a unit — the chart is the
principal open `D(detMinorPoly s t)`. -/
theorem eval_detMinorPoly (M : Matrix (Fin p) (Fin q) k)
    (s : Fin r → Fin p) (t : Fin r → Fin q) :
    MvPolynomial.eval (fun ij ↦ M ij.1 ij.2) (detMinorPoly (k := k) s t)
      = (M.submatrix s t).det := by
  -- `eval e` is a ring hom; it commutes with `det` (`RingHom.map_det`). The mapped minor matrix
  -- is `M.submatrix s t`: `map` commutes with `submatrix`, and `eval e` sends the generic matrix
  -- `mvPolynomialX` to `M` (`mvPolynomialX_mapMatrix_eval`).
  have hmap : ((Matrix.mvPolynomialX (Fin p) (Fin q) k).submatrix s t).map
      (MvPolynomial.eval fun ij ↦ M ij.1 ij.2) = M.submatrix s t := by
    rw [← Matrix.submatrix_map]
    -- the RECTANGULAR generic matrix maps to `M` under `eval e = eval₂ id e`
    -- (`mvPolynomialX_map_eval₂`); `submatrix` then matches.
    congr 1
    rw [MvPolynomial.eval, MvPolynomial.coe_eval₂Hom]
    exact Matrix.mvPolynomialX_map_eval₂ (RingHom.id k) M
  rw [detMinorPoly, RingHom.map_det, RingHom.mapMatrix_apply, hmap]

/-- **The per-minor charts are principal opens, and their overlaps carry the transition cocycle.**
For two pivot positions `(s, t)`, `(s', t')`, the overlap `minorChart s t ∩ minorChart s' t'` is the
principal open `D(detMinorPoly s t · detMinorPoly s' t')` of the matrix coordinate ring, and the two
iterated localizations (localize at one minor then the other) are canonically identified by the
transition `AlgEquiv` `awayOverlapTransition (detMinorPoly s t) (detMinorPoly s' t')`. This
instantiates the abstract base-space cocycle at the genuine per-minor cover of `Mat^{=r}`. -/
noncomputable def minorChartTransition (s : Fin r → Fin p) (t : Fin r → Fin q)
    (s' : Fin r → Fin p) (t' : Fin r → Fin q) :
    awayOverlap (detMinorPoly (k := k) s t) (detMinorPoly (k := k) s' t')
      ≃ₐ[MvPolynomial (Fin p × Fin q) k]
        awayOverlap (detMinorPoly (k := k) s' t') (detMinorPoly (k := k) s t) :=
  awayOverlapTransition (detMinorPoly s t) (detMinorPoly s' t')

end MinorChart

end DLNFibre.Core
