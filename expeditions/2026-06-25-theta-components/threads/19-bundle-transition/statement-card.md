# Statement card — the transition cocycle on chart overlaps (B3-3)

Thread 19 (`19-bundle-transition`). Builds the **transition coherence** rung that thread 18
(`FibreBundlePerMinor`) explicitly disclaimed: a genuine cocycle datum **at the ring/localization
level** for the per-minor principal-open cover of `Mat^{=r}`. NOT the existential `GL × GL`
base-change transport, and NOT (honestly disclaimed) the deep Schur-chart `e_β` comparison.

File: `lean/DLNFibre/Core/FibreBundleTransition.lean` (imports `Core.RankMinorCover`,
`Mathlib.RingTheory.Localization.Away.Basic`, `Mathlib.LinearAlgebra.Matrix.MvPolynomial`).

---

## Card 1 — the overlap transition `AlgEquiv` (the headline)

> **Claim.** Over any commutative ring `R` and `f, g : R`, the two iterated localizations representing
> the principal-open overlap `D(f) ∩ D(g)` — localize at `f` then `g`, vs at `g` then `f` — are
> canonically isomorphic as `R`-algebras: the genuine transition datum of the cover.
>
> - **Lean:** `DLNFibre.Core.awayOverlapTransition`
>   - `awayOverlap f g := Localization.Away (algebraMap R (Localization.Away f) g)`
>   - `awayOverlapTransition (f g : R) : awayOverlap f g ≃ₐ[R] awayOverlap g f`
> - **Gloss.** Both `awayOverlap f g` and `awayOverlap g f` are `IsLocalization.Away (f * g) R` (the
>   Mathlib double-localization instances from `IsLocalization.Away.mul'` / `.mul`), i.e. localizations
>   of `R` at the **same** submonoid `powers (f * g)`. `IsLocalization.algEquiv` supplies the canonical
>   `R`-algebra iso between any two such.
> - **Proved.** Definition via `IsLocalization.algEquiv`; non-vacuous (it is the genuine localization
>   iso, not a stub).
> - **Assumed.** `[CommRing R]` only.
> - **Cited.** none. **Deferred.** the deep Schur-chart comparison (see Card 5).
> - **Status.** sorry-free; axiom-clean `[propext, Classical.choice, Quot.sound]`.

## Card 2 — the cocycle coherence laws

> **Claim.** The transition `AlgEquiv` satisfies the genuine cocycle laws: it fixes `R`, is its own
> inverse under swap, round-trips to the identity, and the triple-overlap composite is the identity.
>
> - **Lean:**
>   - `awayOverlapTransition_commutes (f g : R) (x : R) :`
>     `awayOverlapTransition f g (algebraMap R (awayOverlap f g) x) = algebraMap R (awayOverlap g f) x`
>     — base normalization (`AlgEquiv.commutes`).
>   - `awayOverlapTransition_symm (f g : R) :`
>     `(awayOverlapTransition f g).symm = awayOverlapTransition g f` — symmetry.
>   - `awayOverlapTransition_trans_symm (f g : R) :`
>     `(awayOverlapTransition f g).trans (awayOverlapTransition g f) = AlgEquiv.refl` — round-trip id.
> - **Gloss.** A localization is initial among `R`-algebras inverting the denominators, so any two
>   `R`-algebra maps out of it agree (`IsLocalization.algHom_subsingleton`). The symm/round-trip laws
>   reduce to a `Subsingleton (… →ₐ[R] …)` elimination.
> - **Proved.** Unconditionally. **Assumed.** `[CommRing R]`.
> - **Status.** sorry-free; axiom-clean.

## Card 3 — the triple-overlap cocycle identity

> **Claim.** On `D(f) ∩ D(g) ∩ D(h)`, the three cyclic iterated-localization presentations are all
> localizations of `R` at `powers (f * g * h)`, and the three pairwise transitions compose around the
> cycle to the identity — the cocycle identity `g_{fg} ∘ g_{gh} ∘ g_{hf} = 1`. **Precision:** this
> identity is *automatic by localization initiality* (the cyclic composite is the unique `R`-algebra
> endomorphism of the localization, hence `refl`), NOT a compatibility checked on independently-built
> maps — for canonical localization isos at one monoid the diagram commutes for free. The content is
> that the three iterated presentations of the same triple overlap are coherently identified.
>
> - **Lean:** `DLNFibre.Core.awayTriple_cocycle` (with helper
>   `DLNFibre.Core.isLocalization_awayTriple {a b c x : R} (hx : x = a * b * c) :`
>   `IsLocalization (Submonoid.powers x) (awayTriple a b c)`)
>   - `awayTriple f g h := Localization.Away (algebraMap R (awayOverlap f g) h)`
>   - `awayTriple_cocycle (f g h : R) :`
>     `((algEquiv (powers (f*g*h)) (awayTriple f g h) (awayTriple g h f)).trans (algEquiv …
>       (awayTriple g h f) (awayTriple h f g))).trans (algEquiv … (awayTriple h f g)
>       (awayTriple f g h)) = AlgEquiv.refl`
> - **Gloss.** `awayTriple a b c` is `IsLocalization.Away ((a*b)*c)`; `IsLocalization.Away.of_associated`
>   realigns the product so all three cyclic orders localize at the same `powers (f*g*h)`. The cyclic
>   composite is an `R`-algebra endomorphism of `awayTriple f g h`, hence `= refl`
>   (`IsLocalization.algHom_subsingleton`). The three required instances are supplied in the statement's
>   type via `haveI := isLocalization_awayTriple …`.
> - **Proved.** Unconditionally. **Assumed.** `[CommRing R]`.
> - **Status.** sorry-free; axiom-clean.

## Card 4 — instantiation at the per-minor charts of `Mat^{=r}`

> **Claim.** The per-minor charts `minorChart s t` of `Mat^{=r}` are principal opens
> `D(detMinorPoly s t)` of the matrix coordinate ring, and two such charts' overlap carries the
> transition cocycle of Card 1.
>
> - **Lean:** `DLNFibre.Core.detMinorPoly`, `DLNFibre.Core.eval_detMinorPoly`,
>   `DLNFibre.Core.minorChartTransition`
>   - `detMinorPoly (s : Fin r → Fin p) (t : Fin r → Fin q) : MvPolynomial (Fin p × Fin q) k :=`
>     `((Matrix.mvPolynomialX (Fin p) (Fin q) k).submatrix s t).det` — the minor det of the generic
>     matrix.
>   - `eval_detMinorPoly (M …) : MvPolynomial.eval (fun ij ↦ M ij.1 ij.2) (detMinorPoly s t)`
>     `= (M.submatrix s t).det` — evaluation recovers the pointwise minor det, so
>     `minorChart s t = D(detMinorPoly s t)`.
>   - `minorChartTransition (s t s' t') :` the overlap transition `AlgEquiv`
>     `awayOverlap (detMinorPoly s t) (detMinorPoly s' t') ≃ₐ[R] awayOverlap (detMinorPoly s' t')`
>     `(detMinorPoly s t)` (= `awayOverlapTransition (detMinorPoly s t) (detMinorPoly s' t')`).
> - **Gloss.** `eval_detMinorPoly`: `eval e` is a ring hom, commutes with `det` (`RingHom.map_det`),
>   and the RECTANGULAR generic matrix `mvPolynomialX (Fin p) (Fin q)` maps to `M` under `eval₂ id e`
>   (`Matrix.mvPolynomialX_map_eval₂`), matching after `submatrix`.
> - **Proved.** `k : Type` (universe 0) — pinned to match `RankMinorCover.minorChart`'s `Type`
>   monomorphism (harmless: `k = ℂ` is `Type 0`).
> - **Assumed.** `[Field k]`. **Cited.** none.
> - **Status.** sorry-free; axiom-clean.

## Card 5 — what is DEFERRED (honest scope; NOT named `locallyTrivial`)

> **NOT built.** This is the transition cocycle on the **ambient affine-space** principal-open cover
> (`R = O(Mat) = MvPolynomial (Fin p × Fin q) k`). It does **not** identify these ambient overlap
> transitions with the deep **Schur-chart** localized `AlgEquiv` `Core.chartLocalizedAlgEquiv`
> (`e_β : Away chartDsig ≃ₐ[k] Away chartGfib`), which lives in localized *chart* coordinates and is
> built (~250 LoC) only at the top-left pivot of a single `(d, r)`.
>
> - **Cost to finish (`locallyTrivial` in the deep-chart sense).** A per-pivot transport identifying
>   each `e_{s,t}` with the ambient principal-open presentation, OR re-deriving `e_β` at each pivot
>   `(s, t)` — a separate multi-module build (the thread-11/thread-18 reads both flag re-deriving the
>   ~250-LoC chart machinery per pivot as out of one tide's budget). Until that bridge exists, the
>   bundle is **not** named `locallyTrivial`; this rung is the genuine base-space transition cocycle.

---

## Aggregator import line (controller to wire — single-writer `DLNFibre.lean`)

```
import DLNFibre.Core.FibreBundleTransition
```

(`FibreBundleTransition` imports `Core.RankMinorCover` + two Mathlib files. The abstract
`awayOverlap*` / `awayTriple*` engine is network-free / Mathlib-adjacent — a spin-out candidate, like
`mvPolynomialAwayMapTensorAlgEquiv` and `RankMinorCover`.)

## Codex consult

`threads/19-bundle-transition/codex/transition-route-{prompt,answer}.md` (xhigh): confirmed route (A)
[the base-space localization cocycle via `IsLocalization.algEquiv` + `Away.mul'`] is the right genuine
cocycle datum, with the three coherence laws discharged by localization uniqueness, and with the
deep-chart comparison honestly disclaimed (do NOT call it `locallyTrivial`).
