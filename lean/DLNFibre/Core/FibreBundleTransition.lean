/-
Copyright (c) 2026. Released under Apache 2.0; see LICENSE.
-/
import DLNFibre.Core.RankMinorCover
import DLNFibre.Core.RingTheory.Localization.Overlap
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

The **abstract** transition cocycle for a principal-open cover of `Spec R` over an arbitrary
`CommRing R` — `awayOverlap`/`awayOverlapTransition` + the three pairwise cocycle laws, the
single-chart restriction `awayOverlapTransition_restrict_left`/`chartToSwappedOverlap`, and the
triple-overlap cocycle `awayTriple_cocycle` — now lives in
[`DLNFibre.Core.RingTheory.Localization.Overlap`](RingTheory/Localization/Overlap.lean) (bare
`Localization` namespace, the Mathlib-mirror home for these general localization combinators).

This module **instantiates** that abstract cocycle at the per-minor cover of `Mat^{=r}`. Over the
coordinate ring `R = MvPolynomial (Fin p × Fin q) k` of the ambient matrix space, each per-minor
chart `minorChart s t = {M | the (s,t) minor is invertible}` is the **principal open**
`D(detMinorPoly s t)` cut by the minor-determinant polynomial `detMinorPoly s t` (its evaluation at
a point `M` is `(M.submatrix s t).det`, `eval_detMinorPoly`). On the overlap `D(f) ∩ D(g)` of two
charts (`f = detMinorPoly s t`, `g = detMinorPoly s' t'`), the two iterated localizations are
canonically identified by `minorChartTransition` = `Localization.awayOverlapTransition` at the two
minor polynomials — the genuine per-minor instance of the abstract base-space cocycle.

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

open MvPolynomial Matrix Localization

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
