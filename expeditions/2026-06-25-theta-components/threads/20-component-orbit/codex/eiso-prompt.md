# Codex consult — which component iso is actually achievable from the chart transport?

DESIGN/SOUNDNESS consult before a ~500-line Lean build. Adjudicate a structural fork; do not write
Lean. I am building the variety-level "fibre component ≅ orbit × affine" iso (NOT for smoothness —
that's already done unconditionally; this is for the Lemma-4.6 bundle / geometric component
description).

## The labeled transport chain (each rung an AlgEquiv of component-quotient rings)
Fibre top-component minimal prime `I` of `R_F = sweepFibreRing` (reduced, dim of component = `dim F`).
1. Schur poly extension: `R_FS = MvPolynomial SchurVar R_F`, `|SchurVar| = δ`. Component `map C I`.
   `R_FS ⧸ (map C I) ≃ₐ[k] MvPolynomial SchurVar (R_F ⧸ I)`  [Mathlib `quotientEquivQuotientMvPolynomial`].
   So the component on the Schur side is `MvPolynomial SchurVar (R_F⧸I)` — dim `dim F + δ`.
2. Localize at `gF` (avoidance: `gF ∉ map C I`): `Away gF`. Component survives.
3. Chart `e_β : Away dsig ≃ₐ[k] Away gF` [BUILT, `ChartLocalizedAlgEquiv`]. Transport component back.
4. `Away dsig` = localization of `O(Σ^r) = sweepSigmaRing` at `dsig`. Descend component to `O(Σ^r)`.
5. W0: `O(Σ^r)` top component ↔ `O(Σ̄^r)` top component `q`, and `O(Σ̄^r)⧸q ≃ₐ[k] orbitRing (realizerD m)`
   over the FULL `d` [BUILT, my `exists_sigma_topComponent_orbitRingEquiv`], dim `dim F + δ`.

## What the transport ACTUALLY produces
Tracing the component quotient through 1–5, the natural output is a `k`-algebra iso of the
(equal-dimension, `dim F + δ`) objects:

  **`MvPolynomial SchurVar (R_F ⧸ I)  ≃ₐ[k]  (a localization-matched form of) orbitRing (realizerD m)`**

i.e. `(fibre component) × A^δ  ≅  (full-d sigma orbit)`. Call this **(B) ≅ (A) × A^δ**.

BUT the consumer `isSmoothAt_sweepFibre_of_component_orbitPolyEquiv` (thread-20) wants the OTHER shape:

  **`R_F ⧸ I  ≃ₐ[k]  MvPolynomial η (orbitRing M)`**   with `M` a SHIFTED orbit over `d−r` (dim `dim F − δ`).

i.e. `(A) ≅ (C) × A^δ`. The poly wrapper is on the ORBIT side, and the orbit is the small shifted one.

## The fork (adjudicate sharply)

1. **Is the transport's natural output really `(B) ≅ (A)×A^δ` (poly wrapper on the FIBRE side, full-d
   orbit), not the consumer's `(A) ≅ (C)×A^δ`?** Confirm the chain lands `MvPolynomial SchurVar (R_F⧸I)
   ≃ orbitRing(realizerD m)`, NOT `R_F⧸I ≃ MvPolynomial η (orbit over d−r)`. (The localizations in
   steps 2-4 mean the iso is between LOCALIZED rings; does descending to the unlocalized component
   give a clean global iso, or only an iso after inverting some element on each side?)

2. **Is `(A) ≅ (C)×A^δ` (the consumer's target) even TRUE as a global k-algebra iso?** Dimensionally
   yes (`dim F = (dim F − δ) + δ`). But is the fibre component GLOBALLY a product (shifted orbit
   closure) × A^δ, or only locally/birationally? Block-triangular fibre intuition: the fibre over E_r
   = {(maps) : product = E_r}; fixing the "C-part" (the δ Schur coords on the invertible r×r pivot
   block) the rest is the residual zero-product locus = shifted orbit. Is that a GLOBAL trivial
   product over the whole component, or does it hold only on the pivot chart (where Δ invertible)?
   If only on the chart, then `(A) ≅ (C)×A^δ` is FALSE globally and the consumer target is
   unreachable as a global iso — only a LOCALIZED version `Away(R_F⧸I at something) ≃ …` holds.

3. **Given 1-2, what is the strongest TRUE, GLOBALLY-VALID, faithfully-stateable iso I can land?**
   Options:
   (i) the localized `(B)≅(A)×A^δ` form `MvPolynomial SchurVar (R_F⧸I) ≃ orbitRing(realizerD m)`
       (if it holds globally — does it? both are dim `dim F+δ`, the Schur ext is a genuine poly ext,
       the orbit is genuine);
   (ii) a LOCALIZED iso (invert dsig/gF) — honest but weaker (`Away` on both sides);
   (iii) the consumer's `(A)≅(C)×A^δ` (only if globally true).
   Which is provable from the BUILT pieces (chart e_β, the poly correspondence, my sigma iso) with
   the LEAST new geometry, and is it global or only-localized? Name the cleanest TRUE target.

4. **Does landing (i) [`MvPolynomial SchurVar (R_F⧸I) ≃ orbitRing(realizerD m)`] have value**, even
   though it does NOT match the consumer's `…_of_component_orbitPolyEquiv` shape? It IS a genuine
   "fibre component × A^δ ≅ shifted-up orbit closure" labeled identification — arguably the honest
   geometric content (the fibre component is the orbit closure with δ of its coordinates freed). Or
   is it a near-vacuous restatement? Adjudicate whether (i) is the right deliverable to aim for.

Be skeptical. The KEY: tell me the cleanest GLOBALLY-TRUE component iso reachable from the built
pieces, whether it's global or only-after-localization, and which of (i)/(ii)/(iii) to target.
