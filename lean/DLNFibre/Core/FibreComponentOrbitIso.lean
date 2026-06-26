/-
Copyright (c) 2026. Released under Apache 2.0; see LICENSE.
-/
import DLNFibre.Core.FibreComponentOrbit
import DLNFibre.Core.FibreBundleReduced

/-!
# `DLNFibre.Core.FibreComponentOrbitIso` — the variety-level fibre-component ↔ orbit iso (thread 24)

**Standalone geometric deliverable** (operator-approved enrichment; **NOT** on the critical path —
smoothness, the θ-count, and the bundle do not consume it). The explicit dense-chart identification
of a fibre top component with a full-`d` orbit-closure component.

## Honest scope — the consumer shape is UNREACHABLE; only a LOCALIZED iso holds

The thread-20 consumer `isSmoothAt_sweepFibre_of_component_orbitPolyEquiv` wanted
`sweepFibreRing ⧸ I ≃ₐ[k] MvPolynomial η (orbitRing M_shifted)` (poly wrapper on the orbit side,
*shifted* orbit over `d − r`). That shape is **globally false / unreachable** from the chart
transport (Codex-adjudicated): the chart `e_β = chartLocalizedAlgEquiv` is intrinsically *localized*
(`Away dsig ≃ Away gF`), `gF = detSchurS` is a pivot-chart determinant (not a unit mod `I`), so the
chart only sees the dense principal open `D(g_I)`. The reachable, globally-true identification is
**localized**, with the polynomial wrapper on the *fibre* side and the *full-`d`* orbit:

> `(SchurLoc ⊗_k (sweepFibreRing ⧸ I))  ≃ₐ[k]  (the localized full-`d` sigma orbit component)`

i.e. `(C-part) ⊗ (fibre component) ≅ (full-`d` orbit component), after localization` — the (B) ≅
(A) × A^δ shape (`SchurLoc` is the regular δ-dimensional C-part). The un-localized version and the
shifted-orbit version both overclaim (cancellation `R[x] ≅ S[y] ⇏ R ≅ S[…]` is invalid).

This module builds that honest localized identification. It does **not** advance smoothness (already
fully unconditional, `Core.FibreComponentOrbitTransport`) or the θ-count.

**Dependency rule:** `Core` only — never import `DLNFibre.DLN`.
-/

namespace DLNFibre.Core

open MvPolynomial Matrix Algebra
open scoped TensorProduct

universe u

variable {k : Type u} [Field k] {N : ℕ}

/-! ## Rung 1 — the product-keystone component transport (chart ↔ C-part ⊗ fibre-component)

The product keystone `reducedFibre_chartDsig_tensorEquiv_reducedVariety :
Away (chartDsig …) ≃ₐ[k] SchurLoc ⊗_k sweepFibreRing`, with a fibre component ideal `I` pulled to
chart side via `comap`, identifies `SchurLoc ⊗_k (sweepFibreRing ⧸ I)` with the corresponding
quotient of the localized chart ring `Away (chartDsig …)`. This is the labeled chart-localization
component transport's core — the genuine new rung; it uses `tensorQuotientEquiv` (base change of a
quotient) glued to the keystone by `Ideal.quotientEquivAlg`. -/

/-- The chart-side component ideal: the fibre component `I` pulled to `Away (chartDsig …)` along the
product keystone, as the `comap` of the right-tensor extension `I.map includeRight` in
`SchurLoc ⊗_k sweepFibreRing`. -/
noncomputable def chartComponentIdeal [Infinite k] (d : Fin (N + 2) → ℕ) (r : ℕ)
    (hp : r ≤ d (Fin.last (N + 1))) (hq : r ≤ d 0)
    (I : Ideal (sweepFibreRing k d r hp hq)) :
    Ideal (Localization.Away (chartDsig k d r hp hq)) :=
  (Ideal.map (Algebra.TensorProduct.includeRight (R := k)
      (A := SchurLoc (k := k) (d 0) (d (Fin.last (N + 1))) r)
      (B := sweepFibreRing k d r hp hq)) I).comap
    (reducedFibre_chartDsig_tensorEquiv_reducedVariety (k := k) d r hp hq :
      Localization.Away (chartDsig k d r hp hq) →+* _)

/-- **Rung 1 — the chart-localization component transport.** For a fibre component ideal `I` of
`sweepFibreRing`, the C-part-tensored component `SchurLoc ⊗_k (sweepFibreRing ⧸ I)` is `k`-algebra
isomorphic to the quotient of the localized chart ring `Away (chartDsig …)` by the pulled-back
component ideal `chartComponentIdeal`:

> `SchurLoc ⊗_k (sweepFibreRing ⧸ I)  ≃ₐ[k]  Away (chartDsig …) ⧸ chartComponentIdeal I`.

`tensorQuotientEquiv` identifies `SchurLoc ⊗ (R_F⧸I)` with `(SchurLoc ⊗ R_F)⧸(I.map includeRight)`;
`Ideal.quotientEquivAlg` descends the keystone `Φ⁻¹ : SchurLoc ⊗ R_F ≃ₐ[k] Away dsig` to the
quotients (`chartComponentIdeal = comap Φ (I.map includeRight) = (I.map includeRight).map Φ⁻¹`). -/
noncomputable def schurComponent_chartQuotientEquiv [Infinite k]
    (d : Fin (N + 2) → ℕ) (r : ℕ) (hp : r ≤ d (Fin.last (N + 1))) (hq : r ≤ d 0)
    (I : Ideal (sweepFibreRing k d r hp hq)) :
    SchurLoc (k := k) (d 0) (d (Fin.last (N + 1))) r ⊗[k] (sweepFibreRing k d r hp hq ⧸ I)
      ≃ₐ[k] Localization.Away (chartDsig k d r hp hq) ⧸ chartComponentIdeal d r hp hq I := by
  set Φ := reducedFibre_chartDsig_tensorEquiv_reducedVariety (k := k) d r hp hq with hΦ
  set Jmap := Ideal.map (Algebra.TensorProduct.includeRight (R := k)
    (A := SchurLoc (k := k) (d 0) (d (Fin.last (N + 1))) r)
    (B := sweepFibreRing k d r hp hq)) I with hJmap
  -- `chartComponentIdeal = comap Φ Jmap = map Φ.symm Jmap` (comap of equiv = map of inverse).
  have hcm : chartComponentIdeal d r hp hq I = Jmap.map (Φ.symm : _ →+* _) := by
    rw [chartComponentIdeal, ← hJmap, ← hΦ]
    have h := Ideal.comap_symm (I := Jmap) (f := Φ.toRingEquiv.symm)
    -- `h : Jmap.comap (Φ⁻¹).symm = Jmap.map Φ⁻¹`; `.symm.symm = id` reduces the comap side to `Φ`.
    rw [RingEquiv.symm_symm] at h
    exact h
  -- `SchurLoc ⊗ (R_F⧸I) ≃ (SchurLoc ⊗ R_F)⧸Jmap` (base change of a quotient); descend `Φ.symm`.
  refine (Algebra.TensorProduct.tensorQuotientEquiv
      (R := k) (S := k) (T := sweepFibreRing k d r hp hq)
      (A := SchurLoc (k := k) (d 0) (d (Fin.last (N + 1))) r) I).trans ?_
  exact Ideal.quotientEquivAlg Jmap (chartComponentIdeal d r hp hq I) Φ.symm hcm

/-! ## The remaining rung (residual) — `chartComponentIdeal`'s quotient is the localized orbit ring

Rung 1 (`schurComponent_chartQuotientEquiv`) lands
`SchurLoc ⊗_k (R_F⧸I) ≃ₐ[k] (Away chartDsig)⧸chartComponentIdeal`. To reach the orbit ring, the
remaining rung descends the right-hand quotient to the **sigma side** and identifies it with a
localized full-`d` orbit ring:

> **`exists_chartComponent_localizedOrbitEquiv` (NOT built — the residual)**: for a fibre
> top-component prime `I`, a corner-`r` Kostant `m` and a `k`-algebra iso
> `(Away chartDsig)⧸chartComponentIdeal I ≃ₐ[k] Away (image of dsig in orbitRing (realizerD m))`.

Pieces available but needing assembly (~mid-hundreds LoC): (i) the contraction of
`chartComponentIdeal` to `sweepSigmaRing` is a sigma top-dim minimal prime `q_Σ`, `dsig ∉ q_Σ` (the
avoidance via the W1/chartE no-drop lemmas — stated for the `Away gF`/`Away dsig` chart `e_β`, not
the product keystone, so a bridge `chartComponentIdeal = comap (algebraMap _ (Away dsig)) q_Σ` is
needed); (ii) the localization-quotient ring iso `(Away f)⧸(map p) ≃+* Away (mk p f)` (built inside
`TopDimMinPrimesLocalization.ringKrullDim_quotient_map_localizationAway_eq` — to extract as an
`AlgEquiv`); (iii) the W0 descent `sweepSigmaRing⧸q_Σ ↝ O(Σ̄^r)⧸q ≃ orbitRing (realizerD m)`
(`exists_sigma_topComponent_orbitRingEquiv`). Composing rung 1 with this residual gives the honest
**localized** `e`: `SchurLoc ⊗_k (R_F⧸I) ≃ₐ[k] Away Δ (orbitRing (realizerD m))` — the dense-chart
`(C-part) ⊗ (fibre component) ≅ (localized full-`d` orbit)` identification. The *un-localized* and
*shifted-orbit* shapes are NOT reachable (cancellation invalid; see the module docstring). -/

end DLNFibre.Core
