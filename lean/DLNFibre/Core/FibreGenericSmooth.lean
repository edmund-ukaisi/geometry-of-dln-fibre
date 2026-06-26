/-
Copyright (c) 2026. Released under Apache 2.0; see LICENSE.
-/
import DLNFibre.Core.FibreBundleReduced
import Mathlib.RingTheory.Smooth.Locus

/-!
# `DLNFibre.Core.FibreGenericSmooth` — generic smoothness of the reduced fibre chart (thread 16)

The reduced fibre variety is **smooth at the generic point of each top-dimensional component**:
`Algebra.IsSmoothAt k p` at the prime `p` of that generic point. The fibre is REDUCIBLE for
`θ ≥ 2` (several components meeting), so the global statement `Smooth k (fibre ring)` is FALSE; only
the per-component-generic-point `IsSmoothAt` is true. This module assembles the **reduced-variety
route** to that pointwise smoothness, from the banked per-chart product trivialization
(`Away chartDsig ≃ₐ[k] SchurLoc ⊗_k sweepFibreRing`, `FibreBundleReduced`) and the always-smooth
matrix factor.

## What is unconditional here (reusable bricks)

* `Algebra.Smooth.tensorProduct` — over a field `k`, `Smooth k A` and `Smooth k B` ⟹
  `Smooth k (A ⊗_k B)` (base change + composition + `comm`).
* `smooth_away_mvPolynomial` — `Smooth k (Localization.Away g)` for `g` in a polynomial ring over
  `k` in finitely many variables (so the matrix factor `SchurLoc` is smooth: `smooth_schurLoc`).
* `isSmoothAt_of_smooth_localizationAway` — the basic-open bridge: `Smooth k (Localization.Away g)`
  with `g ∉ q` ⟹ `Algebra.IsSmoothAt k q` (`Algebra.basicOpen_subset_smoothLocus_iff_smooth`).
* `Algebra.FinitePresentation k (sweepFibreRing …)` — the fibre ring is finitely presented (a
  quotient of a polynomial ring in finitely many variables over `k`).

## The conditional headline (the one honest hypothesis — thread-14 verified, NOT discharged here)

`smooth_schurLoc_tensor_away_of_isSmoothAt_sweepFibre`: if the **reduced fibre ring**
`sweepFibreRing` is `IsSmoothAt k q` at a prime `q` (the generic point of a top component — the
thread-14 fact (C): generic Jacobian rank `= codim = C+δ` on every top component), then there is a
fibre element `g ∉ q` with `Smooth k (SchurLoc ⊗_k Localization.Away g)`: the local matrix-times-
fibre chart-piece is genuinely smooth. This is the substance of the LEAD route's "smoothness is
factor-wise on the tensor product"; the only open input is the `IsSmoothAt` of the fibre factor.

**Cost to go unconditional (the gap, stated honestly).** Two further steps, deferred:
(i) discharge the hypothesis `IsSmoothAt k q` of `sweepFibreRing` at top-component generic points —
this is the thread-14 fact (C), needing either the orbit-closure transport (`OrbitSmooth`'s
`isSmoothAt_normalFormIdeal` + a local "the fibre equals one shifted orbit closure at this
component's generic point" comparison, a quotient-by-intersection localization lemma not in this
harness) or the
determinantal `rank = C+δ` minor-unit (`FibreSmoothPlumbing`, blocked on thin Mathlib determinantal
support); and (ii) transport `Smooth k (SchurLoc ⊗ Away g)` to `Algebra.IsSmoothAt k p` of
`Away chartDsig` across the banked iso — this needs the localization-of-base-change identification
`SchurLoc ⊗ Away g ≃ Localization.Away (1 ⊗ g)` in `SchurLoc ⊗ sweepFibreRing`
(`IsLocalization.tensorProduct_tensorProduct`, the `FibreBundleReduced` bookkeeping pattern) then
the basic-open bridge through `e`. Both (i) and (ii) are scoped, not vacuous.

**Dependency rule:** `Core` only — never import `DLNFibre.DLN`.
-/

namespace DLNFibre.Core

open MvPolynomial Matrix Algebra
open scoped TensorProduct

universe u

variable {k : Type u} [Field k]

/-! ## Unconditional reusable bricks -/

/-- **Tensor of smooth `k`-algebras is smooth** (`k` any commutative base). `B ⊗_k A` is smooth over
`B` (base change) and `B` is smooth over `k`, so `B ⊗_k A` is smooth over `k` (composition); flip to
`A ⊗_k B` along `Algebra.TensorProduct.comm`. -/
theorem Algebra.Smooth.tensorProduct {R A B : Type*} [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B] [Smooth R A] [Smooth R B] :
    Smooth R (A ⊗[R] B) :=
  haveI : Smooth R (B ⊗[R] A) := Smooth.comp R B (B ⊗[R] A)
  Smooth.of_equiv (Algebra.TensorProduct.comm R B A)

/-- **`Localization.Away g` of a finite-variable polynomial ring is smooth over the base field.**
`Localization.Away g` is smooth over `MvPolynomial σ k` (localization at an element) and
`MvPolynomial σ k` is smooth over `k` (`σ` finite ⟹ finitely presented), so the composite is
smooth. -/
theorem smooth_away_mvPolynomial {σ : Type*} [Finite σ] (g : MvPolynomial σ k) :
    Smooth k (Localization.Away g) := by
  haveI : Smooth (MvPolynomial σ k) (Localization.Away g) := Smooth.of_isLocalization_Away g
  haveI : Smooth k (MvPolynomial σ k) := ⟨inferInstance, inferInstance⟩
  exact Smooth.comp k (MvPolynomial σ k) (Localization.Away g)

/-- **The matrix factor `SchurLoc` is smooth over `k`.** It is `Localization.Away (detSchurS …)`, an
away-localization of a polynomial ring in the finitely many Schur coordinates. -/
theorem smooth_schurLoc (q p r : ℕ) : Smooth k (SchurLoc (k := k) q p r) :=
  smooth_away_mvPolynomial (detSchurS (k := k) q p r)

/-- **The basic-open bridge.** If `Localization.Away g` is smooth over `k` (with `B` finitely
presented) and `g ∉ q`, then `B` is smooth at `q`: `Smooth k (Away g)` says the basic open `{g ≠ 0}`
lies in the smooth locus (`Algebra.basicOpen_subset_smoothLocus_iff_smooth`), and `q` is in it. -/
theorem isSmoothAt_of_smooth_localizationAway {B : Type*} [CommRing B] [Algebra k B]
    [Algebra.FinitePresentation k B] {g : B} {q : Ideal B} [q.IsPrime] (hgq : g ∉ q)
    (hsm : Smooth k (Localization.Away g)) : Algebra.IsSmoothAt k q :=
  (Algebra.basicOpen_subset_smoothLocus_iff_smooth (R := k) (A := B) (f := g)).mpr hsm
    (show (⟨q, ‹_›⟩ : PrimeSpectrum B) ∈ PrimeSpectrum.basicOpen g from hgq)

/-! ## The reduced fibre ring is finitely presented -/

variable {N : ℕ}

/-- **`sweepFibreRing` is finitely presented over `k`.** It is a quotient of the polynomial ring in
the finitely many representation coordinates `RepCoord d` over `k`, and that ring is Noetherian, so
the defining ideal is finitely generated (`FinitePresentation.quotient`). -/
instance finitePresentation_sweepFibreRing (d : Fin (N + 2) → ℕ) (r : ℕ)
    (hp : r ≤ d (Fin.last (N + 1))) (hq : r ≤ d 0) :
    Algebra.FinitePresentation k (sweepFibreRing k d r hp hq) :=
  Algebra.FinitePresentation.quotient
    (IsNoetherian.noetherian (vanishingIdeal k (sweepFibre k d r hp hq)))

/-! ## The conditional headline (FLOOR): the local matrix×fibre chart-piece is smooth -/

/-- **The reduced-variety smoothness rung (FLOOR, conditional on the thread-14 fact).** If the
reduced fibre ring `sweepFibreRing` is smooth at a prime `q` — the generic point of a
top-dimensional component, where thread-14 verifies generic Jacobian rank `= codim = C+δ` — then
there is a fibre element `g ∉ q` such that the **local matrix-times-fibre chart-piece**
`SchurLoc ⊗_k Localization.Away g` is genuinely `Smooth k`: the matrix factor `SchurLoc` is
unconditionally smooth (`smooth_schurLoc`), the fibre factor `Localization.Away g` is smooth on the
basic open `{g ≠ 0}` around `q` (`IsSmoothAt.exists_notMem_smooth`), and the tensor of smooth
factors is smooth (`Algebra.Smooth.tensorProduct`).

This is the substance of the LEAD route's "smoothness is factor-wise on the tensor product": the
only open input is `IsSmoothAt` of the fibre factor (NOT discharged here — see the module docstring
for the precise unconditional cost: orbit-closure transport or determinantal minor-unit). The
remaining transport `SchurLoc ⊗ Away g ⟹ IsSmoothAt (Away chartDsig)` across the banked product iso
`reducedFibre_chartDsig_tensorEquiv_reducedVariety` needs the localization-of-base-change
bookkeeping, also documented as deferred. -/
theorem smooth_schurLoc_tensor_away_of_isSmoothAt_sweepFibre
    (d : Fin (N + 2) → ℕ) (r : ℕ) (hp : r ≤ d (Fin.last (N + 1))) (hq : r ≤ d 0)
    (q : Ideal (sweepFibreRing k d r hp hq)) [q.IsPrime]
    (hq_smooth : Algebra.IsSmoothAt k q) :
    ∃ g ∉ q, Smooth k
      (SchurLoc (k := k) (d 0) (d (Fin.last (N + 1))) r ⊗[k] Localization.Away g) := by
  obtain ⟨g, hgq, hg_smooth⟩ := Algebra.IsSmoothAt.exists_notMem_smooth k q
  refine ⟨g, hgq, ?_⟩
  haveI : Smooth k (SchurLoc (k := k) (d 0) (d (Fin.last (N + 1))) r) := smooth_schurLoc _ _ _
  haveI : Smooth k (Localization.Away g) := hg_smooth
  exact Algebra.Smooth.tensorProduct

end DLNFibre.Core
