/-
Copyright (c) 2026. Released under Apache 2.0; see LICENSE.
-/
import DLNFibre.Core.FibreOverBaseTriv
import DLNFibre.Core.MultComorphism

/-!
# `DLNFibre.Core.FibreProjectionCompat` — the in-chart base map IS `mult`'s comorphism (projection compatibility)

The S4b/S5 over-base trivialization is over the **named** structure map `schurToDsigAt :
SchurLoc →ₐ[k] Away (chartDsigAt s t)`. The S5 capstone names one honest residual: that this base map
is the **pullback of `mult`'s projection** — i.e. that the in-chart Schur/base direction agrees with the
geometric multiplication map. This module discharges that residual at the **top-left chart** as a genuine
**factorization through `mult`'s comorphism `multComap`** (`Core.MultComorphism`), then carries it to an
arbitrary pivot through the gauge transport.

## Why this is the geometric content (and not a vacuous restatement)

`schurToDsigAt = awayCongr(gauge) ∘ schurToDsig`, and `schurToDsig = liftAlgHom chartPhiSchurAeval`
with `chartPhiSchurAeval = aeval chartPhiVarSub` (`Core.ChartPhiSubstitution`). The var leg
`chartPhiVarSub` is DEFINED to read off the entries of the **generic product** `multPoly d` (the
coordinate-ring image of `mult`): the Δ-block generator `Sum.inl (i, j)` maps to
`mk_Σ (multPoly (castLE i) (castLE j))`, the `B12`/`B21` generators to the corresponding bordering
entries. Those product entries are exactly `multComap`'s images of the target matrix coordinate
variables (`multComap_X`). So the in-chart base map factors through `mult`'s comorphism — the structure
map IS the geometric projection, descended to the chart, not an artificial chart base map.

## Main results

* `schurVarToEntry` / `targetSchurEmbed` — the target Schur block coordinate `Sum.inl/inr …` ↦ the
  target matrix entry variable `X (row, col)` of `MvPolynomial (Fin d_last × Fin d_0) k`, packaged as a
  `k`-algebra hom `targetSchurEmbed` from the Schur coordinate ring to the target matrix coordinate ring.
* `phiSourceHom` — the descend-then-localize `k`-algebra hom
  `MvPolynomial (RepCoord d) k →ₐ[k] Away (chartDsig)` (= `aeval sigmaCoordT`, `X x ↦ mk_Σ (X x)` pushed
  into the localization); `chartPhiVarSub s = phiSourceHom (multPoly …)` (`phiSourceHom_multPoly`).
* `chartPhiSchurAeval_eq_comp_multComap` — **the factorization**: the Φ Schur comorphism equals
  `phiSourceHom ∘ multComap ∘ targetSchurEmbed`. So the Schur-coordinate aeval is `mult`'s comorphism,
  restricted to the Schur block and descended to the chart localization.
* `schurToDsig_comp_targetSchurLocEmbed` — the localized statement on `schurToDsig`: the top-left base
  map, precomposed with the localized Schur embedding, equals `mult`'s comorphism localized. The honest
  "the base map is the pullback of `mult`'s projection" at the top-left chart.
* `schurToDsigAt_factors_multComap` — the per-pivot carry: `schurToDsigAt` factors through `mult`'s
  comorphism via the gauge transport (the geometric structure map at every pivot).

## Scope (honest)

This proves projection compatibility as a **ring-level factorization through `mult`'s comorphism**
`multComap`, at every pivot. It is NOT a scheme-morphism / continuity statement, and it does not by
itself assemble a global `Flat π` / `FiberBundle` (that additionally needs the target-side overlap
cocycle R1). What it removes is the S5/S4b open item "(i) projection compatibility": the named base map
`schurToDsigAt` is no longer an artificial chart base map — it is `mult`'s comorphism on the Schur block,
descended to the chart.

**Dependency rule:** `Core` only — never import `DLNFibre.DLN`.
-/

namespace DLNFibre.Core

open MvPolynomial Matrix
open scoped TensorProduct

variable {k : Type} [Field k] {N : ℕ}

/-! ## The target Schur-block coordinate ↦ target matrix entry -/

/-- **The target matrix entry of a Schur block coordinate.** A Schur block generator names a position
in the target/base product matrix `Fin d_last × Fin d_0`: the Δ-block `Sum.inl (i, j)` is the pivot
entry `(castLE i, castLE j)`, the `B12` generator `Sum.inr (Sum.inl (i, b))` the bordering entry
`(castLE i, natAdd r b)`, the `B21` generator `Sum.inr (Sum.inr (a, j))` the entry `(natAdd r a,
castLE j)`. This mirrors EXACTLY `chartPhiVarSub`'s reading of the product blocks. -/
def schurVarToEntry (d : Fin (N + 2) → ℕ) (r : ℕ)
    (hp : r ≤ d (Fin.last (N + 1))) (hq : r ≤ d 0) :
    SchurVar (d 0) (d (Fin.last (N + 1))) r → Fin (d (Fin.last (N + 1))) × Fin (d 0) :=
  fun s ↦ match s with
    | Sum.inl (i, j) => (Fin.castLE hp i, Fin.castLE hq j)
    | Sum.inr (Sum.inl (i, b)) =>
        (Fin.castLE hp i, Fin.cast (show r + (d 0 - r) = d 0 by omega) (Fin.natAdd r b))
    | Sum.inr (Sum.inr (a, j)) =>
        (Fin.cast (show r + (d (Fin.last (N + 1)) - r) = d (Fin.last (N + 1)) by omega)
          (Fin.natAdd r a), Fin.castLE hq j)

variable (k) in
/-- **The target Schur-block embedding** `MvPolynomial SchurVar k →ₐ[k] MvPolynomial (Fin d_last ×
Fin d_0) k`: a Schur block coordinate variable `X s` ↦ the target matrix entry variable
`X (schurVarToEntry s)`. The Schur block coordinates as a sub-coordinate-system of the full target
matrix. -/
noncomputable def targetSchurEmbed (d : Fin (N + 2) → ℕ) (r : ℕ)
    (hp : r ≤ d (Fin.last (N + 1))) (hq : r ≤ d 0) :
    MvPolynomial (SchurVar (d 0) (d (Fin.last (N + 1))) r) k →ₐ[k]
      MvPolynomial (Fin (d (Fin.last (N + 1))) × Fin (d 0)) k :=
  aeval (fun s ↦ X (schurVarToEntry d r hp hq s))

@[simp] theorem targetSchurEmbed_X (d : Fin (N + 2) → ℕ) (r : ℕ)
    (hp : r ≤ d (Fin.last (N + 1))) (hq : r ≤ d 0)
    (s : SchurVar (d 0) (d (Fin.last (N + 1))) r) :
    targetSchurEmbed k d r hp hq (X s) = X (schurVarToEntry d r hp hq s) := by
  simp [targetSchurEmbed]

/-! ## The descend-then-localize source hom -/

variable (k) in
/-- **The descend-then-localize source hom** `MvPolynomial (RepCoord d) k →ₐ[k] Away (chartDsig)`:
`aeval sigmaCoordT`, sending `X x ↦ mk_Σ (X x)` pushed into the source localization. This is the
`k`-algebra hom `algebraMap ∘ Ideal.Quotient.mk` packaged via `aeval` (so it agrees with
`chartPhiVarSub`'s `algebraMap (mk_Σ …)` on the product entries). -/
noncomputable def phiSourceHom (d : Fin (N + 2) → ℕ) (r : ℕ)
    (hp : r ≤ d (Fin.last (N + 1))) (hq : r ≤ d 0) :
    MvPolynomial (RepCoord d) k →ₐ[k] Localization.Away (chartDsig k d r hp hq) :=
  aeval (sigmaCoordT k d r hp hq)

/-- `phiSourceHom` agrees with the explicit `algebraMap ∘ mk_Σ` composite on every polynomial: both are
`k`-algebra homs that send `X x ↦ algebraMap (mk_Σ (X x))`. -/
theorem phiSourceHom_eq_algebraMap_comp (d : Fin (N + 2) → ℕ) (r : ℕ)
    (hp : r ≤ d (Fin.last (N + 1))) (hq : r ≤ d 0)
    (p : MvPolynomial (RepCoord d) k) :
    phiSourceHom k d r hp hq p
      = algebraMap (sweepSigmaRing k d r) (Localization.Away (chartDsig k d r hp hq))
          (Ideal.Quotient.mk (vanishingIdeal k (sweepSigma k d r)) p) := by
  -- both sides are `k`-algebra homs `MvPolynomial (RepCoord d) k → Away chartDsig` agreeing on `X`.
  have h : phiSourceHom k d r hp hq
      = ((IsScalarTower.toAlgHom k (sweepSigmaRing k d r)
            (Localization.Away (chartDsig k d r hp hq))).comp
          (Ideal.Quotient.mkₐ k (vanishingIdeal k (sweepSigma k d r)))) := by
    apply MvPolynomial.algHom_ext
    intro x
    rw [phiSourceHom, aeval_X, AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk,
      IsScalarTower.coe_toAlgHom']
    rfl
  rw [h, AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk, IsScalarTower.coe_toAlgHom']

/-- **The var leg reads `multPoly` through `phiSourceHom`.** `chartPhiVarSub s = phiSourceHom (multPoly
d (row s) (col s))`, where `(row s, col s) = schurVarToEntry s`. Both push the same product-entry
polynomial into `Away chartDsig` (`chartPhiVarSub` via `algebraMap ∘ mk_Σ`, `phiSourceHom` via the same
by `phiSourceHom_eq_algebraMap_comp`). -/
theorem phiSourceHom_multPoly (d : Fin (N + 2) → ℕ) (r : ℕ)
    (hp : r ≤ d (Fin.last (N + 1))) (hq : r ≤ d 0)
    (s : SchurVar (d 0) (d (Fin.last (N + 1))) r) :
    phiSourceHom k d r hp hq (multPoly d (schurVarToEntry d r hp hq s).1
        (schurVarToEntry d r hp hq s).2)
      = chartPhiVarSub k d r hp hq s := by
  rw [phiSourceHom_eq_algebraMap_comp]
  -- match the `match`-defined `chartPhiVarSub` block-by-block.
  rcases s with ⟨i, j⟩ | (⟨i, b⟩ | ⟨a, j⟩) <;> rfl

/-! ## The factorization of the Φ Schur comorphism through `mult`'s comorphism -/

/-- **The Φ Schur comorphism factors through `mult`'s comorphism (the projection-compatibility crux).**
`chartPhiSchurAeval = phiSourceHom ∘ multComap ∘ targetSchurEmbed`. Both sides are `k`-algebra homs
`MvPolynomial SchurVar k → Away chartDsig`; on a generator `X s` the RHS is
`phiSourceHom (multComap (X (schurVarToEntry s))) = phiSourceHom (multPoly … …) = chartPhiVarSub s`
(`multComap_X` + `phiSourceHom_multPoly`), the LHS is `aeval chartPhiVarSub (X s) = chartPhiVarSub s`.
So the Schur-coordinate aeval is genuinely `mult`'s comorphism on the Schur block, descended to the
chart localization. -/
theorem chartPhiSchurAeval_eq_comp_multComap (d : Fin (N + 2) → ℕ) (r : ℕ)
    (hp : r ≤ d (Fin.last (N + 1))) (hq : r ≤ d 0) :
    chartPhiSchurAeval k d r hp hq
      = (phiSourceHom k d r hp hq).comp
          ((multComap d).comp (targetSchurEmbed k d r hp hq)) := by
  apply MvPolynomial.algHom_ext
  intro s
  rw [chartPhiSchurAeval, aeval_X, AlgHom.comp_apply, AlgHom.comp_apply, targetSchurEmbed_X,
    multComap_X, phiSourceHom_multPoly]

/-! ## The localized statement on the top-left base map `schurToDsig` -/

variable (k) in
/-- **The canonical Schur-coordinate → `SchurLoc` localization hom.** The `k`-algebra map
`MvPolynomial SchurVar k →ₐ[k] SchurLoc` (`= algebraMap`, `SchurLoc = Localization.Away detSchurS`);
naming it lets the projection-compatibility statement read as an AlgHom equality. -/
noncomputable def localizeSchur (d : Fin (N + 2) → ℕ) (r : ℕ) :
    MvPolynomial (SchurVar (d 0) (d (Fin.last (N + 1))) r) k →ₐ[k]
      SchurLoc (k := k) (d 0) (d (Fin.last (N + 1))) r :=
  IsScalarTower.toAlgHom k (MvPolynomial (SchurVar (d 0) (d (Fin.last (N + 1))) r) k)
    (SchurLoc (k := k) (d 0) (d (Fin.last (N + 1))) r)

/-- **The top-left base map IS `mult`'s comorphism (projection compatibility, top-left chart).**
Precomposed with the canonical Schur localization hom `localizeSchur`, the top-left structure map
`schurToDsig : SchurLoc →ₐ[k] Away (chartDsig)` equals `mult`'s comorphism `multComap` (restricted to
the Schur block via `targetSchurEmbed`) descended-and-localized to the chart (via `phiSourceHom`):

> `schurToDsig ∘ localizeSchur = phiSourceHom ∘ multComap ∘ targetSchurEmbed`.

So the in-chart base direction is the geometric multiplication map on the Schur block, descended to the
chart localization — not an artificial chart base map. Proof: `schurToDsig (algebraMap f) =
chartPhiSchurAeval f` (`schurToDsig_algebraMap`) then the factorization
`chartPhiSchurAeval_eq_comp_multComap`. -/
theorem schurToDsig_comp_localizeSchur (d : Fin (N + 2) → ℕ) (r : ℕ)
    (hp : r ≤ d (Fin.last (N + 1))) (hq : r ≤ d 0) :
    (schurToDsig k d r hp hq).comp (localizeSchur k d r)
      = (phiSourceHom k d r hp hq).comp
          ((multComap d).comp (targetSchurEmbed k d r hp hq)) := by
  apply MvPolynomial.algHom_ext
  intro s
  rw [AlgHom.comp_apply, localizeSchur, IsScalarTower.toAlgHom_apply, schurToDsig_algebraMap,
    chartPhiSchurAeval_eq_comp_multComap]

/-! ## The per-pivot carry: `schurToDsigAt` factors through `mult`'s comorphism -/

variable [Infinite k]

/-- **The per-pivot base map factors through `mult`'s comorphism (projection compatibility, every
pivot).** For a pivot `(s, t)` (with `σ, τ` carrying the first `r` rows/columns to it), the structure
map `schurToDsigAt`, precomposed with the canonical Schur localization hom `localizeSchur`, equals the
gauge transport `awayCongr (gaugeEquivSigma (pivotGauge σ τ))` applied to `mult`'s comorphism
(restricted to the Schur block, descended-and-localized at the top-left chart):

> `schurToDsigAt ∘ localizeSchur = awayCongr(gauge) ∘ phiSourceHom ∘ multComap ∘ targetSchurEmbed`.

Carries `schurToDsig_comp_localizeSchur` along the gauge `awayCongr` (`schurToDsigAt = awayCongr(gauge)
∘ schurToDsig`). So at EVERY pivot the named structure map is `mult`'s comorphism, transported by the
pivot gauge — the geometric projection in chart coordinates, not an artificial base map. -/
theorem schurToDsigAt_comp_localizeSchur (d : Fin (N + 2) → ℕ) (r : ℕ)
    (hp : r ≤ d (Fin.last (N + 1))) (hq : r ≤ d 0)
    (s : Fin r → Fin (d (Fin.last (N + 1)))) (t : Fin r → Fin (d 0))
    (σ : Equiv.Perm (Fin (d (Fin.last (N + 1))))) (τ : Equiv.Perm (Fin (d 0)))
    (hσ : ∀ i : Fin r, σ (Fin.castLE hp i) = s i) (hτ : ∀ j : Fin r, τ (Fin.castLE hq j) = t j) :
    (schurToDsigAt d r hp hq s t σ τ hσ hτ).comp (localizeSchur k d r)
      = ((awayCongr (gaugeEquivSigma d r (pivotGauge d σ τ)) (chartDsig k d r hp hq)
            (chartDsigAt d r s t)
            (gaugeEquivSigma_chartDsig d r hp hq s t σ τ hσ hτ)).toAlgHom.comp
          (phiSourceHom k d r hp hq)).comp
        ((multComap d).comp (targetSchurEmbed k d r hp hq)) := by
  -- `schurToDsigAt = gauge.comp schurToDsig`; re-associate (`comp_assoc` is `rfl`) and rewrite the
  -- inner top-left compatibility `schurToDsig.comp localizeSchur`.
  rw [show (schurToDsigAt d r hp hq s t σ τ hσ hτ).comp (localizeSchur k d r)
        = (awayCongr (gaugeEquivSigma d r (pivotGauge d σ τ)) (chartDsig k d r hp hq)
            (chartDsigAt d r s t)
            (gaugeEquivSigma_chartDsig d r hp hq s t σ τ hσ hτ)).toAlgHom.comp
          ((schurToDsig k d r hp hq).comp (localizeSchur k d r)) from rfl,
    schurToDsig_comp_localizeSchur]
  rfl

/-! ## The projection-compatible over-base chart datum (the S4b over-base triv, now over `mult`)

Packaging C2: at a pivot, the over-base trivialization `chartDsigAt_schurLocTensorEquiv` is over the
NAMED structure map `schurToDsigAt`, and (projection compatibility above) `schurToDsigAt` is `mult`'s
comorphism transported by the pivot gauge. So the chartwise over-base product + flatness is genuinely
over the geometric projection (chartwise), not over an artificial base map. This bundles the two banked
S4b facts with the projection-compatibility equality, so a consumer reads both off one object. -/

/-- **The projection-compatible over-base chart datum at a pivot.** For a pivot `(s, t)` (with `σ, τ`
carrying the first `r` rows/columns to it), bundles the three facts that, together, say the chart total
ring is the standard fibre product OVER THE GEOMETRIC PROJECTION (chartwise):

* `projCompat` — projection compatibility: `schurToDsigAt ∘ localizeSchur = gauge ∘ phiSourceHom ∘
  multComap ∘ targetSchurEmbed`, i.e. the in-chart base map IS `mult`'s comorphism (Schur block,
  gauge-transported);
* `triv` — the over-base trivialization (S4b `chartDsigAt_schurLocTensorEquiv`): over the
  `schurToDsigAt`-induced `SchurLoc`-algebra, `Away (chartDsigAt s t) ≃ₐ[SchurLoc] SchurLoc ⊗_k
  sweepFibreRing`;
* `flat` — flatness over the base (S4b `chartDsigAt_flat_over_schurLoc`).

The S4b `triv`/`flat` were over the NAMED `schurToDsigAt`; `projCompat` certifies that this named map is
the geometric projection — closing the S5/S4b open item "(i) projection compatibility". Still chartwise
(R1 global gluing remains). -/
structure ProjCompatOverBaseChart (d : Fin (N + 2) → ℕ) (r : ℕ)
    (hp : r ≤ d (Fin.last (N + 1))) (hq : r ≤ d 0)
    (s : Fin r → Fin (d (Fin.last (N + 1)))) (t : Fin r → Fin (d 0))
    (σ : Equiv.Perm (Fin (d (Fin.last (N + 1))))) (τ : Equiv.Perm (Fin (d 0)))
    (hσ : ∀ i : Fin r, σ (Fin.castLE hp i) = s i) (hτ : ∀ j : Fin r, τ (Fin.castLE hq j) = t j) where
  /-- Projection compatibility: the in-chart base map is `mult`'s comorphism, gauge-transported. -/
  projCompat : (schurToDsigAt d r hp hq s t σ τ hσ hτ).comp (localizeSchur k d r)
      = ((awayCongr (gaugeEquivSigma d r (pivotGauge d σ τ)) (chartDsig k d r hp hq)
            (chartDsigAt d r s t)
            (gaugeEquivSigma_chartDsig d r hp hq s t σ τ hσ hτ)).toAlgHom.comp
          (phiSourceHom k d r hp hq)).comp
        ((multComap d).comp (targetSchurEmbed k d r hp hq))
  /-- The over-base trivialization over the `schurToDsigAt`-induced `SchurLoc`-algebra. -/
  triv :
    letI := chartDsigAtSchurLocAlgebra (k := k) d r hp hq s t σ τ hσ hτ
    Localization.Away (chartDsigAt (k := k) d r s t)
      ≃ₐ[SchurLoc (k := k) (d 0) (d (Fin.last (N + 1))) r]
        SchurLoc (k := k) (d 0) (d (Fin.last (N + 1))) r ⊗[k] sweepFibreRing k d r hp hq
  /-- Flatness over the base. -/
  flat :
    letI := chartDsigAtSchurLocAlgebra (k := k) d r hp hq s t σ τ hσ hτ
    Module.Flat (SchurLoc (k := k) (d 0) (d (Fin.last (N + 1))) r)
      (Localization.Away (chartDsigAt (k := k) d r s t))

open scoped TensorProduct in
/-- **The projection-compatible over-base chart datum is genuinely assembled** at every pivot: the
projection-compatibility equality (`schurToDsigAt_comp_localizeSchur`), the over-base trivialization
(`chartDsigAt_schurLocTensorEquiv`), and the flatness (`chartDsigAt_flat_over_schurLoc`). -/
noncomputable def projCompatOverBaseChart (d : Fin (N + 2) → ℕ) (r : ℕ)
    (hp : r ≤ d (Fin.last (N + 1))) (hq : r ≤ d 0)
    (s : Fin r → Fin (d (Fin.last (N + 1)))) (t : Fin r → Fin (d 0))
    (σ : Equiv.Perm (Fin (d (Fin.last (N + 1))))) (τ : Equiv.Perm (Fin (d 0)))
    (hσ : ∀ i : Fin r, σ (Fin.castLE hp i) = s i) (hτ : ∀ j : Fin r, τ (Fin.castLE hq j) = t j) :
    ProjCompatOverBaseChart (k := k) d r hp hq s t σ τ hσ hτ where
  projCompat := schurToDsigAt_comp_localizeSchur d r hp hq s t σ τ hσ hτ
  triv := chartDsigAt_schurLocTensorEquiv d r hp hq s t σ τ hσ hτ
  flat := chartDsigAt_flat_over_schurLoc d r hp hq s t σ τ hσ hτ

/-! ## Non-vacuity witnesses -/

section Witness

/-- **Projection-compatibility witness.** The per-pivot base map equals `mult`'s comorphism transported
by the pivot gauge — the genuine geometric content (it mentions `multComap`, not only `schurToDsigAt`). -/
example {k : Type} [Field k] [Infinite k] {N : ℕ} (d : Fin (N + 2) → ℕ) (r : ℕ)
    (hp : r ≤ d (Fin.last (N + 1))) (hq : r ≤ d 0)
    (s : Fin r → Fin (d (Fin.last (N + 1)))) (t : Fin r → Fin (d 0))
    (σ : Equiv.Perm (Fin (d (Fin.last (N + 1))))) (τ : Equiv.Perm (Fin (d 0)))
    (hσ : ∀ i : Fin r, σ (Fin.castLE hp i) = s i) (hτ : ∀ j : Fin r, τ (Fin.castLE hq j) = t j) :
    (projCompatOverBaseChart (k := k) d r hp hq s t σ τ hσ hτ).projCompat
      = schurToDsigAt_comp_localizeSchur d r hp hq s t σ τ hσ hτ := rfl

end Witness

end DLNFibre.Core
