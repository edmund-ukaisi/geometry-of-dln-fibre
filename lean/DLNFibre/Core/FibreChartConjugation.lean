/-
Copyright (c) 2026. Released under Apache 2.0; see LICENSE.
-/
import DLNFibre.Core.EndpointNormalization
import DLNFibre.Core.DeepChartRing
import DLNFibre.Core.FibreBundlePerMinor
import DLNFibre.Core.OrbitClosure
import DLNFibre.Core.ChartLocalizedCoordinates
import DLNFibre.Core.ChartLocalizedAlgEquiv
import DLNFibre.Core.EndBaseChangeSweep
import DLNFibre.Core.FibreBundleLocallyTrivial
import Mathlib.LinearAlgebra.Matrix.Permutation

/-!
# `DLNFibre.Core.FibreChartConjugation` — the per-pivot conjugation seam (B3-5)

Thread 21 instantiated a genuine **top-left** `LocalTrivializationDatum` from the deep chart
`e_β = chartLocalizedAlgEquiv`, built only at the top-left `r × r` pivot of one `(d, r)`. The
remaining rung to a `locallyTrivial` name is to transport that trivialization to **every** pivot
`(s, t)` of the per-minor cover (`Core.FibreBundlePerMinor`).

This module builds the **conjugation skeleton** of that transport: the **endpoint-permutation
gauge** conjugates the deep-chart construction at the top-left pivot to its `(s, t)` analogue, and
the trivialization `e_β` transports along it to a genuine per-pivot `LocalTrivializationDatum` at
**every** pivot.

## What is built (the conjugation skeleton + per-pivot trivializations)

The end-factor `GL_{d_last} × GL_{d_0}` action carries the top-left chart to the `(s, t)` chart via
a coordinate permutation. For selectors `s : Fin r → Fin (d last)`, `t : Fin r → Fin (d 0)` let
`σ : Perm (Fin (d last))`, `τ : Perm (Fin (d 0))` be permutations carrying the first `r`
rows / columns to the selected ones (`perMinorEquiv`). The endpoint-permutation gauge `pivotGauge`
carries `σ`'s permutation matrix at the target vertex, `τ`'s at the source vertex, identity inside.

1. **The seam** `gaugeEquiv_ΔPdeep_eq_ΔPdeepAt`: the coordinate-change `AlgEquiv`
   `Core.EndpointNormalization.gaugeEquiv` of `MvPolynomial (RepCoord d) k` sends the **top-left**
   deep pivot minor `ΔPdeep` to the **`(s, t)`** deep minor `ΔPdeepAt s t` (`N ≥ 1`). The genuine
   determinant identity: `gaugeEquiv` sends the generic product to its endpoint conjugation
   `σ · M · τ⁻¹ = M.submatrix σ τ`, whose top-left block is the `(s, t)` minor, and det commutes.
2. **The descent** `gaugeEquivSigma` + `gaugeEquivSigma_chartDsig`: `gaugeEquiv` evaluates as the
   `G_d`-shift (`eval_gaugeEquiv`), the rank-`r` locus is `G_d`-stable
   (`productRankLocus_smul_stable`), so `gaugeEquiv` preserves `vanishingIdeal (sweepSigma)` and
   descends to a `k`-algebra automorphism `gaugeEquivSigma` of the chart-closure ring
   `sweepSigmaRing`, carrying the top-left chart element `chartDsig` to the `(s, t)` element
   `chartDsigAt s t`.
3. **The per-pivot trivializations** `chartLocalizedAlgEquivAt`, `chartDsigAt_tensorEquiv`,
   `perPivotLocalTrivializationDatum`: the localization transport `awayCongr` of `gaugeEquivSigma`
   composed with `e_β` (and the thread-11 tensor package) gives, at **every** pivot, an `AlgEquiv`
   `Away (chartDsigAt s t) ≃ₐ Away chartGfib ≃ₐ SchurLoc ⊗ sweepFibreRing` and a genuine
   `LocalTrivializationDatum` — all sharing the standard fibre+schur ring (Codex-confirmed feature).

## What is NOT built (disclaimed — why this is NOT yet `locallyTrivial`)

A `locallyTrivial` name additionally needs (Codex xhigh, decorrelated — the genuinely new rung): the
**transition cocycle on the per-pivot trivializations** — restricting the per-pivot charts to a
double overlap `D(chartDsigAt s t · chartDsigAt s' t')` and identifying the restricted composite
(`e_{s,t} ∘ e_{s',t'}⁻¹` *on that overlap*) with the ambient transition cocycle
(`Core.FibreBundleTransition.awayOverlapTransition`). The per-pivot trivializations live in the same
standard schur ring, so they compose to a uniform normal form, but that is NOT the cocycle: the
source localizations `Away (chartDsigAt s t)` and `Away (chartDsigAt s' t')` differ, and matching
the restricted overlap composite with the *ambient* cocycle (over a different coordinate ring) is a
denominator-bookkeeping comparison of two localization presentations on the double overlap. That
comparison is **not** built here, so this module is honestly **not** named `locallyTrivial`: it is
the per-pivot trivialization family (the conjugation skeleton), with the cocycle transport the
precise remaining cost.

**Dependency rule:** `Core` only — never import `DLNFibre.DLN`.
-/

namespace DLNFibre.Core

open Matrix MvPolynomial Equiv

universe u

variable {k : Type u} [CommRing k] {N : ℕ}

/-! ## The permutation unit and the endpoint-permutation gauge -/

/-- A permutation `σ : Perm (Fin n)` as a unit of the matrix ring (its inverse is `σ⁻¹`'s
permutation matrix). The endpoint factor of the per-pivot gauge. -/
noncomputable def permUnit {n : ℕ} (σ : Equiv.Perm (Fin n)) :
    (Matrix (Fin n) (Fin n) k)ˣ where
  val := Equiv.Perm.permMatrix k σ
  inv := Equiv.Perm.permMatrix k σ⁻¹
  val_inv := by rw [← Matrix.permMatrix_mul σ⁻¹ σ, inv_mul_cancel, Matrix.permMatrix_one]
  inv_val := by rw [← Matrix.permMatrix_mul σ σ⁻¹, mul_inv_cancel, Matrix.permMatrix_one]

/-- **The endpoint-permutation gauge** for a target permutation `σ : Perm (Fin (d last))` and a
source permutation `τ : Perm (Fin (d 0))`: the base-change datum carrying `σ`'s permutation matrix
at the target vertex `Fin.last N`, `τ`'s at the source vertex `0`, and the identity at every
interior vertex. (For `N = 0` the lone vertex is both endpoints; the gauge there is `σ`.) -/
noncomputable def pivotGauge (d : Fin (N + 1) → ℕ)
    (σ : Equiv.Perm (Fin (d (Fin.last N)))) (τ : Equiv.Perm (Fin (d 0))) :
    BaseChangeGroup (k := k) d :=
  fun v ↦
    if h : v = Fin.last N then (h ▸ permUnit σ : (Matrix (Fin (d v)) (Fin (d v)) k)ˣ)
    else if h0 : v = 0 then (h0 ▸ permUnit τ : (Matrix (Fin (d v)) (Fin (d v)) k)ˣ)
    else 1

/-- The pivot gauge at the target vertex `Fin.last N` is `permUnit σ`. -/
@[simp] theorem pivotGauge_last (d : Fin (N + 1) → ℕ)
    (σ : Equiv.Perm (Fin (d (Fin.last N)))) (τ : Equiv.Perm (Fin (d 0))) :
    pivotGauge (k := k) d σ τ (Fin.last N) = permUnit σ := by
  rw [pivotGauge, dif_pos rfl]

/-- For `N ≥ 1` (`last ≠ 0`) the pivot gauge at the source vertex `0` is `permUnit τ`. -/
@[simp] theorem pivotGauge_zero (d : Fin (N + 1) → ℕ) (hN : (Fin.last N) ≠ 0)
    (σ : Equiv.Perm (Fin (d (Fin.last N)))) (τ : Equiv.Perm (Fin (d 0))) :
    pivotGauge (k := k) d σ τ 0 = permUnit τ := by
  rw [pivotGauge, dif_neg (by simpa using hN.symm), dif_pos rfl]

/-! ## The `(s, t)` deep minor -/

/-- **The `(s, t)` deep minor** `ΔPdeepAt d r s t`: the determinant of the `(s, t)` submatrix of the
deep generic product `Matrix.of (multPoly d)`. The top-left case `s = t = Fin.castLE` is the banked
`ΔPdeep`. Inverting it is the `(s, t)` pivot chart. -/
noncomputable def ΔPdeepAt (d : Fin (N + 1) → ℕ) (r : ℕ)
    (s : Fin r → Fin (d (Fin.last N))) (t : Fin r → Fin (d 0)) :
    MvPolynomial (RepCoord d) k :=
  ((Matrix.of (multPoly d)).submatrix s t).det

/-! ## The conjugation seam (over a field, where `ΔPdeep` lives) -/

section Field

variable {k : Type u} [Field k]

/-- `permMatrix` commutes with a ring-hom `map`: `(σ.permMatrix R).map f = σ.permMatrix S`. -/
theorem permMatrix_map {n : ℕ} {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S)
    (σ : Equiv.Perm (Fin n)) :
    (σ.permMatrix R).map f = σ.permMatrix S := by
  ext i j
  simp [Equiv.Perm.permMatrix, PEquiv.toMatrix_apply, Equiv.toPEquiv_apply, apply_ite f]

/-- The top-left `(s, t) = (castLE, castLE)` deep minor is the banked `ΔPdeep`. -/
theorem ΔPdeepAt_topLeft (d : Fin (N + 1) → ℕ) (r : ℕ)
    (hp : r ≤ d (Fin.last N)) (hq : r ≤ d 0) :
    ΔPdeepAt (k := k) d r (fun i ↦ Fin.castLE hp i) (fun j ↦ Fin.castLE hq j)
      = ΔPdeep d r hp hq := rfl

/-- **The generic product conjugates to its `(σ, τ)`-submatrix.** Applying the coordinate-change
`gaugeEquiv` for the endpoint-permutation gauge `pivotGauge σ τ` (`N ≥ 1`) to every entry of the
deep generic product `M = Matrix.of (multPoly d)` gives the reindexed matrix `M.submatrix σ τ`:
`gaugeEquiv` sends each entry to the endpoint conjugation `σ.permMatrix · M · τ⁻¹.permMatrix`
(`gaugeEquiv_multPoly` + the `pivotGauge` endpoint values), and the permutation-matrix products
reindex rows by `σ` and columns by `τ` (`PEquiv.toMatrix_toPEquiv_mul` / `mul_toMatrix_toPEquiv`,
`τ⁻¹.symm = τ`). -/
theorem map_gaugeEquiv_multPoly (d : Fin (N + 1) → ℕ) (hN : (Fin.last N) ≠ 0)
    (σ : Equiv.Perm (Fin (d (Fin.last N)))) (τ : Equiv.Perm (Fin (d 0))) :
    (Matrix.of (multPoly d)).map (gaugeEquiv d (pivotGauge (k := k) d σ τ))
      = (Matrix.of (multPoly d)).submatrix σ τ := by
  ext a b
  rw [Matrix.map_apply, Matrix.of_apply, gaugeEquiv_multPoly, Matrix.submatrix_apply,
    Matrix.of_apply]
  -- the two endpoint gauge matrices are the `C`-images of the permutation matrices
  have hlast : Units.val (liftGauge d (pivotGauge (k := k) d σ τ) (Fin.last N))
      = σ.permMatrix (MvPolynomial (RepCoord d) k) := by
    rw [liftGauge_val_eq, pivotGauge_last]
    exact permMatrix_map _ σ
  have hzero : Units.val ((liftGauge d (pivotGauge (k := k) d σ τ) 0)⁻¹)
      = (τ⁻¹).permMatrix (MvPolynomial (RepCoord d) k) := by
    rw [liftGauge_inv_val_eq, pivotGauge_zero d hN]
    change ((Units.val ((permUnit τ)⁻¹)).map (C : k →+* _)) = _
    rw [show Units.val ((permUnit τ)⁻¹) = (permUnit τ).inv from rfl]
    exact permMatrix_map _ τ⁻¹
  -- reindex rows by `σ` then columns by `τ` via the permutation-matrix products
  rw [hlast, hzero,
    show σ.permMatrix (MvPolynomial (RepCoord d) k) = σ.toPEquiv.toMatrix from rfl,
    show (τ⁻¹).permMatrix (MvPolynomial (RepCoord d) k) = (τ⁻¹).toPEquiv.toMatrix from rfl,
    PEquiv.toMatrix_toPEquiv_mul, PEquiv.mul_toMatrix_toPEquiv, Matrix.submatrix_submatrix]
  -- the reindexed entry `M (σ a) ((τ⁻¹).symm b) = multPoly (σ a) (τ b)`
  rw [Matrix.submatrix_apply, Matrix.of_apply, Function.comp_apply, Function.comp_apply,
    Equiv.Perm.inv_def, Equiv.symm_symm]
  rfl

/-- **The conjugation seam.** The endpoint-permutation gauge `pivotGauge σ τ`, applied through the
coordinate-change `AlgEquiv` `gaugeEquiv`, carries the **top-left** deep minor `ΔPdeep` to the
**`(s, t)`** deep minor `ΔPdeepAt s t` — provided the permutations carry the first `r`
rows/columns to the selected ones (`σ (castLE i) = s i`, `τ (castLE j) = t j`). The whole deep chart
at `(s, t)` is thus the gauge-conjugate of the top-left one: `gaugeEquiv` sends the generic product
to its endpoint conjugation `σ.permMatrix · M · τ⁻¹.permMatrix = M.submatrix σ τ`
(`gaugeEquiv_multPoly` + `PEquiv.toMatrix_toPEquiv_mul`), whose top-left block is `M.submatrix s t`,
and det commutes with the algebra map (`AlgEquiv.map_det`). -/
theorem gaugeEquiv_ΔPdeep_eq_ΔPdeepAt (d : Fin (N + 1) → ℕ) (hN : (Fin.last N) ≠ 0) (r : ℕ)
    (hp : r ≤ d (Fin.last N)) (hq : r ≤ d 0)
    (s : Fin r → Fin (d (Fin.last N))) (t : Fin r → Fin (d 0))
    (σ : Equiv.Perm (Fin (d (Fin.last N)))) (τ : Equiv.Perm (Fin (d 0)))
    (hσ : ∀ i : Fin r, σ (Fin.castLE hp i) = s i)
    (hτ : ∀ j : Fin r, τ (Fin.castLE hq j) = t j) :
    gaugeEquiv d (pivotGauge d σ τ) (ΔPdeep d r hp hq)
      = ΔPdeepAt (k := k) d r s t := by
  -- `gaugeEquiv` is a `k`-algebra map; `det` commutes with it (via its `RingHom`).
  have hdet : gaugeEquiv d (pivotGauge (k := k) d σ τ) (ΔPdeep d r hp hq)
      = (((Matrix.of (multPoly d)).submatrix (fun i ↦ Fin.castLE hp i)
          (fun j ↦ Fin.castLE hq j)).map
          (gaugeEquiv d (pivotGauge (k := k) d σ τ))).det := by
    rw [ΔPdeep]
    exact RingHom.map_det (gaugeEquiv d (pivotGauge (k := k) d σ τ)).toAlgHom.toRingHom _
  rw [hdet, ← Matrix.submatrix_map, map_gaugeEquiv_multPoly d hN σ τ,
    Matrix.submatrix_submatrix, ΔPdeepAt]
  -- the top-left block of the reindexed matrix is the `(s, t)` minor: selectors `σ∘castLE = s` etc.
  have hs : (⇑σ ∘ fun i ↦ Fin.castLE hp i) = s := funext hσ
  have ht : (⇑τ ∘ fun j ↦ Fin.castLE hq j) = t := funext hτ
  rw [hs, ht]

end Field

/-! ## Descent to the chart-closure quotient `sweepSigmaRing` (B3-5b)

The coordinate change `gaugeEquiv P` agrees with the banked `baseChangePullback P`
(`gaugeSub = baseChangeSub`), so it evaluates as the `G_d`-shift on points
(`eval_gaugeEquiv`). The rank-`r` product locus is `G_d`-stable (`mult_smul` + endpoint-unit rank
invariance), hence `gaugeEquiv P` preserves the vanishing ideal of `sweepSigma` and descends to a
`k`-algebra automorphism `gaugeEquivSigma P` of the chart-closure ring `sweepSigmaRing`. -/

section Descent

variable {k : Type u} [Field k]

/-- `gaugeEquiv P` and the banked `baseChangePullback P` are the **same** coordinate substitution
(`gaugeSub = baseChangeSub`, both the `aeval` of the base-change action on the generic tuple). -/
theorem gaugeEquiv_eq_baseChangePullback (d : Fin (N + 1) → ℕ) (P : BaseChangeGroup (k := k) d)
    (f : MvPolynomial (RepCoord d) k) :
    gaugeEquiv d P f = baseChangePullback P f := by
  have hsub : gaugeSub d P = baseChangeSub P := by
    funext x
    rw [gaugeSub, baseChangeSub, baseChange_apply]
    rfl
  rw [gaugeEquiv_apply, baseChangePullback, hsub]

/-- The inverse of the gauge `AlgEquiv` is the gauge of the inverse base change:
`(gaugeEquiv P).symm = gaugeEquiv P⁻¹` (the `ofAlgHom` round-trip identity, on generators). -/
theorem gaugeEquiv_symm_eq_inv (d : Fin (N + 1) → ℕ) (P : BaseChangeGroup (k := k) d)
    (f : MvPolynomial (RepCoord d) k) :
    (gaugeEquiv d P).symm f = gaugeEquiv d P⁻¹ f := by
  -- `gaugeEquiv P ∘ gaugeEquiv P⁻¹ = id` (the `aeval_gaugeSub_gaugeSub` round-trip on generators)
  have hcomp : (aeval (R := k) (gaugeSub d P)).comp (aeval (R := k) (gaugeSub d P⁻¹))
      = AlgHom.id k (MvPolynomial (RepCoord d) k) := by
    apply MvPolynomial.algHom_ext
    intro x
    rw [AlgHom.comp_apply, AlgHom.id_apply, aeval_X, aeval_gaugeSub_gaugeSub, inv_mul_cancel,
      liftGauge_one, baseChange_one, genericTuple_apply]
  have hid : (gaugeEquiv d P) ((gaugeEquiv d P⁻¹) f) = f := by
    rw [gaugeEquiv_apply, gaugeEquiv_apply]
    simpa only [AlgHom.comp_apply, AlgHom.id_apply] using AlgHom.congr_fun hcomp f
  rw [AlgEquiv.symm_apply_eq, hid]

/-- **`gaugeEquiv` evaluates as the `G_d`-shift.** `eval x (gaugeEquiv P f) = eval (shifted x) f`,
where the shift is the base-change action `P • ·` read through `canonicalCoord`. Reduces to the
banked `eval_baseChangePullback` via `gaugeEquiv_eq_baseChangePullback`. -/
theorem eval_gaugeEquiv [Infinite k] (d : Fin (N + 1) → ℕ) (P : BaseChangeGroup (k := k) d)
    (x : RepCoord d → k) (f : MvPolynomial (RepCoord d) k) :
    MvPolynomial.eval x (gaugeEquiv d P f)
      = MvPolynomial.eval (canonicalCoord d (P • (canonicalCoord d).symm x)) f := by
  rw [gaugeEquiv_eq_baseChangePullback, eval_baseChangePullback]

/-- **The rank-`r` product locus is `G_d`-stable.** If `(mult A).rank = r` then
`(mult (P • A)).rank = r`: `mult (P • A) = P_last · mult A · P_0⁻¹` (`mult_smul`) and the endpoint
units preserve rank (`rank_endpoint_conj`). -/
theorem productRankLocus_smul_stable (d : Fin (N + 1) → ℕ) (r : ℕ)
    (P : BaseChangeGroup (k := k) d) {A : Tuple (k := k) d}
    (hA : A ∈ productRankLocus d r) : P • A ∈ productRankLocus d r := by
  rw [mem_productRankLocus, mult_smul, rank_endpoint_conj]
  exact hA

/-- **`gaugeEquiv P` preserves the chart-closure vanishing ideal.** A polynomial vanishing on
`sweepSigma = canonicalCoord '' productRankLocus` still vanishes after the gauge change, because the
gauge evaluates as the `G_d`-shift (`eval_gaugeEquiv`) and the rank-`r` locus is `G_d`-stable
(`productRankLocus_smul_stable`). -/
theorem gaugeEquiv_mem_vanishingIdeal_sweepSigma [Infinite k]
    (d : Fin (N + 2) → ℕ) (r : ℕ) (P : BaseChangeGroup (k := k) d)
    {f : MvPolynomial (RepCoord d) k}
    (hf : f ∈ vanishingIdeal k (sweepSigma k d r)) :
    gaugeEquiv d P f ∈ vanishingIdeal k (sweepSigma k d r) := by
  rw [sweepSigma, mem_vanishingIdeal_iff] at hf ⊢
  intro y hy
  obtain ⟨A, hA, rfl⟩ := hy
  rw [MvPolynomial.aeval_eq_eval, eval_gaugeEquiv, ← MvPolynomial.aeval_eq_eval]
  refine hf _ ⟨P • A, productRankLocus_smul_stable d r P hA, ?_⟩
  rw [Equiv.symm_apply_apply]

/-- **`gaugeEquiv P` maps the chart-closure vanishing ideal onto itself.** Both `gaugeEquiv P` and
`gaugeEquiv P⁻¹` preserve `vanishingIdeal (sweepSigma)`
(`gaugeEquiv_mem_vanishingIdeal_sweepSigma`), so for the `AlgEquiv` `gaugeEquiv P` the `Ideal.map`
of `vanishingIdeal (sweepSigma)` is itself. -/
theorem vanishingIdeal_sweepSigma_map_gaugeEquiv [Infinite k]
    (d : Fin (N + 2) → ℕ) (r : ℕ) (P : BaseChangeGroup (k := k) d) :
    (vanishingIdeal k (sweepSigma k d r)).map
        ((gaugeEquiv d P).toAlgHom.toRingHom)
      = vanishingIdeal k (sweepSigma k d r) := by
  apply le_antisymm
  · rw [Ideal.map_le_iff_le_comap]
    intro f hf
    rw [Ideal.mem_comap]
    exact gaugeEquiv_mem_vanishingIdeal_sweepSigma d r P hf
  · intro f hf
    rw [show f = (gaugeEquiv d P) ((gaugeEquiv d P).symm f) from
      ((gaugeEquiv d P).apply_symm_apply f).symm]
    refine Ideal.mem_map_of_mem _ ?_
    rw [gaugeEquiv_symm_eq_inv]
    exact gaugeEquiv_mem_vanishingIdeal_sweepSigma d r P⁻¹ hf

/-- **The descent of `gaugeEquiv P` to the chart-closure quotient.** Since `gaugeEquiv P` maps the
chart-closure vanishing ideal onto itself (`vanishingIdeal_sweepSigma_map_gaugeEquiv`), it descends
to a `k`-algebra automorphism of `sweepSigmaRing = O(Σ^r)`. -/
noncomputable def gaugeEquivSigma [Infinite k] (d : Fin (N + 2) → ℕ) (r : ℕ)
    (P : BaseChangeGroup (k := k) d) :
    sweepSigmaRing k d r ≃ₐ[k] sweepSigmaRing k d r :=
  Ideal.quotientEquivAlg (vanishingIdeal k (sweepSigma k d r))
    (vanishingIdeal k (sweepSigma k d r)) (gaugeEquiv d P)
    (vanishingIdeal_sweepSigma_map_gaugeEquiv d r P).symm

/-- `gaugeEquivSigma P` acts on a quotient class by the gauge change of a representative
(`quotientEquivAlg_mk`). -/
theorem gaugeEquivSigma_mk [Infinite k] (d : Fin (N + 2) → ℕ) (r : ℕ)
    (P : BaseChangeGroup (k := k) d) (f : MvPolynomial (RepCoord d) k) :
    gaugeEquivSigma d r P (Ideal.Quotient.mk (vanishingIdeal k (sweepSigma k d r)) f)
      = Ideal.Quotient.mk (vanishingIdeal k (sweepSigma k d r)) (gaugeEquiv d P f) := by
  rw [gaugeEquivSigma, Ideal.quotientEquivAlg_mk]

/-! ## The `(s, t)` chart localizing element and the carry (B3-5b) -/

/-- **The `(s, t)` chart localizing element** `chartDsigAt d r s t`: the class of the `(s, t)` deep
minor `ΔPdeepAt s t` in the chart-closure ring `O(Σ^r)`. The top-left case is `chartDsig`. -/
noncomputable def chartDsigAt (d : Fin (N + 2) → ℕ) (r : ℕ)
    (s : Fin r → Fin (d (Fin.last (N + 1)))) (t : Fin r → Fin (d 0)) :
    sweepSigmaRing k d r :=
  Ideal.Quotient.mk (vanishingIdeal k (sweepSigma k d r)) (ΔPdeepAt d r s t)

/-- The top-left `(s, t) = (castLE, castLE)` chart element is `chartDsig`. -/
theorem chartDsigAt_topLeft (d : Fin (N + 2) → ℕ) (r : ℕ)
    (hp : r ≤ d (Fin.last (N + 1))) (hq : r ≤ d 0) :
    chartDsigAt (k := k) d r (fun i ↦ Fin.castLE hp i) (fun j ↦ Fin.castLE hq j)
      = chartDsig k d r hp hq := rfl

/-- **The carry of the chart localizing element.** The descended gauge `gaugeEquivSigma P` carries
the top-left chart element `chartDsig` to the `(s, t)` chart element `chartDsigAt s t`, provided
the permutations carry the first `r` rows/columns to the selected ones — the
chart-closure-quotient image of the polynomial seam `gaugeEquiv_ΔPdeep_eq_ΔPdeepAt`. (`N ≥ 1`: the
chart dimension vector is `Fin (N + 2) → ℕ`, so `Fin.last (N + 1) ≠ 0` always.) -/
theorem gaugeEquivSigma_chartDsig [Infinite k] (d : Fin (N + 2) → ℕ) (r : ℕ)
    (hp : r ≤ d (Fin.last (N + 1))) (hq : r ≤ d 0)
    (s : Fin r → Fin (d (Fin.last (N + 1)))) (t : Fin r → Fin (d 0))
    (σ : Equiv.Perm (Fin (d (Fin.last (N + 1))))) (τ : Equiv.Perm (Fin (d 0)))
    (hσ : ∀ i : Fin r, σ (Fin.castLE hp i) = s i)
    (hτ : ∀ j : Fin r, τ (Fin.castLE hq j) = t j) :
    gaugeEquivSigma d r (pivotGauge d σ τ) (chartDsig k d r hp hq)
      = chartDsigAt d r s t := by
  rw [chartDsig, gaugeEquivSigma_mk, chartDsigAt,
    gaugeEquiv_ΔPdeep_eq_ΔPdeepAt d (Fin.last_pos.ne') r hp hq s t σ τ hσ hτ]

end Descent

/-! ## The localization transport of an `AlgEquiv` carrying one element to another -/

section AwayCongr

variable {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]

/-- **The localization transport of an `AlgEquiv`.** An `R`-algebra automorphism `e` of `A`
carrying `a` to `b` lifts to an `R`-algebra iso `Localization.Away a ≃ₐ[R] Localization.Away b`
(`mapₐ` of `e` and of `e.symm`, round-trips by localization initiality,
`IsLocalization.ringHom_ext`). This is the
clean abstract bridge: the chart `e_β` at the top-left pivot transports to the `(s, t)` pivot along
`gaugeEquivSigma`. -/
noncomputable def awayCongr (e : A ≃ₐ[R] A) (a b : A) (hb : e a = b) :
    Localization.Away a ≃ₐ[R] Localization.Away b := by
  haveI h1 : IsLocalization.Away (e.toAlgHom a) (Localization.Away b) := by
    change IsLocalization.Away (e a) (Localization.Away b); rw [hb]; infer_instance
  haveI h2 : IsLocalization.Away (e.symm.toAlgHom b) (Localization.Away a) := by
    change IsLocalization.Away (e.symm b) (Localization.Away a)
    rw [← hb, e.symm_apply_apply]; infer_instance
  refine AlgEquiv.ofAlgHom
    (IsLocalization.Away.mapₐ (Localization.Away a) (Localization.Away b) e.toAlgHom a)
    (IsLocalization.Away.mapₐ (Localization.Away b) (Localization.Away a) e.symm.toAlgHom b)
    (AlgHom.coe_ringHom_injective (IsLocalization.ringHom_ext (Submonoid.powers b)
      (by ext x; simp [IsLocalization.Away.mapₐ, IsLocalization.Away.map])))
    (AlgHom.coe_ringHom_injective (IsLocalization.ringHom_ext (Submonoid.powers a)
      (by ext x; simp [IsLocalization.Away.mapₐ, IsLocalization.Away.map])))

end AwayCongr

/-! ## The per-pivot trivialization `e_{s,t}` (B3-5c)

Composing the gauge-induced localization transport `awayCongr (gaugeEquivSigma P) chartDsig
(chartDsigAt s t)` with the deep chart `e_β = chartLocalizedAlgEquiv` gives the per-pivot
trivialization at the `(s, t)` pivot — an `AlgEquiv` from the localized `(s, t)` chart total ring
`Away (chartDsigAt s t)` to the schur-side ring `Away chartGfib`, the SAME fibre+schur ring the
top-left chart uses (Codex-confirmed: a feature — all pivots trivialize to the standard chart). -/

section PerPivot

variable {k : Type} [Field k] [Infinite k] {N : ℕ}

/-- **The per-pivot trivialization `e_{s,t}`.** The localized `(s, t)` chart total ring
`Localization.Away (chartDsigAt s t)` is identified with the schur-side ring
`Localization.Away (chartGfib)` — the SAME ring the top-left chart uses — by transporting along the
gauge `gaugeEquivSigma (pivotGauge σ τ)` (which carries `chartDsig` to `chartDsigAt s t`,
`gaugeEquivSigma_chartDsig`) and then applying the deep chart `e_β = chartLocalizedAlgEquiv`. So
every pivot chart trivializes against the standard fibre model. -/
noncomputable def chartLocalizedAlgEquivAt (d : Fin (N + 2) → ℕ) (r : ℕ)
    (hp : r ≤ d (Fin.last (N + 1))) (hq : r ≤ d 0)
    (s : Fin r → Fin (d (Fin.last (N + 1)))) (t : Fin r → Fin (d 0))
    (σ : Equiv.Perm (Fin (d (Fin.last (N + 1))))) (τ : Equiv.Perm (Fin (d 0)))
    (hσ : ∀ i : Fin r, σ (Fin.castLE hp i) = s i)
    (hτ : ∀ j : Fin r, τ (Fin.castLE hq j) = t j) :
    Localization.Away (chartDsigAt (k := k) d r s t)
      ≃ₐ[k] Localization.Away (chartGfib k d r hp hq) :=
  (awayCongr (gaugeEquivSigma d r (pivotGauge d σ τ)) (chartDsig k d r hp hq)
      (chartDsigAt d r s t) (gaugeEquivSigma_chartDsig d r hp hq s t σ τ hσ hτ)).symm.trans
    (chartLocalizedAlgEquiv k d r hp hq)

open scoped TensorProduct in
/-- **The per-pivot tensor trivialization.** The localized `(s, t)` chart total ring
`Localization.Away (chartDsigAt s t)` is exhibited as the product
`SchurLoc ⊗_k sweepFibreRing` — the SAME local product structure (local matrix direction ⊗ reduced
fibre ring) as the top-left chart — by transporting the top-left tensor trivialization
`reducedFibre_chartDsig_tensorEquiv_reducedVariety` along the gauge. The `(s, t)` analogue of the
thread-11 tensor package. -/
noncomputable def chartDsigAt_tensorEquiv (d : Fin (N + 2) → ℕ) (r : ℕ)
    (hp : r ≤ d (Fin.last (N + 1))) (hq : r ≤ d 0)
    (s : Fin r → Fin (d (Fin.last (N + 1)))) (t : Fin r → Fin (d 0))
    (σ : Equiv.Perm (Fin (d (Fin.last (N + 1))))) (τ : Equiv.Perm (Fin (d 0)))
    (hσ : ∀ i : Fin r, σ (Fin.castLE hp i) = s i)
    (hτ : ∀ j : Fin r, τ (Fin.castLE hq j) = t j) :
    Localization.Away (chartDsigAt (k := k) d r s t)
      ≃ₐ[k] SchurLoc (k := k) (d 0) (d (Fin.last (N + 1))) r ⊗[k] sweepFibreRing k d r hp hq :=
  (awayCongr (gaugeEquivSigma d r (pivotGauge d σ τ)) (chartDsig k d r hp hq)
      (chartDsigAt d r s t) (gaugeEquivSigma_chartDsig d r hp hq s t σ τ hσ hτ)).symm.trans
    (reducedFibre_chartDsig_tensorEquiv_reducedVariety d r hp hq)

/-- **The per-pivot local-trivialization datum, genuinely instantiated.** For each pivot `(s, t)`
(with permutations `σ, τ` carrying the first `r` rows/columns to it) the datum has chart element the
`(s, t)` deep minor class `chartDsigAt s t`, and trivialization the gauge-transported tensor package
`chartDsigAt_tensorEquiv`. This is the `(s, t)` analogue of the top-left
`Core.topLeftLocalTrivializationDatum` — a genuine chart datum at **every** pivot, all sharing the
standard fibre+schur ring. (One chart of the would-be atlas per pivot; see the module docstring for
what remains for `locallyTrivial`.) -/
noncomputable def perPivotLocalTrivializationDatum (d : Fin (N + 2) → ℕ) (r : ℕ)
    (hp : r ≤ d (Fin.last (N + 1))) (hq : r ≤ d 0)
    (s : Fin r → Fin (d (Fin.last (N + 1)))) (t : Fin r → Fin (d 0))
    (σ : Equiv.Perm (Fin (d (Fin.last (N + 1))))) (τ : Equiv.Perm (Fin (d 0)))
    (hσ : ∀ i : Fin r, σ (Fin.castLE hp i) = s i)
    (hτ : ∀ j : Fin r, τ (Fin.castLE hq j) = t j) :
    LocalTrivializationDatum k
      (sweepSigmaRing k d r)
      (Localization.Away (chartDsigAt (k := k) d r s t))
      (SchurLoc (k := k) (d 0) (d (Fin.last (N + 1))) r)
      (sweepFibreRing k d r hp hq) where
  chartElt := chartDsigAt d r s t
  trivialization := chartDsigAt_tensorEquiv d r hp hq s t σ τ hσ hτ

/-- The identity gauge `(σ, τ) = (1, 1)` recovers the top-left datum: its chart element is the
top-left `chartDsig` (`chartDsigAt_topLeft`). Honest non-vacuity — the per-pivot construction
restricts to the top-left chart. -/
theorem perPivotLocalTrivializationDatum_topLeft (d : Fin (N + 2) → ℕ) (r : ℕ)
    (hp : r ≤ d (Fin.last (N + 1))) (hq : r ≤ d 0) :
    (perPivotLocalTrivializationDatum d r hp hq (fun i ↦ Fin.castLE hp i)
        (fun j ↦ Fin.castLE hq j) 1 1 (fun _ ↦ rfl) (fun _ ↦ rfl)).chartElt
      = chartDsig k d r hp hq :=
  chartDsigAt_topLeft d r hp hq

end PerPivot

/-! ## Non-vacuity witnesses

The conjugation seam fires on a concrete single matrix; the descent + per-pivot datum fire at an
abstract `[Infinite k]` field and dimension vector (the deep chart `e_β` carries `[Infinite k]`). -/

section Witness

/-- **Seam witness.** At `q = p = 2`, `r = 1` over `ℚ`, with the top-left pivot reached by the
identity permutation, the gauge change carries `ΔPdeep` to itself — a concrete instance of
`gaugeEquiv_ΔPdeep_eq_ΔPdeepAt` at the identity gauge (`s = t = castLE`, `σ = τ = 1`). -/
example (h : (1 : ℕ) ≤ 2) :
    gaugeEquiv (![2, 2] : Fin 2 → ℕ) (pivotGauge (k := ℚ) ![2, 2] 1 1)
        (ΔPdeep ![2, 2] 1 h h)
      = ΔPdeepAt (k := ℚ) ![2, 2] 1 (fun i ↦ Fin.castLE h i) (fun j ↦ Fin.castLE h j) :=
  gaugeEquiv_ΔPdeep_eq_ΔPdeepAt ![2, 2] (by decide) 1 h h _ _ 1 1 (fun _ ↦ rfl) (fun _ ↦ rfl)

end Witness

end DLNFibre.Core
