import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Determinant
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Data.Real.Basic
import DLNFibre.DLN.RLCT.Validate.RouteMCardBridge

/-!
# `RouteMColumnFactor` — the column-factor det spine (Route A; the least-cast assembly)

The decorrelated-Codex-chosen spine (`threads/80-genM-nodechart/codex/assembly-arch`) for the
unconditional interior-det headline, over the abstract `stairMap` conjugacy (route B, which would
force a full linear-map equality `eOut ∘ Dφ ∘ eIn.symm = stairMap`): work at the DET level on the
Jacobian matrix `J = toMatrix' Dφ`. The radial cert's mechanism is that `J`'s `R`-columns (the
`u`-scaled `Rmat`/`Rfin` free entries) each carry a `u_p` factor, so
`J i j = (if j ∈ Rcols then u_p else 1) · G i j` with `G` `u`-free and `Rcols.card = minAdm − 1`.
Pulling the `u`-columns gives `|det J| = |u_p|^{minAdm−1}·|det G|` (`Matrix.det_mul_row`), and `G`
block-triangular (the banked locality) factorizes into the per-boundary engine dets. NO recursive
`StairProd`, NO global `composeFold fs = phiFlatLiveR1` map equality.

* `abs_det_scaledColumns_finset` — `|det (of fun i j => (if j ∈ S then u else 1) · G i j)| =
  |u|^{S.card} · |det G|` (column-scaling det, via `Matrix.det_mul_row` + `Finset.prod_ite_mem`).
* `interior_abs_det_of_columnFactorization` — the headline shape: from the column factorization
  `J = scaledColumns Rcols u_p G` + `Rcols.card = minAdm − 1` + `|det G| = ∏_s engine s`, the
  interior Jacobian abs-det is `|u_p|^{minAdm−1} · ∏_s engine s`.

Axiom-clean `[propext, Classical.choice, Quot.sound]` (determinant + finite products; no analysis —
the real `fderiv` enters only as `J`, whose factorization is the separate
`phiFlatLiveR1_jacobian_scaledColumns` obligation).
-/

open Matrix
open scoped BigOperators

namespace DLNFibre.DLN.RLCT

/-- **The `u`-scaled column vector** `if j ∈ S then u else 1`; `univ`-product `u^{S.card}`. -/
private theorem prod_scaleVec {N : ℕ} (S : Finset (Fin N)) (u : ℝ) :
    ∏ i : Fin N, (if i ∈ S then u else 1) = u ^ S.card := by
  rw [Finset.prod_ite_mem Finset.univ S (fun _ => u), Finset.univ_inter, Finset.prod_const]

/-- **The column-scaling determinant (abs form).** If a square matrix is `G` with its columns in `S`
each scaled by `u`, its det abs-value is `|u|^{S.card} · |det G|`. Via `Matrix.det_mul_row`
(`det (of fun i j => v j · A i j) = (∏ i, v i)·det A`) with `v j := if j ∈ S then u else 1`, then
`∏ = u^{S.card}` (`prod_scaleVec`). No division by `u` — valid at `u = 0`. -/
theorem abs_det_scaledColumns_finset {N : ℕ} (S : Finset (Fin N)) (u : ℝ)
    (G : Matrix (Fin N) (Fin N) ℝ) :
    |(Matrix.of fun i j => (if j ∈ S then u else 1) * G i j).det|
      = |u| ^ S.card * |G.det| := by
  rw [Matrix.det_mul_row (fun j => if j ∈ S then u else 1) G, prod_scaleVec, abs_mul, abs_pow]

/-- **The interior-det headline from the column factorization (Route A spine).** Let `D` be the
interior Jacobian (`LinearMap`). If its standard-basis matrix factors as
`J i j = (if j ∈ Rcols then u_p else 1) · G i j` (the radial `u`-scaled `R`-columns pulled out),
with `Rcols.card = minAdm − 1` and the `u`-free residual `G` whose det abs-value is the engine
product `∏_s engine s`, then the interior Jacobian abs-det is `|u_p|^{minAdm−1} · ∏_s engine s`. The
column-factorization (`phiFlatLiveR1_jacobian_scaledColumns`) and the `G`-det identification
(`boundary_diagBlock_abs_det_engine`) are the two remaining obligations. -/
theorem interior_abs_det_of_columnFactorization {L N : ℕ} (M : Fin (L + 1) → ℕ)
    (D : (Fin N → ℝ) →ₗ[ℝ] (Fin N → ℝ)) (Rcols : Finset (Fin N)) (up : ℝ)
    (G : Matrix (Fin N) (Fin N) ℝ) (engine : Fin L → ℝ)
    (hJ : LinearMap.toMatrix' D = Matrix.of fun i j => (if j ∈ Rcols then up else 1) * G i j)
    (hcard : Rcols.card = minAdm M - 1)
    (hG : |G.det| = ∏ s : Fin L, engine s) :
    |LinearMap.det D| = |up| ^ (minAdm M - 1) * ∏ s : Fin L, engine s := by
  rw [← LinearMap.det_toMatrix' D, hJ, abs_det_scaledColumns_finset Rcols up G, hcard, hG]

/-! ## The radial `Rcols` and its cardinality (`= minAdm − 1`)

`Rcols` is the radial active set minus the pivot — the `u`-scaled `R`-columns. Its cardinality is
`minAdm − 1` (the spine's `hcard`), from `radialActive_exists` (`active.card = minAdm`,
`structPivot ∈ active`) + `Finset.card_erase_of_mem`. Decouples the COUNT obligation from the
Jacobian-factorization (P) and the `G`-det (B). -/

/-- **The radial `R`-column set** `active.erase structPivot` — the `u`-scaled non-pivot coords. -/
noncomputable def radialRcols {L : ℕ} (M : Fin (L + 1) → ℕ) (hN : 0 < routeMAmbient M)
    (active : Finset (Fin (routeMAmbient M))) : Finset (Fin (routeMAmbient M)) :=
  active.erase (structPivot M hN)

/-- **`radialRcols.card = minAdm − 1`** — the spine's `hcard`, from `active.card = minAdm` (radial
active set, `radialActive_exists`) + `Finset.card_erase_of_mem` (the pivot is in `active`). -/
theorem radialRcols_card {L : ℕ} (M : Fin (L + 1) → ℕ) (hN : 0 < routeMAmbient M)
    (active : Finset (Fin (routeMAmbient M))) (hp : structPivot M hN ∈ active)
    (hcard : active.card = minAdm M) :
    (radialRcols M hN active).card = minAdm M - 1 := by
  rw [radialRcols, Finset.card_erase_of_mem hp, hcard]

/-! ## Non-vacuity: the column-factor spine fires on a concrete factorization

The spine is a genuine conditional: on a `1×1` Jacobian the headline shape fires. -/

/-- **Non-vacuity (`L = 0`, `N = 1`, scalar).** A `1×1` Jacobian `[u]` factors with `Rcols = ∅`
(`minAdm = 1`, exponent `0`), `G = [u]`, empty engine product — the spine fires (`|det| = |u|^0·1`).
Confirms the column-factor conditional is satisfiable end-to-end. -/
example (M : Fin 1 → ℕ) (hM : minAdm M = 1) (up : ℝ)
    (D : (Fin 1 → ℝ) →ₗ[ℝ] (Fin 1 → ℝ))
    (hJ : LinearMap.toMatrix' D = (Matrix.of fun _ _ => up : Matrix (Fin 1) (Fin 1) ℝ))
    (hGdet : |(Matrix.of fun _ _ => up : Matrix (Fin 1) (Fin 1) ℝ).det| = 1) :
    |LinearMap.det D| = |up| ^ (minAdm M - 1) * ∏ _s : Fin 0, (1 : ℝ) := by
  refine interior_abs_det_of_columnFactorization M D (∅ : Finset (Fin 1)) up
    (Matrix.of fun _ _ => up) (fun _ => 1) ?_ ?_ ?_
  · rw [hJ]; ext i j; simp
  · rw [hM]; rfl
  · rw [hGdet, Finset.prod_const_one]

end DLNFibre.DLN.RLCT
