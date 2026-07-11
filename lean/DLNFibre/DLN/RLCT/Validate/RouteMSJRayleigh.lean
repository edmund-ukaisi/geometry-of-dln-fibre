import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Data.Real.StarOrdered

set_option linter.style.longLine false

/-!
# `DLNFibre.DLN.RLCT.Validate.RouteMSJRayleigh` — the matrix Rayleigh lower bound

**Thread `genm-vsdeep` (aoyagi-full), the shared spectral bridge for (b)-integrability and (a).** The
front-first majorant `σ_r(P)^{−α}` is integrated against the Gram-determinant weight consumed by the
banked `qbox_lintegral_lt_top`; the bridge is the **Rayleigh lower bound**

    (⨅ᵢ λᵢ) · ‖y‖²  ≤  ⟨G y, y⟩      (G real Hermitian, λ = its eigenvalues),

which yields `smallest singular value` ≥ `smallest eigenvalue of the Gram` and, together with
`det = ∏ eigenvalues`, the box comparison `det(gram)^{1/2} ≤ C · σ_r`. Proved elementarily from the
spectral theorem: `G − c·1` (with `c` the least eigenvalue) is a unitary conjugate `U·diagonal(λ−c)·Uᴴ`
of a **nonnegative** diagonal, hence positive semidefinite, so its quadratic form is `≥ 0`.

* **`gram_rayleigh_lb`** — `(⨅ᵢ hG.eigenvalues i) · (star y ⬝ᵥ y) ≤ star y ⬝ᵥ (G *ᵥ y)`.

Network-free (pure matrix spectral theory). Axiom-clean `[propext, Classical.choice, Quot.sound]`.
-/

namespace DLNFibre.DLN.RLCT

open Matrix
open scoped BigOperators

variable {r : ℕ}

/-- **Matrix Rayleigh lower bound**: for a real Hermitian matrix `G`, the quadratic form
`star y ⬝ᵥ (G *ᵥ y)` is bounded below by the smallest eigenvalue times `star y ⬝ᵥ y`. Via the spectral
theorem: `G − c·1` (`c` = least eigenvalue) is the unitary conjugate `U·diagonal(λ−c)·Uᴴ` of a
nonnegative diagonal, hence positive semidefinite. -/
theorem gram_rayleigh_lb {G : Matrix (Fin r) (Fin r) ℝ} (hG : G.IsHermitian) (y : Fin r → ℝ) :
    (⨅ i, hG.eigenvalues i) * (star y ⬝ᵥ y) ≤ star y ⬝ᵥ (G *ᵥ y) := by
  set c : ℝ := ⨅ i, hG.eigenvalues i with hc
  have hbdd : BddBelow (Set.range hG.eigenvalues) := (Set.finite_range _).bddBelow
  set U : Matrix (Fin r) (Fin r) ℝ := (↑hG.eigenvectorUnitary : Matrix (Fin r) (Fin r) ℝ) with hU
  -- `G - c • 1` is positive semidefinite: it is `U · diagonal(λ - c) · Uᴴ`, a unitary conjugate of a
  -- nonnegative diagonal.
  have hUmulstar : U * Uᴴ = 1 := by
    have h := hG.eigenvectorUnitary.2
    rw [Matrix.mem_unitaryGroup_iff] at h
    -- `U * star U = 1`; `star U = Uᴴ`
    simpa [hU, Matrix.star_eq_conjTranspose] using h
  have hdiagpsd : (diagonal (fun i => hG.eigenvalues i - c)).PosSemidef :=
    PosSemidef.diagonal (fun i => sub_nonneg.mpr (ciInf_le hbdd i))
  have hconj := hdiagpsd.mul_mul_conjTranspose_same U
  -- rewrite `G - c•1` into the conjugated diagonal
  have hspec : G = U * diagonal hG.eigenvalues * Uᴴ := by
    have h := hG.spectral_theorem
    rw [Unitary.conjStarAlgAut_apply] at h
    -- `RCLike.ofReal ∘ eigenvalues = eigenvalues` over ℝ; `star U = Uᴴ`
    simpa [hU, Matrix.star_eq_conjTranspose, Function.comp_def] using h
  have hdiagc : (diagonal (fun _ : Fin r => c)) = c • (1 : Matrix (Fin r) (Fin r) ℝ) := by
    rw [← diagonal_one, ← diagonal_smul]; congr 1; funext i; simp
  have hc1 : U * diagonal (fun _ : Fin r => c) * Uᴴ = c • (1 : Matrix (Fin r) (Fin r) ℝ) := by
    rw [hdiagc, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, hUmulstar]
  -- rewrite the CONJUGATED-DIAGONAL side down to `G - c•1` (avoids rewriting `G`, on which `c` depends)
  have hrw : G - c • (1 : Matrix (Fin r) (Fin r) ℝ)
      = U * diagonal (fun i => hG.eigenvalues i - c) * Uᴴ := by
    rw [show diagonal (fun i => hG.eigenvalues i - c)
          = diagonal hG.eigenvalues - diagonal (fun _ : Fin r => c) from
          (diagonal_sub hG.eigenvalues (fun _ => c)).symm,
        mul_sub, sub_mul, hc1, ← hspec]
  have hpsd : (G - c • (1 : Matrix (Fin r) (Fin r) ℝ)).PosSemidef := by rw [hrw]; exact hconj
  -- expand the nonnegativity of the shifted quadratic form
  have hnn := hpsd.dotProduct_mulVec_nonneg y
  rw [sub_mulVec, dotProduct_sub, Matrix.smul_mulVec, one_mulVec, dotProduct_smul,
    smul_eq_mul] at hnn
  -- `hnn : 0 ≤ star y ⬝ᵥ (G *ᵥ y) - c * (star y ⬝ᵥ y)`
  linarith

/-- Each eigenvalue of a positive semidefinite matrix is at most its trace (a sum of nonnegatives). -/
theorem posSemidef_eigenvalues_le_trace {G : Matrix (Fin r) (Fin r) ℝ} (hG : G.PosSemidef)
    (i : Fin r) : hG.isHermitian.eigenvalues i ≤ Matrix.trace G := by
  rw [hG.isHermitian.trace_eq_sum_eigenvalues]
  simp only [RCLike.ofReal_real_eq_id, id]
  exact Finset.single_le_sum (fun j _ => hG.eigenvalues_nonneg j) (Finset.mem_univ i)

/-- **Positive-semidefinite determinant bound**: `det G ≤ (⨅ᵢ λᵢ) · (trace G)^{r−1}`, the product of
eigenvalues bounded by the least eigenvalue times `(r−1)` copies of the trace. Combined with the
Rayleigh bound (`⨅ᵢ λᵢ ≤ σ_min²`) and `trace ≤ r·R²` on a box, this yields
`det(gram)^{1/2} ≤ C · σ_min`, the comparison the banked `qbox` integrability consumes. -/
theorem posSemidef_det_le_iInf_mul_trace_pow {G : Matrix (Fin r) (Fin r) ℝ} (hG : G.PosSemidef)
    (hr : 0 < r) :
    G.det ≤ (⨅ i, hG.isHermitian.eigenvalues i) * (Matrix.trace G) ^ (r - 1) := by
  classical
  haveI : Nonempty (Fin r) := ⟨⟨0, hr⟩⟩
  set ev := hG.isHermitian.eigenvalues with hev
  have hbdd : BddBelow (Set.range ev) := (Set.finite_range _).bddBelow
  -- a least eigenvalue index `i₀`, and `⨅ λ = λ i₀`
  obtain ⟨i₀, -, hi₀⟩ := Finset.exists_min_image Finset.univ ev Finset.univ_nonempty
  have hmin : (⨅ i, ev i) = ev i₀ :=
    le_antisymm (ciInf_le hbdd i₀) (le_ciInf (fun j => hi₀ j (Finset.mem_univ j)))
  -- `det G = ∏ λ = λ i₀ · ∏_{j ≠ i₀} λ j`
  have hdet : G.det = ev i₀ * ∏ j ∈ Finset.univ.erase i₀, ev j := by
    rw [hG.isHermitian.det_eq_prod_eigenvalues]
    simp only [RCLike.ofReal_real_eq_id, id]
    exact (Finset.mul_prod_erase Finset.univ ev (Finset.mem_univ i₀)).symm
  rw [hmin, hdet]
  refine mul_le_mul_of_nonneg_left ?_ (hG.eigenvalues_nonneg i₀)
  -- `∏_{j ≠ i₀} λ j ≤ trace^{r-1}`, each factor in `[0, trace]`, `r-1` of them
  calc ∏ j ∈ Finset.univ.erase i₀, ev j
      ≤ ∏ _j ∈ Finset.univ.erase i₀, Matrix.trace G :=
        Finset.prod_le_prod (fun j _ => hG.eigenvalues_nonneg j)
          (fun j _ => posSemidef_eigenvalues_le_trace hG j)
    _ = (Matrix.trace G) ^ (r - 1) := by
        rw [Finset.prod_const, Finset.card_erase_of_mem (Finset.mem_univ i₀),
          Finset.card_univ, Fintype.card_fin]

end DLNFibre.DLN.RLCT
