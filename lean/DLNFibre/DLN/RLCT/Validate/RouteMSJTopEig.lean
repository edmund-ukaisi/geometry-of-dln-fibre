import DLNFibre.DLN.RLCT.Validate.RouteMSJRayleigh
import DLNFibre.DLN.RLCT.Validate.RouteMSJGammaAtom
import DLNFibre.DLN.RLCT.Validate.RouteMSJProductTube

set_option linter.style.longLine false

/-!
# `RouteMSJTopEig` — the leading-singular-slice lower bound (ℓ=0 twoBlock spectral sub-brick)

**Thread `genm-3abase` (aoyagi-full Stage 2), Brick A ℓ=0 corner (reassembly-cert §4).** The biquadratic
corner `‖Y·W‖²` closes through `twoBlock_radial_le` with the σ-scaled block being the LEADING left-singular
slice `Y·e` (`d_v = M₀`, NOT all of `Y` — that would need a Loewner floor, the failure mode). The core:

    ∃ e, ‖e‖=1 ∧ (frobSq W / u) · ‖Y·e‖² ≤ frobSq (Y · W).

Proof: `W·Wᵀ = U·diag(λ)·Uᵀ` (spectral theorem), `frobSq (Y·W) = tr(Y·(W·Wᵀ)·Yᵀ) = ∑ₖ λₖ·‖Y·eₖ‖²`
(`eₖ = U col k` orthonormal), drop all but the top-eigenvalue term (`Finset.single_le_sum`), and
`λ_max ≥ (∑λ)/u = frobSq W / u` (max ≥ average). Feeds the ℓ=0 corner monotonicity into `twoBlock_radial_le`.
-/

namespace DLNFibre.DLN.RLCT

open Matrix
open scoped BigOperators

variable {m u d : ℕ}

/-- **Trace of a conjugated diagonal = weighted column-norms.** `tr(C · diagonal λ · Cᵀ) = ∑ₖ λₖ·∑ᵢ Cᵢₖ²`.
Pure matrix algebra (no spectral). -/
theorem traceConjDiag_eq_weightedCols (C : Matrix (Fin m) (Fin u) ℝ) (lam : Fin u → ℝ) :
    Matrix.trace (C * diagonal lam * Cᵀ) = ∑ k, lam k * ∑ i, (C i k) ^ 2 := by
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, Matrix.transpose_apply,
    Matrix.diagonal_apply]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [Finset.sum_eq_single k (fun l _ hl => by rw [if_neg hl, mul_zero])
      (fun h => absurd (Finset.mem_univ k) h), if_pos rfl]
  ring

/-- **The leading-singular-slice lower bound (ℓ=0 spectral sub-brick, reassembly-cert §4).** There is a
unit vector `e` (the top eigenvector of `W·Wᵀ`) with `(frobSq W / u) · ‖Y·e‖² ≤ frobSq (Y·W)`. The σ-scaled
block `Y·e` is `M₀`-dimensional (the leading slice), so `twoBlock_radial_le` applies with NO external
Loewner floor (the §4 droppable-frame construction). -/
theorem frobSq_mul_ge_top_slice [NeZero u] (Y : Matrix (Fin m) (Fin u) ℝ)
    (W : Matrix (Fin u) (Fin d) ℝ) :
    ∃ e : Fin u → ℝ, e ⬝ᵥ e = 1 ∧
      (frobSq W / u) * (Y.mulVec e ⬝ᵥ Y.mulVec e) ≤ frobSq (Y * W) := by
  classical
  have hdsn : ∀ v : Fin m → ℝ, (0 : ℝ) ≤ v ⬝ᵥ v :=
    fun v => Finset.sum_nonneg fun i _ => mul_self_nonneg (v i)
  set G : Matrix (Fin u) (Fin u) ℝ := W * Wᵀ with hGdef
  have hpsd : G.PosSemidef := posSemidef_mul_transpose W
  have hHerm : G.IsHermitian := hpsd.isHermitian
  set lam := hHerm.eigenvalues with hlam
  set U : Matrix (Fin u) (Fin u) ℝ := (↑hHerm.eigenvectorUnitary : Matrix (Fin u) (Fin u) ℝ) with hU
  -- spectral form `G = U · diagonal lam · Uᵀ` (as in `gram_rayleigh_lb`)
  have hspec : G = U * diagonal lam * Uᵀ := by
    have h := hHerm.spectral_theorem
    rw [Unitary.conjStarAlgAut_apply] at h
    simpa [hU, Matrix.star_eq_conjTranspose, Function.comp_def] using h
  -- eigenvector columns `e k`, each a unit vector (`Uᵀ · U = 1`)
  have hUtU : Uᵀ * U = 1 := by
    have h := hHerm.eigenvectorUnitary.2
    rw [Matrix.mem_unitaryGroup_iff'] at h
    simpa [hU, Matrix.star_eq_conjTranspose] using h
  set e : Fin u → (Fin u → ℝ) := fun k j => U j k with he
  have heunit : ∀ k, e k ⬝ᵥ e k = 1 := by
    intro k
    have hc := congrFun (congrFun hUtU k) k
    simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply_eq] at hc
    simpa [he, dotProduct] using hc
  -- the spectral expansion `frobSq (Y·W) = ∑ k, lam k · ‖Y·e k‖²`
  have hcol : ∀ k, (Y.mulVec (e k) ⬝ᵥ Y.mulVec (e k)) = ∑ i, ((Y * U) i k) ^ 2 := by
    intro k
    rw [dotProduct]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [sq]; congr 1
  have hexp : frobSq (Y * W) = ∑ k, lam k * (Y.mulVec (e k) ⬝ᵥ Y.mulVec (e k)) := by
    rw [frobSq_eq_trace]
    have h1 : (Y * W) * (Y * W)ᵀ = (Y * U) * diagonal lam * (Y * U)ᵀ := by
      have hexpand : (Y * W) * (Y * W)ᵀ = Y * (W * Wᵀ) * Yᵀ := by
        simp only [Matrix.transpose_mul, Matrix.mul_assoc]
      rw [hexpand, ← hGdef, hspec]
      simp only [Matrix.transpose_mul, Matrix.mul_assoc]
    rw [h1, traceConjDiag_eq_weightedCols]
    exact Finset.sum_congr rfl (fun k _ => by rw [hcol])
  -- select the top eigenvalue `k₀`
  obtain ⟨k₀, -, hk₀⟩ := Finset.exists_max_image Finset.univ lam Finset.univ_nonempty
  refine ⟨e k₀, heunit k₀, ?_⟩
  -- `lam k₀ ≥ frobSq W / u` (max ≥ average, and `∑ lam = trace G = frobSq W`)
  have hsum_lam : ∑ k, lam k = frobSq W := by
    have ht : Matrix.trace G = ∑ k, lam k := by
      rw [hlam, hHerm.trace_eq_sum_eigenvalues]; simp
    rw [← ht, hGdef, ← frobSq_eq_trace]
  have hu0 : 0 < (u : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne u)
  have havg : frobSq W / u ≤ lam k₀ := by
    rw [div_le_iff₀ hu0, ← hsum_lam]
    calc (∑ k, lam k) ≤ ∑ _k : Fin u, lam k₀ :=
          Finset.sum_le_sum (fun k _ => hk₀ k (Finset.mem_univ k))
      _ = lam k₀ * u := by rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
                              mul_comm]
  -- drop all but the `k₀` term (each `lam k · ‖Y e k‖² ≥ 0`)
  have hnn : ∀ k ∈ Finset.univ, 0 ≤ lam k * (Y.mulVec (e k) ⬝ᵥ Y.mulVec (e k)) := fun k _ =>
    mul_nonneg (hpsd.eigenvalues_nonneg k) (hdsn _)
  calc (frobSq W / u) * (Y.mulVec (e k₀) ⬝ᵥ Y.mulVec (e k₀))
      ≤ lam k₀ * (Y.mulVec (e k₀) ⬝ᵥ Y.mulVec (e k₀)) :=
        mul_le_mul_of_nonneg_right havg (hdsn _)
    _ ≤ ∑ k, lam k * (Y.mulVec (e k) ⬝ᵥ Y.mulVec (e k)) :=
        Finset.single_le_sum hnn (Finset.mem_univ k₀)
    _ = frobSq (Y * W) := hexp.symm

end DLNFibre.DLN.RLCT
