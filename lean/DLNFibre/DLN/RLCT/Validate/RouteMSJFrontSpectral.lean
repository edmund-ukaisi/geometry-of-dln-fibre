import DLNFibre.DLN.RLCT.Validate.RouteMSJProductTube
import DLNFibre.DLN.RLCT.Validate.RouteMSJGammaAtom

set_option linter.style.longLine false

/-!
# `DLNFibre.DLN.RLCT.Validate.RouteMSJFrontSpectral` — the front-loss Frobenius–Gram spectral identity and the u-block sector

**Thread `genm-…` (aoyagi-full), pieces (2)+(3-defs) of the (3,3,3,4) vslice step (a) chart reduction.**
The front-first majorant of step (a) needs the front loss `‖A₀·P‖_F²` (`frobSq (A₀·P)`) diagonalised into
a **two-block radial** form: one collapsing direction (the smallest Gram eigenvalue = `sigMin`²) and a
bounded-below complement (`d_u` directions with weight `≥ κ²`). This module builds the pieces of that
diagonalisation that are **structure-independent** (they do NOT rest on the still-open "which region is the
sector" question):

* **(2) The Frobenius–Gram spectral identity** `frobSq (A₀·P) = ∑_j λ_j · ‖(A₀·Q)_{·j}‖²`, where
  `λ = eigenvalues(P·Pᵀ)` and `Q = eigenvectorUnitary(P·Pᵀ)` (the spectral basis of the Gram). Proved via
  `frobSq (A₀·P) = trace(A₀·(P·Pᵀ)·A₀ᵀ)` and `spectral_theorem` on the Hermitian Gram (the banked
  `posSemidef_mul_transpose`). NO SVD of `P` itself — only the spectral decomposition of the `r×r` Gram.
  * (`frobSq M = trace(M·Mᵀ)` is the banked `RouteMSJGammaAtom.frobSq_eq_trace`.)
  * `trace_conj_hermitian_eq_sum_eigenvalues` — the reusable trace-diagonalisation (general Hermitian `G`).
  * `frobSq_mul_eq_sum_eigenvalues` — the headline identity.

* **The min-eigenvalue = `sigMin`² equality** `sigMin P ^ 2 = ⨅_j λ_j` — completes the banked one-sided
  `iInf_eigenvalues_le_sigMin_sq` to an equality (the reverse via the achieving unit eigenvector), so the
  collapsing v-block weight is exactly `sigMin`², connecting to the LAYER-2 `sigMin^{−α}` integrability.

* **(3-defs) The collapsing index and the u-block sector.** `collapseIndex` — an argmin of the Gram
  eigenvalues (the collapsing direction). `sjSector κ P` — the sector predicate "every non-collapsing Gram
  eigenvalue is `≥ κ²`" (option A: a min over the finite index set MINUS the argmin, **no** eigenvalue
  sorting). `sjSector_iff_iInf` records the `⨅`-form. `frobSq_ge_twoBlock_of_sector` — **the bridge to the
  two-block radial**: on the sector, `frobSq (A₀·P) ≥ (⨅ λ)·(v-block) + κ²·(u-block)`, the exact shape the
  banked `twoBlock_radial_le` consumes. Here the sector is an INPUT HYPOTHESIS, not derived — the
  sector-from-region bridge (3iii) and the sector's measurability (3ii) are HELD pending the structure
  adjudication.

Network-free (pure matrix spectral theory). Axiom-clean `[propext, Classical.choice, Quot.sound]`.
-/

namespace DLNFibre.DLN.RLCT

open Matrix MeasureTheory
open scoped BigOperators InnerProductSpace ENNReal

variable {m r n : ℕ}

/-! ## Part A — the Frobenius–Gram spectral identity (piece 2) -/

/-- **The real spectral decomposition** `G = U · diagonal(eigenvalues) · Uᵀ`, `U = eigenvectorUnitary`. -/
theorem isHermitian_eq_eigenvectorUnitary_conj {G : Matrix (Fin r) (Fin r) ℝ} (hG : G.IsHermitian) :
    G = (hG.eigenvectorUnitary : Matrix (Fin r) (Fin r) ℝ) * diagonal hG.eigenvalues
          * (hG.eigenvectorUnitary : Matrix (Fin r) (Fin r) ℝ)ᵀ := by
  have h := hG.spectral_theorem
  rw [Unitary.conjStarAlgAut_apply] at h
  simpa [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial,
    Function.comp_def] using h

/-- **Trace diagonalisation** `trace (Y · diagonal d · Yᵀ) = ∑ j, d j · ∑ i, (Y i j)²`. -/
theorem trace_mul_diagonal_mul_transpose (Y : Matrix (Fin m) (Fin r) ℝ) (d : Fin r → ℝ) :
    Matrix.trace (Y * diagonal d * Yᵀ) = ∑ j, d j * ∑ i, (Y i j) ^ 2 := by
  have hi : ∀ i, (Y * diagonal d * Yᵀ) i i = ∑ k, d k * (Y i k) ^ 2 := by
    intro i
    rw [Matrix.mul_apply]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [Matrix.mul_diagonal, Matrix.transpose_apply]
    ring
  rw [Matrix.trace]
  calc ∑ i, (Y * diagonal d * Yᵀ).diag i
      = ∑ i, ∑ k, d k * (Y i k) ^ 2 := by
        refine Finset.sum_congr rfl (fun i _ => ?_); rw [Matrix.diag_apply]; exact hi i
    _ = ∑ k, ∑ i, d k * (Y i k) ^ 2 := Finset.sum_comm
    _ = ∑ k, d k * ∑ i, (Y i k) ^ 2 := by
        refine Finset.sum_congr rfl (fun k _ => ?_); rw [Finset.mul_sum]

/-- **The reusable trace-diagonalisation of a conjugated Hermitian matrix** (general `G`): for Hermitian
`G` with spectral data `(λ, U)`, the conjugated trace `trace (A₀·G·A₀ᵀ)` diagonalises to
`∑ j, λ_j · ‖(A₀·U)_{·j}‖²`. This is the algebraic heart of the Frobenius–Gram identity. -/
theorem trace_conj_hermitian_eq_sum_eigenvalues (A₀ : Matrix (Fin m) (Fin r) ℝ)
    {G : Matrix (Fin r) (Fin r) ℝ} (hG : G.IsHermitian) :
    Matrix.trace (A₀ * G * A₀ᵀ)
      = ∑ j, hG.eigenvalues j *
          ∑ i, ((A₀ * (hG.eigenvectorUnitary : Matrix (Fin r) (Fin r) ℝ)) i j) ^ 2 := by
  set U : Matrix (Fin r) (Fin r) ℝ := (hG.eigenvectorUnitary : Matrix (Fin r) (Fin r) ℝ) with hU
  have hspec := isHermitian_eq_eigenvectorUnitary_conj hG
  rw [← hU] at hspec
  have key : A₀ * G * A₀ᵀ = (A₀ * U) * diagonal hG.eigenvalues * (A₀ * U)ᵀ := by
    conv_lhs => rw [hspec]
    simp only [Matrix.transpose_mul, Matrix.mul_assoc]
  rw [key, trace_mul_diagonal_mul_transpose]

/-- **(2) The Frobenius–Gram spectral identity.** The front loss `frobSq (A₀·P)` diagonalises as
`∑_j λ_j · ‖(A₀·Q)_{·j}‖²`, where `λ = eigenvalues(P·Pᵀ)` and `Q = eigenvectorUnitary(P·Pᵀ)`. This is the
form the two-block radial consumes (the `j`-th column of `A₀·Q` carries the `j`-th Gram eigen-direction). -/
theorem frobSq_mul_eq_sum_eigenvalues (A₀ : Matrix (Fin m) (Fin r) ℝ)
    (P : Matrix (Fin r) (Fin n) ℝ) :
    frobSq (A₀ * P)
      = ∑ j, (posSemidef_mul_transpose P).isHermitian.eigenvalues j *
          ∑ i, ((A₀ * ((posSemidef_mul_transpose P).isHermitian.eigenvectorUnitary :
            Matrix (Fin r) (Fin r) ℝ)) i j) ^ 2 := by
  rw [frobSq_eq_trace]
  have hPP : (A₀ * P) * (A₀ * P)ᵀ = A₀ * (P * Pᵀ) * A₀ᵀ := by
    simp only [Matrix.transpose_mul, Matrix.mul_assoc]
  rw [hPP]
  exact trace_conj_hermitian_eq_sum_eigenvalues A₀ (posSemidef_mul_transpose P).isHermitian

/-! ## Part B — the min-eigenvalue = `sigMin`² equality -/

/-- **The reverse Rayleigh bound** `sigMin P ^ 2 ≤ ⨅ j, eigenvalues(P·Pᵀ) j`: for EACH index `i` the
`i`-th unit eigenvector realises `‖Pᵀ v‖² = λ_i`, so `sigMin P ≤ √λ_i`, i.e. `sigMin P ^ 2 ≤ λ_i`;
taking the infimum over `i` (`le_ciInf`) gives the bound. Together with the banked
`iInf_eigenvalues_le_sigMin_sq` this yields the equality below. -/
theorem sigMin_sq_le_iInf_eigenvalues (P : Matrix (Fin r) (Fin n) ℝ) (hr : 0 < r) :
    sigMin P ^ 2 ≤ ⨅ i, (posSemidef_mul_transpose P).isHermitian.eigenvalues i := by
  haveI : Nonempty (Fin r) := ⟨⟨0, hr⟩⟩
  haveI : Nontrivial (EuclideanSpace ℝ (Fin r)) :=
    Module.nontrivial_of_finrank_pos (R := ℝ) (by rw [finrank_euclideanSpace_fin]; exact hr)
  set hG := posSemidef_mul_transpose P with hGdef
  refine le_ciInf (fun i => ?_)
  -- the `i`-th unit eigenvector `v` of the Gram, seen in `EuclideanSpace`
  set v : EuclideanSpace ℝ (Fin r) := hG.isHermitian.eigenvectorBasis i with hv
  have hvnorm : ‖v‖ = 1 := hG.isHermitian.eigenvectorBasis.orthonormal.1 i
  -- `‖sigMinCLM P v‖² = eigenvalues i`
  have hquad : ‖sigMinCLM P v‖ ^ 2 = hG.isHermitian.eigenvalues i := by
    rw [norm_sq_sigMinCLM]
    -- `(P·Pᵀ) *ᵥ (ofLp v) = eigenvalues i • (ofLp v)`, then `star v ⬝ᵥ (λ • v) = λ · ‖v‖² = λ`
    have hev : (P * Pᵀ) *ᵥ (WithLp.ofLp v) = hG.isHermitian.eigenvalues i • (WithLp.ofLp v) := by
      have h := hG.isHermitian.mulVec_eigenvectorBasis i
      simpa [hv] using h
    rw [hev, dotProduct_smul, smul_eq_mul, dotProduct_ofLp_self, hvnorm, one_pow, mul_one]
  -- `sigMin P ≤ ‖sigMinCLM P v‖` since `v` is a unit vector
  have hstretch : sigMin P ≤ ‖sigMinCLM P v‖ := by
    have h := minStretch_mul_le (sigMinCLM P) v
    rwa [hvnorm, mul_one] at h
  have hsig0 : 0 ≤ sigMin P := sigMin_nonneg P hr
  calc sigMin P ^ 2 ≤ ‖sigMinCLM P v‖ ^ 2 := by
        exact pow_le_pow_left₀ hsig0 hstretch 2
    _ = hG.isHermitian.eigenvalues i := hquad

/-- **The min Gram-eigenvalue equals `sigMin`²** — the collapsing v-block weight is exactly `sigMin P ^ 2`.
Combines the banked `iInf_eigenvalues_le_sigMin_sq` (`≤`) with `sigMin_sq_le_iInf_eigenvalues` (`≥`). -/
theorem sigMin_sq_eq_iInf_eigenvalues (P : Matrix (Fin r) (Fin n) ℝ) (hr : 0 < r) :
    sigMin P ^ 2 = ⨅ i, (posSemidef_mul_transpose P).isHermitian.eigenvalues i :=
  le_antisymm (sigMin_sq_le_iInf_eigenvalues P hr) (iInf_eigenvalues_le_sigMin_sq P hr)

/-! ## Part C — the collapsing index and the u-block sector (piece 3-defs) -/

/-- The finite family of Gram eigenvalues attains a minimum (`Fin r` nonempty via `hr`). -/
theorem exists_argmin_eigenvalues (P : Matrix (Fin r) (Fin n) ℝ) (hr : 0 < r) :
    ∃ i₀ : Fin r, ∀ j, (posSemidef_mul_transpose P).isHermitian.eigenvalues i₀
      ≤ (posSemidef_mul_transpose P).isHermitian.eigenvalues j := by
  haveI : Nonempty (Fin r) := ⟨⟨0, hr⟩⟩
  obtain ⟨i₀, -, hi₀⟩ :=
    Finset.exists_min_image Finset.univ (posSemidef_mul_transpose P).isHermitian.eigenvalues
      Finset.univ_nonempty
  exact ⟨i₀, fun j => hi₀ j (Finset.mem_univ j)⟩

/-- **The collapsing index** — an argmin of the Gram eigenvalues (the smallest-singular-value direction).
Chosen by `exists_argmin_eigenvalues`; its defining minimality is `collapseIndex_le`. -/
noncomputable def collapseIndex (P : Matrix (Fin r) (Fin n) ℝ) (hr : 0 < r) : Fin r :=
  (exists_argmin_eigenvalues P hr).choose

/-- The collapsing index minimises the Gram eigenvalues. -/
theorem collapseIndex_le (P : Matrix (Fin r) (Fin n) ℝ) (hr : 0 < r) (j : Fin r) :
    (posSemidef_mul_transpose P).isHermitian.eigenvalues (collapseIndex P hr)
      ≤ (posSemidef_mul_transpose P).isHermitian.eigenvalues j :=
  (exists_argmin_eigenvalues P hr).choose_spec j

/-- The collapsing eigenvalue is the infimum eigenvalue (`= sigMin`² by `sigMin_sq_eq_iInf_eigenvalues`). -/
theorem eigenvalues_collapseIndex_eq_iInf (P : Matrix (Fin r) (Fin n) ℝ) (hr : 0 < r) :
    (posSemidef_mul_transpose P).isHermitian.eigenvalues (collapseIndex P hr)
      = ⨅ i, (posSemidef_mul_transpose P).isHermitian.eigenvalues i := by
  haveI : Nonempty (Fin r) := ⟨⟨0, hr⟩⟩
  have hbdd : BddBelow (Set.range (posSemidef_mul_transpose P).isHermitian.eigenvalues) :=
    (Set.finite_range _).bddBelow
  exact le_antisymm (le_ciInf (collapseIndex_le P hr)) (ciInf_le hbdd _)

/-- **(3) The u-block sector** (option A, sorting-free): every Gram eigenvalue OTHER than the collapsing
one is `≥ κ²`. Equivalently `κ² ≤ ⨅_{j ≠ collapseIndex} eigenvalue(P·Pᵀ) j` (`sjSector_iff_iInf`). This is
exactly the region where the two-block radial's u-block weight is bounded below. -/
def sjSector (κ : ℝ) (P : Matrix (Fin r) (Fin n) ℝ) (hr : 0 < r) : Prop :=
  ∀ j : Fin r, j ≠ collapseIndex P hr → κ ^ 2 ≤ (posSemidef_mul_transpose P).isHermitian.eigenvalues j

/-- The sector, in the `⨅`-over-the-complement form of option A (needs the complement nonempty, i.e.
`2 ≤ r`; for the (3,3,3,4) vslice `r = 3`, so `hne` holds — see the non-vacuity example). For `r = 1` the
`⨅` over the empty complement is the junk `sInf ∅`, so the `⨅`-form is only equivalent when `hne`. -/
theorem sjSector_iff_iInf (κ : ℝ) (P : Matrix (Fin r) (Fin n) ℝ) (hr : 0 < r)
    (hne : Nonempty {j : Fin r // j ≠ collapseIndex P hr}) :
    sjSector κ P hr ↔
      κ ^ 2 ≤ ⨅ j : {j : Fin r // j ≠ collapseIndex P hr},
        (posSemidef_mul_transpose P).isHermitian.eigenvalues j := by
  haveI := hne
  have hbdd : BddBelow (Set.range (fun j : {j : Fin r // j ≠ collapseIndex P hr} =>
      (posSemidef_mul_transpose P).isHermitian.eigenvalues j)) := (Set.finite_range _).bddBelow
  constructor
  · intro h; exact le_ciInf (fun j => h j.1 j.2)
  · intro h j hj; exact h.trans (ciInf_le hbdd ⟨j, hj⟩)

/-- **The bridge to the two-block radial.** On the sector, the front loss dominates the two-block form
`(⨅ λ)·‖(A₀·Q)_{·collapse}‖² + κ²·∑_{j ≠ collapse} ‖(A₀·Q)_{·j}‖²` — a collapsing v-block (weight `= ⨅ λ =
sigMin`², `d_v = m`) plus a bounded-below u-block (weight `≥ κ²`, `d_u = m·(r−1)`). The sector is an INPUT
hypothesis here (the sector-from-region bridge is held). Directly from the Frobenius–Gram identity. -/
theorem frobSq_ge_twoBlock_of_sector (A₀ : Matrix (Fin m) (Fin r) ℝ) (P : Matrix (Fin r) (Fin n) ℝ)
    (hr : 0 < r) {κ : ℝ} (hsec : sjSector κ P hr) :
    (⨅ i, (posSemidef_mul_transpose P).isHermitian.eigenvalues i) *
        (∑ i, ((A₀ * ((posSemidef_mul_transpose P).isHermitian.eigenvectorUnitary :
          Matrix (Fin r) (Fin r) ℝ)) i (collapseIndex P hr)) ^ 2)
      + κ ^ 2 * (∑ j ∈ Finset.univ.erase (collapseIndex P hr),
          ∑ i, ((A₀ * ((posSemidef_mul_transpose P).isHermitian.eigenvectorUnitary :
            Matrix (Fin r) (Fin r) ℝ)) i j) ^ 2)
      ≤ frobSq (A₀ * P) := by
  classical
  -- rewrite the loss with the Frobenius–Gram identity, THEN fold the spectral data
  rw [frobSq_mul_eq_sum_eigenvalues A₀ P]
  set e := (posSemidef_mul_transpose P).isHermitian.eigenvalues with he
  set Q : Matrix (Fin r) (Fin r) ℝ :=
    ((posSemidef_mul_transpose P).isHermitian.eigenvectorUnitary : Matrix (Fin r) (Fin r) ℝ) with hQ
  set c := collapseIndex P hr with hc
  -- split the RHS sum at the collapsing index `c`
  rw [← Finset.add_sum_erase Finset.univ (fun j => e j * ∑ i, ((A₀ * Q) i j) ^ 2)
    (Finset.mem_univ c)]
  -- the collapsing eigenvalue equals ⨅ λ
  have hcieq : e c = ⨅ i, e i := eigenvalues_collapseIndex_eq_iInf P hr
  rw [hcieq]
  -- bound the erased sum below by κ² · (u-block)
  have hlow : κ ^ 2 * (∑ j ∈ Finset.univ.erase c, ∑ i, ((A₀ * Q) i j) ^ 2)
      ≤ ∑ j ∈ Finset.univ.erase c, e j * ∑ i, ((A₀ * Q) i j) ^ 2 := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum (fun j hj => ?_)
    exact mul_le_mul_of_nonneg_right (hsec j (Finset.ne_of_mem_erase hj))
      (Finset.sum_nonneg (fun i _ => sq_nonneg _))
  linarith [hlow]

/-! ## Part E — the orthogonal change of variables (piece 2b) -/

/-- An orthogonal matrix (`Q · Qᵀ = 1`) has `det Q · det Q = 1`. -/
theorem det_mul_self_of_orth {q : ℕ} {Q : Matrix (Fin q) (Fin q) ℝ} (hQ : Q * Qᵀ = 1) :
    Q.det * Q.det = 1 := by
  have h := congrArg Matrix.det hQ
  rw [Matrix.det_mul, Matrix.det_transpose, Matrix.det_one] at h
  exact h

/-- **The orthogonal right-multiplication change of variables (measure-preserving).** For orthogonal `Q`
(`Q · Qᵀ = 1`), precomposing an integrand with the per-row right-multiplication `Γ ↦ (Γ_i ᵥ* Q)_i =
Γ · Q` preserves the full-space Lebesgue integral — the Jacobian `|det Q|^p = 1`. Specialises the banked
`lintegral_comp_rightMulₚ` (which already navigates the `Matrix.module` vs `NormedSpace` diamond via the
raw pi type). This is the CoV that turns `A₀ ↦ A₀·Q` (rotating the front factor into the Gram spectral
basis) into a measure-preserving relabelling. -/
theorem lintegral_comp_orthRightMulₚ (p : ℕ) {q : ℕ} (Q : Matrix (Fin q) (Fin q) ℝ)
    (hQ : Q * Qᵀ = 1) (g : (Fin p → Fin q → ℝ) → ℝ≥0∞) (hg : Measurable g) :
    ∫⁻ Γ : Fin p → Fin q → ℝ, g (fun i => Γ i ᵥ* Q)
      = ∫⁻ Γ : Fin p → Fin q → ℝ, g Γ := by
  have hself : Q.det * Q.det = 1 := det_mul_self_of_orth hQ
  have hdet : Q.det ≠ 0 := by
    intro h0; rw [h0, mul_zero] at hself; exact one_ne_zero hself.symm
  have habs : |Q.det| ^ p = 1 := by
    have hcases : Q.det = 1 ∨ Q.det = -1 := mul_self_eq_one_iff.mp hself
    have h1 : |Q.det| = 1 := by rcases hcases with h | h <;> rw [h] <;> norm_num
    rw [h1, one_pow]
  rw [lintegral_comp_rightMulₚ p Q hdet g hg, habs, inv_one, ENNReal.ofReal_one, one_mul]

/-- The per-row right-multiplication `fun i ↦ Γ_i ᵥ* Q` equals the raw matrix product `rmatMul Γ Q`. -/
theorem rmatMul_eq_vecMul_rows {p q : ℕ} (Γ : Fin p → Fin q → ℝ) (Q : Matrix (Fin q) (Fin q) ℝ) :
    rmatMul Γ Q = fun i => Γ i ᵥ* Q := by
  funext i j
  rw [rmatMul, Matrix.vecMul_eq_sum, Finset.sum_apply]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [Pi.smul_apply, smul_eq_mul]

/-- **The orthogonal CoV, `rmatMul` form.** For orthogonal `Q`, precomposing with `Γ ↦ rmatMul Γ Q`
preserves the full-space integral — the directly composable form for the `ProductTube`/`rmatMul` front
factor. -/
theorem lintegral_comp_rmatMul_orth (p : ℕ) {q : ℕ} (Q : Matrix (Fin q) (Fin q) ℝ)
    (hQ : Q * Qᵀ = 1) (g : (Fin p → Fin q → ℝ) → ℝ≥0∞) (hg : Measurable g) :
    ∫⁻ Γ : Fin p → Fin q → ℝ, g (rmatMul Γ Q) = ∫⁻ Γ : Fin p → Fin q → ℝ, g Γ := by
  simp only [rmatMul_eq_vecMul_rows]
  exact lintegral_comp_orthRightMulₚ p Q hQ g hg

/-! ## Part D — non-vacuity -/

/-- **Non-vacuity of the Frobenius–Gram identity.** For the identity `1×1` front (`A₀ = 1`) and any `P`,
`frobSq P = ∑_j λ_j · ‖Q_{·j}‖²` — the loss reads off the Gram spectrum, the identity is not vacuous. -/
example (P : Matrix (Fin r) (Fin n) ℝ) :
    frobSq ((1 : Matrix (Fin r) (Fin r) ℝ) * P)
      = ∑ j, (posSemidef_mul_transpose P).isHermitian.eigenvalues j *
          ∑ i, (((1 : Matrix (Fin r) (Fin r) ℝ) *
            ((posSemidef_mul_transpose P).isHermitian.eigenvectorUnitary :
              Matrix (Fin r) (Fin r) ℝ)) i j) ^ 2 :=
  frobSq_mul_eq_sum_eigenvalues 1 P

end DLNFibre.DLN.RLCT
