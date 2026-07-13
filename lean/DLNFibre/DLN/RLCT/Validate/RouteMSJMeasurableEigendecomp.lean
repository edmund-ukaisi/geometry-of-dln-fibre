import DLNFibre.DLN.RLCT.Validate.RouteMSJResolution
import Mathlib.Analysis.Matrix.Spectrum

/-!
# `DLNFibre.DLN.RLCT.Validate.RouteMSJMeasurableEigendecomp` — Brick F2: `measurableEigendecomp`

The isolated Mathlib-gap primitive of Brick F. For a measurable Hermitian (real-symmetric) matrix
family `A : X → Matrix (Fin M₂) (Fin M₂) ℝ` we want a MEASURABLE sorted orthogonal diagonalization
`A z = U z · diagonal(λ↓(z)) · (U z)ᵀ`, with `λ↓` the sorted (`eigenvalues₀`) eigenvalues, themselves a
measurable function of `z`.

## Status: decomposition SKELETON — glue CLOSED, two analytic primitives ISOLATED as named sorries.

The pen-and-paper adjudication
(`expeditions/2026-06-20-aoyagi-full/threads/genm-sj5-domination/brickF-measurable-frame-adjudication.md`)
established the TRUTH-VALUE (a concrete Borel formula exists; no Kuratowski–Ryll-Nardzewski, no contour
integral). The Lean realisation, however, is a MULTI-MODULE build: a formaliser-scoping pass confirms
that EVERY primitive it needs is ABSENT from Mathlib at the v4.29 pin —

* no Weyl / eigenvalue-Lipschitz / eigenvalue-continuity lemma,
* no polynomial-root-continuity (roots as a function of coefficients),
* no Ky-Fan maximum principle `∑_{i<k} λᵢ = maxₚ tr(P·A)`,
* no compactness instance for `Matrix.unitaryGroup`,
* no measurability rider on `eigenvalues₀` (it is `Classical.choice`-built).

So each conjunct rests on a from-scratch sub-brick. This file lays the honest decomposition: the
linear-algebra GLUE (`frame_diagonalizes`) and the ASSEMBLY are CLOSED sorry-free; the two analytic
primitives (`measurableEigenvalues₀`, `exists_measurableEigenframe`) are isolated as correctly-typed
sorries carrying their build recipe, one sub-tide each.

## The decomposition

* **`measurableEigenvalues₀`** — conjunct (i). `Measurable (fun z => (hherm z).eigenvalues₀)`.
  Recipe: the Weyl-continuity brick `maxᵢ|λᵢ(A)−λᵢ(B)| ≤ ‖A−B‖_op` (⟹ Lipschitz ⟹ continuous ⟹ Borel),
  or the LSC route `Sₖ(A) = ⨆_{P rank-k orth proj} tr(P·A)` (Ky Fan) + `LowerSemicontinuous.measurable`
  with `λₖ = S_{k+1} − Sₖ`. Both need a Mathlib-absent primitive built first.

* **`exists_measurableEigenframe`** — conjunct (ii) core. A measurable orthogonal `U` whose columns are
  eigenvectors in sorted order (`A z · U z = U z · diagonal(λ↓)`). Recipe (contour-free, no KRN):
  (1) multiplicity-pattern stratification into finitely many Borel strata; (2) per-stratum Sylvester
  eigenprojection `P_a = ∏_{b≠a}(A − μ_b I)/(μ_a − μ_b)` (matrix-polynomial arithmetic + division by
  measurable eigenvalue-gaps); (3) deterministic lex-first-pivot Gram-Schmidt (`gramSchmidt` present in
  Mathlib) on each block's columns; (4) sorted concatenation. Borel, not continuous (the diabolical point
  `[[x,y],[y,−x]]` has an odd Berry phase — no global continuous frame).

* **`frame_diagonalizes`** (CLOSED) — the linear-algebra reduction: an orthogonal `U` (`Uᵀ U = 1`) whose
  columns diagonalise `A` (`A U = U · diagonal d`) gives the triple-product form `A = U · diagonal d · Uᵀ`.
  This is what turns `exists_measurableEigenframe`'s per-column eigenvector condition into the contract's
  `A z = U z · diagonal(λ↓) · (U z)ᵀ`.

* **`measurableEigendecomp`** (CLOSED assembly modulo the two primitives) — the exact F1 contract.
-/

namespace DLNFibre.DLN.RLCT

open MeasureTheory Matrix

/-- **Sorted-eigenvalue diagonal (contract indexing).** `sortedDiag hherm z i = eigenvalues₀`
reindexed value-preservingly from `Fin (Fintype.card (Fin M₂))` to `Fin M₂` — the decreasing
(`eigenvalues₀` is antitone) eigenvalue placed at position `i`. This is the diagonal appearing in the
F1 contract. -/
noncomputable def sortedDiag {X : Type*} {M₂ : ℕ}
    {A : X → Matrix (Fin M₂) (Fin M₂) ℝ} (hherm : ∀ z, (A z).IsHermitian) (z : X) :
    Fin M₂ → ℝ :=
  fun i => (hherm z).eigenvalues₀ (finCongr (Fintype.card_fin M₂).symm i)

/-- **The linear-algebra reduction (CLOSED).** For a square real matrix and an orthogonal `U`
(`Uᵀ * U = 1`) whose columns diagonalise `A` (`A * U = U * diagonal d`, i.e. each column of `U` is an
eigenvector of `A` with eigenvalue the matching diagonal entry), `A = U * diagonal d * Uᵀ`. The
right-inverse `U * Uᵀ = 1` follows from the left-inverse by `Matrix.mul_eq_one_comm` (square matrices).
-/
theorem frame_diagonalizes {n : ℕ} {A U : Matrix (Fin n) (Fin n) ℝ} {d : Fin n → ℝ}
    (hU : Uᵀ * U = 1) (hAU : A * U = U * Matrix.diagonal d) :
    A = U * Matrix.diagonal d * Uᵀ := by
  have hUU : U * Uᵀ = 1 := mul_eq_one_comm.mpr hU
  calc A = A * (U * Uᵀ) := by rw [hUU, Matrix.mul_one]
    _ = (A * U) * Uᵀ := by rw [Matrix.mul_assoc]
    _ = U * Matrix.diagonal d * Uᵀ := by rw [hAU]

/-- **Conjunct (i) — measurable sorted eigenvalues (ISOLATED sub-brick).** `eigenvalues₀` of a
measurable Hermitian family is a measurable function of the parameter. Mathlib-absent primitive.

RECIPE (Vieta + Lusin–Souslin — contour-free, no root-continuity; decorrelated-Codex first choice,
all API verified present at v4.29):
* Reusable engine `measurable_orderedRoots_of_vieta`: with `vietaCoeff (r : Fin n → ℝ) : Fin (n+1) → ℝ
  := fun k => (∏ i, (X - C (r i))).coeff k`, the map `⟨r, Antitone r⟩ ↦ vietaCoeff r` is (a) measurable
  (each coeff is `Finset.esymm` of the coords by `Multiset.prod_X_sub_C_coeff`/`Finset.esymm_map_val` —
  a finite sum of finite products of coordinate maps) and (b) injective on the antitone subtype (equal
  coeffs ⟹ equal monic degree-`n` polynomials by `Polynomial.ext` + `coeff_eq_zero_of_natDegree_lt` ⟹
  equal root-multisets by `Polynomial.roots_multiset_prod_X_sub_C` ⟹ equal decreasing sorts ⟹ equal
  tuples by `List.ofFn_inj`). The antitone subtype is `StandardBorelSpace` (`isClosed`/`IsClosed.measurableSet`
  + `MeasurableSet.standardBorel`); `Fin (n+1) → ℝ` is `StandardBorelSpace` (`StandardBorelSpace.pi_countable`)
  hence `CountablySeparated`. So `Measurable.measurableEmbedding` gives a measurable embedding, and
  `MeasurableEmbedding.measurable_comp_iff` inverts it: `Measurable (vietaCoeff ∘ f) → Measurable f`.
* Instantiate: `c z := fun k => (A z).charpoly.coeff k` is measurable (charpoly coeffs polynomial in
  entries); `r z := eigenvalues₀ (A z)` is antitone (`eigenvalues₀_antitone`) with
  `A.charpoly = ∏ (X - C (eigenvalues₀ ·))` (`charpoly_eq` reindexed by the `card_fin` bijection). -/
theorem measurableEigenvalues₀ {X : Type*} [MeasurableSpace X] {M₂ : ℕ}
    (A : X → Matrix (Fin M₂) (Fin M₂) ℝ) (hA : Measurable A)
    (hherm : ∀ z, (A z).IsHermitian) :
    Measurable (fun z => (hherm z).eigenvalues₀) := by
  sorry

/-- **Conjunct (ii) core — a measurable sorted orthonormal eigenframe (ISOLATED sub-brick).** There is a
measurable orthogonal `U` whose columns are eigenvectors of `A` in sorted (decreasing) eigenvalue order:
`A z * U z = U z * diagonal (sortedDiag hherm z)`. Mathlib-absent primitive.

RECIPE (global zero-safe Lagrange projector + measurable first-nonzero-column pivot — avoids explicit
multiplicity strata; decorrelated-Codex refinement of the pen-and-paper Sylvester+Gram-Schmidt route):
* `lagrangeProjector A λ i := ∏ j, (1 + (λ i − λ j)⁻¹ • (A − λ i • 1))`, using Lean's total inverse
  `0⁻¹ = 0`: on an eigenvector of eigenvalue `μ`, each factor acts as `1` (if `μ = λ i`, including the
  automatic `λ j = λ i` factors) or `0` (pick `j` with `λ j = μ ≠ λ i`). So `P i` is the ORTHOGONAL
  projector onto the FULL `λ i`-eigenspace, globally measurable with NO equality-pattern partition
  (the total-inverse totality absorbs the stratification).
* Build columns sequentially: with `U₍<i₎` the previously chosen columns, `R i := P i * (1 − U₍<i₎ U₍<i₎ᵀ)`
  is the projector onto the part of the `λ i`-eigenspace orthogonal to earlier columns; `R i ≠ 0` by
  multiplicity counting; `v i :=` normalize the first nonzero column of `R i` (the sole finite pivot,
  unavoidable — no continuous global frame, cf. the diabolical point). Fold over `List.finRange M₂`.
* NB (v4.29 whnf-timeout, lean/CLAUDE.md): prove the projector/recursion lemmas over ABSTRACT `A, λ,
  eigenbasis`; instantiate `eigenvalues₀`/`eigenvectorBasis` only in thin terminal `…Aux` lemmas
  (`set` is insufficient; syntactic `rw`, not `unfold`). -/
theorem exists_measurableEigenframe {X : Type*} [MeasurableSpace X] {M₂ : ℕ}
    (A : X → Matrix (Fin M₂) (Fin M₂) ℝ) (hA : Measurable A)
    (hherm : ∀ z, (A z).IsHermitian) :
    ∃ U : X → Matrix (Fin M₂) (Fin M₂) ℝ,
      Measurable U ∧ (∀ z, (U z)ᵀ * U z = 1) ∧
        (∀ z, A z * U z = U z * Matrix.diagonal (sortedDiag hherm z)) := by
  sorry

/-- **Brick F2 — measurable sorted eigendecomposition (F1 contract).** ASSEMBLED sorry-free from the two
isolated analytic primitives via the `frame_diagonalizes` reduction. -/
theorem measurableEigendecomp {X : Type*} [MeasurableSpace X] {M₂ : ℕ}
    (A : X → Matrix (Fin M₂) (Fin M₂) ℝ) (hA : Measurable A)
    (hherm : ∀ z, (A z).IsHermitian) :
    Measurable (fun z => (hherm z).eigenvalues₀) ∧
      ∃ U : X → Matrix (Fin M₂) (Fin M₂) ℝ,
        Measurable U ∧ (∀ z, (U z)ᵀ * U z = 1) ∧
          (∀ z, A z = U z *
            Matrix.diagonal (fun i => (hherm z).eigenvalues₀ (finCongr (Fintype.card_fin M₂).symm i))
            * (U z)ᵀ) := by
  refine ⟨measurableEigenvalues₀ A hA hherm, ?_⟩
  obtain ⟨U, hUmeas, hUorth, hUdiag⟩ := exists_measurableEigenframe A hA hherm
  exact ⟨U, hUmeas, hUorth, fun z => frame_diagonalizes (hUorth z) (hUdiag z)⟩

end DLNFibre.DLN.RLCT
