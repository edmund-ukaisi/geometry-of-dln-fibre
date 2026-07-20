import DLNFibre.DLN.RLCT.Validate.RouteMSJCorankResidual
import DLNFibre.Core.RankLocusClosed
import DLNFibre.Core.MeasureTheory.PolynomialZeroSet

/-!
# `DLNFibre.DLN.RLCT.Validate.RouteMSJCorankSurvival` — AG-free free-matrix corank survival (#2b)

**Thread `genm-sj5-desc2`, piece #2 of the §5 decorated-descent discharge — the free-`A_cor` corank
survival (`transversality-recursion.md §8`; controller's #2 part (b)).**

The transversality's corank-survival core, AG-FREE (genericity in the FREE integration variable
`A`, minor-cut null set — D1-lane — NOT generic-rank-on-a-variety-component):

> For a FIXED deeper product `Zdeep` of rank `≥ b`, a.e. free block `A : Fin b → Fin m → ℝ` has
> `rank (A · Zdeep) = b`.

This is what makes the `b` free corank rows survive full-row-rank `b` through a rank-`≥ b` deeper
product (`p = 0`). The rank of `Zdeep` is an INPUT (`b ≤ Zdeep.rank`, supplied combinatorially by
#1's `ρ ≥ b`); no irreducible-component decomposition, no generic rank on a component.

## Proof (minor-cut null set)

`rank (A·Zdeep) ≤ b` always (`b` rows). The deficient set `{A | rank < b}` is contained in the zero
set of ONE fixed `b×b` minor `det ((A·Zdeep).submatrix id ec)` (banked `Core.RankLocusClosed`
`submatrix_det_eq_zero_of_rank_le`). That minor is `eval A P` for a fixed polynomial `P` (matrix
product commutes with `eval`, `RingHom.map_det`); `P ≠ 0` because a **row-selection** witness `A₀`
(one-hot on the `b` independent rows `er` from `exists_submatrix_det_ne_zero_of_le_rank`) gives
`A₀·Zdeep = Zdeep.submatrix er id`, whose `ec`-minor is the nonzero `det (Zdeep.submatrix er ec)`.
A nonzero polynomial's zero set is Lebesgue-null
(`PolynomialZeroSet.MvPolynomial.ae_eval_ne_zero`), transported to the matrix box by the
measure-preserving flatten `eMatFlat` (banked `measurePreserving_eMatFlat`).

Axiom-clean `[propext, Classical.choice, Quot.sound]`.
-/

open MeasureTheory Matrix MvPolynomial
open scoped BigOperators

namespace DLNFibre.DLN.RLCT

/-! ## The matrix-shaped a.e.-nonzero corollary of `ae_eval_ne_zero` -/

/-- **A nonzero polynomial in the matrix entries is a.e. nonzero on the matrix box.** For
`P : MvPolynomial (Fin b × Fin m) ℝ` with `P ≠ 0`, a.e. `A : Fin b → Fin m → ℝ` has
`eval (fun ij ↦ A ij.1 ij.2) P ≠ 0`. Relabels the `Fin b × Fin m` variables to `Fin (b*m)` by
`finProdFinEquiv` (`rename`), applies the banked `ae_eval_ne_zero`, and transports the null zero-set
back along the measure-preserving flatten `eMatFlat`. -/
theorem ae_matrix_eval_ne_zero {b m : ℕ} (P : MvPolynomial (Fin b × Fin m) ℝ) (hP : P ≠ 0) :
    ∀ᵐ A : Fin b → Fin m → ℝ, MvPolynomial.eval (fun ij : Fin b × Fin m ↦ A ij.1 ij.2) P ≠ 0 := by
  -- relabel variables `Fin b × Fin m → Fin (b*m)` by `finProdFinEquiv`
  set e : Fin b × Fin m ≃ Fin (b * m) := finProdFinEquiv with he
  set P' : MvPolynomial (Fin (b * m)) ℝ := rename e P with hP'
  have hP'ne : P' ≠ 0 := by
    rw [hP']
    intro h
    exact hP (MvPolynomial.rename_injective (⇑e) e.injective (by rw [h, map_zero]))
  -- the deficient set is the eMatFlat-preimage of `P'`'s (null) zero set
  have hnull : (volume : Measure (Fin (b * m) → ℝ)) {x | MvPolynomial.eval x P' = 0} = 0 :=
    MvPolynomial.volume_zeroSet_eq_zero P' hP'ne
  have hmeas : MeasurableSet {x : Fin (b * m) → ℝ | MvPolynomial.eval x P' = 0} :=
    MvPolynomial.measurableSet_zeroSet P'
  -- key: for every `A`, `eval (eMatFlat A) P' = eval (A ·.1 ·.2) P`
  have hkey : ∀ A : Fin b → Fin m → ℝ,
      MvPolynomial.eval (eMatFlat b m A) P' = MvPolynomial.eval (fun ij ↦ A ij.1 ij.2) P := by
    intro A
    rw [hP', eval_rename]
    have hpt : (eMatFlat b m A) ∘ (⇑e) = fun ij : Fin b × Fin m ↦ A ij.1 ij.2 := by
      funext ij
      simp only [Function.comp_apply, he, eMatFlat_apply]
      have hs : (sigFlatEquiv b m).symm (finProdFinEquiv ij) = ⟨ij.1, ij.2⟩ := by
        simp only [sigFlatEquiv, Equiv.symm_trans_apply, Equiv.symm_apply_apply,
          Equiv.sigmaEquivProd_symm_apply]
      rw [hs]
    rw [hpt]
  -- transport the null set through the measure-preserving flatten
  rw [ae_iff]
  have hset : {A : Fin b → Fin m → ℝ | ¬ MvPolynomial.eval (fun ij ↦ A ij.1 ij.2) P ≠ 0}
      = eMatFlat b m ⁻¹' {x | MvPolynomial.eval x P' = 0} := by
    ext A; simp only [Set.mem_setOf_eq, Set.mem_preimage, not_not, hkey A]
  rw [hset, (measurePreserving_eMatFlat b m).measure_preimage hmeas.nullMeasurableSet, hnull]

/-! ## The corank-survival lemma (#2b) -/

/-- **AG-free free-matrix corank survival.** For a FIXED `Zdeep : Matrix (Fin m) (Fin D) ℝ` with
`b ≤ Zdeep.rank`, a.e. free `A : Fin b → Fin m → ℝ` has `(Matrix.of A * Zdeep).rank = b`. Genericity
in the FREE variable `A` (minor-cut null set), `Zdeep`'s rank an INPUT — the corank block survives
full-row-rank `b` through the rank-`≥ b` deeper product (`p = 0`). -/
theorem corank_survival_ae {b m D : ℕ} (Zdeep : Matrix (Fin m) (Fin D) ℝ) (hb : b ≤ Zdeep.rank) :
    ∀ᵐ A : Fin b → Fin m → ℝ, (Matrix.of A * Zdeep).rank = b := by
  rcases Nat.eq_zero_or_pos b with hb0 | hbpos
  · -- `b = 0`: a `0`-row matrix has rank `0 = b`, everywhere.
    subst hb0
    filter_upwards with A
    have : (Matrix.of A * Zdeep).rank ≤ 0 := (Matrix.of A * Zdeep).rank_le_height.trans (by simp)
    omega
  -- `b ≥ 1`: extract `b` independent rows/cols of `Zdeep` (the achievability witness).
  obtain ⟨c, rfl⟩ : ∃ c, b = c + 1 := ⟨b - 1, by omega⟩
  obtain ⟨er, ec, her, hec, hdet⟩ :=
    Matrix.exists_submatrix_det_ne_zero_of_le_rank Zdeep (r := c) hb
  -- the polynomial `P` = the `ec`-minor of the generic `A · Zdeep`
  set Agen : Matrix (Fin (c + 1)) (Fin m) (MvPolynomial (Fin (c + 1) × Fin m) ℝ) :=
    Matrix.of (fun i j ↦ X (i, j)) with hAgen
  set P : MvPolynomial (Fin (c + 1) × Fin m) ℝ :=
    ((Agen * Zdeep.map (C : ℝ → MvPolynomial (Fin (c + 1) × Fin m) ℝ)).submatrix id ec).det with hP
  -- encoding: `eval (A ·.1 ·.2) P = det ((Matrix.of A * Zdeep).submatrix id ec)`
  have hencode : ∀ A : Fin (c + 1) → Fin m → ℝ,
      MvPolynomial.eval (fun ij ↦ A ij.1 ij.2) P
        = ((Matrix.of A * Zdeep).submatrix id ec).det := by
    intro A
    set pt : Fin (c + 1) × Fin m → ℝ := fun ij ↦ A ij.1 ij.2 with hpt
    have hprod : (Agen * Zdeep.map (C : ℝ → MvPolynomial (Fin (c + 1) × Fin m) ℝ)).map
          (⇑(MvPolynomial.eval pt)) = Matrix.of A * Zdeep := by
      ext i k
      rw [Matrix.map_apply]
      have e1 : (Agen * Zdeep.map (C : ℝ → MvPolynomial (Fin (c + 1) × Fin m) ℝ)) i k
          = ∑ l, Agen i l * (Zdeep.map (C : ℝ → MvPolynomial (Fin (c + 1) × Fin m) ℝ)) l k :=
        Matrix.mul_apply
      have e2 : (Matrix.of A * Zdeep) i k = ∑ l, (Matrix.of A) i l * Zdeep l k := Matrix.mul_apply
      rw [e1, map_sum, e2]
      refine Finset.sum_congr rfl (fun l _ ↦ ?_)
      rw [map_mul]
      congr 1
      · simp [hAgen, Matrix.of_apply, MvPolynomial.eval_X, hpt]
      · simp [Matrix.map_apply, MvPolynomial.eval_C]
    -- `submatrix_map` and `mapMatrix` are both `rfl`, so `congrArg` transports `hprod` directly.
    have hmap : ((Agen * Zdeep.map C).submatrix id ec).map (⇑(MvPolynomial.eval pt))
        = (Matrix.of A * Zdeep).submatrix id ec :=
      congrArg (fun M ↦ M.submatrix id ec) hprod
    rw [hP, RingHom.map_det]
    exact congrArg Matrix.det hmap
  -- `P ≠ 0`: the one-hot row selection `A₀ = selMat er` realises `det (Zdeep.submatrix er ec) ≠ 0`
  have hPne : P ≠ 0 := by
    intro hzero
    have hsel : ((Matrix.of (fun i j ↦ if er i = j then (1 : ℝ) else 0)) * Zdeep)
        = Zdeep.submatrix er id := by
      ext i k
      rw [Matrix.mul_apply,
        Finset.sum_eq_single (er i)
          (fun j _ hj ↦ by rw [Matrix.of_apply, if_neg (Ne.symm hj), zero_mul])
          (fun h ↦ absurd (Finset.mem_univ _) h),
        Matrix.of_apply, if_pos rfl, one_mul, Matrix.submatrix_apply, id_eq]
    have hev := hencode (fun i j ↦ if er i = j then (1 : ℝ) else 0)
    simp only [hzero, map_zero] at hev
    rw [hsel] at hev
    have hsub : (Zdeep.submatrix er id).submatrix id ec = Zdeep.submatrix er ec := by
      simp [Matrix.submatrix_submatrix]
    rw [hsub] at hev
    exact hdet hev.symm
  -- a.e. the minor is nonzero, hence rank `= b`
  filter_upwards [ae_matrix_eval_ne_zero P hPne] with A hA
  rw [hencode] at hA
  refine le_antisymm (Matrix.of A * Zdeep).rank_le_height ?_
  -- if rank `< c+1`, the `ec`-minor would vanish (contradiction)
  by_contra hlt
  rw [not_le] at hlt
  exact hA (Matrix.submatrix_det_eq_zero_of_rank_le (A := Matrix.of A * Zdeep) (r := c)
    (by omega) id ec)

end DLNFibre.DLN.RLCT
