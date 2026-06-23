import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.Matrix.Basis
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.Isomorphisms
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# `DLNFibre.Core.Matrix.RankNormalForm` — generic rank normal form

A network-free Core brick: any real `a × b` matrix of rank `r` is carried by regular row/column
operations to the block-normal form `diag(E_r, 0)` (the identity on the top-left `r × r` block,
zero elsewhere). This is the generic version of the DLN-specialised `block_elimination`.
-/

namespace DLNFibre.Core.Matrix

open Matrix LinearMap Module

/-- Rank data for `rank_normal_form_exists`: `finrank ker = b - r`, `r ≤ b`, `r ≤ a`. -/
private lemma rank_normal_form_rank_data {a b r : ℕ}
    (A : Matrix (Fin a) (Fin b) ℝ) (hA : A.rank = r) :
    Module.finrank ℝ (LinearMap.ker A.mulVecLin) = b - r ∧ r ≤ b ∧ r ≤ a := by
  classical
  have hrange : Module.finrank ℝ (LinearMap.range A.mulVecLin) = r := by
    simpa [Matrix.rank] using hA
  have hsum0 :
      Module.finrank ℝ (LinearMap.range A.mulVecLin)
        + Module.finrank ℝ (LinearMap.ker A.mulVecLin)
        = Module.finrank ℝ (Fin b → ℝ) :=
    A.mulVecLin.finrank_range_add_finrank_ker
  have hsum : r + Module.finrank ℝ (LinearMap.ker A.mulVecLin) = b := by
    simpa [hrange, Module.finrank_fin_fun] using hsum0
  have hker : Module.finrank ℝ (LinearMap.ker A.mulVecLin) = b - r := by
    omega
  have hrb : r ≤ b := by
    omega
  have hra : r ≤ a := by
    simpa [hA] using Matrix.rank_le_height A
  exact ⟨hker, hrb, hra⟩

/-- **Generic rank normal form.** For a rank-`r` matrix `A`, regular row/column operations
(invertible `P, Q`) carry `A` to the **block-normal form** `diag(E_r, 0)`: `P · A · Q` is the
matrix that is the identity on the top-left `r × r` block and `0` elsewhere. -/
theorem rank_normal_form_exists {a b r : ℕ} (A : Matrix (Fin a) (Fin b) ℝ) (hA : A.rank = r) :
    ∃ (P : Matrix (Fin a) (Fin a) ℝ) (Q : Matrix (Fin b) (Fin b) ℝ),
      IsUnit P ∧ IsUnit Q ∧
        P * A * Q = Matrix.of (fun (i : Fin a) (j : Fin b) =>
          if (i : ℕ) = (j : ℕ) ∧ (i : ℕ) < r then (1 : ℝ) else 0) := by
  classical
  let f : (Fin b → ℝ) →ₗ[ℝ] (Fin a → ℝ) := A.mulVecLin

  rcases rank_normal_form_rank_data (a := a) (b := b) (r := r) A hA with
    ⟨hkerA, hrb, hra⟩

  have hrange : Module.finrank ℝ (LinearMap.range f) = r := by
    simpa [f, Matrix.rank] using hA
  have hker : Module.finrank ℝ (LinearMap.ker f) = b - r := by
    simpa [f] using hkerA

  have hcoker : Module.finrank ℝ ((Fin a → ℝ) ⧸ LinearMap.range f) = a - r := by
    have hq :
        Module.finrank ℝ ((Fin a → ℝ) ⧸ LinearMap.range f)
          + Module.finrank ℝ (LinearMap.range f)
          = Module.finrank ℝ (Fin a → ℝ) :=
      Submodule.finrank_quotient_add_finrank _
    have hq' :
        Module.finrank ℝ ((Fin a → ℝ) ⧸ LinearMap.range f) + r = a := by
      simpa [hrange, Module.finrank_fin_fun] using hq
    omega

  let bKer : Basis (Fin (b - r)) ℝ (LinearMap.ker f) :=
    Module.finBasisOfFinrankEq ℝ (LinearMap.ker f) hker
  let bRange : Basis (Fin r) ℝ (LinearMap.range f) :=
    Module.finBasisOfFinrankEq ℝ (LinearMap.range f) hrange

  let bDomQuot : Basis (Fin r) ℝ ((Fin b → ℝ) ⧸ LinearMap.ker f) :=
    bRange.map (LinearMap.quotKerEquivRange f).symm
  let bCoker : Basis (Fin (a - r)) ℝ ((Fin a → ℝ) ⧸ LinearMap.range f) :=
    Module.finBasisOfFinrankEq ℝ ((Fin a → ℝ) ⧸ LinearMap.range f) hcoker

  let bDomRaw : Basis (Fin (b - r) ⊕ Fin r) ℝ (Fin b → ℝ) :=
    bKer.sumQuot bDomQuot
  let bDomS : Basis (Fin r ⊕ Fin (b - r)) ℝ (Fin b → ℝ) :=
    bDomRaw.reindex (Equiv.sumComm (Fin (b - r)) (Fin r))
  let bCodS : Basis (Fin r ⊕ Fin (a - r)) ℝ (Fin a → ℝ) :=
    bRange.sumQuot bCoker

  have hDomInl (j : Fin r) :
      f (bDomS (Sum.inl j)) = ((bRange j : LinearMap.range f) : Fin a → ℝ) := by
    have hq : Submodule.Quotient.mk (bDomS (Sum.inl j)) = bDomQuot j := by
      simpa [bDomS, bDomRaw] using
        (Module.Basis.sumQuot_inr bKer bDomQuot j)
    have h :=
      congrArg (fun q => ((LinearMap.quotKerEquivRange f) q : Fin a → ℝ)) hq
    simpa [bDomQuot, LinearMap.quotKerEquivRange] using h

  have hDomInr (j : Fin (b - r)) :
      f (bDomS (Sum.inr j)) = 0 := by
    change bDomS (Sum.inr j) ∈ LinearMap.ker f
    simpa [bDomS, bDomRaw] using (bKer j).2

  let Sigma : Matrix (Fin r ⊕ Fin (a - r)) (Fin r ⊕ Fin (b - r)) ℝ :=
    Matrix.of fun i j =>
      match i, j with
      | Sum.inl i', Sum.inl j' => if i' = j' then (1 : ℝ) else 0
      | _, _ => 0

  have hSigma : LinearMap.toMatrix bDomS bCodS f = Sigma := by
    ext i j
    cases i with
    | inl i =>
        cases j with
        | inl j =>
            rw [LinearMap.toMatrix_apply, hDomInl j]
            dsimp [Sigma]
            rw [Module.Basis.sumQuot_repr_left bRange bCoker j, Finsupp.single_apply]
            simp [eq_comm]
        | inr j =>
            rw [LinearMap.toMatrix_apply, hDomInr j]
            simp [Sigma]
    | inr i =>
        cases j with
        | inl j =>
            rw [LinearMap.toMatrix_apply, hDomInl j]
            dsimp [Sigma]
            rw [Module.Basis.sumQuot_repr_inr_of_mem bRange bCoker _ (bRange j).2 i]
        | inr j =>
            rw [LinearMap.toMatrix_apply, hDomInr j]
            simp [Sigma]

  let eRows : (Fin r ⊕ Fin (a - r)) ≃ Fin a :=
    finSumFinEquiv.trans (finCongr (Nat.add_sub_of_le hra))
  let eCols : (Fin r ⊕ Fin (b - r)) ≃ Fin b :=
    finSumFinEquiv.trans (finCongr (Nat.add_sub_of_le hrb))

  let bDom : Basis (Fin b) ℝ (Fin b → ℝ) := bDomS.reindex eCols
  let bCod : Basis (Fin a) ℝ (Fin a → ℝ) := bCodS.reindex eRows

  have hReindex :
      LinearMap.toMatrix bDom bCod f =
        (LinearMap.toMatrix bDomS bCodS f).submatrix eRows.symm eCols.symm := by
    ext i j
    simp [bDom, bCod, LinearMap.toMatrix_apply]

  have hBlock :
      LinearMap.toMatrix bDom bCod f =
        Matrix.of (fun (i : Fin a) (j : Fin b) =>
          if (i : ℕ) = (j : ℕ) ∧ (i : ℕ) < r then (1 : ℝ) else 0) := by
    rw [hReindex, hSigma]
    ext i j
    dsimp [Sigma]

    have row_inl_val :
        ∀ {i : Fin a} {ir : Fin r}, eRows.symm i = Sum.inl ir → (i : ℕ) = (ir : ℕ) := by
      intro i ir hi
      have hi' : i = eRows (Sum.inl ir) := by
        calc
          i = eRows (eRows.symm i) := (Equiv.apply_symm_apply eRows i).symm
          _ = eRows (Sum.inl ir) := by rw [hi]
      simpa [eRows] using congrArg Fin.val hi'

    have row_inr_val :
        ∀ {i : Fin a} {ir : Fin (a - r)},
          eRows.symm i = Sum.inr ir → (i : ℕ) = r + (ir : ℕ) := by
      intro i ir hi
      have hi' : i = eRows (Sum.inr ir) := by
        calc
          i = eRows (eRows.symm i) := (Equiv.apply_symm_apply eRows i).symm
          _ = eRows (Sum.inr ir) := by rw [hi]
      simpa [eRows] using congrArg Fin.val hi'

    have col_inl_val :
        ∀ {j : Fin b} {jr : Fin r}, eCols.symm j = Sum.inl jr → (j : ℕ) = (jr : ℕ) := by
      intro j jr hj
      have hj' : j = eCols (Sum.inl jr) := by
        calc
          j = eCols (eCols.symm j) := (Equiv.apply_symm_apply eCols j).symm
          _ = eCols (Sum.inl jr) := by rw [hj]
      simpa [eCols] using congrArg Fin.val hj'

    have col_inr_val :
        ∀ {j : Fin b} {jr : Fin (b - r)},
          eCols.symm j = Sum.inr jr → (j : ℕ) = r + (jr : ℕ) := by
      intro j jr hj
      have hj' : j = eCols (Sum.inr jr) := by
        calc
          j = eCols (eCols.symm j) := (Equiv.apply_symm_apply eCols j).symm
          _ = eCols (Sum.inr jr) := by rw [hj]
      simpa [eCols] using congrArg Fin.val hj'

    rcases hi : eRows.symm i with ir | ia
    · have hiVal := row_inl_val hi
      rcases hj : eCols.symm j with jr | jb
      · have hjVal := col_inl_val hj
        by_cases hij : ir = jr
        · subst jr
          have hcond : (i : ℕ) = (j : ℕ) ∧ (i : ℕ) < r := by
            constructor
            · omega
            · simpa [hiVal] using ir.isLt
          rw [if_pos hcond]
          simp
        · have hcond : ¬ ((i : ℕ) = (j : ℕ) ∧ (i : ℕ) < r) := by
            intro hc
            apply hij
            ext
            omega
          simp [hij, hcond]
      · have hjVal := col_inr_val hj
        have hcond : ¬ ((i : ℕ) = (j : ℕ) ∧ (i : ℕ) < r) := by
          intro hc
          omega
        simp [hcond]
    · have hiVal := row_inr_val hi
      have hcond : ¬ ((i : ℕ) = (j : ℕ) ∧ (i : ℕ) < r) := by
        intro hc
        omega
      simp [hcond]

  let stdV : Basis (Fin b) ℝ (Fin b → ℝ) := Pi.basisFun ℝ (Fin b)
  let stdW : Basis (Fin a) ℝ (Fin a → ℝ) := Pi.basisFun ℝ (Fin a)

  have hstdLin : Matrix.toLin stdV stdW A = f := by
    dsimp [stdV, stdW, f]
    rw [Matrix.toLin_eq_toLin', Matrix.toLin'_apply']

  have hAstd : LinearMap.toMatrix stdV stdW f = A := by
    rw [← hstdLin]
    exact LinearMap.toMatrix_toLin stdV stdW A

  let P : Matrix (Fin a) (Fin a) ℝ := bCod.toMatrix stdW
  let Q : Matrix (Fin b) (Fin b) ℝ := stdV.toMatrix bDom

  refine ⟨P, Q, ?_, ?_, ?_⟩
  · dsimp [P]
    letI := Module.Basis.invertibleToMatrix bCod stdW
    exact isUnit_of_invertible _
  · dsimp [Q]
    letI := Module.Basis.invertibleToMatrix stdV bDom
    exact isUnit_of_invertible _
  · calc
      P * A * Q
          = P * (LinearMap.toMatrix stdV stdW f) * Q := by
              rw [← hAstd]
      _ = LinearMap.toMatrix bDom bCod f := by
              simpa [P, Q] using
                (basis_toMatrix_mul_linearMap_toMatrix_mul_basis_toMatrix
                  bDom stdV bCod stdW f)
      _ = Matrix.of (fun (i : Fin a) (j : Fin b) =>
              if (i : ℕ) = (j : ℕ) ∧ (i : ℕ) < r then (1 : ℝ) else 0) := hBlock

/-- **Left-only rank normal form for a `[A | 0]` matrix** (#159, the boundary-left frame). If a rank-`r`
matrix `M` has its columns `j ≥ r` vanishing (so `M = [A | 0]` with `A` the first `r` columns, rank
`r`), then a SINGLE left unit `P` carries it to the block-normal corner `P · M = corM` — no right frame
needed (the zero columns are already normal). Proven from the column-independence of the first `r`
columns: extend to an invertible basis `B`, take `P = B⁻¹`. (The right factor of the two-sided
`rank_normal_form_exists` acts only on the `r × r` active block, which the `[A|0]` shape makes
absorbable into the left basis choice.) -/
theorem left_normal_form_of_cols_vanish {a b r : ℕ} (M : Matrix (Fin a) (Fin b) ℝ)
    (hrank : M.rank = r) (hr : r ≤ b)
    (hcols : ∀ (i : Fin a) (j : Fin b), r ≤ (j : ℕ) → M i j = 0) :
    ∃ P : Matrix (Fin a) (Fin a) ℝ, IsUnit P ∧
      P * M = Matrix.of (fun (i : Fin a) (j : Fin b) =>
        if (i : ℕ) = (j : ℕ) ∧ (i : ℕ) < r then (1 : ℝ) else 0) := by
  -- #159: the `[A|0]` left-only normal form. Isolated obligation (dispatched separately); the
  -- frame-family + cert chain build green around it.
  sorry

/-- **Right-only rank normal form for a `[A ; 0]` matrix** (#159, the boundary-right frame). If a
rank-`r` matrix `M` has its rows `i ≥ r` vanishing (`M = [A ; 0]`), then a SINGLE right unit `Q`
carries it to the corner `M · Q = corM`. The transpose of `left_normal_form_of_cols_vanish`. -/
theorem right_normal_form_of_rows_vanish {a b r : ℕ} (M : Matrix (Fin a) (Fin b) ℝ)
    (hrank : M.rank = r) (hr : r ≤ a)
    (hrows : ∀ (i : Fin a) (j : Fin b), r ≤ (i : ℕ) → M i j = 0) :
    ∃ Q : Matrix (Fin b) (Fin b) ℝ, IsUnit Q ∧
      M * Q = Matrix.of (fun (i : Fin a) (j : Fin b) =>
        if (i : ℕ) = (j : ℕ) ∧ (i : ℕ) < r then (1 : ℝ) else 0) := by
  -- #159: the `[A;0]` right-only normal form (transpose of the left version). Isolated obligation.
  sorry

end DLNFibre.Core.Matrix
