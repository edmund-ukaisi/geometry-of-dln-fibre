import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.Matrix.Basis
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Isomorphisms
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas

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

/-- **One-sided (left-only) rank normal form for a tail-columns-zero matrix.** If a rank-`r` matrix
`A` has all columns indexed `j ≥ r` equal to zero, a single regular row operation (invertible `P`,
with `Q = 1`) carries it to the block-normal form `diag(E_r, 0)`: `P · A = corM`. The frame acts
only on the left. The math: the first `r` columns of `A` span its `r`-dim column space, so they are
linearly independent; extend them to a codomain basis whose change-of-basis matrix is `P`, and the
domain stays standard (`Q = 1`). The deepest point's layer-0 boundary frame needs exactly this
(its tail columns vanish) — strictly stronger than `rank_normal_form_exists` on such a matrix. -/
theorem rank_normal_form_left_only {a b r : ℕ}
    (A : Matrix (Fin a) (Fin b) ℝ) (hA : A.rank = r)
    (htail : ∀ (i : Fin a) (j : Fin b), r ≤ (j : ℕ) → A i j = 0) :
    ∃ P : Matrix (Fin a) (Fin a) ℝ, IsUnit P ∧
      P * A = Matrix.of (fun (i : Fin a) (j : Fin b) =>
        if (i : ℕ) = (j : ℕ) ∧ (i : ℕ) < r then (1 : ℝ) else 0) := by
  classical
  have hrb : r ≤ b := by rw [← hA]; exact A.rank_le_width
  have hra : r ≤ a := by rw [← hA]; exact A.rank_le_height
  have hjb : ∀ j : Fin r, (j : ℕ) < b := fun j => Nat.lt_of_lt_of_le j.isLt hrb
  have hja : ∀ j : Fin r, (j : ℕ) < a := fun j => Nat.lt_of_lt_of_le j.isLt hra
  -- The first `r` columns of `A` (vectors in `Fin a → ℝ`; the column index `j < r ≤ b`).
  set w : Fin r → (Fin a → ℝ) := fun j => A.col ⟨(j : ℕ), hjb j⟩ with hw
  -- They are linearly independent: they span `A`'s column space (tail columns vanish), of dim `r`.
  have hindep : LinearIndependent ℝ w := by
    rw [linearIndependent_iff_card_eq_finrank_span, Fintype.card_fin]
    have hspan : Submodule.span ℝ (Set.range w) = Submodule.span ℝ (Set.range A.col) := by
      apply le_antisymm
      · apply Submodule.span_mono; rintro x ⟨j, rfl⟩; exact ⟨⟨(j : ℕ), hjb j⟩, rfl⟩
      · rw [Submodule.span_le]; rintro x ⟨j, rfl⟩
        by_cases hj : (j : ℕ) < r
        · apply Submodule.subset_span; exact ⟨⟨(j : ℕ), hj⟩, by simp [hw, Matrix.col]⟩
        · have : A.col j = 0 := by ext i; exact htail i j (by omega)
          rw [this]; exact Submodule.zero_mem _
    unfold Set.finrank; rw [hspan, ← Matrix.rank_eq_finrank_span_cols, hA]
  -- Extend the family to a `Fin a`-indexed codomain basis whose first `r` vectors are `w`.
  set S := Basis.sumExtendIndex hindep with hS
  haveI : Finite S := by
    haveI : Finite (Fin r ⊕ S) := Module.Finite.finite_basis (Basis.sumExtend hindep)
    exact Finite.of_injective (β := Fin r ⊕ S) Sum.inr Sum.inr_injective
  haveI : Fintype S := Fintype.ofFinite S
  have hScard : Fintype.card S = a - r := by
    have hb : Fintype.card (Fin r ⊕ S) = Module.finrank ℝ (Fin a → ℝ) :=
      (Module.finrank_eq_card_basis (Basis.sumExtend hindep)).symm
    simp only [Fintype.card_sum, Fintype.card_fin, Module.finrank_fintype_fun_eq_card,
      Fintype.card_fin] at hb
    omega
  let eS : S ≃ Fin (a - r) := Fintype.equivFinOfCardEq hScard
  let e : (Fin r ⊕ S) ≃ Fin a :=
    (Equiv.sumCongr (Equiv.refl (Fin r)) eS).trans (finSumFinEquiv.trans (finCongr (by omega)))
  have he_inl : ∀ j : Fin r, e (Sum.inl j) = ⟨(j : ℕ), hja j⟩ := by
    intro j
    simp only [e, Equiv.trans_apply, Equiv.sumCongr_apply, Equiv.refl_apply, Sum.map_inl,
      finSumFinEquiv_apply_left, finCongr_apply]
    apply Fin.ext; simp [Fin.castAdd, Fin.castLE]
  let bCod : Module.Basis (Fin a) ℝ (Fin a → ℝ) := (Basis.sumExtend hindep).reindex e
  have hbCod_lt : ∀ j : Fin r, bCod ⟨(j : ℕ), hja j⟩ = w j := by
    intro j
    have hei : e (Sum.inl j) = ⟨(j : ℕ), hja j⟩ := he_inl j
    rw [show (⟨(j : ℕ), hja j⟩ : Fin a) = e (Sum.inl j) from hei.symm]
    simp only [bCod, Basis.coe_reindex, Function.comp_apply, Equiv.symm_apply_apply]
    change (Basis.sumExtend hindep) (Sum.inl j) = w j
    rw [Basis.sumExtend]
    simp only [Basis.coe_reindex, Function.comp_apply, Equiv.symm_symm]
    change (Basis.extend hindep.linearIndepOn_id)
        (((Equiv.ofInjective w hindep.injective).sumCongr (Equiv.refl _)).trans
          (Equiv.Set.sumDiffSubset (hindep.linearIndepOn_id.subset_extend _))
            (Sum.inl j)) = _
    rw [Equiv.trans_apply, Equiv.sumCongr_apply, Sum.map_inl, Equiv.Set.sumDiffSubset_apply_inl,
      Basis.extend_apply_self, Equiv.ofInjective_apply]
  let stdW : Module.Basis (Fin a) ℝ (Fin a → ℝ) := Pi.basisFun ℝ (Fin a)
  let stdV : Module.Basis (Fin b) ℝ (Fin b → ℝ) := Pi.basisFun ℝ (Fin b)
  -- `P := bCod.toMatrix stdW` is invertible; `P · A = toMatrix stdV bCod A.mulVecLin`, entrywise.
  refine ⟨bCod.toMatrix stdW, ?_, ?_⟩
  · letI := Module.Basis.invertibleToMatrix bCod stdW
    exact isUnit_of_invertible _
  · have hPA : bCod.toMatrix stdW * A = LinearMap.toMatrix stdV bCod A.mulVecLin := by
      have h := basis_toMatrix_mul bCod stdW stdV A
      rw [h, Matrix.toLin_eq_toLin', Matrix.toLin'_apply']
    rw [hPA]
    ext i j
    rw [LinearMap.toMatrix_apply]
    simp only [Matrix.of_apply]
    have hcol : A.mulVecLin (stdV j) = A.col j := by
      ext k; simp [stdV, Matrix.mulVecLin, Pi.basisFun_apply, Matrix.mulVec_single, Matrix.col]
    rw [hcol]
    by_cases hjr : (j : ℕ) < r
    · -- `A.col j = w ⟨j,_⟩ = bCod ⟨j,_⟩`, whose repr is the `j`-th standard vector.
      have hcolw : A.col j = bCod ⟨(j : ℕ), by omega⟩ := by
        have h := hbCod_lt ⟨(j : ℕ), hjr⟩
        rw [hw] at h; simp only at h
        rw [← h]
      rw [hcolw, Basis.repr_self, Finsupp.single_apply]
      have hiff : ((⟨(j : ℕ), by omega⟩ : Fin a) = i) ↔ ((i : ℕ) = (j : ℕ) ∧ (i : ℕ) < r) := by
        constructor
        · intro h; have hv := Fin.val_eq_of_eq h
          exact ⟨by simpa using hv.symm, by simpa using hv ▸ hjr⟩
        · intro ⟨h1, _⟩; apply Fin.ext; simpa using h1.symm
      simp only [hiff]
    · -- Tail column is zero, so its representation is zero.
      have : A.col j = 0 := by ext k; exact htail k j (by omega)
      rw [this, map_zero, Finsupp.coe_zero, Pi.zero_apply]
      rw [if_neg (by rintro ⟨_, h2⟩; omega)]

/-- **One-sided (right-only) rank normal form for a tail-rows-zero matrix.** If a rank-`r` matrix
`A` has all rows indexed `i ≥ r` equal to zero, a single regular column operation (invertible `Q`,
with `P = 1`) carries it to the block-normal form: `A · Q = corM`. The dual of
`rank_normal_form_left_only`, obtained by transposing (`Matrix.rank_transpose`,
`Matrix.transpose_mul`). The boundary frame at the deepest point's last layer needs exactly this
(its tail rows vanish). -/
theorem rank_normal_form_right_only {a b r : ℕ}
    (A : Matrix (Fin a) (Fin b) ℝ) (hA : A.rank = r)
    (htail : ∀ (i : Fin a) (j : Fin b), r ≤ (i : ℕ) → A i j = 0) :
    ∃ Q : Matrix (Fin b) (Fin b) ℝ, IsUnit Q ∧
      A * Q = Matrix.of (fun (i : Fin a) (j : Fin b) =>
        if (i : ℕ) = (j : ℕ) ∧ (i : ℕ) < r then (1 : ℝ) else 0) := by
  have hAT : (Matrix.transpose A).rank = r := by rw [Matrix.rank_transpose]; exact hA
  have htailT : ∀ (i : Fin b) (j : Fin a), r ≤ (j : ℕ) → Matrix.transpose A i j = 0 := by
    intro i j hj; rw [Matrix.transpose_apply]; exact htail j i hj
  obtain ⟨P, hP, hPeq⟩ := rank_normal_form_left_only (Matrix.transpose A) hAT htailT
  refine ⟨Matrix.transpose P, by rwa [Matrix.isUnit_transpose], ?_⟩
  have hAPt : A * Matrix.transpose P = Matrix.transpose (P * Matrix.transpose A) := by
    rw [Matrix.transpose_mul, Matrix.transpose_transpose]
  rw [hAPt, hPeq]
  ext i j
  simp only [Matrix.transpose_apply, Matrix.of_apply]
  by_cases h : (i : ℕ) = (j : ℕ)
  · simp [h]
  · rw [if_neg (fun hc => h hc.1.symm), if_neg (fun hc => h hc.1)]

/-- **Pivot columns of a full-row-rank matrix.** For a rank-`r` matrix `V : Fin r × Fin c` (so
`r ≤ c`, full ROW rank), there exist `r` column indices — packaged as an embedding
`J : Fin r ↪ Fin c` — whose `r × r` submatrix `V.submatrix id J` is invertible. The math:
`rank V = r` is the column-span dimension, so a maximal linearly-independent subfamily of the
columns has exactly `r` members; reindexed to `Fin r` they give the embedding `J`, the selected
columns stay independent, a square matrix with independent columns is a unit. The new Core brick for
the boundary-frame pivot alignment (the last interface's `B22` block invertible). Any field. -/
theorem exists_pivot_cols_of_rank {K : Type*} [Field K] {r c : ℕ}
    (V : Matrix (Fin r) (Fin c) K) (hV : V.rank = r) :
    ∃ J : Fin r ↪ Fin c,
      IsUnit (V.submatrix (_root_.id : Fin r → Fin r) (J : Fin r → Fin c)) := by
  classical
  -- A maximal independent subfamily of the columns, with the SAME span.
  obtain ⟨κ, a, ha_inj, ha_span, ha_li⟩ := exists_linearIndependent' K V.col
  haveI : Finite κ := ha_li.finite
  haveI : Fintype κ := Fintype.ofFinite κ
  -- `finrank (span columns) = rank V = r`.
  have hrank : Module.finrank K (Submodule.span K (Set.range V.col)) = r := by
    rw [← Matrix.rank_eq_finrank_span_cols V, hV]
  -- The independent subfamily has cardinal `r`.
  have hcard : Fintype.card κ = r := by
    have hfin : Module.finrank K (Submodule.span K (Set.range (V.col ∘ a))) = Fintype.card κ :=
      finrank_span_eq_card ha_li
    rw [ha_span] at hfin
    exact hfin.symm.trans hrank
  -- Reindex `κ ≃ Fin r`, build the embedding.
  let e : κ ≃ Fin r := Fintype.equivFinOfCardEq hcard
  let J : Fin r ↪ Fin c :=
    ⟨fun i => a (e.symm i), fun i j hij => e.symm.injective (ha_inj hij)⟩
  refine ⟨J, ?_⟩
  -- The selected columns stay independent (reindex along `e.symm`).
  have hJli : LinearIndependent K (fun i : Fin r => V.col (J i)) := by
    have := ha_li.comp (e.symm : Fin r → κ) e.symm.injective
    simpa [J, Function.comp_def] using this
  -- `(V.submatrix id J).col = fun i => V.col (J i)`, so the submatrix's columns are independent.
  have hcols : LinearIndependent K
      (V.submatrix (_root_.id : Fin r → Fin r) (J : Fin r → Fin c)).col := by
    have hcoleq : (V.submatrix (_root_.id : Fin r → Fin r) (J : Fin r → Fin c)).col
        = fun i => V.col (J i) := by
      funext k i; rfl
    rw [hcoleq]; exact hJli
  -- A square matrix with independent columns is a unit.
  exact Matrix.linearIndependent_cols_iff_isUnit.mp hcols

end DLNFibre.Core.Matrix
