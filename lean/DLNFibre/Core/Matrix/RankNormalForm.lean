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

/-- **Left-only rank normal form for a column-trailing-zero matrix.** If `D`'s last `b − r` columns
vanish (`D i j = 0` for `r ≤ j`) and `D.rank = r`, then a LEFT frame alone (invertible `P`, `Q = I`)
carries `D` to the block-normal corM: `∃ P unit, P · D = corM`. The vanishing right columns are
already in corM-shape, so no right-frame is needed to clear them — only `D`'s nonzero `a × r` left
block needs left-normalizing (it has full column rank `r`). This is the boundary-layer frame the
`endpoint_telescoping` needs: layer 0's right frame `Q_0 = I`, so only `P_0` survives on the left
boundary. -/
theorem left_normal_form_of_cols_vanish {a b r : ℕ} (D : Matrix (Fin a) (Fin b) ℝ)
    (hD : D.rank = r) (hcols : ∀ (i : Fin a) (j : Fin b), r ≤ (j : ℕ) → D i j = 0) :
    ∃ (P : Matrix (Fin a) (Fin a) ℝ), IsUnit P ∧
      P * D = Matrix.of (fun (i : Fin a) (j : Fin b) =>
        if (i : ℕ) = (j : ℕ) ∧ (i : ℕ) < r then (1 : ℝ) else 0) := by
  classical
  -- `r = 0` is the degenerate case: `rank 0 ⟹ D = 0`, corM is the zero matrix, `P = 1`.
  rcases Nat.eq_zero_or_pos r with hr0 | hrpos
  · subst hr0
    refine ⟨1, isUnit_one, ?_⟩
    have hrange0 : Module.finrank ℝ (LinearMap.range D.mulVecLin) = 0 := by
      simpa [Matrix.rank] using hD
    have hbot : LinearMap.range D.mulVecLin = ⊥ := Submodule.finrank_eq_zero.mp hrange0
    have hD0 : D = 0 := by
      ext i j
      have hfv : D.mulVecLin (Pi.single j 1) = 0 := by
        rw [← Submodule.mem_bot ℝ, ← hbot]; exact LinearMap.mem_range_self _ _
      have := congrFun hfv i
      simpa [Matrix.mulVecLin_apply, Matrix.mulVec_single_one, Matrix.col_apply] using this
    rw [hD0, Matrix.mul_zero]
    ext i j
    simp
  haveI : Nonempty (Fin r) := ⟨⟨0, hrpos⟩⟩
  let f : (Fin b → ℝ) →ₗ[ℝ] (Fin a → ℝ) := D.mulVecLin
  rcases rank_normal_form_rank_data (a := a) (b := b) (r := r) D hD with ⟨_, hrb, hra⟩
  have hrange : Module.finrank ℝ (LinearMap.range f) = r := by
    simpa [f, Matrix.rank] using hD
  let stdV : Basis (Fin b) ℝ (Fin b → ℝ) := Pi.basisFun ℝ (Fin b)
  let stdW : Basis (Fin a) ℝ (Fin a → ℝ) := Pi.basisFun ℝ (Fin a)
  -- The first `r` columns of `D`, as elements of the range of `f`.
  have hmem : ∀ j : Fin r, f (stdV (Fin.castLE hrb j)) ∈ LinearMap.range f :=
    fun j => LinearMap.mem_range_self _ _
  let cR : Fin r → LinearMap.range f := fun j => ⟨f (stdV (Fin.castLE hrb j)), hmem j⟩
  -- `f (stdV k) = 0` whenever `k ≥ r` (the trailing columns of `D` vanish).
  have hzero : ∀ k : Fin b, r ≤ (k : ℕ) → f (stdV k) = 0 := by
    intro k hk
    funext i
    have : f (stdV k) i = D i k := by
      simp [f, stdV, Pi.basisFun_apply, Matrix.col_apply]
    rw [this, hcols i k hk, Pi.zero_apply]
  -- The ambient family of the first `r` columns of `D`.
  let g : Fin r → (Fin a → ℝ) := fun j => f (stdV (Fin.castLE hrb j))
  -- `range f` is spanned by the images of the standard basis under `f`.
  have hrange_span : LinearMap.range f = Submodule.span ℝ (Set.range (fun k => f (stdV k))) := by
    rw [LinearMap.range_eq_map, ← stdV.span_eq, Submodule.map_span, ← Set.range_comp]
    rfl
  -- The `r` columns span `range f` (the trailing columns vanish, so add nothing).
  have hg_span : Submodule.span ℝ (Set.range g) = LinearMap.range f := by
    apply le_antisymm
    · rw [Submodule.span_le]
      rintro _ ⟨j, rfl⟩
      exact LinearMap.mem_range_self _ _
    · rw [hrange_span, Submodule.span_le]
      rintro _ ⟨k, rfl⟩
      change f (stdV k) ∈ (Submodule.span ℝ (Set.range g) : Submodule ℝ (Fin a → ℝ))
      by_cases hk : (k : ℕ) < r
      · have hcast : Fin.castLE hrb ⟨(k : ℕ), hk⟩ = k := by ext; simp
        refine Submodule.subset_span ⟨⟨(k : ℕ), hk⟩, ?_⟩
        simp only [g, hcast]
      · rw [hzero k (not_lt.mp hk)]
        exact Submodule.zero_mem _
  -- Hence the `r` columns are linearly independent (ambient), then in the subtype.
  have hg_li : LinearIndependent ℝ g := by
    rw [linearIndependent_iff_card_eq_finrank_span]
    rw [Set.finrank, hg_span, hrange]
    simp
  have hcR_li : LinearIndependent ℝ cR :=
    LinearIndependent.of_comp (LinearMap.range f).subtype hg_li
  let bRange : Basis (Fin r) ℝ (LinearMap.range f) :=
    basisOfLinearIndependentOfCardEqFinrank hcR_li (by simpa using hrange.symm)
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
  let bCoker : Basis (Fin (a - r)) ℝ ((Fin a → ℝ) ⧸ LinearMap.range f) :=
    Module.finBasisOfFinrankEq ℝ ((Fin a → ℝ) ⧸ LinearMap.range f) hcoker
  let bCodS : Basis (Fin r ⊕ Fin (a - r)) ℝ (Fin a → ℝ) :=
    bRange.sumQuot bCoker
  let eRows : (Fin r ⊕ Fin (a - r)) ≃ Fin a :=
    finSumFinEquiv.trans (finCongr (Nat.add_sub_of_le hra))
  let bCod : Basis (Fin a) ℝ (Fin a → ℝ) := bCodS.reindex eRows
  let P : Matrix (Fin a) (Fin a) ℝ := bCod.toMatrix stdW
  refine ⟨P, ?_, ?_⟩
  · dsimp [P]
    letI := Module.Basis.invertibleToMatrix bCod stdW
    exact isUnit_of_invertible _
  -- `P * D = LinearMap.toMatrix stdV bCod f`, computed entrywise to be corM.
  have hDstd : LinearMap.toMatrix stdV stdW f = D := by
    have hstdLin : Matrix.toLin stdV stdW D = f := by
      dsimp [stdV, stdW, f]
      rw [Matrix.toLin_eq_toLin', Matrix.toLin'_apply']
    rw [← hstdLin]
    exact LinearMap.toMatrix_toLin stdV stdW D
  have hPD : P * D = LinearMap.toMatrix stdV bCod f := by
    have h := basis_toMatrix_mul_linearMap_toMatrix (b' := stdV) bCod stdW f
    rw [hDstd] at h
    exact h
  -- Row-index bookkeeping for `eRows : (Fin r ⊕ Fin (a-r)) ≃ Fin a`.
  have row_inl_val :
      ∀ {i : Fin a} {ir : Fin r}, eRows.symm i = Sum.inl ir → (i : ℕ) = (ir : ℕ) := by
    intro i ir hi
    have hi' : i = eRows (Sum.inl ir) := by
      calc i = eRows (eRows.symm i) := (Equiv.apply_symm_apply eRows i).symm
        _ = eRows (Sum.inl ir) := by rw [hi]
    simpa [eRows] using congrArg Fin.val hi'
  have row_inr_val :
      ∀ {i : Fin a} {ir : Fin (a - r)},
        eRows.symm i = Sum.inr ir → (i : ℕ) = r + (ir : ℕ) := by
    intro i ir hi
    have hi' : i = eRows (Sum.inr ir) := by
      calc i = eRows (eRows.symm i) := (Equiv.apply_symm_apply eRows i).symm
        _ = eRows (Sum.inr ir) := by rw [hi]
    simpa [eRows] using congrArg Fin.val hi'
  rw [hPD]
  ext i j
  rw [LinearMap.toMatrix_apply]
  simp only [bCod, Module.Basis.repr_reindex_apply, Matrix.of_apply]
  by_cases hj : (j : ℕ) < r
  · -- `f (stdV j)` is the `j`-th range-basis vector, so its coords are `single (inl ⟨j,_⟩) 1`.
    have hcast : Fin.castLE hrb ⟨(j : ℕ), hj⟩ = j := by ext; simp
    have hval : f (stdV j) = ((bRange ⟨(j : ℕ), hj⟩ : LinearMap.range f) : Fin a → ℝ) := by
      have : bRange ⟨(j : ℕ), hj⟩ = cR ⟨(j : ℕ), hj⟩ := by
        simp [bRange, coe_basisOfLinearIndependentOfCardEqFinrank]
      rw [this]; simp [cR, hcast]
    rw [hval, Module.Basis.sumQuot_repr_left]
    rcases hi : eRows.symm i with ir | ia
    · have hiVal := row_inl_val hi
      rw [Finsupp.single_apply]
      by_cases hij : (Sum.inl ir : Fin r ⊕ Fin (a - r)) = Sum.inl ⟨(j : ℕ), hj⟩
      · have hirj : (ir : ℕ) = (j : ℕ) := by
          have := Sum.inl.inj hij; rw [this]
        have hcond : (i : ℕ) = (j : ℕ) ∧ (i : ℕ) < r := ⟨by omega, by omega⟩
        rw [if_pos hij.symm, if_pos hcond]
      · have hcond : ¬ ((i : ℕ) = (j : ℕ) ∧ (i : ℕ) < r) := by
          rintro ⟨he, _⟩
          apply hij
          have : (ir : ℕ) = (j : ℕ) := by omega
          simp [Fin.ext_iff, this]
        rw [if_neg (fun h => hij h.symm), if_neg hcond]
    · have hiVal := row_inr_val hi
      rw [Finsupp.single_apply]
      have hcond : ¬ ((i : ℕ) = (j : ℕ) ∧ (i : ℕ) < r) := by
        rintro ⟨_, hlt⟩; omega
      rw [if_neg (by simp), if_neg hcond]
  · -- `f (stdV j) = 0` for `j ≥ r`; both sides vanish.
    rw [hzero j (not_lt.mp hj)]
    have hcond : ¬ ((i : ℕ) = (j : ℕ) ∧ (i : ℕ) < r) := by
      rintro ⟨he, hlt⟩; omega
    rw [if_neg hcond, map_zero]
    rfl

/-- **Right-only rank normal form for a row-trailing-zero matrix.** If `D`'s last `a − r` rows
vanish (`D i j = 0` for `r ≤ i`) and `D.rank = r`, then a RIGHT frame alone (invertible `Q`,
`P = I`) carries `D` to the block-normal corM: `∃ Q unit, D · Q = corM`. Symmetric to
`left_normal_form_of_cols_vanish`: the boundary-layer frame for layer `L−1`'s left frame
`P_{L−1} = I`, so only `Q_{L−1}` survives on the right boundary. -/
theorem right_normal_form_of_rows_vanish {a b r : ℕ} (D : Matrix (Fin a) (Fin b) ℝ)
    (hD : D.rank = r) (hrows : ∀ (i : Fin a) (j : Fin b), r ≤ (i : ℕ) → D i j = 0) :
    ∃ (Q : Matrix (Fin b) (Fin b) ℝ), IsUnit Q ∧
      D * Q = Matrix.of (fun (i : Fin a) (j : Fin b) =>
        if (i : ℕ) = (j : ℕ) ∧ (i : ℕ) < r then (1 : ℝ) else 0) := by
  -- Apply the left lemma to `Dᵀ` (rows of `D` ↔ cols of `Dᵀ`), then transpose back, `Q := Pᵀ`.
  have hDT : (Matrix.transpose D).rank = r := by rw [Matrix.rank_transpose, hD]
  have hcolsT : ∀ (i : Fin b) (j : Fin a), r ≤ (j : ℕ) → (Matrix.transpose D) i j = 0 := by
    intro i j hj
    rw [Matrix.transpose_apply]
    exact hrows j i hj
  obtain ⟨P, hPunit, hPD⟩ := left_normal_form_of_cols_vanish (Matrix.transpose D) hDT hcolsT
  refine ⟨Matrix.transpose P, ?_, ?_⟩
  · rw [Matrix.isUnit_iff_isUnit_det] at hPunit ⊢
    rw [Matrix.det_transpose]
    exact hPunit
  -- `(P * Dᵀ)ᵀ = D * Pᵀ` and `corM_{b,a}ᵀ = corM_{a,b}`.
  have ht := congrArg Matrix.transpose hPD
  rw [Matrix.transpose_mul, Matrix.transpose_transpose] at ht
  rw [ht]
  ext i j
  simp only [Matrix.transpose_apply, Matrix.of_apply]
  by_cases h : (i : ℕ) = (j : ℕ)
  · by_cases hlt : (i : ℕ) < r
    · rw [if_pos ⟨h.symm, by omega⟩, if_pos ⟨h, hlt⟩]
    · rw [if_neg (by rintro ⟨_, hc⟩; omega), if_neg (by rintro ⟨_, hc⟩; omega)]
  · rw [if_neg (fun hc => h hc.1.symm), if_neg (fun hc => h hc.1)]

end DLNFibre.Core.Matrix
