I would avoid `Submodule.exists_isCompl` here. `Basis.sumQuot` gives the adapted bases directly: kernel plus quotient lift in the domain, range plus quotient lift in the codomain. The key names used below are documented as `Module.Basis.sumQuot` with its `sumQuot_*` lemmas, the basis-change glue theorem, and the standard-basis `toMatrix_toLin` / `toLin_eq_toLin'` bridge. ([leanprover-community.github.io](https://leanprover-community.github.io/mathlib4_docs/Mathlib/LinearAlgebra/Dimension/Constructions.html))

```lean
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.LinearAlgebra.Matrix.Basis
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.Tactic

namespace DLNFibre.DLN.RLCT

open Matrix LinearMap Module

noncomputable section

lemma block_elimination_rank_data {a b r : ℕ}
    (B : Matrix (Fin a) (Fin b) ℝ) (hB : B.rank = r) :
    Module.finrank ℝ (LinearMap.ker B.mulVecLin) = b - r ∧ r ≤ b ∧ r ≤ a := by
  classical
  have hrange : Module.finrank ℝ (LinearMap.range B.mulVecLin) = r := by
    simpa [Matrix.rank] using hB
  have hsum0 :
      Module.finrank ℝ (LinearMap.range B.mulVecLin)
        + Module.finrank ℝ (LinearMap.ker B.mulVecLin)
        = Module.finrank ℝ (Fin b → ℝ) :=
    B.mulVecLin.finrank_range_add_finrank_ker
  have hsum : r + Module.finrank ℝ (LinearMap.ker B.mulVecLin) = b := by
    simpa [hrange, Module.finrank_fin_fun] using hsum0
  have hker : Module.finrank ℝ (LinearMap.ker B.mulVecLin) = b - r := by
    omega
  have hrb : r ≤ b := by
    omega
  have hra : r ≤ a := by
    simpa [hB] using Matrix.rank_le_height B
  exact ⟨hker, hrb, hra⟩

theorem block_elimination {L : ℕ} (H : Fin (L + 1) → ℕ) (r : ℕ)
    (B : Matrix (Fin (H 0)) (Fin (H (Fin.last L))) ℝ) (hB : B.rank = r) :
    ∃ (P : Matrix (Fin (H 0)) (Fin (H 0)) ℝ)
      (Q : Matrix (Fin (H (Fin.last L))) (Fin (H (Fin.last L))) ℝ),
      IsUnit P ∧ IsUnit Q ∧
        P * B * Q = Matrix.of (fun (i : Fin (H 0)) (j : Fin (H (Fin.last L))) =>
          if (i : ℕ) = (j : ℕ) ∧ (i : ℕ) < r then (1 : ℝ) else 0) := by
  classical
  let a := H 0
  let b := H (Fin.last L)
  let f : (Fin b → ℝ) →ₗ[ℝ] (Fin a → ℝ) := B.mulVecLin

  rcases block_elimination_rank_data (a := a) (b := b) (r := r) B hB with
    ⟨hkerB, hrb, hra⟩

  have hrange : Module.finrank ℝ (LinearMap.range f) = r := by
    simpa [f, Matrix.rank] using hB
  have hker : Module.finrank ℝ (LinearMap.ker f) = b - r := by
    simpa [f] using hkerB

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
  let bDomΣ : Basis (Fin r ⊕ Fin (b - r)) ℝ (Fin b → ℝ) :=
    bDomRaw.reindex (Equiv.sumComm (Fin (b - r)) (Fin r))
  let bCodΣ : Basis (Fin r ⊕ Fin (a - r)) ℝ (Fin a → ℝ) :=
    bRange.sumQuot bCoker

  have hDomInl (j : Fin r) :
      f (bDomΣ (Sum.inl j)) = ((bRange j : LinearMap.range f) : Fin a → ℝ) := by
    have hq : Submodule.Quotient.mk (bDomΣ (Sum.inl j)) = bDomQuot j := by
      simpa [bDomΣ, bDomRaw] using
        (Module.Basis.sumQuot_inr bKer bDomQuot j)
    have h :=
      congrArg (fun q => ((LinearMap.quotKerEquivRange f) q : Fin a → ℝ)) hq
    simpa [bDomQuot, LinearMap.quotKerEquivRange] using h

  have hDomInr (j : Fin (b - r)) :
      f (bDomΣ (Sum.inr j)) = 0 := by
    change bDomΣ (Sum.inr j) ∈ LinearMap.ker f
    simpa [bDomΣ, bDomRaw] using (bKer j).2

  let Sigma : Matrix (Fin r ⊕ Fin (a - r)) (Fin r ⊕ Fin (b - r)) ℝ :=
    Matrix.of fun i j =>
      match i, j with
      | Sum.inl i', Sum.inl j' => if i' = j' then (1 : ℝ) else 0
      | _, _ => 0

  have hSigma : LinearMap.toMatrix bDomΣ bCodΣ f = Sigma := by
    ext i j
    cases i with
    | inl i =>
        cases j with
        | inl j =>
            rw [LinearMap.toMatrix_apply, hDomInl j]
            dsimp [Sigma]
            simpa [bCodΣ] using
              congrFun (Module.Basis.sumQuot_repr_left bRange bCoker j) (Sum.inl i)
        | inr j =>
            rw [LinearMap.toMatrix_apply, hDomInr j]
            simp [Sigma]
    | inr i =>
        cases j with
        | inl j =>
            rw [LinearMap.toMatrix_apply, hDomInl j]
            dsimp [Sigma]
            simpa [bCodΣ] using
              Module.Basis.sumQuot_repr_inr_of_mem bRange bCoker
                (((bRange j : LinearMap.range f) : Fin a → ℝ)) (bRange j).2 i
        | inr j =>
            rw [LinearMap.toMatrix_apply, hDomInr j]
            simp [Sigma]

  let eRows : (Fin r ⊕ Fin (a - r)) ≃ Fin a :=
    finSumFinEquiv.trans (finCongr (Nat.add_sub_of_le hra))
  let eCols : (Fin r ⊕ Fin (b - r)) ≃ Fin b :=
    finSumFinEquiv.trans (finCongr (Nat.add_sub_of_le hrb))

  let bDom : Basis (Fin b) ℝ (Fin b → ℝ) := bDomΣ.reindex eCols
  let bCod : Basis (Fin a) ℝ (Fin a → ℝ) := bCodΣ.reindex eRows

  have hReindex :
      LinearMap.toMatrix bDom bCod f =
        (LinearMap.toMatrix bDomΣ bCodΣ f).submatrix eRows.symm eCols.symm := by
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
          simp [hi, hj, hcond]
        · have hcond : ¬ ((i : ℕ) = (j : ℕ) ∧ (i : ℕ) < r) := by
            intro hc
            apply hij
            ext
            omega
          simp [hi, hj, hij, hcond]
      · have hjVal := col_inr_val hj
        have hcond : ¬ ((i : ℕ) = (j : ℕ) ∧ (i : ℕ) < r) := by
          intro hc
          omega
        simp [hi, hj, hcond]
    · have hiVal := row_inr_val hi
      have hcond : ¬ ((i : ℕ) = (j : ℕ) ∧ (i : ℕ) < r) := by
        intro hc
        omega
      simp [hi, hcond]

  let stdV : Basis (Fin b) ℝ (Fin b → ℝ) := Pi.basisFun ℝ (Fin b)
  let stdW : Basis (Fin a) ℝ (Fin a → ℝ) := Pi.basisFun ℝ (Fin a)

  have hstdLin : Matrix.toLin stdV stdW B = f := by
    dsimp [stdV, stdW, f]
    rw [Matrix.toLin_eq_toLin', Matrix.toLin'_apply']

  have hBstd : LinearMap.toMatrix stdV stdW f = B := by
    rw [← hstdLin]
    exact LinearMap.toMatrix_toLin stdV stdW B

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
      P * B * Q
          = P * (LinearMap.toMatrix stdV stdW f) * Q := by
              rw [← hBstd]
      _ = LinearMap.toMatrix bDom bCod f := by
              simpa [P, Q] using
                (basis_toMatrix_mul_linearMap_toMatrix_mul_basis_toMatrix
                  bDom stdV bCod stdW f)
      _ = Matrix.of (fun (i : Fin a) (j : Fin b) =>
              if (i : ℕ) = (j : ℕ) ∧ (i : ℕ) < r then (1 : ℝ) else 0) := hBlock

end

end DLNFibre.DLN.RLCT
```

Uncertain API flag: `[?]` I did not mechanically verify the simp-normal form for `LinearMap.quotKerEquivRange` on `Submodule.Quotient.mk`; the code relies on `simpa [bDomQuot, LinearMap.quotKerEquivRange]` in `hDomInl`. All other named lemmas above are either in your confirmed list, in the local repo, or in the generated Mathlib docs.