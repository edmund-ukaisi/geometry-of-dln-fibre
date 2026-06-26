import DLNFibre.DLN.RLCT.Validate.RouteMChainFactor
import Mathlib.Logic.Equiv.Fin.Basic

/-!
# `RouteMChainBlock` — the block-assembly engine (`Q_s`, `A^(s)` on `Fin (M k)`, the chaining `hQA`)

The per-`M` achiever chain's `hQA` (the cert's unit-triangular `B/C`-chaining `Q_s · A^(s) = C_{s+1}`)
lives on the AMBIENT widths `Fin (M k)`, but the block algebra `[I | N]·[C − N·W ; W] = C`
(`chain_block`) lives on the sum-split `Fin t ⊕ Fin c`. This module banks the seam: the canonical width
split `finSplit`, the chaining row `chainQ` (`= [I | N]` reindexed onto `Fin M'` columns) and the lift
column `chainA` (`= [C − N·W ; W]` reindexed onto `Fin M'` rows), and the chaining identity
`chainQ_mul_chainA : chainQ · chainA = C` — proved once, M-agnostically, by the `submatrix_mul_equiv`
inner-equiv cancellation reducing to `chain_block` (the decorrelated-Codex `S-hybrid` route).

The per-`M` achiever `FactoredChain` then supplies `Qmat k := chainQ …`, `A k := chainA …`, and
`hQA k := chainQ_mul_chainA …` directly — the dependent-`Fin (M k)` block algebra is closed here. The
residual per-`M` work is `hC` (the compressed-transition shape `C_k = B_k·Q_k + u•R̄_k`) + the width
profile + the `B`/`C`/`R` matrices.

* `finSplit` — the canonical `Fin M ≃ Fin t ⊕ Fin (M − t)` (`finCongr ∘ finSumFinEquiv.symm`).
* `chainQ` / `chainA` — the chaining row / lift column, reindexed onto `Fin M'`.
* `chainQ_mul_chainA` — `chainQ · chainA = C` (the `hQA` content, on `Fin (M k)`).

Axiom-clean `[propext, Classical.choice, Quot.sound]` (pure matrix algebra; no analysis).
-/

namespace DLNFibre.DLN.RLCT

open Matrix

/-- **The canonical width split** `Fin M ≃ Fin t ⊕ Fin (M − t)` (`t ≤ M`): kept directions first,
residual second. The single equivalence reused at every block seam (the cast-at-the-equiv-level
discipline; do NOT rebuild equivalent splits with fresh `by omega` proofs). -/
noncomputable def finSplit {t M : ℕ} (h : t ≤ M) : Fin M ≃ Fin t ⊕ Fin (M - t) :=
  (finCongr (show M = t + (M - t) by omega)).trans finSumFinEquiv.symm

/-- **The chaining row `Q_s = [I_t | N_s]`** on `Fin M'` columns. The horizontal block `[I | N]` (over
`Fin t ⊕ Fin (M' − t)`) with the residual block `N : t × c` reindexed to the `Fin (M' − t)` residual
slot (`c = M' − t`) and the whole row's columns reindexed onto `Fin M'`. -/
noncomputable def chainQ {M' t c : ℕ} (h : t + c = M') (N : Matrix (Fin t) (Fin c) ℝ) :
    Matrix (Fin t) (Fin M') ℝ :=
  Matrix.reindex (Equiv.refl (Fin t)) (finSplit (M := M') (t := t) (by omega)).symm
    (Matrix.of (fun (i : Fin t) (j : Fin t ⊕ Fin (M' - t)) =>
      Sum.elim ((1 : Matrix (Fin t) (Fin t) ℝ) i)
        (Matrix.reindex (Equiv.refl (Fin t)) (finCongr (by omega : c = M' - t)) N i) j))

/-- **The lift column `A^(s) = [C_{s+1} − N_s W_{s+1} ; W_{s+1}]`** on `Fin M'` rows. The vertical block
`[C − N·W ; W]` (over `Fin t ⊕ Fin (M' − t)`) with the residual lift `W : c × m'` reindexed to the
`Fin (M' − t)` residual slot, and the whole column's rows reindexed onto `Fin M'`. The cert's
unit-triangular chaining factor `G_s⁻¹ [C_{s+1} ; W_{s+1}]`. -/
noncomputable def chainA {M' t c m' : ℕ} (h : t + c = M') (N : Matrix (Fin t) (Fin c) ℝ)
    (W : Matrix (Fin c) (Fin m') ℝ) (C : Matrix (Fin t) (Fin m') ℝ) :
    Matrix (Fin M') (Fin m') ℝ :=
  Matrix.reindex (finSplit (M := M') (t := t) (by omega)).symm (Equiv.refl (Fin m'))
    (Matrix.of (fun (i : Fin t ⊕ Fin (M' - t)) (j : Fin m') =>
      Sum.elim (C - N * W)
        (Matrix.reindex (finCongr (by omega : c = M' - t)) (Equiv.refl (Fin m')) W) i j))

/-- **The chaining identity `Q_s · A^(s) = C_{s+1}`** (on `Fin (M k)`). `chainQ · chainA = C`: the
column-reindex of `chainQ` and the row-reindex of `chainA` share the `finSplit` inner equiv, which
cancels under `submatrix_mul_equiv`, collapsing the product to the on-block `chain_block`
(`[I | N']·[C − N'·W' ; W'] = C` with `N' = N.submatrix id e.symm`, `W' = W.submatrix e.symm id`; the
residual-block reindex `e = finCongr (c = M' − t)` distributes through `N'·W' = N·W`). The cert's
`B/C`-chaining, closed M-agnostically. -/
theorem chainQ_mul_chainA {M' t c m' : ℕ} (h : t + c = M') (N : Matrix (Fin t) (Fin c) ℝ)
    (W : Matrix (Fin c) (Fin m') ℝ) (C : Matrix (Fin t) (Fin m') ℝ) :
    chainQ h N * chainA h N W C = C := by
  unfold chainQ chainA
  simp only [Matrix.reindex_apply, Equiv.refl_symm, Equiv.symm_symm]
  rw [Matrix.submatrix_mul_equiv _ _ _ (finSplit (M := M') (t := t) (by omega)) _]
  set e := finCongr (show c = M' - t by omega) with he
  have hNW : (N.submatrix (Equiv.refl (Fin t)) e.symm) * (W.submatrix e.symm (Equiv.refl (Fin m')))
      = N * W := by
    rw [Matrix.submatrix_mul_equiv N W (Equiv.refl (Fin t)) e.symm (Equiv.refl (Fin m'))]; simp
  rw [← hNW]
  simp only [Equiv.coe_refl, Matrix.submatrix_id_id]
  exact chain_block (N.submatrix id (e.symm : Fin (M' - t) → Fin c))
    (W.submatrix (e.symm : Fin (M' - t) → Fin c) id) C

end DLNFibre.DLN.RLCT
