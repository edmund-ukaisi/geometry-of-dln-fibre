import DLNFibre.DLN.RLCT.Validate.RouteMSJTailProd
import DLNFibre.DLN.RLCT.Validate.RouteMFrontPeel
import DLNFibre.DLN.RLCT.Validate.RouteMBoxReduction
import DLNFibre.DLN.RLCT.Validate.MatMulFibre
import DLNFibre.DLN.RLCT.Validate.RouteMLayerSplit
import DLNFibre.DLN.RLCT.Validate.RouteMSJDecoratedCharge
import DLNFibre.DLN.RLCT.Foundations.Rlct
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.MeasurableSpace.Embedding

/-!
# `DLNFibre.DLN.RLCT.Validate.RouteMSJHeadSplit` — the `Params` head-split + dim-clause bedrock (#5)

**Thread `genm-sj5` (#5 `DecoratedStepHyp`, S1 foundation).** The reusable measure/algebra bedrock the
`#5` reduced-comparator construction (the reduced-decoration producibility, `RouteMSJCornerComparator`)
consumes for its `genuineCarrier` obligation — the piece the base-leg witness (`witnessDecoration222`)
left un-asserted and the recon flagged as `#5`'s own obligation:

* **`paramsHeadSplit M`** — the measure-preserving head split
  `Params M ≃ᵐ (Fin (M 0) → Fin (M 1) → ℝ) × Params (dropHead M)` (peel the FIRST layer as a free front
  block over the head-dropped tail). Built directly from `MeasurableEquiv.piFinSuccAbove` at index `0`
  over the RAW pi type (`Fin _ → Fin _ → ℝ`, per the measure-diamond pitfall) — the tail type is DEFEQ to
  `Params (dropHead M)` (the `succAbove 0 = succ` / `castSucc_succ` reindex), so no cast is needed.
  Measure-preserving (`volume_preserving_piFinSuccAbove`); components are `.1 = A 0`, `.2 = A ∘ succ`.

* **`prod_headSplit`** — the layer-product head factorization in the raw-`rmatMul` form:
  `prod M A = rmatMul (A 0) (prod (dropHead M) (A ∘ succ))`. Wraps the banked matrix-`*` front-peel
  `prod_front_peel` (`Mtail = dropHead` definitionally, the `finCongr` reindexes collapse), transported to
  the entrywise `rmatMul` the `(S,J)` carrier residuals live in.

* **`minAdm_leading_zero` / `minAdm_le_mul_head`** — the dim-clause bound `minAdm M ≤ M 0 · M 1` (widths
  `≥ 2`), via the `t = 0` cut of the charge fold + the fact that a leading-zero chain has `minAdm = 0`.
  This is the `γ'` dims clause `minAdm M ≤ a · M 1` at the FORCED faithful row-count `a = M 0`.

S2-FREE: measure plumbing + banked matrix algebra + `minAdmRec` order. Axiom-clean
`[propext, Classical.choice, Quot.sound]`.
-/

namespace DLNFibre.DLN.RLCT

open Matrix MeasureTheory
open scoped BigOperators

variable {L : ℕ}

/-! ## The measure-preserving `Params` head split -/

/-- **The `Params` head split** `Params M ≃ᵐ (Fin (M 0) → Fin (M 1) → ℝ) × Params (dropHead M)` — peel
the leading layer (index `0`) as a free front block over the head-dropped tail. `MeasurableEquiv.piFinSuccAbove`
at `0` over the raw pi type; the tail type `∀ j, (0).succAbove j …` is DEFEQ to `Params (dropHead M)`. -/
noncomputable def paramsHeadSplit (M : Fin (L + 1 + 1) → ℕ) :
    Params M ≃ᵐ (Fin (M 0) → Fin (M 1) → ℝ) × Params (dropHead M) :=
  MeasurableEquiv.piFinSuccAbove
    (fun s : Fin (L + 1) => Fin (M s.castSucc) → Fin (M s.succ) → ℝ) 0

/-- The head split is measure-preserving (`volume_preserving_piFinSuccAbove`). -/
theorem paramsHeadSplit_mp (M : Fin (L + 1 + 1) → ℕ) :
    MeasurePreserving (paramsHeadSplit M) (volume : Measure (Params M)) volume :=
  volume_preserving_piFinSuccAbove
    (fun s : Fin (L + 1) => Fin (M s.castSucc) → Fin (M s.succ) → ℝ) 0

/-- The head component reads the leading layer `A 0`. -/
@[simp] theorem paramsHeadSplit_fst (M : Fin (L + 1 + 1) → ℕ) (A : Params M) :
    (paramsHeadSplit M A).1 = A 0 := rfl

/-- The tail component reads the head-dropped layers `A ∘ succ` (`= Atail M A`). -/
@[simp] theorem paramsHeadSplit_snd (M : Fin (L + 1 + 1) → ℕ) (A : Params M) (j : Fin L) :
    (paramsHeadSplit M A).2 j = A j.succ := rfl

/-- **The head split pulls the product box back to the `Params` box.** The front block box `matBox`
(entries of `A 0` in `[−1,1]`) times the tail `paramsBoxM (dropHead M) 1` pulls back under
`paramsHeadSplit` to the full `paramsBoxM M 1` (all layer entries bounded). -/
theorem paramsHeadSplit_preimage_box (M : Fin (L + 1 + 1) → ℕ) :
    paramsHeadSplit M ⁻¹' (matBox (M 0) (M 1) 1 ×ˢ paramsBoxM (dropHead M) 1)
      = paramsBoxM M 1 := by
  ext A
  simp only [Set.mem_preimage, Set.mem_prod, matBox, paramsBoxM, dropHead, Set.mem_setOf_eq,
    paramsHeadSplit_fst, paramsHeadSplit_snd]
  constructor
  · rintro ⟨h0, htail⟩ s i j
    rcases Fin.eq_zero_or_eq_succ s with rfl | ⟨s', rfl⟩
    · exact h0 i j
    · exact htail s' i j
  · intro h
    exact ⟨fun i j => h 0 i j, fun s' i j => h s'.succ i j⟩

/-! ## The layer-product head factorization (raw `rmatMul` form) -/

/-- **The layer-product head factorization** `prod M A = rmatMul (A 0) (prod (dropHead M) (A ∘ succ))`
(entrywise, the raw form the `(S,J)` residuals live in). Wraps the banked matrix-`*` front-peel
`prod_front_peel` (`Mtail M = dropHead M` definitionally, `Atail M A` reads `A ∘ succ`); the `finCongr`
reindexes are `rfl`-true so they collapse to the identity, and `Matrix.mul_apply` matches `rmatMul`. -/
theorem prod_headSplit (M : Fin (L + 1 + 1) → ℕ) (A : Params M) :
    (prod M A : Fin (M 0) → Fin (M (Fin.last (L + 1))) → ℝ)
      = rmatMul (A 0) (prod (dropHead M) (fun j => A j.succ)) := by
  have emid : Mtail M (0 : Fin (L + 1)) = M ((0 : Fin (L + 1)).succ) := rfl
  have ecol : Mtail M (Fin.last L) = M (Fin.last (L + 1)) := by
    simp only [Mtail, Fin.succ_last]
  rw [prod_front_peel M A emid ecol,
      show (finCongr emid) = Equiv.refl _ from finCongr_refl _,
      show (finCongr ecol) = Equiv.refl _ from finCongr_refl _]
  erw [Matrix.reindex_refl_refl]
  rfl

/-! ## The dim-clause bound `minAdm M ≤ M 0 · M 1` -/

/-- **A leading-zero chain has `minAdm = 0`.** If `M 0 = 0` then no product constraint binds (the top
row-count is empty), so the minimal admissible codim is `0`. Induction on width via `minAdmRec`: at width
`≥ 2` the legal cut is forced to `t = 0` (`min (M 0) (M 1) = 0`), the block charge `(M 0)(M 1) = 0`
vanishes, and `redChain 0 M` again leads with `0`. -/
theorem minAdm_leading_zero : ∀ {L : ℕ} (M : Fin (L + 1) → ℕ), M 0 = 0 → minAdm M = 0
  | 0, M, _ => by
      -- width 1: `minAdm` is `0` (the `minAdmRec` leaf-below case).
      rw [← minAdmRec_eq_minAdm]; rfl
  | 1, M, h0 => by
      -- width 2: `minAdm = M 0 · M 1 = 0`.
      rw [← minAdmRec_eq_minAdm, minAdmRec_leaf, h0, Nat.zero_mul]
  | (_ + 1 + 1), M, h0 => by
      rw [← minAdmRec_eq_minAdm, minAdmRec_succ_succ]
      have hrec : minAdmRec (redChain 0 M) = 0 := by
        rw [minAdmRec_eq_minAdm]
        exact minAdm_leading_zero (redChain 0 M) (redChain_zero 0 M)
      apply le_antisymm _ (Nat.zero_le _)
      have h0mem : (0 : ℕ) ∈ Finset.range (min (M 0) (M 1) + 1) := by
        rw [Finset.mem_range]; omega
      refine le_trans (Finset.inf'_le _ h0mem) ?_
      simp [h0, hrec]

/-- **The dim-clause bound `minAdm M ≤ M 0 · M 1`** (widths `≥ 2`). The `γ'` dims clause
`minAdm M ≤ a · M 1` at the faithful row-count `a = M 0`. Via the `t = 0` cut of the charge fold
(`minAdm_le_peelCharge_add_redChain`, so `minAdm M ≤ M 0 · M 1 + minAdm (redChain 0 M)`) plus the fact
that `redChain 0 M` leads with `0`, hence `minAdm (redChain 0 M) = 0`. -/
theorem minAdm_le_mul_head : ∀ {L : ℕ} (M : Fin (L + 1 + 1) → ℕ), minAdm M ≤ M 0 * M 1
  | 0, M => by rw [← minAdmRec_eq_minAdm, minAdmRec_leaf]
  | (_ + 1), M => by
      have hcut : (0 : ℕ) ≤ min (M 0) (M 1) := Nat.zero_le _
      have h := minAdm_le_peelCharge_add_redChain M 0 hcut
      have hrec : minAdm (redChain 0 M) = 0 :=
        minAdm_leading_zero (redChain 0 M) (redChain_zero 0 M)
      simpa [peelCharge, hrec] using h

end DLNFibre.DLN.RLCT
