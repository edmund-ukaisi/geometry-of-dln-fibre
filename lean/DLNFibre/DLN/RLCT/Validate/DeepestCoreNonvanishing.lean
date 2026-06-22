import DLNFibre.DLN.RLCT.Validate.DeepestGaugeChart

/-!
# `DLNFibre.DLN.RLCT.Validate.DeepestCoreNonvanishing` — the `hMid ⟹ hGne` bridge

The L2 lemmas (`deepest_regular_smooth_split`, `deepest_regular_core_reduces`) carry the analytic
precondition `hGne`: the reduced core `dlnLoss M 0 ∘ flatSymm` is `≠ 0` a.e. on a neighbourhood of the
flat origin. This module discharges `hGne` from the structural non-degeneracy of the reduced widths.

## The fidelity finding (crux2, 2026-06-22) — the hypothesis is `r < H_s` for ALL `s`

`dlnLoss M 0 A = ‖prod M A‖²` (sum of squares of the layer-product entries). `hGne` (`≢ 0` a.e.) needs
the product map `prod M` to be NOT identically zero — which holds iff **every** reduced width
`M_s = H_s − r ≥ 1`, ENDPOINTS included. If any `M_s = 0` (interior `r = H_s`, or endpoint `r = H_0`
/ `r = H_L`), then `prod M ≡ 0` (a zero-width vertex annihilates the chain, or an entry-empty endpoint
product), so `dlnLoss M 0 ≡ 0` and `hGne` FAILS. The interior-only `hMid` (`∀ s, 0 < s.val → r < H
s.castSucc`) does NOT suffice — it misses `M_0 = 0` and `M_L = 0`. The faithful hypothesis is `∀ s,
1 ≤ M s` (equivalently `r < H_s ∀ s`). [Escalated to controller/fm3 — resolution (A) widen the locked
form vs (B) keep interior-only + a degenerate-endpoint branch (the headline IS true there, `lambdaCore
= 0`, only the smooth-block proof route breaks). This module proves the non-degenerate (all-`M_s ≥ 1`)
case, which both (A) and (B)'s non-vanishing branch need.]

## Route (crux2 own assessment; Codex consult g175 stalled on a contended CLI)

`hGne` needs `≠ 0` A.E. (not everywhere — the basepoint `0` has `dlnLoss M 0 0 = 0`), so a measure-zero
argument is unavoidable. Two pieces:
1. **The constructive nonzero witness** (`dlnLoss_deepest_core_ne_zero_witness`): an explicit `A` with
   `dlnLoss M 0 A ≠ 0` when all `M_s ≥ 1` — each layer `= e₀₀` (a `1` at `(0,0)`), so the product's
   `(0,0)` entry is `1`. Route-independent, pure algebra.
2. **The measure-zero of the polynomial zero-set** (`dlnLoss_deepest_core_ae_ne_zero`): `dlnLoss M 0 ∘
   flatSymm` is a nonzero polynomial, so `{= 0}` is measure-zero, so `≠ 0` a.e. The heavy piece (no
   multivariate "nonzero poly ⟹ ae ne zero" in Mathlib v4.29; `#vars`-induction + Fubini + univariate
   finite-roots, ~150-250 LoC). Roadmap-grade.
-/

open MeasureTheory Matrix
open scoped ENNReal BigOperators Topology
namespace DLNFibre.DLN.RLCT

variable {L : ℕ}

/-- The `e₀₀` witness parameter: every layer is the matrix with `1` at `(0,0)`, `0` elsewhere. The
constructive non-degeneracy witness — when every reduced width `M_s ≥ 1`, its layer product has
`(0,0)`-entry `1`, so `dlnLoss M 0` is `≥ 1 > 0` there (not identically zero). -/
noncomputable def e00Witness (M : Fin (L + 1) → ℕ) : Params M :=
  fun s => Matrix.of fun i j => if (i : ℕ) = 0 ∧ (j : ℕ) = 0 then (1 : ℝ) else 0

/-- A matrix-type cast (from dimension equalities) pushes through to entries of an `e₀₀`-style `of`
matrix: the cast preserves the polymorphic `if ↑i = 0 ∧ ↑j = 0` formula, with the indices `Fin.cast`-ed
(both `0 ↦ 0`). Used to evaluate `prodAux`'s cast-transported layer at `(0,0)`. -/
private theorem cast_e00_entry {a a' b b' : ℕ} (ha : a = a') (hb : b = b')
    (h : Matrix (Fin a) (Fin b) ℝ = Matrix (Fin a') (Fin b') ℝ)
    (f : Fin a → Fin b → ℝ) (i : Fin a') (j : Fin b') :
    (cast h (Matrix.of f)) i j = f (Fin.cast ha.symm i) (Fin.cast hb.symm j) := by
  subst ha; subst hb; rfl

/-- The `(0,0)` entry of the `e₀₀`-witness partial product is `1` (induction on chain length). The
`0`-indices are valid since each `M_s ≥ 1`. -/
theorem prodAux_e00Witness_zero (M : Fin (L + 1) → ℕ) (hpos : ∀ s, 1 ≤ M s)
    (k : ℕ) (hk : k < L + 1) :
    prodAux M (e00Witness M) k hk ⟨0, hpos 0⟩ ⟨0, hpos ⟨k, hk⟩⟩ = 1 := by
  induction k with
  | zero => simp [prodAux, Matrix.one_apply]
  | succ k ih =>
      have hk' : k < L + 1 := Nat.lt_of_succ_lt hk
      have hkL : k < L := Nat.lt_of_succ_lt_succ hk
      have e1 : (⟨k, hk'⟩ : Fin (L + 1)) = (⟨k, hkL⟩ : Fin L).castSucc := by
        apply Fin.ext; simp [Fin.castSucc]
      have e2 : (⟨k + 1, hk⟩ : Fin (L + 1)) = (⟨k, hkL⟩ : Fin L).succ := by
        apply Fin.ext; simp [Fin.succ]
      -- the cast-transported layer `Lyr` is the `e₀₀` matrix at the `prodAux`-needed type. Its entries:
      -- `Lyr i j = if ↑i=0 ∧ ↑j=0` (push the nested cast through via `cast_cast` + `cast_e00_entry`).
      set Lyr : Matrix (Fin (M ⟨k, hk'⟩)) (Fin (M ⟨k + 1, hk⟩)) ℝ :=
        (by rw [e1, e2]; exact e00Witness M ⟨k, hkL⟩) with hLyr
      have hLyr_entry : ∀ (i : Fin (M ⟨k, hk'⟩)) (j : Fin (M ⟨k + 1, hk⟩)),
          Lyr i j = if (i : ℕ) = 0 ∧ (j : ℕ) = 0 then (1 : ℝ) else 0 := by
        intro i j
        simp only [hLyr, e00Witness, eq_mpr_eq_cast, cast_cast]
        -- the collapsed single cast of an `of` matrix evaluates by `cast_e00_entry` (term-mode unify).
        exact (cast_e00_entry (congrArg M e1) (congrArg M e2) (by rw [e1, e2]) _ i j).trans (by
          simp [Fin.coe_cast])
      -- `prodAux (k+1) = prodAux k * Lyr`; evaluate at `(0,0)` via `mul_apply` + the single 0-term.
      show (prodAux M (e00Witness M) k hk' * Lyr) ⟨0, hpos 0⟩ ⟨0, hpos ⟨k + 1, hk⟩⟩ = 1
      rw [Matrix.mul_apply,
        Finset.sum_eq_single (⟨0, hpos ⟨k, hk'⟩⟩ : Fin (M ⟨k, hk'⟩))]
      · rw [ih hk', hLyr_entry]; simp
      · intro l _ hl
        have hl0 : (l : ℕ) ≠ 0 := fun h => hl (Fin.ext h)
        rw [hLyr_entry]; simp [hl0]
      · intro h; exact absurd (Finset.mem_univ _) h

theorem dlnLoss_deepest_core_ne_zero_witness (M : Fin (L + 1) → ℕ) (hpos : ∀ s, 1 ≤ M s) :
    ∃ A : Params M, dlnLoss M (0 : Matrix (Fin (M 0)) (Fin (M (Fin.last L))) ℝ) A ≠ 0 := by
  refine ⟨e00Witness M, ?_⟩
  -- `prod M (e00) (0,0) = 1`, so the `(0,0)` summand of `dlnLoss = ∑∑ (prod − 0)²` is `1 > 0`.
  have hprod : prod M (e00Witness M) ⟨0, hpos 0⟩ ⟨0, hpos (Fin.last L)⟩ = 1 := by
    have := prodAux_e00Witness_zero M hpos L (Nat.lt_succ_self L)
    -- `prod = prodAux L`, and `⟨0, hpos ⟨L, _⟩⟩ = ⟨0, hpos (Fin.last L)⟩` (same `Fin.last`).
    rw [prod]
    convert this using 2
  -- the loss is a sum of squares with a `1`-term, so it is positive (hence `≠ 0`).
  intro hzero
  have hsq : (prod M (e00Witness M) ⟨0, hpos 0⟩ ⟨0, hpos (Fin.last L)⟩
      - (0 : Matrix (Fin (M 0)) (Fin (M (Fin.last L))) ℝ) ⟨0, hpos 0⟩ ⟨0, hpos (Fin.last L)⟩) ^ 2 = 0 := by
    have hnn : ∀ i, (0 : ℝ) ≤ ∑ j, ((prod M (e00Witness M) - 0) i j) ^ 2 :=
      fun i => Finset.sum_nonneg fun j _ => sq_nonneg _
    have hi : ∑ j, ((prod M (e00Witness M) - 0) ⟨0, hpos 0⟩ j) ^ 2 = 0 := by
      have := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => hnn i)).1 hzero ⟨0, hpos 0⟩
        (Finset.mem_univ _)
      simpa using this
    have := (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => sq_nonneg _)).1 hi
      ⟨0, hpos (Fin.last L)⟩ (Finset.mem_univ _)
    simpa [Matrix.sub_apply] using this
  simp only [Matrix.zero_apply, sub_zero, hprod] at hsq
  norm_num at hsq

/-- **The reduced core is `≠ 0` a.e. near the origin** (`hGne`, the bridge target). When every reduced
width `M_s ≥ 1`, `dlnLoss M 0 ∘ (paramsEquivFlat M).symm` is a nonzero polynomial, so its zero set is
measure-zero, so it is `≠ 0` a.e. on any neighbourhood of `0`. The measure-zero of a nonzero-polynomial
zero-set is the heavy step (roadmap; see header). -/
theorem dlnLoss_deepest_core_ae_ne_zero (M : Fin (L + 1) → ℕ) (hpos : ∀ s, 1 ≤ M s) :
    ∃ U ∈ 𝓝 (0 : Fin (flatDim M) → ℝ),
      ∀ᵐ z ∂(volume.restrict U),
        dlnLoss M (0 : Matrix (Fin (M 0)) (Fin (M (Fin.last L))) ℝ)
          ((paramsEquivFlat M).symm z) ≠ 0 := by
  sorry

end DLNFibre.DLN.RLCT
