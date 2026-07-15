/-
Copyright (c) 2026. Released under Apache 2.0; see LICENSE.
-/
import DLNFibre.DLN.RLCT.Validate.RouteMSJDeepIndex
import DLNFibre.DLN.RLCT.Validate.RouteMSJDeepChainPeel
import DLNFibre.DLN.RLCT.Validate.RouteMSJDeepCover
import DLNFibre.DLN.RLCT.Validate.RouteMSJIncidenceGluing

set_option linter.style.longLine false
set_option linter.unusedVariables false

/-!
# `RouteMSJDeepCoverage` — the deep atlas coverage + gluing (Tide B §3.2/§3.3)

**Thread `genm-deepatlas`, aoyagi-full Stage 2 (branch β, NATIVE).** The set-theoretic
**coverage-completeness** of the deep stratified-resolution atlas (design §3.2) and the **null-overlap
gluing** wiring (§3.3), assembled on the banked spine (leaf `rankEqLocus_eq_iUnion_pivot_inter`,
general-pivot bridge `generalPivot_reduce_rank`, chain descent `prodAux_reduce_rank`, finite index
`CRIndex`). Design locked by the `gluing-shape` Codex pass; the coverage is INVARIANT-FREE (an earlier
`Q.rank = q` invariant does NOT survive the descent — the terminal cell carries the rank constraint
instead, so the coverage holds for ANY right factor `Q`).

## The cells and coverage

`deepCell` recurses on a CR-path, threading the effective-state right factor `Q` (a function of the
parameter tuple, whose type shrinks along the path): a descent node cuts to the pivot chart
`{IsUnit ((effLayer·Q).submatrix ρ κ) ∧ (effLayer·Q).rank ≤ r}` (exact-rank, non-vacuous) and reduces
`Q` to `Q' = (effLayer·Q)[:,κ]·((effLayer·Q)[ρ,κ])⁻¹`; the terminal cell is `{A | (Q A).rank ≤ s}`.

* **`deepCover_aux`** — the coverage set-equality, by chain-length induction on the effective state:
  `{A | (prodAux j · Q A).rank ≤ s} = ⋃ path, deepCell … path Q`, for any `Q`. Base: `prodAux 0 = 1`,
  the terminal cell IS the constraint. Step: the leaf covers `⋃ (rank, pivot)`, the chain descent
  `prodAux_reduce_rank_of` swaps the composed rank for the reduced state's, and the induction closes.
* **`deepRankLE_eq_iUnion_cells`** — the top-level coverage at the full chain (`Q = 1`):
  `{A | (prod H A).rank ≤ s} = ⋃ i : CRIndex H, deepCell … i (fun _ ↦ 1)`.
* **`deepRankLE_lintegral_lt_top`** — the gluing wrapper: for a GENERIC `ℝ≥0∞` integrand `f`, per-cell
  finiteness gives `∫⁻_{rank ≤ s} f < ⊤`. ONE application of the banked
  `lintegral_lt_top_of_finite_cover` (`hcover` trivial from the set-equality). **Loss-independent**:
  `f` is generic; per-cell finiteness `hfin` is a HYPOTHESIS (the loss tide discharges it, carrying the
  `|det J|` weight). No measurability needed (the gluing lemma requires none).

Standalone (NOT aggregator-wired). Axiom target `[propext, Classical.choice, Quot.sound]`.
-/

namespace DLNFibre.DLN.RLCT

open Matrix

namespace DeepAtlas

variable {L : ℕ}

/-- **The chain descent with an EXPLICIT rank `r`.** `prodAux_reduce_rank` taking the effective layer's
rank as a witness `hr : (effLayer·Q).rank = r` and a size-`r` pivot, matching a CR-path node's data.
`subst hr` reduces to `prodAux_reduce_rank`. -/
theorem prodAux_reduce_rank_of (H : Fin (L + 1) → ℕ) (A : Params H) (k q : ℕ) (hk : k + 1 < L + 1)
    (Q : Matrix (Fin (H (⟨k + 1, hk⟩ : Fin (L + 1)))) (Fin q) ℝ) (r : ℕ)
    (hr : (effLayer H A k hk * Q).rank = r) (ρ : Fin r ↪ Fin (H (⟨k, by omega⟩ : Fin (L + 1))))
    (κ : Fin r ↪ Fin q) (hU : IsUnit ((effLayer H A k hk * Q).submatrix ρ κ)) :
    (prodAux H A (k + 1) hk * Q).rank
      = (prodAux H A k (Nat.lt_of_succ_lt hk) * (effLayer H A k hk * Q).submatrix id κ
          * ((effLayer H A k hk * Q).submatrix ρ κ)⁻¹).rank := by
  subst hr; exact prodAux_reduce_rank H A k q hk Q ρ κ hU

/-- **The atlas cell of a CR-path.** Recurses on the path, threading the effective-state right factor
`Q`: a descent node is the pivot chart (exact-rank, non-vacuous) intersected with the reduced-factor
tail cell; the terminal cell is `{A | (Q A).rank ≤ s}`. Invariant-free (the rank-`≤ s` constraint lives
in the terminal cell, not the index). -/
noncomputable def deepCell (H : Fin (L + 1) → ℕ) (s : ℕ) :
    (j : ℕ) → (hj : j ≤ L) → (q : ℕ) → CRPath H j hj q
      → (Params H → Matrix (Fin (H ⟨j, Nat.lt_succ_of_le hj⟩)) (Fin q) ℝ) → Set (Params H)
  | 0, _, _, _, Q => {A | (Q A).rank ≤ s}
  | (k + 1), hk, q, ⟨r, ρ, κ, tail⟩, Q =>
      {A | IsUnit ((effLayer H A k (Nat.lt_succ_of_le hk) * Q A).submatrix ρ κ)
            ∧ (effLayer H A k (Nat.lt_succ_of_le hk) * Q A).rank ≤ r.1}
        ∩ deepCell H s k (Nat.le_of_succ_le hk) r.1 tail
            (fun A => (effLayer H A k (Nat.lt_succ_of_le hk) * Q A).submatrix id κ
              * ((effLayer H A k (Nat.lt_succ_of_le hk) * Q A).submatrix ρ κ)⁻¹)

/-- **Coverage set-equality (the deferred charts-exhaust obligation, invariant-free).** For any
effective state (level `j`, right factor `Q`), the rank-`≤ s` locus of `prodAux j · Q` is exactly the
union of the CR-path cells. Chain-length induction: base is `prodAux 0 = 1` + the terminal cell; the
step covers by the actual-rank pivot (`exists_nonsingular_submatrix_of_le_rank` / leaf) and swaps the
composed rank for the reduced state's via the chain descent `prodAux_reduce_rank_of`. No `Q.rank = q`
invariant — the terminal cell carries the constraint. -/
theorem deepCover_aux (H : Fin (L + 1) → ℕ) (s : ℕ) :
    ∀ (j : ℕ) (hj : j ≤ L) (q : ℕ)
      (Q : Params H → Matrix (Fin (H ⟨j, Nat.lt_succ_of_le hj⟩)) (Fin q) ℝ),
      {A | (prodAux H A j (Nat.lt_succ_of_le hj) * Q A).rank ≤ s}
        = ⋃ path : CRPath H j hj q, deepCell H s j hj q path Q := by
  intro j
  induction j with
  | zero =>
      intro hj q Q
      ext A
      simp only [Set.mem_setOf_eq, Set.mem_iUnion]
      have hb : prodAux H A 0 (Nat.lt_succ_of_le hj) * Q A = Q A := by
        have h1 : prodAux H A 0 (Nat.lt_succ_of_le hj)
            = (1 : Matrix (Fin (H ⟨0, Nat.lt_succ_of_le hj⟩)) (Fin (H ⟨0, Nat.lt_succ_of_le hj⟩)) ℝ) :=
          rfl
        rw [h1]; exact Matrix.one_mul (Q A)
      rw [hb]
      constructor
      · intro h; exact ⟨(), show A ∈ deepCell H s 0 hj q () Q from by unfold deepCell; exact h⟩
      · rintro ⟨_, h⟩; unfold deepCell at h; exact h
  | succ k ih =>
      intro hj q Q
      have hk' : k + 1 < L + 1 := Nat.lt_succ_of_le hj
      have hkL : k ≤ L := by omega
      ext A
      simp only [Set.mem_setOf_eq, Set.mem_iUnion]
      constructor
      · intro hA
        obtain ⟨ρ, κ, hUpiv⟩ :=
          exists_nonsingular_submatrix_of_le_rank (effLayer H A k hk' * Q A)
            (le_refl (effLayer H A k hk' * Q A).rank)
        have hrle : (effLayer H A k hk' * Q A).rank
            < min (H ⟨k, Nat.lt_of_succ_lt hk'⟩) q + 1 := by
          have hw : (effLayer H A k hk' * Q A).rank ≤ q := Matrix.rank_le_width _
          have hh : (effLayer H A k hk' * Q A).rank ≤ H ⟨k, Nat.lt_of_succ_lt hk'⟩ := by
            have := Matrix.rank_le_card_height (effLayer H A k hk' * Q A)
            simpa only [Fintype.card_fin] using this
          rw [Nat.lt_succ_iff, le_min_iff]; exact ⟨hh, hw⟩
        set r : Fin (min (H ⟨k, Nat.lt_of_succ_lt hk'⟩) q + 1) :=
          ⟨(effLayer H A k hk' * Q A).rank, hrle⟩
        have hrank :=
          prodAux_reduce_rank_of H A k q hk' (Q A) (effLayer H A k hk' * Q A).rank rfl ρ κ hUpiv
        rw [Matrix.mul_assoc (prodAux H A k (Nat.lt_of_succ_lt hk'))
          ((effLayer H A k hk' * Q A).submatrix id κ)
          ((effLayer H A k hk' * Q A).submatrix ρ κ)⁻¹] at hrank
        have hcov := ih hkL r.1
          (fun A' => (effLayer H A' k hk' * Q A').submatrix id κ
            * ((effLayer H A' k hk' * Q A').submatrix ρ κ)⁻¹)
        rw [Set.ext_iff] at hcov
        have := (hcov A).mp (by simp only [Set.mem_setOf_eq]; rw [← hrank]; exact hA)
        simp only [Set.mem_iUnion] at this
        obtain ⟨tail, htail⟩ := this
        exact ⟨⟨r, ρ, κ, tail⟩, ⟨hUpiv, le_of_eq rfl⟩, htail⟩
      · rintro ⟨⟨r, ρ, κ, tail⟩, hpiv, htail⟩
        have hUpiv : IsUnit ((effLayer H A k hk' * Q A).submatrix ρ κ) := hpiv.1
        have hge : r.1 ≤ (effLayer H A k hk' * Q A).rank := isUnit_submatrix_le_rank _ ρ κ hUpiv
        have hr : (effLayer H A k hk' * Q A).rank = r.1 := le_antisymm hpiv.2 hge
        have hrank := prodAux_reduce_rank_of H A k q hk' (Q A) r.1 hr ρ κ hUpiv
        rw [Matrix.mul_assoc (prodAux H A k (Nat.lt_of_succ_lt hk'))
          ((effLayer H A k hk' * Q A).submatrix id κ)
          ((effLayer H A k hk' * Q A).submatrix ρ κ)⁻¹] at hrank
        have hcov := ih hkL r.1
          (fun A' => (effLayer H A' k hk' * Q A').submatrix id κ
            * ((effLayer H A' k hk' * Q A').submatrix ρ κ)⁻¹)
        rw [Set.ext_iff] at hcov
        rw [hrank]
        have hthis := (hcov A).mpr (by simp only [Set.mem_iUnion]; exact ⟨tail, htail⟩)
        simpa only [Set.mem_setOf_eq] using hthis

/-- **Top-level coverage: the deep rank locus is the finite union of the atlas cells.** At the full
chain (`Q = 1`), `{A | (prod H A).rank ≤ s} = ⋃ i : CRIndex H, deepCell … i (fun _ ↦ 1)`. The
non-vacuous, invariant-free realisation of the deep charts-exhaust completeness. -/
theorem deepRankLE_eq_iUnion_cells (H : Fin (L + 1) → ℕ) (s : ℕ) :
    {A : Params H | (prod H A).rank ≤ s}
      = ⋃ i : CRIndex H, deepCell H s L le_rfl (H (Fin.last L)) i
          (fun _ => (1 : Matrix (Fin (H (Fin.last L))) (Fin (H (Fin.last L))) ℝ)) := by
  have haux := deepCover_aux H s L le_rfl (H ⟨L, Nat.lt_succ_of_le le_rfl⟩)
    (fun _ => (1 : Matrix (Fin (H ⟨L, Nat.lt_succ_of_le le_rfl⟩))
      (Fin (H ⟨L, Nat.lt_succ_of_le le_rfl⟩)) ℝ))
  simp only [Matrix.mul_one] at haux
  simp only [CRIndex]
  exact haux

open MeasureTheory in
/-- **Null-overlap gluing (§3.3, generic-`f` / loss-independent).** From per-cell finiteness of a
generic `ℝ≥0∞` integrand `f`, the rank-`≤ s` domain integral is finite. ONE application of the banked
atlas-parameterised `lintegral_lt_top_of_finite_cover`; `hcover` is trivial (the cells exhaust the
domain by `deepRankLE_eq_iUnion_cells`). Per-cell finiteness `hfin` stays a HYPOTHESIS — the loss tide
discharges it (carrying `|det J|`); nothing loss-specific enters here. -/
theorem deepRankLE_lintegral_lt_top (H : Fin (L + 1) → ℕ) (s : ℕ)
    {μ : Measure (Params H)} (f : Params H → ENNReal)
    (hfin : ∀ i : CRIndex H, ∫⁻ A in deepCell H s L le_rfl (H (Fin.last L)) i
        (fun _ => (1 : Matrix (Fin (H (Fin.last L))) (Fin (H (Fin.last L))) ℝ)), f A ∂μ < ⊤) :
    ∫⁻ A in {A : Params H | (prod H A).rank ≤ s}, f A ∂μ < ⊤ := by
  refine lintegral_lt_top_of_finite_cover
    (fun i : CRIndex H => deepCell H s L le_rfl (H (Fin.last L)) i
      (fun _ => (1 : Matrix (Fin (H (Fin.last L))) (Fin (H (Fin.last L))) ℝ)))
    {A : Params H | (prod H A).rank ≤ s} f ?_ hfin
  rw [deepRankLE_eq_iUnion_cells]
  simp

end DeepAtlas

end DLNFibre.DLN.RLCT
