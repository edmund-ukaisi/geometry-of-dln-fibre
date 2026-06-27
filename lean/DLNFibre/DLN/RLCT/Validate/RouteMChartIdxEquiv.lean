import DLNFibre.DLN.RLCT.Validate.RouteMChartIdx

/-!
# `RouteMChartIdxEquiv` — Phase B item 1 finish: `ChartIdx` + `card = flatDim` + `Fin N ≃ ChartIdx`

The determinant-ready bijective coordinatization (item 1 of the det route, B+b1), built on the arithmetic
foundation `chartDim_eq_flatDim` (`RouteMChartIdx`). The chart coordinates split, per boundary `k : Fin L`,
into a **Schur block** of size `t_k·M_{k+1}` (the `K/X/N/E` roles, `= (t_k+r_k)(t_k+c_k)`) and a **chain
lift** of size `c_k·M_{k+2}` (`0` at the leaf). The radial and the fixed residual already cancel in
`chartDim_eq_flatDim` (no `±1`), so `card (ChartIdx) = ∑_k (schurDim k + liftDim k) = flatDim M`.

* `ChartIdx M t` — `Σ k : Fin L, Fin (schurDim k) ⊕ Fin (liftDim k)` (the per-boundary role coordinates).
* `card_chartIdx` — `Fintype.card (ChartIdx M t) = flatDim M` (`Fintype.card_sigma` + the foundation).
* `chartIdxEquiv` — `Fin (routeMAmbient M) ≃ ChartIdx M t` (`Fintype.equivFin` + the cardinality).

Axiom-clean `[propext, Classical.choice, Quot.sound]` (finite cardinality; no analysis).
-/

namespace DLNFibre.DLN.RLCT

open scoped BigOperators

variable {L : ℕ}

/-! ## The per-boundary role dimensions (ℕ-indexed, from the descent path) -/

/-- The Schur-block coordinate count at boundary `k`: `t_k·M_{k+1}` (`= (t_k+r_k)(t_k+c_k)`, the
`K/X/N/E` roles). -/
def schurDim (M : Fin (L + 1) → ℕ) (t : ℕ → ℕ) (k : ℕ) : ℕ :=
  t k * (Wext M) (k + 1)

/-- The chain-lift coordinate count at boundary `k`: `c_k·M_{k+2}` (`0` at the leaf `k = L−1`). -/
def liftDim (M : Fin (L + 1) → ℕ) (t : ℕ → ℕ) (k : ℕ) : ℕ :=
  if k + 1 < L then ((Wext M) (k + 1) - t (k + 1)) * (Wext M) (k + 2) else 0

/-- **The chart-coordinate index** `ChartIdx M t = Σ k : Fin L, Fin (schurDim k) ⊕ Fin (liftDim k)`. The
per-boundary Schur-block + chain-lift coordinates; its cardinality is `flatDim M`. -/
abbrev ChartIdx (M : Fin (L + 1) → ℕ) (t : ℕ → ℕ) : Type :=
  Σ k : Fin L, Fin (schurDim M t k.val) ⊕ Fin (liftDim M t k.val)

/-! ## `card (ChartIdx) = flatDim` -/

/-- The chain-lift sum `∑_{k<L} liftDim k = ∑_{k<L−1} c_k·M_{k+2}` (the leaf lift is `0`). -/
theorem sum_liftDim (M : Fin (L + 1) → ℕ) (t : ℕ → ℕ) (hL : 0 < L) :
    (∑ k ∈ Finset.range L, liftDim M t k)
      = ∑ k ∈ Finset.range (L - 1), ((Wext M) (k + 1) - t (k + 1)) * (Wext M) (k + 2) := by
  rw [← Finset.sum_range_add_sum_Ico _ (show L - 1 ≤ L by omega)]
  have h0 : (∑ k ∈ Finset.Ico (L - 1) L, liftDim M t k) = 0 := by
    apply Finset.sum_eq_zero
    intro k hk; rw [Finset.mem_Ico] at hk
    unfold liftDim; rw [if_neg (by omega)]
  rw [h0, add_zero]
  apply Finset.sum_congr rfl
  intro k hk; rw [Finset.mem_range] at hk
  unfold liftDim; rw [if_pos (by omega)]

/-- **`Fintype.card (ChartIdx M t) = flatDim M`** — via `card_sigma` (`card (Σ k, Aₖ ⊕ Bₖ) =
∑ (card Aₖ + card Bₖ)`), the `Fin`-to-`range` sum bridge, and the arithmetic foundation
`chartDim_eq_flatDim` (the Schur sum `∑ schurDim` + the lift sum `∑ liftDim` = `flatDim`). -/
theorem card_chartIdx (M : Fin (L + 1) → ℕ) (t : ℕ → ℕ)
    (h0 : t 0 = M 0) (hc : ∀ k, t (k + 1) ≤ (Wext M) (k + 1)) (hL : 0 < L) :
    Fintype.card (ChartIdx M t) = flatDim M := by
  rw [Fintype.card_sigma]
  simp only [Fintype.card_sum, Fintype.card_fin]
  rw [Finset.sum_add_distrib,
    Fin.sum_univ_eq_sum_range (fun k => schurDim M t k) L,
    Fin.sum_univ_eq_sum_range (fun k => liftDim M t k) L,
    sum_liftDim M t hL]
  rw [show (∑ k ∈ Finset.range L, schurDim M t k)
        = ∑ k ∈ Finset.range L, t k * (Wext M) (k + 1) from rfl]
  exact chartDim_eq_flatDim M t h0 hc hL

/-! ## The flat-coordinate equivalence -/

/-- **`Fin (routeMAmbient M) ≃ ChartIdx M t`** — the determinant-ready bijective coordinatization. The
flat coordinate space `Fin N` (`N = routeMAmbient M = flatDim M`) is in bijection with the per-boundary
Schur/lift role coordinates, since `card (ChartIdx) = flatDim M = N` (`card_chartIdx`). -/
noncomputable def chartIdxEquiv (M : Fin (L + 1) → ℕ) (t : ℕ → ℕ)
    (h0 : t 0 = M 0) (hc : ∀ k, t (k + 1) ≤ (Wext M) (k + 1)) (hL : 0 < L) :
    Fin (routeMAmbient M) ≃ ChartIdx M t :=
  (finCongr (show routeMAmbient M = Fintype.card (ChartIdx M t) by
    rw [card_chartIdx M t h0 hc hL]; rfl)).trans (Fintype.equivFin (ChartIdx M t)).symm

end DLNFibre.DLN.RLCT
