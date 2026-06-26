import DLNFibre.DLN.RLCT.Validate.RouteMChartIdxEquiv
import Mathlib.Logic.Equiv.Fin.Basic

/-!
# `RouteMChartSlots` — the disjoint role-slot reader API (the shared decoder/factor foundation)

The shared coordinate-accessor foundation for the structured achiever-chart decoder + its factor CLEs
(the unblock for the item-3 map equality — see `thread.md` UPDATE + `codex/decoder-*`). The diagnosed
flaw was that `genBlkFlat` reads its block data via an arbitrary modular hash that COLLAPSES distinct
entries. The fix: read every block entry from a DISJOINT flat slot via the banked bijective
coordinatization `chartIdxEquiv : Fin (routeMAmbient M) ≃ ChartIdx M t`, with
`ChartIdx = Σ k : Fin L, Fin (schurDim k) ⊕ Fin (liftDim k)`.

The per-boundary slot allocation (verified against `(3,3,3,3)`, `chartDim_eq_flatDim` ⟹ `∑ = N`):
* `schurDim k = t_k · M_{k+1}` holds the Schur frame at boundary `s = k+1` (`(t_s+r_s)(t_s+c_s) =
  t_{k}·M_{k+1}` after the `schurDim(s-1)↔frame(s)` shift); for `k = L−1` it holds the leaf residual.
* `liftDim k = (M_{k+1}−t_{k+1})·M_{k+2}` holds the lift `W_{k+1}`.

This module gives the `Fin`-product slot equivalences (`Fin (schurDim k) ≃ Fin (t_k) × Fin (M_{k+1})`
etc.) and the `chartIdxEquiv`-based scalar readers — disjoint by construction (distinct `ChartIdx`
indices ⟹ distinct flat coords). The structured decoder + the factor CLEs both read through these, so
the item-3 map equality is accessor lemmas, not a coordinate-collapse fight.

Axiom-clean `[propext, Classical.choice, Quot.sound]` (finite equivalences; no analysis).
-/

namespace DLNFibre.DLN.RLCT

open scoped BigOperators

variable {L : ℕ}

/-! ## The per-boundary slot ↔ matrix-index equivalences -/

/-- The Schur-block slot at boundary `k` as a `Fin (t_k) × Fin (M_{k+1})` matrix index
(`schurDim k = t_k · Wext (k+1)` via `finProdFinEquiv`). -/
def schurSlotEquiv (M : Fin (L + 1) → ℕ) (t : ℕ → ℕ) (k : ℕ) :
    Fin (schurDim M t k) ≃ (Fin (t k) × Fin (Wext M (k + 1))) :=
  (finCongr (show schurDim M t k = t k * Wext M (k + 1) from rfl)).trans finProdFinEquiv.symm

/-- The lift slot at boundary `k` as a `Fin (M_{k+1} − t_{k+1}) × Fin (M_{k+2})` matrix index
(`liftDim k = (Wext (k+1) − t (k+1)) · Wext (k+2)` when `k+1 < L`). -/
def liftSlotEquiv (M : Fin (L + 1) → ℕ) (t : ℕ → ℕ) (k : ℕ) (hk : k + 1 < L) :
    Fin (liftDim M t k) ≃ (Fin (Wext M (k + 1) - t (k + 1)) × Fin (Wext M (k + 2))) :=
  (finCongr (show liftDim M t k = (Wext M (k + 1) - t (k + 1)) * Wext M (k + 2) by
    rw [liftDim, if_pos hk])).trans finProdFinEquiv.symm

/-! ## The disjoint scalar readers (via `chartIdxEquiv`) -/

/-- Read the flat coordinate at the Schur-block slot `(i, j)` of boundary `k`. Disjoint across
`(k, i, j)` by `chartIdxEquiv`'s injectivity. -/
noncomputable def readSchur (M : Fin (L + 1) → ℕ) (t : ℕ → ℕ)
    (h0 : t 0 = M 0) (hc : ∀ p, t (p + 1) ≤ (Wext M) (p + 1)) (hL : 0 < L)
    (x : Fin (routeMAmbient M) → ℝ) (k : Fin L) (i : Fin (t k.val)) (j : Fin (Wext M (k.val + 1))) :
    ℝ :=
  x ((chartIdxEquiv M t h0 hc hL).symm ⟨k, Sum.inl ((schurSlotEquiv M t k.val).symm (i, j))⟩)

/-- Read the flat coordinate at the lift slot `(i, j)` of boundary `k` (`k+1 < L`). Disjoint across
`(k, i, j)`. -/
noncomputable def readLift (M : Fin (L + 1) → ℕ) (t : ℕ → ℕ)
    (h0 : t 0 = M 0) (hc : ∀ p, t (p + 1) ≤ (Wext M) (p + 1)) (hL : 0 < L)
    (x : Fin (routeMAmbient M) → ℝ) (k : Fin L) (hk : k.val + 1 < L)
    (i : Fin (Wext M (k.val + 1) - t (k.val + 1))) (j : Fin (Wext M (k.val + 2))) : ℝ :=
  x ((chartIdxEquiv M t h0 hc hL).symm ⟨k, Sum.inr ((liftSlotEquiv M t k.val hk).symm (i, j))⟩)

/-! ## Disjointness: distinct `(boundary, role, entry)` triples read distinct flat coords -/

/-- The Schur reader's flat index is injective in `(k, i, j)` — distinct Schur entries read distinct
flat coords (the disjointness the modular hash lacked). -/
theorem readSchur_index_injective (M : Fin (L + 1) → ℕ) (t : ℕ → ℕ)
    (h0 : t 0 = M 0) (hc : ∀ p, t (p + 1) ≤ (Wext M) (p + 1)) (hL : 0 < L)
    {k k' : Fin L} {i : Fin (t k.val)} {j : Fin (Wext M (k.val + 1))}
    {i' : Fin (t k'.val)} {j' : Fin (Wext M (k'.val + 1))}
    (h : (chartIdxEquiv M t h0 hc hL).symm ⟨k, Sum.inl ((schurSlotEquiv M t k.val).symm (i, j))⟩
       = (chartIdxEquiv M t h0 hc hL).symm ⟨k', Sum.inl ((schurSlotEquiv M t k'.val).symm (i', j'))⟩) :
    (⟨k, Sum.inl ((schurSlotEquiv M t k.val).symm (i, j))⟩ : ChartIdx M t)
      = ⟨k', Sum.inl ((schurSlotEquiv M t k'.val).symm (i', j'))⟩ :=
  (chartIdxEquiv M t h0 hc hL).symm.injective h

/-- A Schur slot and a lift slot at the same boundary read DISTINCT flat coords (`Sum.inl ≠ Sum.inr`
under the injective `chartIdxEquiv`). -/
theorem readSchur_ne_readLift_index (M : Fin (L + 1) → ℕ) (t : ℕ → ℕ)
    (h0 : t 0 = M 0) (hc : ∀ p, t (p + 1) ≤ (Wext M) (p + 1)) (hL : 0 < L)
    (k : Fin L) (a : Fin (schurDim M t k.val)) (b : Fin (liftDim M t k.val)) :
    (chartIdxEquiv M t h0 hc hL).symm ⟨k, Sum.inl a⟩
      ≠ (chartIdxEquiv M t h0 hc hL).symm ⟨k, Sum.inr b⟩ := by
  intro h
  have hsig := (chartIdxEquiv M t h0 hc hL).symm.injective h
  -- equal sigmas at the SAME fst `k` ⟹ equal snd (a `Sum`), but `inl ≠ inr`
  have hsnd : (Sum.inl a : Fin (schurDim M t k.val) ⊕ Fin (liftDim M t k.val)) = Sum.inr b := by
    simpa using (Sigma.mk.inj_iff.mp hsig).2
  exact absurd hsnd (by simp)

end DLNFibre.DLN.RLCT
