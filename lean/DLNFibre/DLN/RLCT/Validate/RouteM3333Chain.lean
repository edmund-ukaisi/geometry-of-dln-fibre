import DLNFibre.DLN.RLCT.Validate.RouteMChainBlock
import DLNFibre.DLN.RLCT.Validate.RouteMChainRate

/-!
# `RouteM3333Chain` — the `(3,3,3,3)` achiever chain via the rate engine (validation + template)

The decisive multi-pivot witness `(3,3,3,3)` (descent `T* = (2,1,0)`, block codims `1,2,3`) built as a
`FactoredChain 3 u` through the banked rate engine (`RouteMChain*`), reproducing the chart-identity rate
factor `prod = u • H` WITHOUT the per-entry `ring` blow-up of `RouteM3333.prod_chartParams3333_entry`.

This validates the recursive-`C` design (the `step`/`base` discharged by the engine, the `chain_block`
chaining firing at the genuine `c ≥ 1` boundaries) on the hardest banked instance, and is the explicit
template for the general per-`M` construction.

## Widths (the off-by-one, explicit ℕ-indexed `match`, NOT `![…].getD` — the heartbeat caveat)
Ambient `Wwid = (3,3,3,3)`, compressed `Twid = (3,3,2,1)` (`Twid 0 = M 0 = 3`, `Twid (k+1) = t_k` with
`t_0 = 3, t_1 = 2, t_2 = 1`). Boundary `k=0`: `c_0 = 0` (identity boundary, `chainQ = I_3`); `k=1`:
`t=2, c=1` (`chain_block` fires); `k=2`: `t=1, c=2` (`chain_block` fires); leaf `C 3 = u·R : Fin 1 → Fin 3`.

The block matrices are carried as free matrices (the genuine chart coordinatization is the downstream
`φ_M`); the rate identity is established for ANY such block data (the engine's path-agnostic rate).

Axiom-clean `[propext, Classical.choice, Quot.sound]` (pure matrix algebra; no analysis).
-/

namespace DLNFibre.DLN.RLCT

open Matrix

/-- Ambient widths `Wwid = (3,3,3,3)` (all `3`), ℕ-indexed by explicit `match` (cheap defeq). -/
def W3333 : ℕ → ℕ := fun _ => 3

/-- Compressed widths `Twid = (3,3,2,1,…)` ℕ-indexed by explicit `match` (NOT `![…].getD`). -/
def T3333w : ℕ → ℕ
  | 0 => 3
  | 1 => 3
  | 2 => 2
  | 3 => 1
  | _ => 1

@[simp] theorem T3333w_0 : T3333w 0 = 3 := rfl
@[simp] theorem T3333w_1 : T3333w 1 = 3 := rfl
@[simp] theorem T3333w_2 : T3333w 2 = 2 := rfl
@[simp] theorem T3333w_3 : T3333w 3 = 1 := rfl
@[simp] theorem W3333_eq (k : ℕ) : W3333 k = 3 := rfl

/-! ## The block data + the recursive compressed transition `C3333`

`C 0 = I_3`, `C 1 = Bmat1·chainQ(N1) + u•Rmat1`, `C 2 = Bmat2·chainQ(N2) + u•Rmat2`, `C 3 = u•Rleaf`
(the cert's shape, so `hC` interior is `rfl`, `base` is `rfl`). -/

variable (u : ℝ)
variable (Bmat1 : Matrix (Fin 3) (Fin 2) ℝ) (Rmat1 : Matrix (Fin 3) (Fin 3) ℝ)
  (N1 : Matrix (Fin 2) (Fin 1) ℝ) (W1 : Matrix (Fin 1) (Fin 3) ℝ)
variable (Bmat2 : Matrix (Fin 2) (Fin 1) ℝ) (Rmat2 : Matrix (Fin 2) (Fin 3) ℝ)
  (N2 : Matrix (Fin 1) (Fin 2) ℝ) (W2 : Matrix (Fin 2) (Fin 3) ℝ)
variable (Rleaf : Matrix (Fin 1) (Fin 3) ℝ)

/-- **The recursive compressed transition `C` for `(3,3,3,3)`** (ℕ-indexed). The cert's shape; the chaining
rows `chainQ N1` (`Twid 2 = 2 → Wwid 1 = 3`, `c=1`) and `chainQ N2` (`Twid 3 = 1 → Wwid 2 = 3`, `c=2`). -/
noncomputable def C3333 : (k : ℕ) → Matrix (Fin (T3333w k)) (Fin (W3333 k)) ℝ
  | 0 => (1 : Matrix (Fin 3) (Fin 3) ℝ)
  | 1 => Bmat1 * chainQ (show (2 : ℕ) + 1 = 3 by rfl) N1 + u • Rmat1
  | 2 => Bmat2 * chainQ (show (1 : ℕ) + 2 = 3 by rfl) N2 + u • Rmat2
  | 3 => u • Rleaf
  | (_ + 4) => 0

@[simp] theorem C3333_zero :
    C3333 u Bmat1 Rmat1 N1 Bmat2 Rmat2 N2 Rleaf 0 = (1 : Matrix (Fin 3) (Fin 3) ℝ) := rfl

/-! ## The `FactoredChain 3 u` assembly (the engine consumes this)

The identity boundary `k = 0` uses `Qmat 0 = 1`, `Bmat 0 = 1`, `Rmat 0 = 0`, `A 0 = C 1` (so `hC 0`/`hQA 0`
are `one_mul`/`rfl`, sidestepping `chainQ` at `c = 0`); the genuine boundaries `k = 1, 2` use `chainQ`/
`chainA` (so `hQA` is `chainQ_mul_chainA`); the leaf is `base : C 3 = u • Rleaf` (`rfl`). -/

/-- **The `(3,3,3,3)` achiever `FactoredChain`** built through the rate engine. `step`/`base` discharged
by the engine (`step_of_factor`), the `chain_block` chaining firing at the genuine `c ≥ 1` boundaries. -/
noncomputable def chain3333 : FactoredChain 3 u where
  Wwid := W3333
  Twid := T3333w
  A := fun k =>
    match k with
    | 0 => C3333 u Bmat1 Rmat1 N1 Bmat2 Rmat2 N2 Rleaf 1
    | 1 => chainA (show (2 : ℕ) + 1 = 3 by rfl) N1 W1
        (C3333 u Bmat1 Rmat1 N1 Bmat2 Rmat2 N2 Rleaf 2)
    | 2 => chainA (show (1 : ℕ) + 2 = 3 by rfl) N2 W2
        (C3333 u Bmat1 Rmat1 N1 Bmat2 Rmat2 N2 Rleaf 3)
    | (_ + 3) => 0
  C := C3333 u Bmat1 Rmat1 N1 Bmat2 Rmat2 N2 Rleaf
  Bmat := fun k =>
    match k with
    | 0 => (1 : Matrix (Fin 3) (Fin 3) ℝ)
    | 1 => Bmat1
    | 2 => Bmat2
    | (_ + 3) => 0
  Qmat := fun k =>
    match k with
    | 0 => (1 : Matrix (Fin 3) (Fin 3) ℝ)
    | 1 => chainQ (show (2 : ℕ) + 1 = 3 by rfl) N1
    | 2 => chainQ (show (1 : ℕ) + 2 = 3 by rfl) N2
    | (_ + 3) => 0
  Rmat := fun k =>
    match k with
    | 0 => (0 : Matrix (Fin 3) (Fin 3) ℝ)
    | 1 => Rmat1
    | 2 => Rmat2
    | (_ + 3) => 0
  R := Rleaf
  hC := by
    intro k hk
    interval_cases k
    · -- `C 0 = 1 = 1 * 1 + u • 0` (the identity boundary; `Bmat 0 = 1, Qmat 0 = 1, Rmat 0 = 0`).
      show C3333 u Bmat1 Rmat1 N1 Bmat2 Rmat2 N2 Rleaf 0
        = (1 : Matrix (Fin 3) (Fin 3) ℝ) * (1 : Matrix (Fin 3) (Fin 3) ℝ)
          + u • (0 : Matrix (Fin 3) (Fin 3) ℝ)
      rw [C3333_zero, Matrix.one_mul, smul_zero, add_zero]
    · rfl
    · rfl
  hQA := by
    intro k hk
    interval_cases k
    · -- `Qmat 0 * A 0 = 1 * (C 1) = C 1` (the identity boundary).
      exact Matrix.one_mul _
    · exact chainQ_mul_chainA _ _ _ _
    · exact chainQ_mul_chainA _ _ _ _
  base := rfl

/-! ## The chart identity `prod M3333 (chartParams) = u • H` (the rate factor, via the engine)

`M3333 = (3,3,3,3)`. The chart parameter `chartParams3333c` IS the chain's layers (all `3×3`); the width
match `hW` is `rfl`-`3` and the layer match `hA` is `reindex refl refl (A k) = A k` (the `finCongr` of a
`rfl`-true `3=3` is `Equiv.refl`). So `prod_eq_reindex_suffix` gives `prod = reindex (suffix 0)`, and the
recursive `C 0 = 1` + `telescope_zero` simplifies `suffix 0` to `u • Hmat 0`. -/

/-- `M3333 = (3,3,3,3)` (local copy, avoids the heavy `RouteM3333` import). -/
abbrev M3333c : Fin 4 → ℕ := ![3, 3, 3, 3]

/-- **The chart parameter** `chartParams3333c : Params M3333c` — the chain's layers `A 0, A 1, A 2`,
all `3×3` (`M3333c` is constant `3`, so each layer's type matches the `Params` slot by `rfl`-reduction
of `M3333c s.castSucc = M3333c s.succ = 3`). -/
noncomputable def chartParams3333c : Params M3333c := fun s =>
  match s with
  | 0 => (chain3333 u Bmat1 Rmat1 N1 W1 Bmat2 Rmat2 N2 W2 Rleaf).toChain.A 0
  | 1 => (chain3333 u Bmat1 Rmat1 N1 W1 Bmat2 Rmat2 N2 W2 Rleaf).toChain.A 1
  | 2 => (chain3333 u Bmat1 Rmat1 N1 W1 Bmat2 Rmat2 N2 W2 Rleaf).toChain.A 2

/-- The width match: `W3333 k = M3333c ⟨k,_⟩ = 3` for `k ≤ 3` (all widths `3`). -/
theorem hW3333c : ∀ k (hk : k ≤ 3),
    (chain3333 u Bmat1 Rmat1 N1 W1 Bmat2 Rmat2 N2 W2 Rleaf).toChain.Wwid k
      = M3333c ⟨k, Nat.lt_succ_of_le hk⟩ := by
  intro k hk; interval_cases k <;> rfl

/-- The layer match `hA`: the chain's layer `A k`, reindexed by the (`rfl`-true `3=3`) width equalities,
IS `chartParams3333c ⟨k,_⟩` — by construction (`chartParams` is `A 0/A 1/A 2`, the reindex is identity
since every `finCongr (3=3)` is `Equiv.refl`). -/
theorem hA3333c : ∀ k (hk : k < 3),
    Matrix.reindex (finCongr (hW3333c u Bmat1 Rmat1 N1 W1 Bmat2 Rmat2 N2 W2 Rleaf k (le_of_lt hk)))
        (finCongr (hW3333c u Bmat1 Rmat1 N1 W1 Bmat2 Rmat2 N2 W2 Rleaf (k + 1) hk))
        ((chain3333 u Bmat1 Rmat1 N1 W1 Bmat2 Rmat2 N2 W2 Rleaf).toChain.A k)
      = (chartParams3333c u Bmat1 Rmat1 N1 W1 Bmat2 Rmat2 N2 W2 Rleaf ⟨k, hk⟩ :
          Matrix (Fin (M3333c (⟨k, Nat.lt_succ_of_le (le_of_lt hk)⟩ : Fin 4)))
            (Fin (M3333c (⟨k + 1, Nat.succ_lt_succ hk⟩ : Fin 4))) ℝ) := by
  intro k hk
  interval_cases k <;>
    · rw [Matrix.reindex_apply]
      ext i j
      simp only [Matrix.submatrix_apply, finCongr_symm, finCongr_apply, Fin.cast_eq_self]
      rfl

/-- **The chart identity (rate factor), via the engine.** `prod M3333c (chartParams) = u • H`,
`H := reindex (Hmat 0)`. The bridge `prod_eq_reindex_suffix` gives `prod = reindex (suffix 0)`; the
recursive `C 0 = 1` makes `C 0 · suffix 0 = suffix 0`, so `telescope_zero` reads `suffix 0 = u • Hmat 0`,
and `reindex` pulls `u` through (`submatrix_smul`). NO per-entry `ring`. -/
theorem prod_chartParams3333c_eq :
    prod M3333c (chartParams3333c u Bmat1 Rmat1 N1 W1 Bmat2 Rmat2 N2 W2 Rleaf)
      = u • Matrix.reindex
          (finCongr (hW3333c u Bmat1 Rmat1 N1 W1 Bmat2 Rmat2 N2 W2 Rleaf 0 (Nat.zero_le 3)))
          (finCongr (hW3333c u Bmat1 Rmat1 N1 W1 Bmat2 Rmat2 N2 W2 Rleaf 3 (le_refl 3)))
          ((chain3333 u Bmat1 Rmat1 N1 W1 Bmat2 Rmat2 N2 W2 Rleaf).toChain.Hmat 0 (Nat.zero_le 3)) := by
  set c := chain3333 u Bmat1 Rmat1 N1 W1 Bmat2 Rmat2 N2 W2 Rleaf with hc
  have hbridge := FactoredChain.prod_eq_reindex_suffix c M3333c
    (chartParams3333c u Bmat1 Rmat1 N1 W1 Bmat2 Rmat2 N2 W2 Rleaf)
    (hW3333c u Bmat1 Rmat1 N1 W1 Bmat2 Rmat2 N2 W2 Rleaf)
    (hA3333c u Bmat1 Rmat1 N1 W1 Bmat2 Rmat2 N2 W2 Rleaf)
  rw [hbridge]
  -- `suffix 0 = C 0 · suffix 0` (since `C 0 = 1`), `= u • Hmat 0` (telescope_zero); `u` pulls through.
  have hsuf : c.toChain.suffix 0 (Nat.zero_le 3) = u • c.toChain.Hmat 0 (Nat.zero_le 3) := by
    have ht := c.telescope_zero
    -- `C 0 = 1` definitionally, so `C 0 · suffix 0 = 1 · suffix 0 = suffix 0` (fully-applied `one_mul`).
    have h1 : c.toChain.C 0 * c.toChain.suffix 0 (Nat.zero_le 3)
        = c.toChain.suffix 0 (Nat.zero_le 3) :=
      Matrix.one_mul (c.toChain.suffix 0 (Nat.zero_le 3))
    rw [h1] at ht
    exact ht
  rw [hsuf]
  -- `reindex (u • Hmat 0) = u • reindex (Hmat 0)`: fully-applied `submatrix_smul` (dependent-`HSMul`).
  rw [Matrix.reindex_apply, Matrix.reindex_apply]
  exact (congrFun (congrFun (Matrix.submatrix_smul u (c.toChain.Hmat 0 (Nat.zero_le 3))) _) _)

end DLNFibre.DLN.RLCT
