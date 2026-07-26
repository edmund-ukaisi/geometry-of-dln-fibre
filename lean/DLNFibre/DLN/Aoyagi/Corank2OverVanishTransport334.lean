import DLNFibre.DLN.Aoyagi.Corank2OverVanishCanon334

/-!
# `DLN.Aoyagi.Corank2OverVanishTransport334` — the σ_p1 loss-symmetry (transport crux)

The parametric leverage that lifts the 16 canonical `(p1 = 20)` over-vanishing leaves to all 144:
each dominant `p1` chart is the `σ_p1`-conjugate of the canonical, where `σ_p1 = rowswap i ∘ colswap j`
is a genuine **loss-symmetry** of the `(3,3,4)` network (a row/col permutation of the weights).

This file lands the CRUX: the loss `∑_k (coreGen k)²` is invariant under a coordinate permutation
acting as a row/col symmetry on `A0`/`A1`. Concretely, if `A0 (w∘σ) = A0 w` reindexed by
`(swap 0 i, swap 0 j)` and `A1 (w∘σ) = A1 w` reindexed by `(id, swap 0 i)`, then
`A1 (w∘σ) · A0 (w∘σ) = (A1 w · A0 w)` reindexed by `(id, swap 0 j)` — a single column swap — so the
Frobenius norm (= `∑_k coreGen²`) is preserved. (The `swap 0 i` on `A0`-ROWS cancels the `swap 0 i`
on `A1`-COLUMNS in the product, leaving only the `swap 0 j` column permutation.)

The per-`p1` hypotheses `hA0`/`hA1` are decidable finite checks on `σ_p1`'s action on the `A0`/`A1`
coordinate reads (`Corank2NativeFan334` centres); the σ_p1 defs + their discharge + the full chart
conjugation (via `blockBlowupMap_conj`) + the 144-transport theorem are the remaining assembly.
-/

open Matrix
open DLNFibre.Core.Aoyagi
open DLNFibre.DLN.Aoyagi.Corank2CoreGenWrap
open DLNFibre.DLN.Aoyagi.OverVanishCanon334
open DLNFibre.DLN.Aoyagi.NativeShear334
open DLNFibre.DLN.Aoyagi.NativePerm334
open DLNFibre.DLN.Aoyagi.NativeFan334

namespace DLNFibre.DLN.Aoyagi.OverVanishTransport334

/-- **The `coreGen` loss as the Frobenius sum of the `A1·A0` product entries.** Reindexes the flat
`Fin 12` sum to the `4×3` matrix double-sum via `finProdFinEquiv` + `coreGen_eWrap_entry`. -/
theorem sumSq_coreGen_eq_frob (v : Fin 21 → ℝ) :
    (∑ k, (coreGen dvec eWrap k v) ^ 2)
      = ∑ a : Fin 4, ∑ c : Fin 3, ((A1 v * A0 v) a c) ^ 2 := by
  have h : (∑ k, (coreGen dvec eWrap k v) ^ 2)
      = ∑ p : Fin 4 × Fin 3, ((A1 v * A0 v) p.1 p.2) ^ 2 := by
    calc (∑ k, (coreGen dvec eWrap k v) ^ 2)
        = ∑ k, ((A1 v * A0 v) (finProdFinEquiv.symm k).1 (finProdFinEquiv.symm k).2) ^ 2 :=
          Finset.sum_congr rfl (fun k _ => congrArg (· ^ 2) (coreGen_eWrap_entry k v))
      _ = ∑ p : Fin 4 × Fin 3, ((A1 v * A0 v) p.1 p.2) ^ 2 :=
          Equiv.sum_comp finProdFinEquiv.symm (fun p => ((A1 v * A0 v) p.1 p.2) ^ 2)
  rw [h, Fintype.sum_prod_type]

/-- **The σ_p1 loss-symmetry (the transport crux).** If a coordinate permutation `σ` acts on `A0`'s
reads as the `(swap 0 i, swap 0 j)` row/col reindex and on `A1`'s reads as the `(swap 0 i)` column
reindex (the `hA0`/`hA1` hypotheses — decidable per `p1`), then the `coreGen` loss is `σ`-invariant.
The `swap 0 i` on `A0`-rows cancels the `swap 0 i` on `A1`-columns inside the product, leaving a bare
`swap 0 j` column permutation of `A1·A0`, under which `∑_k coreGen²` (the Frobenius sum) is fixed. -/
theorem sumSq_coreGen_symm (w : Fin 21 → ℝ) (σ : Equiv.Perm (Fin 21)) (i j : Fin 3)
    (hA0 : ∀ r c, A0 (fun t => w (σ t)) r c = A0 w (Equiv.swap 0 i r) (Equiv.swap 0 j c))
    (hA1 : ∀ a b, A1 (fun t => w (σ t)) a b = A1 w a (Equiv.swap 0 i b)) :
    (∑ k, (coreGen dvec eWrap k (fun t => w (σ t))) ^ 2)
      = ∑ k, (coreGen dvec eWrap k w) ^ 2 := by
  rw [sumSq_coreGen_eq_frob, sumSq_coreGen_eq_frob]
  -- the product is `A1 w · A0 w` with columns permuted by `swap 0 j`
  have hmult : ∀ a c, (A1 (fun t => w (σ t)) * A0 (fun t => w (σ t))) a c
      = (A1 w * A0 w) a (Equiv.swap 0 j c) := by
    intro a c
    rw [Matrix.mul_apply, Matrix.mul_apply,
      ← Equiv.sum_comp (Equiv.swap (0 : Fin 3) i)
        (fun b => A1 w a b * A0 w b (Equiv.swap 0 j c))]
    exact Finset.sum_congr rfl (fun b _ => by rw [hA1 a b, hA0 b c])
  -- `∑_a ∑_c (M' a c)² = ∑_a ∑_c (M a c)²`: reindex `c` on the RHS through the involution, then `hmult`
  refine Finset.sum_congr rfl (fun a _ => ?_)
  rw [← Equiv.sum_comp (Equiv.swap (0 : Fin 3) j) (fun c => ((A1 w * A0 w) a c) ^ 2)]
  exact Finset.sum_congr rfl (fun c _ => congrArg (· ^ 2) (hmult a c))

/-! ## §1 — the 9 loss-symmetry coordinate permutations `σ_p1` (step 1)

For each A0-dominant pivot `p1 = A0[i,j]`, the loss symmetry `σ_p1` is the `Fin 21` involution that
row/col-swaps the A0 grid (`rows 0↔i`, `cols 0↔j`) and correspondingly col-swaps the A1 grid
(`cols 0↔i`). It carries the crux's `hA0`/`hA1` for `(i,j)`, so `∑ coreGen(w∘σ_p1)² = ∑ coreGen(w)²`
(the loss symmetry holds at every dominant pivot). `p1 = 20 = A0[0,0]` is the identity (canonical).

A0 grid coords (`!![u20,u2,u3; u0,u4,u6; u1,u5,u7]`): rows are `[20,2,3]`/`[0,4,6]`/`[1,5,7]`.
A1 grid coords (`u(8+4b+a)`): col `b=0={8,9,10,11}`, `b=1={12,13,14,15}`, `b=2={16,17,18,19}`.
Each map is a machine-checkable involution (`by decide` injectivity), validated against the emitted
`cperm` data (`conj(cperm20, σ_p1) = cperm_p1`, so the born-native fan data IS the `σ_p1`-conjugate). -/

/-- `σ` for pivot `p1 = 0 = A0[1,0]`: A0 rows `0↔1`, A1 cols `0↔1`. -/
def sigC0 (k : Fin 21) : Fin 21 :=
  if k = 0 then 20 else if k = 20 then 0 else if k = 2 then 4 else if k = 4 then 2
  else if k = 3 then 6 else if k = 6 then 3 else if k = 8 then 12 else if k = 12 then 8
  else if k = 9 then 13 else if k = 13 then 9 else if k = 10 then 14 else if k = 14 then 10
  else if k = 11 then 15 else if k = 15 then 11 else k

/-- `σ` for pivot `p1 = 1 = A0[2,0]`: A0 rows `0↔2`, A1 cols `0↔2`. -/
def sigC1 (k : Fin 21) : Fin 21 :=
  if k = 1 then 20 else if k = 20 then 1 else if k = 2 then 5 else if k = 5 then 2
  else if k = 3 then 7 else if k = 7 then 3 else if k = 8 then 16 else if k = 16 then 8
  else if k = 9 then 17 else if k = 17 then 9 else if k = 10 then 18 else if k = 18 then 10
  else if k = 11 then 19 else if k = 19 then 11 else k

/-- `σ` for pivot `p1 = 2 = A0[0,1]`: A0 cols `0↔1` (A1 unchanged). -/
def sigC2 (k : Fin 21) : Fin 21 :=
  if k = 2 then 20 else if k = 20 then 2 else if k = 0 then 4 else if k = 4 then 0
  else if k = 1 then 5 else if k = 5 then 1 else k

/-- `σ` for pivot `p1 = 3 = A0[0,2]`: A0 cols `0↔2` (A1 unchanged). -/
def sigC3 (k : Fin 21) : Fin 21 :=
  if k = 3 then 20 else if k = 20 then 3 else if k = 0 then 6 else if k = 6 then 0
  else if k = 1 then 7 else if k = 7 then 1 else k

/-- `σ` for pivot `p1 = 4 = A0[1,1]`: A0 rows `0↔1` + cols `0↔1`, A1 cols `0↔1`. -/
def sigC4 (k : Fin 21) : Fin 21 :=
  if k = 4 then 20 else if k = 20 then 4 else if k = 0 then 2 else if k = 2 then 0
  else if k = 3 then 6 else if k = 6 then 3 else if k = 1 then 5 else if k = 5 then 1
  else if k = 8 then 12 else if k = 12 then 8 else if k = 9 then 13 else if k = 13 then 9
  else if k = 10 then 14 else if k = 14 then 10 else if k = 11 then 15 else if k = 15 then 11
  else k

/-- `σ` for pivot `p1 = 5 = A0[2,1]`: A0 rows `0↔2` + cols `0↔1`, A1 cols `0↔2`. -/
def sigC5 (k : Fin 21) : Fin 21 :=
  if k = 5 then 20 else if k = 20 then 5 else if k = 1 then 2 else if k = 2 then 1
  else if k = 3 then 7 else if k = 7 then 3 else if k = 0 then 4 else if k = 4 then 0
  else if k = 8 then 16 else if k = 16 then 8 else if k = 9 then 17 else if k = 17 then 9
  else if k = 10 then 18 else if k = 18 then 10 else if k = 11 then 19 else if k = 19 then 11
  else k

/-- `σ` for pivot `p1 = 6 = A0[1,2]`: A0 rows `0↔1` + cols `0↔2`, A1 cols `0↔1`. -/
def sigC6 (k : Fin 21) : Fin 21 :=
  if k = 6 then 20 else if k = 20 then 6 else if k = 0 then 3 else if k = 3 then 0
  else if k = 2 then 4 else if k = 4 then 2 else if k = 1 then 7 else if k = 7 then 1
  else if k = 8 then 12 else if k = 12 then 8 else if k = 9 then 13 else if k = 13 then 9
  else if k = 10 then 14 else if k = 14 then 10 else if k = 11 then 15 else if k = 15 then 11
  else k

/-- `σ` for pivot `p1 = 7 = A0[2,2]`: A0 rows `0↔2` + cols `0↔2`, A1 cols `0↔2`. -/
def sigC7 (k : Fin 21) : Fin 21 :=
  if k = 7 then 20 else if k = 20 then 7 else if k = 1 then 3 else if k = 3 then 1
  else if k = 2 then 5 else if k = 5 then 2 else if k = 0 then 6 else if k = 6 then 0
  else if k = 8 then 16 else if k = 16 then 8 else if k = 9 then 17 else if k = 17 then 9
  else if k = 10 then 18 else if k = 18 then 10 else if k = 11 then 19 else if k = 19 then 11
  else k

theorem sigC0_invol : Function.Involutive sigC0 := by intro x; fin_cases x <;> decide
theorem sigC1_invol : Function.Involutive sigC1 := by intro x; fin_cases x <;> decide
theorem sigC2_invol : Function.Involutive sigC2 := by intro x; fin_cases x <;> decide
theorem sigC3_invol : Function.Involutive sigC3 := by intro x; fin_cases x <;> decide
theorem sigC4_invol : Function.Involutive sigC4 := by intro x; fin_cases x <;> decide
theorem sigC5_invol : Function.Involutive sigC5 := by intro x; fin_cases x <;> decide
theorem sigC6_invol : Function.Involutive sigC6 := by intro x; fin_cases x <;> decide
theorem sigC7_invol : Function.Involutive sigC7 := by intro x; fin_cases x <;> decide

/-- Each `σ_p1` as an `Equiv.Perm` via `Involutive.toPerm` (so `⇑σ = σ.symm = sigC`, both computable
by kernel `decide` — the key to the `decide`-discharged conjugation identities in §3). -/
def sigP0 : Equiv.Perm (Fin 21) := sigC0_invol.toPerm sigC0
def sigP1 : Equiv.Perm (Fin 21) := sigC1_invol.toPerm sigC1
def sigP2 : Equiv.Perm (Fin 21) := sigC2_invol.toPerm sigC2
def sigP3 : Equiv.Perm (Fin 21) := sigC3_invol.toPerm sigC3
def sigP4 : Equiv.Perm (Fin 21) := sigC4_invol.toPerm sigC4
def sigP5 : Equiv.Perm (Fin 21) := sigC5_invol.toPerm sigC5
def sigP6 : Equiv.Perm (Fin 21) := sigC6_invol.toPerm sigC6
def sigP7 : Equiv.Perm (Fin 21) := sigC7_invol.toPerm sigC7

/-! ## §2 — the per-pivot `hA0`/`hA1` discharge + the loss symmetry (step 2)

Each dominant pivot `p1 = A0[i,j]` carries the crux's two hypotheses for its `(i,j)`: `hA0` reduces
each `A0` entry to one coordinate, the RHS row/col swap `(swap 0 i, swap 0 j)` is computed, and both
sides project to the SAME `w`-read (`simp` + `rfl`); `hA1` reduces to a pure `Fin 21`-index identity
(`A1 a b = w (8+4b+a)`, RHS col-swapped by `swap 0 i`) closed by `decide`. The loss symmetry is then
the crux `sumSq_coreGen_symm`. The `(i,j)` per pivot: `0↦(1,0)`, `1↦(2,0)`, `2↦(0,1)`, `3↦(0,2)`,
`4↦(1,1)`, `5↦(2,1)`, `6↦(1,2)`, `7↦(2,2)`. -/

set_option linter.unusedSimpArgs false in
theorem hA0_P0 (w : Fin 21 → ℝ) (r c : Fin 3) :
    A0 (fun t => w (sigP0 t)) r c = A0 w (Equiv.swap 0 1 r) (Equiv.swap 0 0 c) := by
  fin_cases r <;> fin_cases c <;>
    simp only [A0, sigP0, Function.Involutive.coe_toPerm, sigC0, of_apply, cons_val', cons_val_zero,
      cons_val_one, cons_val_two, tail_cons, head_cons, empty_val', cons_val_fin_one,
      head_fin_const, Fin.isValue, Equiv.swap_apply_left, Equiv.swap_apply_right,
      Equiv.swap_self, Equiv.refl_apply, Equiv.swap_apply_of_ne_of_ne, Fin.reduceEq] <;> rfl

theorem hA1_P0 (w : Fin 21 → ℝ) (a : Fin 4) (b : Fin 3) :
    A1 (fun t => w (sigP0 t)) a b = A1 w a (Equiv.swap 0 1 b) := by
  simp only [A1]; congr 1; simp only [sigP0, Function.Involutive.coe_toPerm]
  fin_cases a <;> fin_cases b <;> decide

set_option linter.unusedSimpArgs false in
theorem hA0_P1 (w : Fin 21 → ℝ) (r c : Fin 3) :
    A0 (fun t => w (sigP1 t)) r c = A0 w (Equiv.swap 0 2 r) (Equiv.swap 0 0 c) := by
  fin_cases r <;> fin_cases c <;>
    simp only [A0, sigP1, Function.Involutive.coe_toPerm, sigC1, of_apply, cons_val', cons_val_zero,
      cons_val_one, cons_val_two, tail_cons, head_cons, empty_val', cons_val_fin_one,
      head_fin_const, Fin.isValue, Equiv.swap_apply_left, Equiv.swap_apply_right,
      Equiv.swap_self, Equiv.refl_apply, Equiv.swap_apply_of_ne_of_ne, Fin.reduceEq] <;> rfl

theorem hA1_P1 (w : Fin 21 → ℝ) (a : Fin 4) (b : Fin 3) :
    A1 (fun t => w (sigP1 t)) a b = A1 w a (Equiv.swap 0 2 b) := by
  simp only [A1]; congr 1; simp only [sigP1, Function.Involutive.coe_toPerm]
  fin_cases a <;> fin_cases b <;> decide

set_option linter.unusedSimpArgs false in
theorem hA0_P2 (w : Fin 21 → ℝ) (r c : Fin 3) :
    A0 (fun t => w (sigP2 t)) r c = A0 w (Equiv.swap 0 0 r) (Equiv.swap 0 1 c) := by
  fin_cases r <;> fin_cases c <;>
    simp only [A0, sigP2, Function.Involutive.coe_toPerm, sigC2, of_apply, cons_val', cons_val_zero,
      cons_val_one, cons_val_two, tail_cons, head_cons, empty_val', cons_val_fin_one,
      head_fin_const, Fin.isValue, Equiv.swap_apply_left, Equiv.swap_apply_right,
      Equiv.swap_self, Equiv.refl_apply, Equiv.swap_apply_of_ne_of_ne, Fin.reduceEq] <;> rfl

theorem hA1_P2 (w : Fin 21 → ℝ) (a : Fin 4) (b : Fin 3) :
    A1 (fun t => w (sigP2 t)) a b = A1 w a (Equiv.swap 0 0 b) := by
  simp only [A1]; congr 1; simp only [sigP2, Function.Involutive.coe_toPerm]
  fin_cases a <;> fin_cases b <;> decide

set_option linter.unusedSimpArgs false in
theorem hA0_P3 (w : Fin 21 → ℝ) (r c : Fin 3) :
    A0 (fun t => w (sigP3 t)) r c = A0 w (Equiv.swap 0 0 r) (Equiv.swap 0 2 c) := by
  fin_cases r <;> fin_cases c <;>
    simp only [A0, sigP3, Function.Involutive.coe_toPerm, sigC3, of_apply, cons_val', cons_val_zero,
      cons_val_one, cons_val_two, tail_cons, head_cons, empty_val', cons_val_fin_one,
      head_fin_const, Fin.isValue, Equiv.swap_apply_left, Equiv.swap_apply_right,
      Equiv.swap_self, Equiv.refl_apply, Equiv.swap_apply_of_ne_of_ne, Fin.reduceEq] <;> rfl

theorem hA1_P3 (w : Fin 21 → ℝ) (a : Fin 4) (b : Fin 3) :
    A1 (fun t => w (sigP3 t)) a b = A1 w a (Equiv.swap 0 0 b) := by
  simp only [A1]; congr 1; simp only [sigP3, Function.Involutive.coe_toPerm]
  fin_cases a <;> fin_cases b <;> decide

set_option linter.unusedSimpArgs false in
theorem hA0_P4 (w : Fin 21 → ℝ) (r c : Fin 3) :
    A0 (fun t => w (sigP4 t)) r c = A0 w (Equiv.swap 0 1 r) (Equiv.swap 0 1 c) := by
  fin_cases r <;> fin_cases c <;>
    simp only [A0, sigP4, Function.Involutive.coe_toPerm, sigC4, of_apply, cons_val', cons_val_zero,
      cons_val_one, cons_val_two, tail_cons, head_cons, empty_val', cons_val_fin_one,
      head_fin_const, Fin.isValue, Equiv.swap_apply_left, Equiv.swap_apply_right,
      Equiv.swap_self, Equiv.refl_apply, Equiv.swap_apply_of_ne_of_ne, Fin.reduceEq] <;> rfl

theorem hA1_P4 (w : Fin 21 → ℝ) (a : Fin 4) (b : Fin 3) :
    A1 (fun t => w (sigP4 t)) a b = A1 w a (Equiv.swap 0 1 b) := by
  simp only [A1]; congr 1; simp only [sigP4, Function.Involutive.coe_toPerm]
  fin_cases a <;> fin_cases b <;> decide

set_option linter.unusedSimpArgs false in
theorem hA0_P5 (w : Fin 21 → ℝ) (r c : Fin 3) :
    A0 (fun t => w (sigP5 t)) r c = A0 w (Equiv.swap 0 2 r) (Equiv.swap 0 1 c) := by
  fin_cases r <;> fin_cases c <;>
    simp only [A0, sigP5, Function.Involutive.coe_toPerm, sigC5, of_apply, cons_val', cons_val_zero,
      cons_val_one, cons_val_two, tail_cons, head_cons, empty_val', cons_val_fin_one,
      head_fin_const, Fin.isValue, Equiv.swap_apply_left, Equiv.swap_apply_right,
      Equiv.swap_self, Equiv.refl_apply, Equiv.swap_apply_of_ne_of_ne, Fin.reduceEq] <;> rfl

theorem hA1_P5 (w : Fin 21 → ℝ) (a : Fin 4) (b : Fin 3) :
    A1 (fun t => w (sigP5 t)) a b = A1 w a (Equiv.swap 0 2 b) := by
  simp only [A1]; congr 1; simp only [sigP5, Function.Involutive.coe_toPerm]
  fin_cases a <;> fin_cases b <;> decide

set_option linter.unusedSimpArgs false in
theorem hA0_P6 (w : Fin 21 → ℝ) (r c : Fin 3) :
    A0 (fun t => w (sigP6 t)) r c = A0 w (Equiv.swap 0 1 r) (Equiv.swap 0 2 c) := by
  fin_cases r <;> fin_cases c <;>
    simp only [A0, sigP6, Function.Involutive.coe_toPerm, sigC6, of_apply, cons_val', cons_val_zero,
      cons_val_one, cons_val_two, tail_cons, head_cons, empty_val', cons_val_fin_one,
      head_fin_const, Fin.isValue, Equiv.swap_apply_left, Equiv.swap_apply_right,
      Equiv.swap_self, Equiv.refl_apply, Equiv.swap_apply_of_ne_of_ne, Fin.reduceEq] <;> rfl

theorem hA1_P6 (w : Fin 21 → ℝ) (a : Fin 4) (b : Fin 3) :
    A1 (fun t => w (sigP6 t)) a b = A1 w a (Equiv.swap 0 1 b) := by
  simp only [A1]; congr 1; simp only [sigP6, Function.Involutive.coe_toPerm]
  fin_cases a <;> fin_cases b <;> decide

set_option linter.unusedSimpArgs false in
theorem hA0_P7 (w : Fin 21 → ℝ) (r c : Fin 3) :
    A0 (fun t => w (sigP7 t)) r c = A0 w (Equiv.swap 0 2 r) (Equiv.swap 0 2 c) := by
  fin_cases r <;> fin_cases c <;>
    simp only [A0, sigP7, Function.Involutive.coe_toPerm, sigC7, of_apply, cons_val', cons_val_zero,
      cons_val_one, cons_val_two, tail_cons, head_cons, empty_val', cons_val_fin_one,
      head_fin_const, Fin.isValue, Equiv.swap_apply_left, Equiv.swap_apply_right,
      Equiv.swap_self, Equiv.refl_apply, Equiv.swap_apply_of_ne_of_ne, Fin.reduceEq] <;> rfl

theorem hA1_P7 (w : Fin 21 → ℝ) (a : Fin 4) (b : Fin 3) :
    A1 (fun t => w (sigP7 t)) a b = A1 w a (Equiv.swap 0 2 b) := by
  simp only [A1]; congr 1; simp only [sigP7, Function.Involutive.coe_toPerm]
  fin_cases a <;> fin_cases b <;> decide

/-- **The loss symmetry at each dominant pivot.** `∑ coreGen(w∘σ_p1)² = ∑ coreGen(w)²` — the loss is
invariant under each `σ_p1` (a genuine row/col symmetry of the `(3,3,4)` network). -/
theorem loss_symm_P0 (w : Fin 21 → ℝ) :
    (∑ k, (coreGen dvec eWrap k (fun t => w (sigP0 t))) ^ 2) = ∑ k, (coreGen dvec eWrap k w) ^ 2 :=
  sumSq_coreGen_symm w sigP0 1 0 (fun r c => hA0_P0 w r c) (fun a b => hA1_P0 w a b)

theorem loss_symm_P1 (w : Fin 21 → ℝ) :
    (∑ k, (coreGen dvec eWrap k (fun t => w (sigP1 t))) ^ 2) = ∑ k, (coreGen dvec eWrap k w) ^ 2 :=
  sumSq_coreGen_symm w sigP1 2 0 (fun r c => hA0_P1 w r c) (fun a b => hA1_P1 w a b)

theorem loss_symm_P2 (w : Fin 21 → ℝ) :
    (∑ k, (coreGen dvec eWrap k (fun t => w (sigP2 t))) ^ 2) = ∑ k, (coreGen dvec eWrap k w) ^ 2 :=
  sumSq_coreGen_symm w sigP2 0 1 (fun r c => hA0_P2 w r c) (fun a b => hA1_P2 w a b)

theorem loss_symm_P3 (w : Fin 21 → ℝ) :
    (∑ k, (coreGen dvec eWrap k (fun t => w (sigP3 t))) ^ 2) = ∑ k, (coreGen dvec eWrap k w) ^ 2 :=
  sumSq_coreGen_symm w sigP3 0 2 (fun r c => hA0_P3 w r c) (fun a b => hA1_P3 w a b)

theorem loss_symm_P4 (w : Fin 21 → ℝ) :
    (∑ k, (coreGen dvec eWrap k (fun t => w (sigP4 t))) ^ 2) = ∑ k, (coreGen dvec eWrap k w) ^ 2 :=
  sumSq_coreGen_symm w sigP4 1 1 (fun r c => hA0_P4 w r c) (fun a b => hA1_P4 w a b)

theorem loss_symm_P5 (w : Fin 21 → ℝ) :
    (∑ k, (coreGen dvec eWrap k (fun t => w (sigP5 t))) ^ 2) = ∑ k, (coreGen dvec eWrap k w) ^ 2 :=
  sumSq_coreGen_symm w sigP5 2 1 (fun r c => hA0_P5 w r c) (fun a b => hA1_P5 w a b)

theorem loss_symm_P6 (w : Fin 21 → ℝ) :
    (∑ k, (coreGen dvec eWrap k (fun t => w (sigP6 t))) ^ 2) = ∑ k, (coreGen dvec eWrap k w) ^ 2 :=
  sumSq_coreGen_symm w sigP6 1 2 (fun r c => hA0_P6 w r c) (fun a b => hA1_P6 w a b)

theorem loss_symm_P7 (w : Fin 21 → ℝ) :
    (∑ k, (coreGen dvec eWrap k (fun t => w (sigP7 t))) ^ 2) = ∑ k, (coreGen dvec eWrap k w) ^ 2 :=
  sumSq_coreGen_symm w sigP7 2 2 (fun r c => hA0_P7 w r c) (fun a b => hA1_P7 w a b)

/-! ## §3 — the coordinate-permutation conjugate of a chart (the generic engine)

`conjChart σ F := fun w t ↦ F (w∘σ) (σ⁻¹ t)` is the loss-symmetry conjugate of a chart — the same
shape as `blockBlowupMap_conj`'s LHS. It is FUNCTORIAL (`conjChart_comp`), fixes `id`, and turns each
born-native atom into its permuted sibling: a block blow-up into the permuted-centre one
(`blockBlowupMap_conj`), a coordinate permutation into the conjugate permutation
(`conjChart_permCoord`), and a `qdisp` block shear into the `σ`-conjugated-term-data shear
(`conjChart_blockShear_qdisp`). These are the atoms of `nativeChart1 = nativeSel ∘ nativePerm`, so the
born-native node-1 chart at each `p1` IS the `σ_p1`-conjugate of the canonical (§3′ per-pivot). -/

/-- The coordinate-permutation conjugate of a chart (matches `blockBlowupMap_conj`'s LHS shape). -/
def conjChart (σ : Equiv.Perm (Fin 21)) (F : (Fin 21 → ℝ) → (Fin 21 → ℝ)) :
    (Fin 21 → ℝ) → (Fin 21 → ℝ) := fun w t ↦ F (fun k ↦ w (σ k)) (σ.symm t)

/-- **Conjugation is functorial.** `conjChart σ (F ∘ G) = conjChart σ F ∘ conjChart σ G`. -/
theorem conjChart_comp (σ : Equiv.Perm (Fin 21)) (F G : (Fin 21 → ℝ) → (Fin 21 → ℝ)) :
    conjChart σ (F ∘ G) = conjChart σ F ∘ conjChart σ G := by
  funext w t
  simp only [conjChart, Function.comp_apply, Equiv.symm_apply_apply]

/-- **Conjugation fixes `id`.** -/
theorem conjChart_id (σ : Equiv.Perm (Fin 21)) : conjChart σ id = id := by
  funext w t
  simp only [conjChart, id_eq, Equiv.apply_symm_apply]

/-- **A block blow-up conjugates to the permuted-centre one** (restated from `blockBlowupMap_conj`). -/
theorem conjChart_blockBlowupMap (σ : Equiv.Perm (Fin 21)) (C : Finset (Fin 21)) (p : Fin 21) :
    conjChart σ (blockBlowupMap C p) = blockBlowupMap (C.image σ) (σ p) :=
  blockBlowupMap_conj σ C p

/-- **A coordinate permutation conjugates to the conjugate permutation.** -/
theorem conjChart_permCoord (σ ρ : Equiv.Perm (Fin 21)) :
    conjChart σ (fun w i ↦ w (ρ i)) = fun w i ↦ w (σ (ρ (σ.symm i))) := by
  funext w t
  simp only [conjChart]

/-- The `σ`-conjugate of a signed-term family: reindex the target coordinate by `σ⁻¹`, push the two
source coordinates through `σ`. -/
def conjTermData (σ : Equiv.Perm (Fin 21))
    (t : Fin 21 → Option (Bool × Fin 21 × Fin 21)) : Fin 21 → Option (Bool × Fin 21 × Fin 21) :=
  fun i ↦ (t (σ.symm i)).map (fun x ↦ (x.1, σ x.2.1, σ x.2.2))

/-- **`sterm` transports through `conjTermData`.** -/
theorem sterm_conjTermData (σ : Equiv.Perm (Fin 21))
    (t : Fin 21 → Option (Bool × Fin 21 × Fin 21)) (w : Fin 21 → ℝ) (i : Fin 21) :
    sterm (conjTermData σ t) w i = sterm t (fun k ↦ w (σ k)) (σ.symm i) := by
  simp only [sterm, conjTermData]
  cases t (σ.symm i) <;> simp

/-- **A `qdisp` block shear conjugates to the `σ`-conjugated-term-data shear.** -/
theorem conjChart_blockShear_qdisp (σ : Equiv.Perm (Fin 21))
    (t1 t2 : Fin 21 → Option (Bool × Fin 21 × Fin 21)) :
    conjChart σ (blockShear (qdisp t1 t2))
      = blockShear (qdisp (conjTermData σ t1) (conjTermData σ t2)) := by
  funext w t
  simp only [conjChart, blockShear, Pi.add_apply, qdisp, sterm_conjTermData, Equiv.apply_symm_apply]

/-! ### §3′ — the born-native node-1 chart at pivot `0` IS the `σ_0`-conjugate (the validator) -/

/-- `nativeSel 0 = conjChart σ_0 (nativeSel 20)` (the shear atom). The `σ_0`-conjugation MIXES the two
signed-term families (a term slides between the `t1`/`t2` slots), so the individual `conjTermData`s
do NOT match the emitted `t1P0`/`t2P0` — but the `qdisp` SUM does, verified per coordinate (`ring`
after `sterm_conjTermData` pulls the RHS back to the canonical data at `x∘σ_0`). -/
theorem nativeSel_conj_P0 : nativeSel 0 = conjChart sigP0 (nativeSel 20) := by
  simp only [nativeSel, Fin.reduceEq, if_true, if_false]
  rw [conjChart_blockShear_qdisp]
  congr 1
  funext x i
  simp only [qdisp, sterm_conjTermData]
  fin_cases i <;>
    simp [sterm, t1P0, t2P0, t1P20, t2P20, sigP0, Function.Involutive.coe_toPerm,
      Function.Involutive.toPerm_symm, sigC0] <;>
    ring

/-- `nativePerm 0 = conjChart σ_0 (nativePerm 20)` (the perm atom; perm match by `decide`). -/
theorem nativePerm_conj_P0 : nativePerm 0 = conjChart sigP0 (nativePerm 20) := by
  have hperm : ∀ i, cpermS0 i = sigP0 (cpermS20 (sigP0.symm i)) := by decide
  simp only [nativePerm, Fin.reduceEq, if_true, if_false]
  rw [conjChart_permCoord]
  funext w i
  exact congrArg w (hperm i)

/-- **`nativeChart1 0 = conjChart σ_0 (nativeChart1 20)`** — the node-1 chart transports. -/
theorem nativeChart1_conj_P0 : nativeChart1 0 = conjChart sigP0 (nativeChart1 20) := by
  simp only [nativeChart1]
  rw [conjChart_comp, ← nativeSel_conj_P0, ← nativePerm_conj_P0]

/-! ## §5 — the product-germ reindex under a coordinate permutation (step 5)

`monoSumSqGerm a Z (w∘σ) = monoSumSqGerm (a∘σ⁻¹) (σ Z) w`: the monomial exponent reindexes by `σ⁻¹`
and the sum-of-squares block by `σ` (both `Equiv`-reindexings of the product / sum). -/

/-- **The product germ reindexes under a coordinate permutation.** -/
theorem monoSumSqGerm_conj (σ : Equiv.Perm (Fin 21)) (a : Fin 21 → ℕ) (Z : Finset (Fin 21))
    (w : Fin 21 → ℝ) :
    monoSumSqGerm a Z (fun t ↦ w (σ t))
      = monoSumSqGerm (fun d ↦ a (σ.symm d)) (Z.image σ) w := by
  simp only [monoSumSqGerm]
  have hp : (∏ d, w (σ d) ^ a d) = ∏ e, w e ^ a (σ.symm e) := by
    rw [← Equiv.prod_comp σ (fun e ↦ w e ^ a (σ.symm e))]
    exact Finset.prod_congr rfl (fun d _ ↦ by rw [Equiv.symm_apply_apply])
  have hs : (∑ j ∈ Z, w (σ j) ^ 2) = ∑ j ∈ Z.image σ, w j ^ 2 := by
    rw [Finset.sum_image (fun x _ y _ h ↦ σ.injective h)]
  rw [hp, hs]

/-! ## §6 — the domination transport (the generic engine + the per-pivot instances)

The over-vanishing domination `monoSumSqGerm vmExp Z ≤ sumSqFam (coreGen ∘ (gFlat ∘ Ψ))` at a
dominant pivot `p1 ≠ 20` follows from the `p1 = 20` canonical, transported by `σ_p1`:
- the chart transports (`gFlat` at `p1` is the `σ_p1`-conjugate of the canonical, §3 + step 4);
- the loss is `σ_p1`-invariant (`loss_symm_Pn`, so the pulled-back sum-of-squares transports:
  `sumSqFam_coreGen_conj`); and
- the product germ reindexes (`monoSumSqGerm_conj`).
So a base domination at `(vmExp, Z)` for `gFlat idx_20 ∘ Ψ_20` yields the domination at the
`σ_p1`-transported data `(vmExp ∘ σ_p1⁻¹, σ_p1 Z)` for the `σ_p1`-conjugate chart. -/

/-- **The pulled-back loss transports under a chart conjugation.** If `σ`'s loss symmetry holds
(`hloss`) and `σ⁻¹ = σ`, then `∑ᵢ (coreGen i ∘ conjChart σ H)²` at `u` equals `∑ᵢ (coreGen i ∘ H)²`
at `u∘σ`. -/
theorem sumSqFam_coreGen_conj (σ : Equiv.Perm (Fin 21)) (hsymm : σ.symm = σ)
    (hloss : ∀ w : Fin 21 → ℝ,
      (∑ k, (coreGen dvec eWrap k (fun t ↦ w (σ t))) ^ 2) = ∑ k, (coreGen dvec eWrap k w) ^ 2)
    (H : (Fin 21 → ℝ) → (Fin 21 → ℝ)) (u : Fin 21 → ℝ) :
    sumSqFam (fun i ↦ coreGen dvec eWrap i ∘ conjChart σ H) u
      = sumSqFam (fun i ↦ coreGen dvec eWrap i ∘ H) (fun t ↦ u (σ t)) := by
  have hcw : conjChart σ H u = (fun t ↦ (H (fun k ↦ u (σ k))) (σ t)) := by
    funext t; simp only [conjChart, hsymm]
  simp only [sumSqFam, Function.comp_apply, hcw]
  exact hloss (H (fun k ↦ u (σ k)))

/-- **The domination transport (the generic engine).** From a base product-germ domination for the
chart `H20` at `(a, Z)`, plus `σ`'s loss symmetry and `σ⁻¹ = σ`, the `σ`-conjugate chart
`conjChart σ H20` dominates the `σ`-transported product germ `monoSumSqGerm (a ∘ σ⁻¹) (σ Z)`. The
caller supplies `H20 = gFlat idx_20 ∘ Ψ_20` and rewrites `conjChart σ H20 = gFlat idx ∘ Ψ_idx` (step
4 + `conjChart_comp`). -/
theorem domination_transport (σ : Equiv.Perm (Fin 21)) (hsymm : σ.symm = σ)
    (hloss : ∀ w : Fin 21 → ℝ,
      (∑ k, (coreGen dvec eWrap k (fun t ↦ w (σ t))) ^ 2) = ∑ k, (coreGen dvec eWrap k w) ^ 2)
    (H20 : (Fin 21 → ℝ) → (Fin 21 → ℝ)) (a : Fin 21 → ℕ) (Z : Finset (Fin 21))
    (hbase : ∀ v, monoSumSqGerm a Z v ≤ sumSqFam (fun i ↦ coreGen dvec eWrap i ∘ H20) v)
    (u : Fin 21 → ℝ) :
    monoSumSqGerm (fun d ↦ a (σ.symm d)) (Z.image σ) u
      ≤ sumSqFam (fun i ↦ coreGen dvec eWrap i ∘ conjChart σ H20) u := by
  rw [sumSqFam_coreGen_conj σ hsymm hloss H20 u, ← monoSumSqGerm_conj σ a Z u]
  exact hbase (fun t ↦ u (σ t))

/-! ## §4 — the leaf composite transports (`gFlat` is the `σ_p1`-conjugate of the canonical)

`gFlat idx` unfolds to `gComposite p1 p2 p3` (the `Idx` projections spelled out). The whole-conjugate
fan was DEFINED so its node-2/node-3 centres are the `σ_p1`-images of the canonical (`sigmaC1Fs`),
so — using §3's `nativeChart1_conj` for the node-1 chart and `blockBlowupMap_conj` for the blow-ups —
`gComposite p1 (σ_p1 p2) (σ_p1 p3) = conjChart σ_p1 (gComposite 20 p2 p3)` (`decide` on the finite
centre/pivot images). Validator on pivot 0. -/

/-- The raw leaf composite (`gFlat` with the `Idx` projections spelled out). -/
noncomputable def gComposite (p1 p2 p3 : Fin 21) : (Fin 21 → ℝ) → (Fin 21 → ℝ) :=
  (blockBlowupMap S1 p1 ∘ nativeChart1 p1) ∘
    ((blockBlowupMap (sigmaC1Fs p1) p2 ∘ id) ∘ (blockBlowupMap (sigmaC2Fs p1) p3 ∘ id))

/-- `gFlat idx = gComposite (idx projections)` (definitional). -/
theorem gFlat_eq_gComposite (idx : Idx) :
    gFlat idx = gComposite idx.1.1 idx.2.1.1 idx.2.2.1 := rfl

/-- **Step 4 (pivot 0): the leaf composite is the `σ_0`-conjugate of the canonical.** -/
theorem gComposite_conj_P0 (p2 p3 : Fin 21) :
    gComposite 0 (sigP0 p2) (sigP0 p3) = conjChart sigP0 (gComposite 20 p2 p3) := by
  have hS1 : (S1 : Finset (Fin 21)).image sigP0 = S1 := by decide
  have h20 : sigP0 20 = 0 := by decide
  have hC1 : (sigmaC1Fs 20).image sigP0 = sigmaC1Fs 0 := by decide
  have hC2 : (sigmaC2Fs 20).image sigP0 = sigmaC2Fs 0 := by decide
  simp only [gComposite, conjChart_comp, conjChart_id, conjChart_blockBlowupMap,
    ← nativeChart1_conj_P0, hS1, h20, hC1, hC2]

/-! ## §6 — the per-pivot leaf domination transport (the ∀-144 step, per dominant pivot)

`leaf_domination_Pn` transports the over-vanishing domination from the canonical `(20,p2,p3)` to the
leaf `(p1, σ_p1 p2, σ_p1 p3)`: given the base domination for the canonical chart
`gComposite 20 p2 p3 ∘ Ψ_20` at data `(a, Z)`, the leaf's native chart
`gComposite p1 (σ_p1 p2)(σ_p1 p3) ∘ (σ_p1-conjugate of Ψ_20)` dominates the `σ_p1`-transported germ
`monoSumSqGerm (a ∘ σ_p1⁻¹) (σ_p1 Z)`. Wiring the 16 canonical `canon_domination` facts in as `hbase`
(one per `(p2,p3)`) over the 8 non-canonical dominant pivots yields all `8×16` transported leaves;
the 16 `p1 = 20` leaves are the base (direct). Validator on pivot 0. -/

/-- **The over-vanishing domination at pivot 0, transported from the canonical (pivot 20).** -/
theorem leaf_domination_P0 (p2 p3 : Fin 21) (psi20 : (Fin 21 → ℝ) → (Fin 21 → ℝ))
    (a : Fin 21 → ℕ) (Z : Finset (Fin 21))
    (hbase : ∀ v, monoSumSqGerm a Z v
      ≤ sumSqFam (fun i ↦ coreGen dvec eWrap i ∘ (gComposite 20 p2 p3 ∘ psi20)) v)
    (u : Fin 21 → ℝ) :
    monoSumSqGerm (fun d ↦ a (sigP0.symm d)) (Z.image sigP0) u
      ≤ sumSqFam (fun i ↦ coreGen dvec eWrap i ∘
          (gComposite 0 (sigP0 p2) (sigP0 p3) ∘ conjChart sigP0 psi20)) u := by
  have hchart : (gComposite 0 (sigP0 p2) (sigP0 p3) ∘ conjChart sigP0 psi20)
      = conjChart sigP0 (gComposite 20 p2 p3 ∘ psi20) := by
    rw [gComposite_conj_P0, conjChart_comp]
  have hval : sumSqFam (fun i ↦ coreGen dvec eWrap i ∘
        (gComposite 0 (sigP0 p2) (sigP0 p3) ∘ conjChart sigP0 psi20)) u
      = sumSqFam (fun i ↦ coreGen dvec eWrap i ∘ conjChart sigP0 (gComposite 20 p2 p3 ∘ psi20)) u :=
    congrArg (fun c ↦ sumSqFam (fun i ↦ coreGen dvec eWrap i ∘ c) u) hchart
  exact le_of_le_of_eq
    (domination_transport sigP0 rfl loss_symm_P0 (gComposite 20 p2 p3 ∘ psi20) a Z hbase u) hval.symm

/-! ### §3′-§6 — the remaining 7 dominant pivots (mechanical replication of the pivot-0 chain) -/

theorem nativeSel_conj_P1 : nativeSel 1 = conjChart sigP1 (nativeSel 20) := by
  simp only [nativeSel, Fin.reduceEq, if_true, if_false]
  rw [conjChart_blockShear_qdisp]; congr 1; funext x i
  simp only [qdisp, sterm_conjTermData]
  fin_cases i <;>
    simp [sterm, t1P1, t2P1, t1P20, t2P20, sigP1, Function.Involutive.coe_toPerm,
      Function.Involutive.toPerm_symm, sigC1] <;> ring

theorem nativePerm_conj_P1 : nativePerm 1 = conjChart sigP1 (nativePerm 20) := by
  have hperm : ∀ i, cpermS1 i = sigP1 (cpermS20 (sigP1.symm i)) := by decide
  simp only [nativePerm, Fin.reduceEq, if_true, if_false]
  rw [conjChart_permCoord]; funext w i; exact congrArg w (hperm i)

theorem nativeChart1_conj_P1 : nativeChart1 1 = conjChart sigP1 (nativeChart1 20) := by
  simp only [nativeChart1]; rw [conjChart_comp, ← nativeSel_conj_P1, ← nativePerm_conj_P1]

theorem gComposite_conj_P1 (p2 p3 : Fin 21) :
    gComposite 1 (sigP1 p2) (sigP1 p3) = conjChart sigP1 (gComposite 20 p2 p3) := by
  have hS1 : (S1 : Finset (Fin 21)).image sigP1 = S1 := by decide
  have hn : sigP1 20 = 1 := by decide
  have hC1 : (sigmaC1Fs 20).image sigP1 = sigmaC1Fs 1 := by decide
  have hC2 : (sigmaC2Fs 20).image sigP1 = sigmaC2Fs 1 := by decide
  simp only [gComposite, conjChart_comp, conjChart_id, conjChart_blockBlowupMap,
    ← nativeChart1_conj_P1, hS1, hn, hC1, hC2]

theorem leaf_domination_P1 (p2 p3 : Fin 21) (psi20 : (Fin 21 → ℝ) → (Fin 21 → ℝ))
    (a : Fin 21 → ℕ) (Z : Finset (Fin 21))
    (hbase : ∀ v, monoSumSqGerm a Z v
      ≤ sumSqFam (fun i ↦ coreGen dvec eWrap i ∘ (gComposite 20 p2 p3 ∘ psi20)) v)
    (u : Fin 21 → ℝ) :
    monoSumSqGerm (fun d ↦ a (sigP1.symm d)) (Z.image sigP1) u
      ≤ sumSqFam (fun i ↦ coreGen dvec eWrap i ∘
          (gComposite 1 (sigP1 p2) (sigP1 p3) ∘ conjChart sigP1 psi20)) u := by
  have hchart : (gComposite 1 (sigP1 p2) (sigP1 p3) ∘ conjChart sigP1 psi20)
      = conjChart sigP1 (gComposite 20 p2 p3 ∘ psi20) := by rw [gComposite_conj_P1, conjChart_comp]
  have hval : sumSqFam (fun i ↦ coreGen dvec eWrap i ∘
        (gComposite 1 (sigP1 p2) (sigP1 p3) ∘ conjChart sigP1 psi20)) u
      = sumSqFam (fun i ↦ coreGen dvec eWrap i ∘ conjChart sigP1 (gComposite 20 p2 p3 ∘ psi20)) u :=
    congrArg (fun c ↦ sumSqFam (fun i ↦ coreGen dvec eWrap i ∘ c) u) hchart
  exact le_of_le_of_eq
    (domination_transport sigP1 rfl loss_symm_P1 (gComposite 20 p2 p3 ∘ psi20) a Z hbase u) hval.symm

theorem nativeSel_conj_P2 : nativeSel 2 = conjChart sigP2 (nativeSel 20) := by
  simp only [nativeSel, Fin.reduceEq, if_true, if_false]
  rw [conjChart_blockShear_qdisp]; congr 1; funext x i
  simp only [qdisp, sterm_conjTermData]
  fin_cases i <;>
    simp [sterm, t1P2, t2P2, t1P20, t2P20, sigP2, Function.Involutive.coe_toPerm,
      Function.Involutive.toPerm_symm, sigC2] <;> ring

theorem nativePerm_conj_P2 : nativePerm 2 = conjChart sigP2 (nativePerm 20) := by
  have hperm : ∀ i, cpermS2 i = sigP2 (cpermS20 (sigP2.symm i)) := by decide
  simp only [nativePerm, Fin.reduceEq, if_true, if_false]
  rw [conjChart_permCoord]; funext w i; exact congrArg w (hperm i)

theorem nativeChart1_conj_P2 : nativeChart1 2 = conjChart sigP2 (nativeChart1 20) := by
  simp only [nativeChart1]; rw [conjChart_comp, ← nativeSel_conj_P2, ← nativePerm_conj_P2]

theorem gComposite_conj_P2 (p2 p3 : Fin 21) :
    gComposite 2 (sigP2 p2) (sigP2 p3) = conjChart sigP2 (gComposite 20 p2 p3) := by
  have hS1 : (S1 : Finset (Fin 21)).image sigP2 = S1 := by decide
  have hn : sigP2 20 = 2 := by decide
  have hC1 : (sigmaC1Fs 20).image sigP2 = sigmaC1Fs 2 := by decide
  have hC2 : (sigmaC2Fs 20).image sigP2 = sigmaC2Fs 2 := by decide
  simp only [gComposite, conjChart_comp, conjChart_id, conjChart_blockBlowupMap,
    ← nativeChart1_conj_P2, hS1, hn, hC1, hC2]

theorem leaf_domination_P2 (p2 p3 : Fin 21) (psi20 : (Fin 21 → ℝ) → (Fin 21 → ℝ))
    (a : Fin 21 → ℕ) (Z : Finset (Fin 21))
    (hbase : ∀ v, monoSumSqGerm a Z v
      ≤ sumSqFam (fun i ↦ coreGen dvec eWrap i ∘ (gComposite 20 p2 p3 ∘ psi20)) v)
    (u : Fin 21 → ℝ) :
    monoSumSqGerm (fun d ↦ a (sigP2.symm d)) (Z.image sigP2) u
      ≤ sumSqFam (fun i ↦ coreGen dvec eWrap i ∘
          (gComposite 2 (sigP2 p2) (sigP2 p3) ∘ conjChart sigP2 psi20)) u := by
  have hchart : (gComposite 2 (sigP2 p2) (sigP2 p3) ∘ conjChart sigP2 psi20)
      = conjChart sigP2 (gComposite 20 p2 p3 ∘ psi20) := by rw [gComposite_conj_P2, conjChart_comp]
  have hval : sumSqFam (fun i ↦ coreGen dvec eWrap i ∘
        (gComposite 2 (sigP2 p2) (sigP2 p3) ∘ conjChart sigP2 psi20)) u
      = sumSqFam (fun i ↦ coreGen dvec eWrap i ∘ conjChart sigP2 (gComposite 20 p2 p3 ∘ psi20)) u :=
    congrArg (fun c ↦ sumSqFam (fun i ↦ coreGen dvec eWrap i ∘ c) u) hchart
  exact le_of_le_of_eq
    (domination_transport sigP2 rfl loss_symm_P2 (gComposite 20 p2 p3 ∘ psi20) a Z hbase u) hval.symm

theorem nativeSel_conj_P3 : nativeSel 3 = conjChart sigP3 (nativeSel 20) := by
  simp only [nativeSel, Fin.reduceEq, if_true, if_false]
  rw [conjChart_blockShear_qdisp]; congr 1; funext x i
  simp only [qdisp, sterm_conjTermData]
  fin_cases i <;>
    simp [sterm, t1P3, t2P3, t1P20, t2P20, sigP3, Function.Involutive.coe_toPerm,
      Function.Involutive.toPerm_symm, sigC3] <;> ring

theorem nativePerm_conj_P3 : nativePerm 3 = conjChart sigP3 (nativePerm 20) := by
  have hperm : ∀ i, cpermS3 i = sigP3 (cpermS20 (sigP3.symm i)) := by decide
  simp only [nativePerm, Fin.reduceEq, if_true, if_false]
  rw [conjChart_permCoord]; funext w i; exact congrArg w (hperm i)

theorem nativeChart1_conj_P3 : nativeChart1 3 = conjChart sigP3 (nativeChart1 20) := by
  simp only [nativeChart1]; rw [conjChart_comp, ← nativeSel_conj_P3, ← nativePerm_conj_P3]

theorem gComposite_conj_P3 (p2 p3 : Fin 21) :
    gComposite 3 (sigP3 p2) (sigP3 p3) = conjChart sigP3 (gComposite 20 p2 p3) := by
  have hS1 : (S1 : Finset (Fin 21)).image sigP3 = S1 := by decide
  have hn : sigP3 20 = 3 := by decide
  have hC1 : (sigmaC1Fs 20).image sigP3 = sigmaC1Fs 3 := by decide
  have hC2 : (sigmaC2Fs 20).image sigP3 = sigmaC2Fs 3 := by decide
  simp only [gComposite, conjChart_comp, conjChart_id, conjChart_blockBlowupMap,
    ← nativeChart1_conj_P3, hS1, hn, hC1, hC2]

theorem leaf_domination_P3 (p2 p3 : Fin 21) (psi20 : (Fin 21 → ℝ) → (Fin 21 → ℝ))
    (a : Fin 21 → ℕ) (Z : Finset (Fin 21))
    (hbase : ∀ v, monoSumSqGerm a Z v
      ≤ sumSqFam (fun i ↦ coreGen dvec eWrap i ∘ (gComposite 20 p2 p3 ∘ psi20)) v)
    (u : Fin 21 → ℝ) :
    monoSumSqGerm (fun d ↦ a (sigP3.symm d)) (Z.image sigP3) u
      ≤ sumSqFam (fun i ↦ coreGen dvec eWrap i ∘
          (gComposite 3 (sigP3 p2) (sigP3 p3) ∘ conjChart sigP3 psi20)) u := by
  have hchart : (gComposite 3 (sigP3 p2) (sigP3 p3) ∘ conjChart sigP3 psi20)
      = conjChart sigP3 (gComposite 20 p2 p3 ∘ psi20) := by rw [gComposite_conj_P3, conjChart_comp]
  have hval : sumSqFam (fun i ↦ coreGen dvec eWrap i ∘
        (gComposite 3 (sigP3 p2) (sigP3 p3) ∘ conjChart sigP3 psi20)) u
      = sumSqFam (fun i ↦ coreGen dvec eWrap i ∘ conjChart sigP3 (gComposite 20 p2 p3 ∘ psi20)) u :=
    congrArg (fun c ↦ sumSqFam (fun i ↦ coreGen dvec eWrap i ∘ c) u) hchart
  exact le_of_le_of_eq
    (domination_transport sigP3 rfl loss_symm_P3 (gComposite 20 p2 p3 ∘ psi20) a Z hbase u) hval.symm

theorem nativeSel_conj_P4 : nativeSel 4 = conjChart sigP4 (nativeSel 20) := by
  simp only [nativeSel, Fin.reduceEq, if_true, if_false]
  rw [conjChart_blockShear_qdisp]; congr 1; funext x i
  simp only [qdisp, sterm_conjTermData]
  fin_cases i <;>
    simp [sterm, t1P4, t2P4, t1P20, t2P20, sigP4, Function.Involutive.coe_toPerm,
      Function.Involutive.toPerm_symm, sigC4] <;> ring

theorem nativePerm_conj_P4 : nativePerm 4 = conjChart sigP4 (nativePerm 20) := by
  have hperm : ∀ i, cpermS4 i = sigP4 (cpermS20 (sigP4.symm i)) := by decide
  simp only [nativePerm, Fin.reduceEq, if_true, if_false]
  rw [conjChart_permCoord]; funext w i; exact congrArg w (hperm i)

theorem nativeChart1_conj_P4 : nativeChart1 4 = conjChart sigP4 (nativeChart1 20) := by
  simp only [nativeChart1]; rw [conjChart_comp, ← nativeSel_conj_P4, ← nativePerm_conj_P4]

theorem gComposite_conj_P4 (p2 p3 : Fin 21) :
    gComposite 4 (sigP4 p2) (sigP4 p3) = conjChart sigP4 (gComposite 20 p2 p3) := by
  have hS1 : (S1 : Finset (Fin 21)).image sigP4 = S1 := by decide
  have hn : sigP4 20 = 4 := by decide
  have hC1 : (sigmaC1Fs 20).image sigP4 = sigmaC1Fs 4 := by decide
  have hC2 : (sigmaC2Fs 20).image sigP4 = sigmaC2Fs 4 := by decide
  simp only [gComposite, conjChart_comp, conjChart_id, conjChart_blockBlowupMap,
    ← nativeChart1_conj_P4, hS1, hn, hC1, hC2]

theorem leaf_domination_P4 (p2 p3 : Fin 21) (psi20 : (Fin 21 → ℝ) → (Fin 21 → ℝ))
    (a : Fin 21 → ℕ) (Z : Finset (Fin 21))
    (hbase : ∀ v, monoSumSqGerm a Z v
      ≤ sumSqFam (fun i ↦ coreGen dvec eWrap i ∘ (gComposite 20 p2 p3 ∘ psi20)) v)
    (u : Fin 21 → ℝ) :
    monoSumSqGerm (fun d ↦ a (sigP4.symm d)) (Z.image sigP4) u
      ≤ sumSqFam (fun i ↦ coreGen dvec eWrap i ∘
          (gComposite 4 (sigP4 p2) (sigP4 p3) ∘ conjChart sigP4 psi20)) u := by
  have hchart : (gComposite 4 (sigP4 p2) (sigP4 p3) ∘ conjChart sigP4 psi20)
      = conjChart sigP4 (gComposite 20 p2 p3 ∘ psi20) := by rw [gComposite_conj_P4, conjChart_comp]
  have hval : sumSqFam (fun i ↦ coreGen dvec eWrap i ∘
        (gComposite 4 (sigP4 p2) (sigP4 p3) ∘ conjChart sigP4 psi20)) u
      = sumSqFam (fun i ↦ coreGen dvec eWrap i ∘ conjChart sigP4 (gComposite 20 p2 p3 ∘ psi20)) u :=
    congrArg (fun c ↦ sumSqFam (fun i ↦ coreGen dvec eWrap i ∘ c) u) hchart
  exact le_of_le_of_eq
    (domination_transport sigP4 rfl loss_symm_P4 (gComposite 20 p2 p3 ∘ psi20) a Z hbase u) hval.symm

theorem nativeSel_conj_P5 : nativeSel 5 = conjChart sigP5 (nativeSel 20) := by
  simp only [nativeSel, Fin.reduceEq, if_true, if_false]
  rw [conjChart_blockShear_qdisp]; congr 1; funext x i
  simp only [qdisp, sterm_conjTermData]
  fin_cases i <;>
    simp [sterm, t1P5, t2P5, t1P20, t2P20, sigP5, Function.Involutive.coe_toPerm,
      Function.Involutive.toPerm_symm, sigC5] <;> ring

theorem nativePerm_conj_P5 : nativePerm 5 = conjChart sigP5 (nativePerm 20) := by
  have hperm : ∀ i, cpermS5 i = sigP5 (cpermS20 (sigP5.symm i)) := by decide
  simp only [nativePerm, Fin.reduceEq, if_true, if_false]
  rw [conjChart_permCoord]; funext w i; exact congrArg w (hperm i)

theorem nativeChart1_conj_P5 : nativeChart1 5 = conjChart sigP5 (nativeChart1 20) := by
  simp only [nativeChart1]; rw [conjChart_comp, ← nativeSel_conj_P5, ← nativePerm_conj_P5]

theorem gComposite_conj_P5 (p2 p3 : Fin 21) :
    gComposite 5 (sigP5 p2) (sigP5 p3) = conjChart sigP5 (gComposite 20 p2 p3) := by
  have hS1 : (S1 : Finset (Fin 21)).image sigP5 = S1 := by decide
  have hn : sigP5 20 = 5 := by decide
  have hC1 : (sigmaC1Fs 20).image sigP5 = sigmaC1Fs 5 := by decide
  have hC2 : (sigmaC2Fs 20).image sigP5 = sigmaC2Fs 5 := by decide
  simp only [gComposite, conjChart_comp, conjChart_id, conjChart_blockBlowupMap,
    ← nativeChart1_conj_P5, hS1, hn, hC1, hC2]

theorem leaf_domination_P5 (p2 p3 : Fin 21) (psi20 : (Fin 21 → ℝ) → (Fin 21 → ℝ))
    (a : Fin 21 → ℕ) (Z : Finset (Fin 21))
    (hbase : ∀ v, monoSumSqGerm a Z v
      ≤ sumSqFam (fun i ↦ coreGen dvec eWrap i ∘ (gComposite 20 p2 p3 ∘ psi20)) v)
    (u : Fin 21 → ℝ) :
    monoSumSqGerm (fun d ↦ a (sigP5.symm d)) (Z.image sigP5) u
      ≤ sumSqFam (fun i ↦ coreGen dvec eWrap i ∘
          (gComposite 5 (sigP5 p2) (sigP5 p3) ∘ conjChart sigP5 psi20)) u := by
  have hchart : (gComposite 5 (sigP5 p2) (sigP5 p3) ∘ conjChart sigP5 psi20)
      = conjChart sigP5 (gComposite 20 p2 p3 ∘ psi20) := by rw [gComposite_conj_P5, conjChart_comp]
  have hval : sumSqFam (fun i ↦ coreGen dvec eWrap i ∘
        (gComposite 5 (sigP5 p2) (sigP5 p3) ∘ conjChart sigP5 psi20)) u
      = sumSqFam (fun i ↦ coreGen dvec eWrap i ∘ conjChart sigP5 (gComposite 20 p2 p3 ∘ psi20)) u :=
    congrArg (fun c ↦ sumSqFam (fun i ↦ coreGen dvec eWrap i ∘ c) u) hchart
  exact le_of_le_of_eq
    (domination_transport sigP5 rfl loss_symm_P5 (gComposite 20 p2 p3 ∘ psi20) a Z hbase u) hval.symm

theorem nativeSel_conj_P6 : nativeSel 6 = conjChart sigP6 (nativeSel 20) := by
  simp only [nativeSel, Fin.reduceEq, if_true, if_false]
  rw [conjChart_blockShear_qdisp]; congr 1; funext x i
  simp only [qdisp, sterm_conjTermData]
  fin_cases i <;>
    simp [sterm, t1P6, t2P6, t1P20, t2P20, sigP6, Function.Involutive.coe_toPerm,
      Function.Involutive.toPerm_symm, sigC6] <;> ring

theorem nativePerm_conj_P6 : nativePerm 6 = conjChart sigP6 (nativePerm 20) := by
  have hperm : ∀ i, cpermS6 i = sigP6 (cpermS20 (sigP6.symm i)) := by decide
  simp only [nativePerm, Fin.reduceEq, if_true, if_false]
  rw [conjChart_permCoord]; funext w i; exact congrArg w (hperm i)

theorem nativeChart1_conj_P6 : nativeChart1 6 = conjChart sigP6 (nativeChart1 20) := by
  simp only [nativeChart1]; rw [conjChart_comp, ← nativeSel_conj_P6, ← nativePerm_conj_P6]

theorem gComposite_conj_P6 (p2 p3 : Fin 21) :
    gComposite 6 (sigP6 p2) (sigP6 p3) = conjChart sigP6 (gComposite 20 p2 p3) := by
  have hS1 : (S1 : Finset (Fin 21)).image sigP6 = S1 := by decide
  have hn : sigP6 20 = 6 := by decide
  have hC1 : (sigmaC1Fs 20).image sigP6 = sigmaC1Fs 6 := by decide
  have hC2 : (sigmaC2Fs 20).image sigP6 = sigmaC2Fs 6 := by decide
  simp only [gComposite, conjChart_comp, conjChart_id, conjChart_blockBlowupMap,
    ← nativeChart1_conj_P6, hS1, hn, hC1, hC2]

theorem leaf_domination_P6 (p2 p3 : Fin 21) (psi20 : (Fin 21 → ℝ) → (Fin 21 → ℝ))
    (a : Fin 21 → ℕ) (Z : Finset (Fin 21))
    (hbase : ∀ v, monoSumSqGerm a Z v
      ≤ sumSqFam (fun i ↦ coreGen dvec eWrap i ∘ (gComposite 20 p2 p3 ∘ psi20)) v)
    (u : Fin 21 → ℝ) :
    monoSumSqGerm (fun d ↦ a (sigP6.symm d)) (Z.image sigP6) u
      ≤ sumSqFam (fun i ↦ coreGen dvec eWrap i ∘
          (gComposite 6 (sigP6 p2) (sigP6 p3) ∘ conjChart sigP6 psi20)) u := by
  have hchart : (gComposite 6 (sigP6 p2) (sigP6 p3) ∘ conjChart sigP6 psi20)
      = conjChart sigP6 (gComposite 20 p2 p3 ∘ psi20) := by rw [gComposite_conj_P6, conjChart_comp]
  have hval : sumSqFam (fun i ↦ coreGen dvec eWrap i ∘
        (gComposite 6 (sigP6 p2) (sigP6 p3) ∘ conjChart sigP6 psi20)) u
      = sumSqFam (fun i ↦ coreGen dvec eWrap i ∘ conjChart sigP6 (gComposite 20 p2 p3 ∘ psi20)) u :=
    congrArg (fun c ↦ sumSqFam (fun i ↦ coreGen dvec eWrap i ∘ c) u) hchart
  exact le_of_le_of_eq
    (domination_transport sigP6 rfl loss_symm_P6 (gComposite 20 p2 p3 ∘ psi20) a Z hbase u) hval.symm

theorem nativeSel_conj_P7 : nativeSel 7 = conjChart sigP7 (nativeSel 20) := by
  simp only [nativeSel, Fin.reduceEq, if_true, if_false]
  rw [conjChart_blockShear_qdisp]; congr 1; funext x i
  simp only [qdisp, sterm_conjTermData]
  fin_cases i <;>
    simp [sterm, t1P7, t2P7, t1P20, t2P20, sigP7, Function.Involutive.coe_toPerm,
      Function.Involutive.toPerm_symm, sigC7] <;> ring

theorem nativePerm_conj_P7 : nativePerm 7 = conjChart sigP7 (nativePerm 20) := by
  have hperm : ∀ i, cpermS7 i = sigP7 (cpermS20 (sigP7.symm i)) := by decide
  simp only [nativePerm, Fin.reduceEq, if_true, if_false]
  rw [conjChart_permCoord]; funext w i; exact congrArg w (hperm i)

theorem nativeChart1_conj_P7 : nativeChart1 7 = conjChart sigP7 (nativeChart1 20) := by
  simp only [nativeChart1]; rw [conjChart_comp, ← nativeSel_conj_P7, ← nativePerm_conj_P7]

theorem gComposite_conj_P7 (p2 p3 : Fin 21) :
    gComposite 7 (sigP7 p2) (sigP7 p3) = conjChart sigP7 (gComposite 20 p2 p3) := by
  have hS1 : (S1 : Finset (Fin 21)).image sigP7 = S1 := by decide
  have hn : sigP7 20 = 7 := by decide
  have hC1 : (sigmaC1Fs 20).image sigP7 = sigmaC1Fs 7 := by decide
  have hC2 : (sigmaC2Fs 20).image sigP7 = sigmaC2Fs 7 := by decide
  simp only [gComposite, conjChart_comp, conjChart_id, conjChart_blockBlowupMap,
    ← nativeChart1_conj_P7, hS1, hn, hC1, hC2]

theorem leaf_domination_P7 (p2 p3 : Fin 21) (psi20 : (Fin 21 → ℝ) → (Fin 21 → ℝ))
    (a : Fin 21 → ℕ) (Z : Finset (Fin 21))
    (hbase : ∀ v, monoSumSqGerm a Z v
      ≤ sumSqFam (fun i ↦ coreGen dvec eWrap i ∘ (gComposite 20 p2 p3 ∘ psi20)) v)
    (u : Fin 21 → ℝ) :
    monoSumSqGerm (fun d ↦ a (sigP7.symm d)) (Z.image sigP7) u
      ≤ sumSqFam (fun i ↦ coreGen dvec eWrap i ∘
          (gComposite 7 (sigP7 p2) (sigP7 p3) ∘ conjChart sigP7 psi20)) u := by
  have hchart : (gComposite 7 (sigP7 p2) (sigP7 p3) ∘ conjChart sigP7 psi20)
      = conjChart sigP7 (gComposite 20 p2 p3 ∘ psi20) := by rw [gComposite_conj_P7, conjChart_comp]
  have hval : sumSqFam (fun i ↦ coreGen dvec eWrap i ∘
        (gComposite 7 (sigP7 p2) (sigP7 p3) ∘ conjChart sigP7 psi20)) u
      = sumSqFam (fun i ↦ coreGen dvec eWrap i ∘ conjChart sigP7 (gComposite 20 p2 p3 ∘ psi20)) u :=
    congrArg (fun c ↦ sumSqFam (fun i ↦ coreGen dvec eWrap i ∘ c) u) hchart
  exact le_of_le_of_eq
    (domination_transport sigP7 rfl loss_symm_P7 (gComposite 20 p2 p3 ∘ psi20) a Z hbase u) hval.symm

-- Forced axiom gate: the transport deliverables rest only on `[propext, Classical.choice,
-- Quot.sound]` (no `sorryAx`, no cite). Force-elaborates the whole σ_p1-transport chain.
#assert_banked_clean_batch [loss_symm_P0, loss_symm_P1, loss_symm_P2, loss_symm_P3, loss_symm_P4,
  loss_symm_P5, loss_symm_P6, loss_symm_P7, monoSumSqGerm_conj, sumSqFam_coreGen_conj,
  domination_transport, nativeChart1_conj_P0, nativeChart1_conj_P7, gComposite_conj_P0,
  gComposite_conj_P7, leaf_domination_P0, leaf_domination_P4, leaf_domination_P7]

end DLNFibre.DLN.Aoyagi.OverVanishTransport334
