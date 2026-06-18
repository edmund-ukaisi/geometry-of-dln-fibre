import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Order.Interval.Finset.Basic
import Mathlib.Data.Int.Interval
import Mathlib.Logic.Equiv.Basic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Ring

/-!
# `DLNFibre.Core.RankPattern` — the inclusion–exclusion inversion (Prop 3.1a)

The **abstract** inclusion–exclusion inversion underlying Le Halleur–Rimányi 2024, Prop 3.1
(`prop:mr_comparison`): the cumulative-sum map and the second finite-difference map on arrays
indexed by integer pairs are mutually inverse. This is pure combinatorics over an `AddCommGroup`;
`ℤ` is the intended instance.

Over an `AddCommGroup R`, arrays are total functions `ℤ → ℤ → R` and the paper's "out-of-range
index `= 0`" convention is realised by **support**: an array is `Supported N` when it vanishes
for `i < 0` and for `j > N` (the half-plane the difference map reaches off the edge — *not* the
square box, which neither map preserves; see the `Supported` section below). The two maps are

* `cumul N m i j = ∑_{k ≤ i, j ≤ l ≤ N} m k l` — the cumulative map `S`
  (the paper's `r_{ij} = ∑_{k≤i≤j≤l} m_{kl}`);
* `diff r i j = r_{ij} − r_{i,j+1} − r_{i−1,j} + r_{i−1,j+1}` — the finite-difference map `T`.

`cumul_diff` and `diff_cumul` are the two telescoping inversions; `cumulDiffEquiv` packages them
as an `Equiv` on `Supported` arrays. This is the *abstract* identity only: the statement that an
actual matrix tuple's rank pattern is `cumul` of its Gabriel multiplicities (Prop 3.1b) needs the
type-A Gabriel decomposition (rung 4) and is **out of scope** here.

**Encoding rationale.** Arrays are `ℤ → ℤ → R`, *not* `Fin (N+1) → Fin (N+1) → R`. The difference
map references `j+1` and `i−1`, which leave any `Fin` range; over `ℤ` the formula is a pure
pointwise combination needing no bounds bookkeeping, and the cumulative map is an honest finite
`Finset.Icc` sum. The "out of range `= 0`" convention is then exactly the support hypothesis. Both
maps are *decoupled* into independent row (`i`) and column (`j`) operators (`cumulRow`/`diffRow`,
`cumulCol`/`diffCol`), each a 1-D telescoping; the 2-D inversion is their composition, which keeps
every proof a one-line `Finset` insert/telescope. See the thread findings for the discarded
alternatives (guarded `Fin`, padded `Fin (N+2)`).

**Typeclass.** `AddCommGroup R` is the weakest class: `diff` needs subtraction and `cumul` needs
finite sums. **Dependency rule:** never import `DLNFibre.DLN`.
-/

namespace DLNFibre.Core

open Finset

universe u

variable {R : Type u} [AddCommGroup R]

/-! ## Interval-insertion lemmas over `ℤ`

Peel the top / bottom element off a closed integer interval; the engine of every telescope below. -/

/-- `Icc a i = insert i (Icc a (i-1))` when `a ≤ i`: peel the top element. -/
theorem Icc_insert_top (a i : ℤ) (hi : a ≤ i) :
    Finset.Icc a i = insert i (Finset.Icc a (i - 1)) := by
  ext x; simp only [Finset.mem_insert, Finset.mem_Icc]; omega

/-- `Icc j N = insert j (Icc (j+1) N)` when `j ≤ N`: peel the bottom element. -/
theorem Icc_insert_bot (j N : ℤ) (hj : j ≤ N) :
    Finset.Icc j N = insert j (Finset.Icc (j + 1) N) := by
  ext x; simp only [Finset.mem_insert, Finset.mem_Icc]; omega

/-! ## One-dimensional cumulative and difference operators

`cumulRow`/`diffRow` act in the row index `i` (cumulative for `k ≤ i`, difference
`r_{ij}-r_{i-1,j}`); `cumulCol`/`diffCol` act in the column index `j` (cumulative for `j ≤ l ≤ N`,
difference `r_{ij}-r_{i,j+1}`). Each `diff`/`cumul` pair is mutually inverse on supported arrays. -/

/-- Row cumulative `(cumulRow m)_{ij} = ∑_{0 ≤ k ≤ i} m_{kj}`. -/
noncomputable def cumulRow (m : ℤ → ℤ → R) (i j : ℤ) : R := ∑ k ∈ Finset.Icc 0 i, m k j

/-- Row difference `(diffRow r)_{ij} = r_{ij} − r_{i-1,j}`. -/
def diffRow (r : ℤ → ℤ → R) (i j : ℤ) : R := r i j - r (i - 1) j

/-- Column cumulative `(cumulCol N m)_{ij} = ∑_{j ≤ l ≤ N} m_{il}`. -/
noncomputable def cumulCol (N : ℤ) (m : ℤ → ℤ → R) (i j : ℤ) : R := ∑ l ∈ Finset.Icc j N, m i l

/-- Column difference `(diffCol r)_{ij} = r_{ij} − r_{i,j+1}`. -/
def diffCol (r : ℤ → ℤ → R) (i j : ℤ) : R := r i j - r i (j + 1)

/-- Row telescope: `diffRow` is a left inverse of `cumulRow` on arrays vanishing for `i < 0`. -/
theorem diffRow_cumulRow (m : ℤ → ℤ → R) (hm : ∀ i j, i < 0 → m i j = 0) (i j : ℤ) :
    diffRow (cumulRow m) i j = m i j := by
  unfold diffRow cumulRow
  rcases lt_or_ge i 0 with hi | hi
  · rw [Finset.Icc_eq_empty (by omega), Finset.Icc_eq_empty (by omega)]
    simp [hm i j hi]
  · rw [Icc_insert_top 0 i hi, Finset.sum_insert (by simp)]; abel

/-- Column telescope: `diffCol` is a left inverse of `cumulCol` on arrays vanishing for `j > N`. -/
theorem diffCol_cumulCol (N : ℤ) (m : ℤ → ℤ → R) (hm : ∀ i j, N < j → m i j = 0) (i j : ℤ) :
    diffCol (cumulCol N m) i j = m i j := by
  unfold diffCol cumulCol
  rcases le_or_gt j N with hj | hj
  · rw [Icc_insert_bot j N hj, Finset.sum_insert (by simp)]; abel
  · rw [Finset.Icc_eq_empty (by omega), Finset.Icc_eq_empty (by omega)]
    simp [hm i j hj]

/-- Summing a row difference telescopes: `∑_{0 ≤ k ≤ i} (diffRow g)_{kj} = g_{ij} − g_{-1,j}`,
for `0 ≤ i`. -/
theorem sum_Icc_diffRow (g : ℤ → ℤ → R) (j : ℤ) {i : ℤ} (hi : 0 ≤ i) :
    ∑ k ∈ Finset.Icc 0 i, diffRow g k j = g i j - g (-1) j := by
  unfold diffRow
  induction i using Int.induction_on with
  | zero => simp
  | succ n ih =>
    rw [Icc_insert_top 0 (n + 1) (by omega), Finset.sum_insert (by simp)]
    by_cases hn : 0 ≤ (n : ℤ)
    · rw [show ((n : ℤ) + 1 - 1) = (n : ℤ) by ring, ih hn]; abel
    · exact absurd (Int.natCast_nonneg n) hn
  | pred n _ => omega

/-- Summing a column difference telescopes: `∑_{j ≤ l ≤ N} (diffCol g)_{il} = g_{ij} − g_{i,N+1}`,
for `j ≤ N`. -/
theorem sum_Icc_diffCol (g : ℤ → ℤ → R) (N i : ℤ) {j : ℤ} (hj : j ≤ N) :
    ∑ l ∈ Finset.Icc j N, diffCol g i l = g i j - g i (N + 1) := by
  obtain ⟨n, rfl⟩ : ∃ n : ℕ, j = N - n := ⟨(N - j).toNat, by omega⟩
  induction n with
  | zero =>
    simp only [Nat.cast_zero, sub_zero]
    rw [Finset.Icc_self, Finset.sum_singleton]; unfold diffCol; rfl
  | succ k ih =>
    rw [show (N - (↑(k + 1) : ℤ)) = (N - k) - 1 by push_cast; ring]
    rw [Icc_insert_bot ((N - k) - 1) N (by omega), Finset.sum_insert (by simp)]
    rw [show ((N - k) - 1 + 1) = N - (k : ℤ) by ring, ih (by omega)]
    unfold diffCol; abel

/-- Row telescope (reverse): `cumulRow` is a left inverse of `diffRow` on arrays vanishing
for `i < 0`. -/
theorem cumulRow_diffRow (r : ℤ → ℤ → R) (hr : ∀ i j, i < 0 → r i j = 0) (i j : ℤ) :
    cumulRow (diffRow r) i j = r i j := by
  unfold cumulRow
  rcases lt_or_ge i 0 with hi | hi
  · rw [Finset.Icc_eq_empty (by omega)]; simp [hr i j hi]
  · rw [sum_Icc_diffRow r j hi, hr (-1) j (by omega), sub_zero]

/-- Column telescope (reverse): `cumulCol` is a left inverse of `diffCol` on arrays vanishing
for `j > N`. -/
theorem cumulCol_diffCol (N : ℤ) (r : ℤ → ℤ → R) (hr : ∀ i j, N < j → r i j = 0) (i j : ℤ) :
    cumulCol N (diffCol r) i j = r i j := by
  unfold cumulCol
  rcases le_or_gt j N with hj | hj
  · rw [sum_Icc_diffCol r N i hj, hr i (N + 1) (by omega), sub_zero]
  · rw [Finset.Icc_eq_empty (by omega)]; simp [hr i j hj]

/-! ## Commutations

The row and column operators act on independent indices, so each row operator commutes with each
column operator (both are `Finset.sum`/subtraction in the *other* index). -/

/-- `diffCol` commutes with `cumulRow` (they touch disjoint indices). -/
theorem diffCol_cumulRow (m : ℤ → ℤ → R) : diffCol (cumulRow m) = cumulRow (diffCol m) := by
  funext i j; unfold diffCol cumulRow; rw [← Finset.sum_sub_distrib]

/-- `cumulCol` commutes with `diffRow` (they touch disjoint indices). -/
theorem cumulCol_diffRow (N : ℤ) (m : ℤ → ℤ → R) :
    cumulCol N (diffRow m) = diffRow (cumulCol N m) := by
  funext i j; unfold cumulCol diffRow; rw [← Finset.sum_sub_distrib]

/-! ## The two-dimensional maps `S` (cumulative) and `T` (finite difference) -/

/-- The cumulative map `S`: `(cumul N m)_{ij} = ∑_{k ≤ i, j ≤ l ≤ N} m_{kl}` (sum over every box
interval `[k,l] ⊇ [i,j]`). Composition of the row and column cumulatives. -/
noncomputable def cumul (N : ℤ) (m : ℤ → ℤ → R) : ℤ → ℤ → R := cumulRow (cumulCol N m)

/-- The finite-difference map `T`: `(diff r)_{ij} = r_{ij} − r_{i,j+1} − r_{i-1,j} + r_{i-1,j+1}`,
with out-of-range indices `0`. Composition of the row and column differences. -/
def diff (r : ℤ → ℤ → R) : ℤ → ℤ → R := diffRow (diffCol r)

/-- `diff` unfolds to the four-term second difference. -/
theorem diff_apply (r : ℤ → ℤ → R) (i j : ℤ) :
    diff r i j = r i j - r i (j + 1) - r (i - 1) j + r (i - 1) (j + 1) := by
  unfold diff diffRow diffCol; abel

/-- `cumul` unfolds to the box double sum. -/
theorem cumul_apply (N : ℤ) (m : ℤ → ℤ → R) (i j : ℤ) :
    cumul N m i j = ∑ k ∈ Finset.Icc 0 i, ∑ l ∈ Finset.Icc j N, m k l := rfl

/-! ## Headline: the two maps are mutually inverse (Prop 3.1a) -/

/-- **Prop 3.1a, half 1.** The finite-difference map `T` is a left inverse of the cumulative map
`S`: `diff (cumul N m) = m` for every array `m` vanishing for `i < 0` and for `j > N`. -/
theorem diff_cumul (N : ℤ) (m : ℤ → ℤ → R)
    (hi : ∀ i j, i < 0 → m i j = 0) (hj : ∀ i j, N < j → m i j = 0) :
    diff (cumul N m) = m := by
  funext i j
  unfold diff cumul
  rw [diffCol_cumulRow]
  have hcol : diffCol (cumulCol N m) = m := by
    funext a b; exact diffCol_cumulCol N m hj a b
  rw [hcol]
  exact diffRow_cumulRow m hi i j

/-- **Prop 3.1a, half 2.** The cumulative map `S` is a left inverse of the finite-difference map
`T`: `cumul N (diff r) = r` for every array `r` vanishing for `i < 0` and for `j > N`. -/
theorem cumul_diff (N : ℤ) (r : ℤ → ℤ → R)
    (hi : ∀ i j, i < 0 → r i j = 0) (hj : ∀ i j, N < j → r i j = 0) :
    cumul N (diff r) = r := by
  funext i j
  unfold cumul diff
  -- cumulRow (cumulCol (diffRow (diffCol r))) → cumulRow (diffRow (cumulCol (diffCol r)))
  rw [cumulCol_diffRow N (diffCol r)]
  have hcol : cumulCol N (diffCol r) = r := by
    funext a b; exact cumulCol_diffCol N r hj a b
  rw [hcol]
  exact cumulRow_diffRow r hi i j

/-! ## The bijection, packaged as an `Equiv`

The "appropriate array space" is `Supported N R`: arrays vanishing for `i < 0` and for `j > N` (the
two index walls the difference map references off the edge — the realisation of the paper's "out of
range `= 0`"). This is the *exact* support `diff_cumul`/`cumul_diff` require, and it is **closed**
under both maps: `cumul` vanishes for `i < 0` (empty row `Icc`) and for `j > N` (empty column `Icc`)
*unconditionally*; `diff` inherits the vanishing because all four reference points keep an offending
index. The paper's finite arrays (supported on `0 ≤ i ≤ j ≤ N`) form a subset.

We do **not** use the square box `0 ≤ i,j ≤ N`: neither map preserves it (`cumul` saturates at
`i > N`, `diff` leaks to `i = N+1`), so the box is the wrong invariant for a guard-free `Equiv`. -/

/-- An array vanishes for `i < 0` and for `j > N` (the paper's "out of range `= 0`", as the two
walls the difference map reaches off the edge). -/
def Supported (N : ℤ) (f : ℤ → ℤ → R) : Prop :=
  (∀ i j, i < 0 → f i j = 0) ∧ (∀ i j, N < j → f i j = 0)

/-- The space of supported arrays — the domain of the inclusion–exclusion bijection. -/
def SuppArray (N : ℤ) (R : Type u) [AddCommGroup R] : Type u :=
  { f : ℤ → ℤ → R // Supported N f }

/-- `cumul N m` vanishes for `i < 0` and `j > N` (the row / column `Icc` is empty), so it is
supported for *any* `m`. -/
theorem supported_cumul (N : ℤ) (m : ℤ → ℤ → R) : Supported N (cumul N m) := by
  refine ⟨fun i j hi => ?_, fun i j hj => ?_⟩
  · rw [cumul_apply, Finset.Icc_eq_empty (by omega), Finset.sum_empty]
  · rw [cumul_apply]
    exact Finset.sum_eq_zero fun k _ => by rw [Finset.Icc_eq_empty (by omega), Finset.sum_empty]

/-- `diff` preserves support: each of the four reference points keeps an offending index. -/
theorem supported_diff {N : ℤ} {r : ℤ → ℤ → R} (hr : Supported N r) : Supported N (diff r) := by
  refine ⟨fun i j hi => ?_, fun i j hj => ?_⟩
  · rw [diff_apply, hr.1 i j hi, hr.1 i (j + 1) hi, hr.1 (i - 1) j (by omega),
      hr.1 (i - 1) (j + 1) (by omega)]; abel
  · rw [diff_apply, hr.2 i j hj, hr.2 i (j + 1) (by omega), hr.2 (i - 1) j hj,
      hr.2 (i - 1) (j + 1) (by omega)]; abel

/-- **Prop 3.1a (characterisation).** On supported arrays the cumulative map `S = cumul N` and the
finite-difference map `T = diff` are mutually inverse — the abstract form of the paper's
rank-pattern ↔ Kostant-partition bijection (no representation theory here). The tuple/Gabriel
direction — orbits ↔ Kostant partitions — is built on this in `Core.OrbitKostant`
(`orbitKostantPartitionEquiv`). -/
noncomputable def cumulDiffEquiv (N : ℤ) : SuppArray N R ≃ SuppArray N R where
  toFun m := ⟨cumul N m.1, supported_cumul N m.1⟩
  invFun r := ⟨diff r.1, supported_diff r.2⟩
  left_inv m := Subtype.ext (diff_cumul N m.1 m.2.1 m.2.2)
  right_inv r := Subtype.ext (cumul_diff N r.1 r.2.1 r.2.2)

section Witness

/-! ## Non-vacuity witness

`N = 2`, over `ℤ`. The Kostant partition `m` with `m₀₀ = m₀₁ = m₁₂ = m₂₂ = 1` (the last of the six
partitions of `(2,2,2)` in the paper's example, upper triangular `[[1,1,0],[0,0,1],[0,0,1]]`) has
cumulative rank pattern `r = [[2,1,0],[·,2,1],[·,·,2]]` — diagonal `(d₀,d₁,d₂) = (2,2,2)`.
`cumul` computes these entries, and `diff` recovers `m`: the maps are not trivial. -/

/-- Witness Kostant partition for `(2,2,2)`: `m₀₀ = m₀₁ = m₁₂ = m₂₂ = 1`, else `0`. -/
def mWitness : ℤ → ℤ → ℤ := fun i j =>
  if i = 0 ∧ j = 0 then 1
  else if i = 0 ∧ j = 1 then 1
  else if i = 1 ∧ j = 2 then 1
  else if i = 2 ∧ j = 2 then 1
  else 0

/-- The witness partition is supported (vanishes for `i < 0` and for `j > 2`). -/
theorem supported_mWitness : Supported 2 mWitness := by
  refine ⟨fun i j hi => ?_, fun i j hj => ?_⟩ <;>
    · unfold mWitness; split_ifs with h₁ h₂ h₃ h₄ <;> omega

/-- `cumul` computes the rank pattern: the diagonal recovers the dimension vector `(2,2,2)`. -/
example : cumul 2 mWitness 0 0 = 2 ∧ cumul 2 mWitness 1 1 = 2 ∧ cumul 2 mWitness 2 2 = 2 := by
  refine ⟨?_, ?_, ?_⟩ <;> · rw [cumul_apply]; unfold mWitness; decide

/-- `cumul` computes the off-diagonal rank pattern entries `r₀₁ = 1`, `r₀₂ = 0`, `r₁₂ = 1`. -/
example : cumul 2 mWitness 0 1 = 1 ∧ cumul 2 mWitness 0 2 = 0 ∧ cumul 2 mWitness 1 2 = 1 := by
  refine ⟨?_, ?_, ?_⟩ <;> · rw [cumul_apply]; unfold mWitness; decide

/-- The bijection round-trips on the witness: `diff (cumul 2 m) = m`, so the maps are inverse and
non-trivial. -/
example : diff (cumul 2 mWitness) = mWitness :=
  diff_cumul 2 mWitness supported_mWitness.1 supported_mWitness.2

/-- The packaged `Equiv` sends the witness partition to its rank pattern and back. -/
example : (cumulDiffEquiv 2 (R := ℤ)).symm ⟨cumul 2 mWitness, supported_cumul 2 mWitness⟩
    = ⟨mWitness, supported_mWitness⟩ :=
  Subtype.ext (diff_cumul 2 mWitness supported_mWitness.1 supported_mWitness.2)

end Witness

/-! ## The matrix-side rank-pattern objects (`submult` / `rankPattern`) — landed in `Submult.lean`

The matrix-side objects `submult d A i j = A_j ⋯ A_{i+1} : Matrix (Fin (d j)) (Fin (d i)) k`
(generalising `Setup.multPrefix`, the `i = 0` slice), the bridge `mult d A = submult d A 0 (last N)`,
and `rankPattern d A i j = (submult d A i j).rank` (with `r_{ii} = d_i`) are in
`DLNFibre.Core.Submult`. The variable-lower-bound dependent-cast obstacle this note once flagged was
sidestepped there by recursing on the *upper* index over `ℕ` via `Nat.leRec` with a function-valued
motive — a cast-free third route (neither the shifted-tail nor the `List.prod` options originally
proposed). The abstract inversion above does not depend on it. -/

end DLNFibre.Core
