import DLNFibre.Core.Setup
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-!
# `DLNFibre.Core.Submult` — interval sub-products and the matrix-side rank pattern

The matrix-side rank-pattern object of Le Halleur–Rimányi 2024 (§3): for a composable tuple
`A : Tuple d` and indices `i ≤ j` in `Fin (N+1)`, the **interval sub-product**
`submult d A i j = A_j ⋯ A_{i+1} : Matrix (Fin (d j)) (Fin (d i)) k` (the empty product at `i = j`
is the identity `1 : Matrix (Fin (d i)) (Fin (d i))`). It generalises `Setup.multPrefix`, which is
the `i = 0` slice; the bridge `mult d A = submult d A 0 (Fin.last N)` recovers the full product.
`rankPattern d A i j = (submult d A i j).rank` is the paper's `r_{ij}` (for `i < j`), with
`r_{ii} = d_i` the rank of the identity.

**Encoding (absolute-upper `Nat.leRec` route).** `submult` is a product of consecutive factors with
a *variable* lower bound `i`, whose return type `Matrix (Fin (d j)) (Fin (d i)) k` depends on both
ends. Recursing from the variable base `i` (as `multPrefix` recurses from the fixed base `0`) would
naively force a dependent cast at the base. We avoid it by recursing on the *upper* index over `ℕ`
with `Nat.leRec` from `i.val ≤ j.val`, holding `i` fixed, with the **function-valued motive**
`m ↦ (m < N+1) → Matrix (Fin (d ⟨m,_⟩)) (Fin (d i)) k` carrying the `< N+1` bound that indexes `d`.
The base `m = i.val` is the identity (its endpoint `d ⟨i.val,_⟩` is `d i` by proof irrelevance on
the `Fin`), and the step prepends `A_m` on the left. **No shifted tuple, no per-factor reindex, and
no cast in any statement:** `submult_self`/`submult_succ`/`submult_zero` close by `Nat.leRec`'s own
reduction lemmas. The step lemma `submult_succ` is the genuine `multPrefix_succ` analogue this
encoding affords.

**Typeclass.** `CommRing k`, matching `Setup`; the diagonal-rank fact additionally needs
`Nontrivial k` (it is `Matrix.rank_one`). **Dependency rule:** never import `DLNFibre.DLN`.
-/

namespace DLNFibre.Core

open Matrix

universe u

variable {k : Type u} [CommRing k] {N : ℕ}

/-- The left-multiply step of `submult`: prepend `A_m` to the sub-product reaching height `m`. Named
so the `Nat.leRec` reduction lemmas (`Nat.leRec_self`, `Nat.leRec_succ`) have a stable term. -/
def submultStep (d : Fin (N + 1) → ℕ) (A : Tuple (k := k) d) (i : Fin (N + 1)) :
    ⦃m : ℕ⦄ → (i ≤ m) → ((hm : m < N + 1) → Matrix (Fin (d ⟨m, hm⟩)) (Fin (d i)) k) →
      ((hm : m + 1 < N + 1) → Matrix (Fin (d ⟨m + 1, hm⟩)) (Fin (d i)) k) :=
  fun {m} _ rec hm ↦
    let p : Fin N := ⟨m, Nat.lt_of_succ_lt_succ hm⟩
    show Matrix (Fin (d p.succ)) (Fin (d i)) k from
      A p * (show Matrix (Fin (d p.castSucc)) (Fin (d i)) k from rec p.castSucc.isLt)

/-- The interval sub-product `submult d A i j = A_j ⋯ A_{i+1} : Matrix (Fin (d j)) (Fin (d i)) k`
for `i ≤ j`, empty (the identity) at `i = j`. The `i = 0` slice is `Setup.multPrefix`. -/
def submult (d : Fin (N + 1) → ℕ) (A : Tuple (k := k) d) (i j : Fin (N + 1)) (hij : i ≤ j) :
    Matrix (Fin (d j)) (Fin (d i)) k :=
  Nat.leRec (motive := fun m _ ↦ (hm : m < N + 1) → Matrix (Fin (d ⟨m, hm⟩)) (Fin (d i)) k)
    (fun _ ↦ 1) (submultStep d A i) hij j.isLt

/-- The diagonal sub-product is the identity on `Fin (d i)` (the empty product). -/
theorem submult_self (d : Fin (N + 1) → ℕ) (A : Tuple (k := k) d) (i : Fin (N + 1)) :
    submult d A i i le_rfl = 1 := by
  unfold submult
  exact congrFun (Nat.leRec_self (motive := fun m _ ↦ (hm : m < N + 1) →
    Matrix (Fin (d ⟨m, hm⟩)) (Fin (d i)) k) (fun _ ↦ 1) (submultStep d A i)) i.isLt

/-- **Composition step** (the `multPrefix_succ` analogue): the sub-product to `p.succ` gains its top
factor on the left, `submult d A i p.succ = A p * submult d A i p.castSucc`. -/
theorem submult_succ (d : Fin (N + 1) → ℕ) (A : Tuple (k := k) d) (i : Fin (N + 1)) (p : Fin N)
    (h : i ≤ p.castSucc) :
    submult d A i p.succ (h.trans (Fin.castSucc_le_succ p)) = A p * submult d A i p.castSucc h := by
  unfold submult
  exact congrFun (Nat.leRec_succ (h1 := Fin.val_fin_le.mpr h)
    (h2 := Fin.val_fin_le.mpr (h.trans (Fin.castSucc_le_succ p)))
    (refl := fun _ ↦ 1) (le_succ_of_le := submultStep d A i)) p.succ.isLt

/-! ## The bridge to `mult`

The `i = 0` sub-product is exactly `Setup.multPrefix`, so the full product is its top slice. Both
proofs run by `Fin.induction` on the upper index through `submult_succ`. -/

/-- The `i = 0` sub-product is the prefix product: `submult d A 0 j = multPrefix d A j`. -/
theorem submult_zero (d : Fin (N + 1) → ℕ) (A : Tuple (k := k) d) (j : Fin (N + 1)) :
    submult d A 0 j (Fin.zero_le j) = multPrefix d A j := by
  induction j using Fin.induction with
  | zero => rw [submult_self, multPrefix_zero]
  | succ p ih => rw [submult_succ d A 0 p (Fin.zero_le _), multPrefix_succ, ih]

/-- **Bridge.** The full multiplication map is the `i = 0` sub-product to the last index:
`mult d A = submult d A 0 (Fin.last N)`. -/
theorem mult_eq_submult (d : Fin (N + 1) → ℕ) (A : Tuple (k := k) d) :
    mult d A = submult d A 0 (Fin.last N) (Fin.zero_le _) := by
  rw [mult, submult_zero]

/-! ## The rank pattern `r_{ij}` -/

/-- `rankPattern d A i j = (submult d A i j).rank` — the paper's `r_{ij}` for `i < j`; on the
diagonal `r_{ii} = d_i`. -/
noncomputable def rankPattern (d : Fin (N + 1) → ℕ) (A : Tuple (k := k) d) (i j : Fin (N + 1))
    (hij : i ≤ j) : ℕ :=
  (submult d A i j hij).rank

/-- **Diagonal rank.** `r_{ii} = d_i` (rank of the identity on `Fin (d i)`), `k` nontrivial. -/
theorem rankPattern_self [Nontrivial k] (d : Fin (N + 1) → ℕ) (A : Tuple (k := k) d)
    (i : Fin (N + 1)) : rankPattern d A i i le_rfl = d i := by
  rw [rankPattern, submult_self, Matrix.rank_one, Fintype.card_fin]

section Witness

/-! ## Non-vacuity witness

`N = 2`, dimension vector `(2, 2, 2)`, over `ℤ`, on `Setup.tupleWitness` (`A₁ = [[1,2],[0,1]]`,
`A₂ = [[1,0],[3,1]]`). The sub-products are `submult 0 0 = submult 1 1 = submult 2 2 = 1`,
`submult 0 1 = A₁`, `submult 1 2 = A₂`, and `submult 0 2 = A₂ A₁ = [[1,2],[3,7]] = mult`. Ranks
are `r_{00}=r_{11}=r_{22}=2`, `r_{01}=r_{12}=r_{02}=2` (all full rank here), and the bridge
`mult = submult 0 (last)` holds definitionally on the witness. -/

/-- `submult 0 1` on the witness is the first factor `A₁ = [[1,2],[0,1]]` (via the `multPrefix`
bridge `submult_zero`). -/
example : submult dWitness tupleWitness 0 1 (Fin.zero_le _) = !![1, 2; 0, 1] := by
  rw [submult_zero]; unfold multPrefix tupleWitness dWitness; decide

/-- `submult 1 2` on the witness is the second factor `A₂ = [[1,0],[3,1]]` — a genuine `i ≠ 0`
slice, via the composition step `submult_succ` and the diagonal `submult_self` (here
`2 = Fin.succ 1` and `1 = Fin.castSucc 1` definitionally). -/
example : submult dWitness tupleWitness 1 (Fin.succ 1) (by decide) = !![1, 0; 3, 1] := by
  rw [submult_succ dWitness tupleWitness 1 1 le_rfl,
    show submult dWitness tupleWitness 1 (Fin.castSucc 1) le_rfl
      = submult dWitness tupleWitness 1 1 le_rfl from rfl, submult_self]
  unfold tupleWitness dWitness
  decide

/-- `submult 0 2 = A₂ A₁ = [[1,2],[3,7]]`, matching `mult` (via the `multPrefix` bridge). -/
example : submult dWitness tupleWitness 0 2 (Fin.zero_le _) = !![1, 2; 3, 7] := by
  rw [submult_zero]; unfold multPrefix tupleWitness dWitness; decide

/-- The bridge holds on the witness: `mult = submult 0 (last 2)`. -/
example : mult dWitness tupleWitness
    = submult dWitness tupleWitness 0 (Fin.last 2) (Fin.zero_le _) :=
  mult_eq_submult dWitness tupleWitness

/-- The diagonal rank recovers the dimension vector: `r_{ii} = d_i = 2` at every `i`. -/
example : rankPattern dWitness tupleWitness 0 0 le_rfl = 2
    ∧ rankPattern dWitness tupleWitness 1 1 le_rfl = 2
    ∧ rankPattern dWitness tupleWitness 2 2 le_rfl = 2 :=
  ⟨rankPattern_self dWitness tupleWitness 0, rankPattern_self dWitness tupleWitness 1,
    rankPattern_self dWitness tupleWitness 2⟩

/-- The off-diagonal rank `r_{02} = rank (A₂ A₁) = rank [[1,2],[3,7]] = 2` (full rank on this
witness, since the product has determinant `1`, hence is a unit over `ℤ`). -/
example : rankPattern dWitness tupleWitness 0 2 (Fin.zero_le _) = 2 := by
  have hsub : submult dWitness tupleWitness 0 2 (Fin.zero_le _) = !![1, 2; 3, 7] := by
    rw [submult_zero]; unfold multPrefix tupleWitness dWitness; decide
  have hunit : IsUnit (!![1, 2; 3, 7] : Matrix (Fin 2) (Fin 2) ℤ) := by
    rw [Matrix.isUnit_iff_isUnit_det,
      show (!![1, 2; 3, 7] : Matrix (Fin 2) (Fin 2) ℤ).det = 1 by decide]
    exact isUnit_one
  have hrank : (!![1, 2; 3, 7] : Matrix (Fin 2) (Fin 2) ℤ).rank = 2 := by
    rw [Matrix.rank_of_isUnit _ hunit, Fintype.card_fin]
  rw [rankPattern, hsub]; exact hrank

end Witness

end DLNFibre.Core
