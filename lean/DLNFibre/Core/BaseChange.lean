import DLNFibre.Core.Submult

/-!
# `DLNFibre.Core.BaseChange` — the `G_d` base-change action and rank-pattern invariance

The change-of-basis action of Le Halleur–Rimányi 2024 (§2.2): the group
`G_d = ∏_{v} GL_{d_v}` acts on `Tuple d` by conjugating each edge map by the units at its two
endpoints. For `P : ∀ v, GL_{d_v}` (units = invertible matrices) the action is
`(P • A)_i = P_{i+1} · A_i · P_i⁻¹` — the target-vertex unit `P i.succ` on the left, the
source-vertex unit inverse `(P i.castSucc)⁻¹` on the right.

**Headlines.**
- `submult_baseChange` / `submult_smul` — **telescoping conjugation** of the interval sub-product:
  `submult (P • A) i j = P_j · (submult A i j) · P_i⁻¹`. The inner units cancel along the product
  (`… P_t⁻¹ P_t …`), so only the two boundary units survive; proved by induction mirroring
  `submult_succ`.
- `rankPattern_baseChange` / `rankPattern_smul` — **rank-pattern base-change invariance**:
  `rankPattern (P • A) i j = rankPattern A i j`. A unit matrix has invertible determinant
  (`Matrix.isUnits_det_units`), and multiplying by such a matrix preserves rank
  (`Matrix.rank_mul_eq_left_of_isUnit_det` / `…_right_…`), so the boundary conjugation drops out.

This is the orbit-side input to Prop 3.1b (the rank pattern is a base-change invariant): two tuples
in the same `G_d`-orbit have the same rank pattern.

**Typeclass.** `CommRing k` throughout — the two rank levers
`Matrix.rank_mul_eq_left_of_isUnit_det` / `…_right_…` are stated over a `CommRing` (no `Field`
needed). The non-vacuity witness additionally uses `Nontrivial ℤ` only through `Matrix.rank_of_isUnit`.
**Dependency rule:** never import `DLNFibre.DLN`.
-/

namespace DLNFibre.Core

open Matrix

universe u

variable {k : Type u} [CommRing k] {N : ℕ}

/-- `G_d = ∏_v GL_{d_v}`: a base-change datum is one invertible matrix per vertex (a unit of the
square matrix ring = an element of `GL_{d_v}`). -/
abbrev BaseChangeGroup (d : Fin (N + 1) → ℕ) : Type u :=
  ∀ v : Fin (N + 1), (Matrix (Fin (d v)) (Fin (d v)) k)ˣ

variable {d : Fin (N + 1) → ℕ}

/-- The `G_d` base-change action on `Tuple d`: on edge `i`, conjugate `A i` by the target-vertex
unit `P i.succ` on the left and the source-vertex unit inverse `(P i.castSucc)⁻¹` on the right. -/
def baseChange (P : BaseChangeGroup (k := k) d) (A : Tuple (k := k) d) : Tuple (k := k) d :=
  fun i ↦ ↑(P i.succ) * A i * ↑((P i.castSucc)⁻¹)

/-- The defining formula of the action, edge by edge. -/
@[simp] theorem baseChange_apply (P : BaseChangeGroup (k := k) d) (A : Tuple (k := k) d)
    (i : Fin N) : baseChange P A i = ↑(P i.succ) * A i * ↑((P i.castSucc)⁻¹) := rfl

/-- The identity base change fixes every tuple. -/
theorem baseChange_one (A : Tuple (k := k) d) :
    baseChange (1 : BaseChangeGroup (k := k) d) A = A := by
  funext i
  simp only [baseChange_apply, Pi.one_apply, Units.val_one, inv_one, Matrix.one_mul, Matrix.mul_one]

/-- Base change is compatible with multiplication in `G_d`: `(P * Q) • A = P • (Q • A)`. -/
theorem baseChange_mul (P Q : BaseChangeGroup (k := k) d) (A : Tuple (k := k) d) :
    baseChange (P * Q) A = baseChange P (baseChange Q A) := by
  funext i
  simp only [baseChange_apply, Pi.mul_apply, Units.val_mul, mul_inv_rev, Matrix.mul_assoc]

/-- The base change is a genuine group action of `G_d = ∏_v GL_{d_v}` on `Tuple d`. -/
instance : MulAction (BaseChangeGroup (k := k) d) (Tuple (k := k) d) where
  smul := baseChange
  one_smul := baseChange_one
  mul_smul := baseChange_mul

/-- `•` is the base-change action (definitional). -/
@[simp] theorem smul_eq_baseChange (P : BaseChangeGroup (k := k) d) (A : Tuple (k := k) d) :
    P • A = baseChange P A := rfl

/-! ## Telescoping conjugation of the sub-product -/

/-- **Telescoping conjugation.** The interval sub-product of a base-changed tuple is the sub-product
conjugated by the two boundary units: `submult (P • A) i j = P_j · (submult A i j) · P_i⁻¹`. The
inner units cancel (`P_t⁻¹ P_t = 1`); proved by induction on the upper index mirroring
`submult_succ`. -/
theorem submult_baseChange (P : BaseChangeGroup (k := k) d) (A : Tuple (k := k) d)
    (i j : Fin (N + 1)) (hij : i ≤ j) :
    submult d (baseChange P A) i j hij
      = (P j : Matrix (Fin (d j)) (Fin (d j)) k) * submult d A i j hij
          * ((P i)⁻¹ : Matrix (Fin (d i)) (Fin (d i)) k) := by
  revert hij
  induction j using Fin.induction with
  | zero =>
    intro hij
    obtain rfl := Fin.le_zero_iff.mp hij
    simp only [submult_self]
    rw [Matrix.mul_one, Units.mul_inv]
  | succ p ih =>
    intro hij
    rcases eq_or_lt_of_le hij with rfl | hlt
    · -- diagonal `i = p.succ`: the empty sub-product, boundary units cancel
      simp only [submult_self]
      rw [Matrix.mul_one, Units.mul_inv]
    · -- active edge `i ≤ p.castSucc`: peel the top factor and cancel the inner units
      have hcast : i ≤ p.castSucc := Fin.le_castSucc_iff.mpr hlt
      rw [submult_succ d (baseChange P A) i p hcast, ih hcast, submult_succ d A i p hcast]
      simp only [baseChange_apply, Matrix.mul_assoc]
      rw [← Matrix.mul_assoc ((P p.castSucc)⁻¹ : Matrix (Fin (d p.castSucc)) (Fin (d p.castSucc)) k)
            (P p.castSucc : Matrix (Fin (d p.castSucc)) (Fin (d p.castSucc)) k),
          Units.inv_mul, Matrix.one_mul]

/-- Telescoping conjugation, in `•` notation. -/
theorem submult_smul (P : BaseChangeGroup (k := k) d) (A : Tuple (k := k) d)
    (i j : Fin (N + 1)) (hij : i ≤ j) :
    submult d (P • A) i j hij
      = (P j : Matrix (Fin (d j)) (Fin (d j)) k) * submult d A i j hij
          * ((P i)⁻¹ : Matrix (Fin (d i)) (Fin (d i)) k) :=
  submult_baseChange P A i j hij

/-! ## Rank-pattern base-change invariance -/

/-- **Rank-pattern base-change invariance.** Conjugating by units does not change rank, so the rank
pattern is constant on `G_d`-orbits: `rankPattern (P • A) i j = rankPattern A i j`. (Orbit-side input
to Prop 3.1b.) -/
theorem rankPattern_baseChange (P : BaseChangeGroup (k := k) d) (A : Tuple (k := k) d)
    (i j : Fin (N + 1)) (hij : i ≤ j) :
    rankPattern d (baseChange P A) i j hij = rankPattern d A i j hij := by
  rw [rankPattern, rankPattern, submult_baseChange,
    Matrix.rank_mul_eq_left_of_isUnit_det _ _ (Matrix.isUnits_det_units _),
    Matrix.rank_mul_eq_right_of_isUnit_det _ _ (Matrix.isUnits_det_units _)]

/-- Rank-pattern base-change invariance, in `•` notation. -/
theorem rankPattern_smul (P : BaseChangeGroup (k := k) d) (A : Tuple (k := k) d)
    (i j : Fin (N + 1)) (hij : i ≤ j) :
    rankPattern d (P • A) i j hij = rankPattern d A i j hij :=
  rankPattern_baseChange P A i j hij

section Witness

/-! ## Non-vacuity witness

Conjugate the landed `(2,2,2)` witness `Setup.tupleWitness` by the `GL₂(ℤ)` element `!![1,1;0,1]`
(determinant `1`) at every vertex, and check the rank pattern is unchanged. The off-diagonal value
`r_{02} = rank(A₂A₁) = 2` survives the conjugation — the headline `rankPattern_smul` applied to a
genuine, non-identity base change of a concrete tuple. -/

/-- A concrete `GL₂(ℤ)` element, `!![1,1;0,1]` (determinant `1`), with explicit inverse `!![1,-1;0,1]`
(so the unit is computable: `val * inv = inv * val = 1` by `decide`). -/
def witnessUnit : (Matrix (Fin 2) (Fin 2) ℤ)ˣ where
  val := !![1, 1; 0, 1]
  inv := !![1, -1; 0, 1]
  val_inv := by decide
  inv_val := by decide

/-- Base-change the `(2,2,2)` witness by `witnessUnit` at every vertex. -/
def witnessBaseChange : BaseChangeGroup (k := ℤ) dWitness :=
  fun v ↦ match v with
    | 0 => witnessUnit
    | 1 => witnessUnit
    | 2 => witnessUnit

/-- The headline applies to a concrete non-identity base change: the rank pattern is unchanged at
every `(i, j)`. -/
example (i j : Fin 3) (hij : i ≤ j) :
    rankPattern dWitness (witnessBaseChange • tupleWitness) i j hij
      = rankPattern dWitness tupleWitness i j hij :=
  rankPattern_smul witnessBaseChange tupleWitness i j hij

/-- The off-diagonal product rank survives the base change: `r_{02} = rank(A₂A₁) = 2`. -/
example : rankPattern dWitness (witnessBaseChange • tupleWitness) 0 2 (Fin.zero_le _) = 2 := by
  rw [rankPattern_smul]
  have hsub : submult dWitness tupleWitness 0 2 (Fin.zero_le _) = !![1, 2; 3, 7] := by
    rw [submult_zero]; unfold multPrefix tupleWitness dWitness; decide
  have hunit : IsUnit (!![1, 2; 3, 7] : Matrix (Fin 2) (Fin 2) ℤ) := by
    rw [Matrix.isUnit_iff_isUnit_det,
      show (!![1, 2; 3, 7] : Matrix (Fin 2) (Fin 2) ℤ).det = 1 from by decide]
    exact isUnit_one
  rw [rankPattern, hsub, Matrix.rank_of_isUnit _ hunit, Fintype.card_fin]

end Witness

end DLNFibre.Core
