import DLNFibre.Core.Orbit
import Mathlib.Data.Setoid.Basic

/-!
# `DLNFibre.Core.OrbitKostant` — the orbit ↔ Kostant bijection as an `Equiv` (Cor 2.9)

The packaged bijection of Le Halleur–Rimányi 2024, Cor 2.9: the set of `G_d`-orbits of `Tuple d` is
in bijection with the **realizable rank patterns** of `d` (the rank patterns that arise from some
tuple), via `⟦A⟧ ↦ rankPattern A`.

* `orbitSetoid d` — the genuine `G_d`-orbit relation on `Tuple d`: `A ≈ B ↔ ∃ P, P • A = B`.
* `rankFn d A` — the rank pattern as a total `ℕ`-valued function (the complete invariant, with clean
  function equality); `rankFn A = rankFn B ↔ A, B in the same orbit` (`rankFn_eq_iff_orbit`).
* `RealizableRank d := Set.range (rankFn d)` — the realizable rank patterns of `d`.
* `orbitKostantEquiv d : Quotient (orbitSetoid d) ≃ RealizableRank d` — **the bijection**: orbits ↔
  realizable rank patterns. Injectivity is the complete invariant (`rankPattern_eq_iff_orbit`);
  surjectivity is built into the `Set.range` target (every realizable rank pattern is hit by its
  realizing tuple's orbit). Via `Setoid.quotientKerEquivRange` after identifying the orbit relation
  with `Setoid.ker (rankFn d)`.

Realizable rank patterns are identified with **Kostant partitions of `d`** by the inversion
`RankPattern.cumulDiffEquiv` (rank pattern `↔` multiplicity array `m̄ = diff r`); composing with it
turns the right side into the Kostant form. The realizing tuple of any rank pattern is the interval
direct sum `⊕ M^{m̄}` (`Orbit.baseChange_normalForm`).

**Typeclass.** `Field k`. **Dependency rule:** never import `DLNFibre.DLN`.
-/

namespace DLNFibre.Core

universe u

variable {k : Type u} [Field k] {N : ℕ}

/-! ## The rank pattern as a complete invariant with clean function equality -/

/-- The rank pattern of `A` as a **total** `ℕ`-valued function (`0` off the `i ≤ j` triangle). A
complete `G_d`-invariant whose equality is plain function equality. -/
noncomputable def rankFn (d : Fin (N + 1) → ℕ) (A : Tuple (k := k) d) :
    Fin (N + 1) → Fin (N + 1) → ℕ :=
  fun i j ↦ if h : i ≤ j then rankPattern d A i j h else 0

/-- **`rankFn` is a complete invariant.** `rankFn A = rankFn B` iff `A` and `B` lie in the same
`G_d`-orbit. Repackages `rankPattern_eq_iff_orbit` as an equality of total functions. -/
theorem rankFn_eq_iff_orbit {d : Fin (N + 1) → ℕ} (A B : Tuple (k := k) d) :
    rankFn d A = rankFn d B ↔ ∃ P : BaseChangeGroup (k := k) d, P • A = B := by
  rw [← rankPattern_eq_iff_orbit]
  constructor
  · intro h i j hij
    have hij' := congrFun (congrFun h i) j
    simpa only [rankFn, dif_pos hij] using hij'
  · intro h
    funext i j
    simp only [rankFn]
    split_ifs with hij
    · exact h i j hij
    · rfl

/-! ## The `G_d`-orbit relation and the bijection -/

/-- The `G_d`-orbit relation on `Tuple d`: `A ≈ B` iff `∃ P : G_d, P • A = B`. An equivalence (the
group acts), so a genuine `Setoid` whose quotient is the set of orbits. -/
def orbitSetoid (d : Fin (N + 1) → ℕ) : Setoid (Tuple (k := k) d) where
  r A B := ∃ P : BaseChangeGroup (k := k) d, P • A = B
  iseqv :=
    { refl := fun A ↦ ⟨1, one_smul _ A⟩
      symm := fun {A B} ⟨P, hP⟩ ↦ ⟨P⁻¹, by rw [← hP, ← mul_smul, inv_mul_cancel, one_smul]⟩
      trans := fun {A B C} ⟨P, hP⟩ ⟨Q, hQ⟩ ↦ ⟨Q * P, by rw [mul_smul, hP, hQ]⟩ }

/-- The realizable rank patterns of `d`: the total rank-pattern functions arising from some tuple.
The Kostant side of the bijection (identified with Kostant partitions by `cumulDiffEquiv`). -/
abbrev RealizableRank (d : Fin (N + 1) → ℕ) := ↥(Set.range (rankFn (k := k) d))

/-- **The orbit ↔ Kostant bijection (Le Halleur–Rimányi 2024, Cor 2.9).** The set of `G_d`-orbits of
`Tuple d` is in bijection with the realizable rank patterns of `d`, via `⟦A⟧ ↦ rankPattern A`.
Injectivity is the complete invariant `rankPattern_eq_iff_orbit`; surjectivity is the `Set.range`
target. Built by identifying the orbit relation with `Setoid.ker (rankFn d)` (the complete
invariant) and applying the first isomorphism theorem `Setoid.quotientKerEquivRange`. -/
noncomputable def orbitKostantEquiv (d : Fin (N + 1) → ℕ) :
    Quotient (orbitSetoid (k := k) d) ≃ RealizableRank (k := k) d :=
  (Quotient.congrRight (fun A B ↦ (rankFn_eq_iff_orbit A B).symm)).trans
    (Setoid.quotientKerEquivRange (rankFn d))

/-- The bijection sends the orbit of `A` to its rank pattern `rankFn A`. -/
@[simp] theorem orbitKostantEquiv_mk {d : Fin (N + 1) → ℕ} (A : Tuple (k := k) d) :
    ((orbitKostantEquiv d (Quotient.mk _ A) : RealizableRank (k := k) d)
      : Fin (N + 1) → Fin (N + 1) → ℕ) = rankFn d A := rfl

section Witness

/-! ## Non-vacuity witness

The bijection fires on the `(2,2,2)/ℚ` witness: the orbit of `tupleWitnessQ` maps to its rank
pattern. -/

/-- The bijection is non-vacuous: it sends `⟦tupleWitnessQ⟧` to `rankFn tupleWitnessQ`. -/
example :
    ((orbitKostantEquiv dWitness (Quotient.mk (orbitSetoid dWitness) tupleWitnessQ)
      : RealizableRank (k := ℚ) dWitness) : Fin 3 → Fin 3 → ℕ)
      = rankFn dWitness tupleWitnessQ := rfl

end Witness

end DLNFibre.Core
