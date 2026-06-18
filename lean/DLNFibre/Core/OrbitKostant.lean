import DLNFibre.Core.Orbit
import Mathlib.Data.Setoid.Basic
import Mathlib.Logic.Equiv.Set

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

Two forms of the bijection:

* `orbitKostantEquiv d : Quotient (orbitSetoid d) ≃ RealizableRank d` — orbits ↔ realizable **rank
  patterns** (the honest building block; `⟦A⟧ ↦ rankFn A`).
* `orbitKostantPartitionEquiv d : Quotient (orbitSetoid d) ≃ RealizableKostant d` — the **literal**
  Cor 2.9: orbits ↔ realizable **Kostant partitions** (multiplicity arrays). It composes
  `orbitKostantEquiv` with the abstract inversion `RankPattern.cumulDiffEquiv.symm = diff`, after
  embedding the `ℕ`-valued `Fin`-indexed rank pattern into the `ℤ`-indexed supported-array shape
  (`embedRank`). The codomain element `⟦A⟧ ↦ diff (rankFn A)` is the genuine Kostant partition on
  the support `i ≤ j`; below the diagonal it carries `rankFn`-convention artifacts (the bijection is
  exact regardless). The realizing tuple of any rank pattern is the interval direct sum `⊕ M^{m̄}`
  (`Orbit.baseChange_normalForm`).

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

/-! ## The literal Kostant codomain: one inversion further (Cor 2.9)

`orbitKostantEquiv` lands in **rank patterns**; the paper's Cor 2.9 phrases the bijection against
**Kostant partitions** — the multiplicity arrays `m̄ = diff r`. Composing with the abstract
inversion `RankPattern.cumulDiffEquiv` (whose `.symm` is `diff`) closes that last step. The bridge
is `embedRank`: a finite `ℕ`-valued rank pattern `Fin (N+1) → Fin (N+1) → ℕ` cast into the
`ℤ`-indexed `ℤ`-valued supported-array shape `cumulDiffEquiv` operates on (zero outside the square
`[0,N]²`, so `Supported` holds by the guard, for free). -/

/-- An integer index lies in the `Fin (N+1)` range `0 ≤ i ≤ N` (decidable, for the guard `if`). -/
abbrev InFinRange (N : ℕ) (i : ℤ) : Prop := 0 ≤ i ∧ i ≤ (N : ℤ)

/-- The `Fin (N+1)` element named by an in-range integer. -/
def finOfInt {N : ℕ} (i : ℤ) (hi : InFinRange N i) : Fin (N + 1) :=
  ⟨i.toNat, by
    have hcast : (i.toNat : ℤ) = i := Int.toNat_of_nonneg hi.1
    have hle : i.toNat ≤ N := Int.ofNat_le.mp (by simpa [hcast] using hi.2)
    exact Nat.lt_succ_of_le hle⟩

/-- `finOfInt (i : ℤ) _ = i` for `i : Fin (N+1)`: the embedding recovers the original index. -/
theorem finOfInt_coe {N : ℕ} (i : Fin (N + 1)) (hi : InFinRange N (i : ℤ)) :
    finOfInt (i : ℤ) hi = i := by
  apply Fin.ext
  simp [finOfInt, Int.toNat_natCast]

/-- Embed a finite total rank pattern into the supported-array shape `cumulDiffEquiv` acts on:
cast `ℕ → ℤ`, extend the `Fin (N+1)` index to all of `ℤ` by `0` outside the square `[0,N]²`. -/
def embedRank {N : ℕ} (r : Fin (N + 1) → Fin (N + 1) → ℕ) : SuppArray (N : ℤ) ℤ :=
  ⟨fun i j ↦
      if hi : InFinRange N i then
        if hj : InFinRange N j then (r (finOfInt i hi) (finOfInt j hj) : ℤ) else 0
      else 0,
    by
      refine ⟨fun i j hi => ?_, fun i j hj => ?_⟩
      · simp [InFinRange, not_le_of_gt hi]
      · by_cases hi : InFinRange N i
        · simp [InFinRange, hi, not_le_of_gt hj]
        · simp [hi]⟩

/-- `embedRank` reads back the original entry at in-range integer indices. -/
@[simp] theorem embedRank_apply_fin {N : ℕ} (r : Fin (N + 1) → Fin (N + 1) → ℕ)
    (i j : Fin (N + 1)) :
    (embedRank r).1 (i : ℤ) (j : ℤ) = (r i j : ℤ) := by
  have hi : InFinRange N (i : ℤ) :=
    ⟨Int.natCast_nonneg _, by exact_mod_cast Nat.lt_succ_iff.mp i.isLt⟩
  have hj : InFinRange N (j : ℤ) :=
    ⟨Int.natCast_nonneg _, by exact_mod_cast Nat.lt_succ_iff.mp j.isLt⟩
  simp only [embedRank, dif_pos hi, dif_pos hj, finOfInt_coe i hi, finOfInt_coe j hj]

/-- `embedRank` is injective: distinct rank patterns embed to distinct arrays. -/
theorem embedRank_injective {N : ℕ} : Function.Injective (embedRank (N := N)) := by
  intro r s h
  funext i j
  have hij := congrFun (congrFun (congrArg Subtype.val h) (i : ℤ)) (j : ℤ)
  rw [embedRank_apply_fin, embedRank_apply_fin] at hij
  exact_mod_cast hij

/-- The **Kostant multiplicity array** `m̄ = diff r` of a rank pattern, via the abstract inversion
`cumulDiffEquiv.symm`. On the support `i ≤ j` (where Kostant partitions live) this is the paper's
interval-multiplicity partition; below the diagonal it carries `rankFn`-convention artifacts (see
the witness). -/
noncomputable def kostantArrayOfRank {N : ℕ} (r : Fin (N + 1) → Fin (N + 1) → ℕ) :
    SuppArray (N : ℤ) ℤ :=
  (cumulDiffEquiv (R := ℤ) (N := (N : ℤ))).symm (embedRank r)

/-- `kostantArrayOfRank r` is literally the second finite difference of the embedded pattern. -/
@[simp] theorem kostantArrayOfRank_val {N : ℕ} (r : Fin (N + 1) → Fin (N + 1) → ℕ) :
    (kostantArrayOfRank r).1 = diff (embedRank r).1 := rfl

/-- `kostantArrayOfRank` is injective: it is `diff ∘ embedRank`, both injective (`diff` via
`cumulDiffEquiv`). The multiplicity array is therefore a complete invariant of the rank pattern. -/
theorem kostantArrayOfRank_injective {N : ℕ} :
    Function.Injective (kostantArrayOfRank (N := N)) := fun _ _ h =>
  embedRank_injective ((cumulDiffEquiv (R := ℤ) (N := (N : ℤ))).symm.injective h)

/-- The realizable Kostant partitions of `d`: the `diff`-image (multiplicity arrays) of the
realizable rank patterns. The literal Kostant codomain of Cor 2.9. -/
abbrev RealizableKostant (d : Fin (N + 1) → ℕ) :=
  ↥(kostantArrayOfRank (N := N) '' Set.range (rankFn (k := k) d))

/-- Realizable rank patterns ↔ realizable Kostant partitions, by the corestriction of `diff` (one
inversion further than `orbitKostantEquiv`). -/
noncomputable def rankKostantEquiv (d : Fin (N + 1) → ℕ) :
    RealizableRank (k := k) d ≃ RealizableKostant (k := k) d :=
  Equiv.Set.image (kostantArrayOfRank (N := N)) (Set.range (rankFn (k := k) d))
    (kostantArrayOfRank_injective (N := N))

/-- **The literal orbit ↔ Kostant-partition bijection (Le Halleur–Rimányi 2024, Cor 2.9).** The set
of `G_d`-orbits of `Tuple d` is in bijection with the realizable **Kostant partitions**
(multiplicity arrays) of `d`, via `⟦A⟧ ↦ diff (rankFn A)`. This is `orbitKostantEquiv` (orbits ↔
rank patterns) composed with `cumulDiffEquiv.symm` (rank patterns ↔ multiplicity arrays). The image
element is the genuine Kostant partition on the support `i ≤ j`; below the diagonal it carries
`rankFn`-convention artifacts (the bijection is exact regardless — see `kostantArrayOfRank`). -/
noncomputable def orbitKostantPartitionEquiv (d : Fin (N + 1) → ℕ) :
    Quotient (orbitSetoid (k := k) d) ≃ RealizableKostant (k := k) d :=
  (orbitKostantEquiv d).trans (rankKostantEquiv d)

/-- The literal bijection sends `⟦A⟧` to its Kostant multiplicity array `diff (rankFn A)`. -/
@[simp] theorem orbitKostantPartitionEquiv_mk {d : Fin (N + 1) → ℕ} (A : Tuple (k := k) d) :
    (orbitKostantPartitionEquiv d (Quotient.mk _ A) : RealizableKostant (k := k) d).1
      = kostantArrayOfRank (rankFn d A) := rfl

section Witness

/-! ## Non-vacuity witness

The bijection fires on the `(2,2,2)/ℚ` witness: the orbit of `tupleWitnessQ` maps to its rank
pattern. -/

/-- The bijection is non-vacuous: it sends `⟦tupleWitnessQ⟧` to `rankFn tupleWitnessQ`. -/
example :
    ((orbitKostantEquiv dWitness (Quotient.mk (orbitSetoid dWitness) tupleWitnessQ)
      : RealizableRank (k := ℚ) dWitness) : Fin 3 → Fin 3 → ℕ)
      = rankFn dWitness tupleWitnessQ := rfl

/-- The **literal** bijection is non-vacuous: it sends `⟦tupleWitnessQ⟧` to the Kostant multiplicity
array of its rank pattern. -/
example :
    (orbitKostantPartitionEquiv dWitness (Quotient.mk (orbitSetoid dWitness) tupleWitnessQ)
      : RealizableKostant (k := ℚ) dWitness).1
      = kostantArrayOfRank (rankFn dWitness tupleWitnessQ) := rfl

/-! ### Concrete multiplicity values

The paper's `(2,2,2)` rank pattern is `rWitness = [[2,1,0],[0,2,1],[0,0,2]]` (`rankFn`'s convention:
`r_{ij}` for `i ≤ j`, `0` below the diagonal). On the support `i ≤ j` — where Kostant partitions
live — `kostantArrayOfRank rWitness = diff (embed rWitness)` reproduces the interval-multiplicity
partition `m̄₀₀ = m̄₀₁ = m̄₁₂ = m̄₂₂ = 1`, rest `0` (the paper's `mWitness`, last of the six
partitions of `(2,2,2)`; cf. `RankPattern.mWitness`). The `decide` checks below exhibit these.

**Caveat (lives next to the claim).** Below the diagonal `kostantArrayOfRank rWitness` carries
**artifacts** (e.g. `(diff r)_{1,0} = -3`) from `rankFn` zeroing the lower triangle rather than
continuing the rank pattern there. The honest content is on `i ≤ j`; `RealizableKostant` is the
genuine bijection image, and its elements *are* the Kostant partition on the `i ≤ j` support. -/

/-- The paper's `(2,2,2)` witness rank pattern `[[2,1,0],[0,2,1],[0,0,2]]` (`rankFn` convention). -/
def rWitness : Fin 3 → Fin 3 → ℕ := ![![2, 1, 0], ![0, 2, 1], ![0, 0, 2]]

/-- On the diagonal the Kostant array of `rWitness` is `m̄₀₀ = m̄₂₂ = 1`, `m̄₁₁ = 0` (the paper's
`mWitness`). -/
example :
    (kostantArrayOfRank (N := 2) rWitness).1 0 0 = 1
      ∧ (kostantArrayOfRank (N := 2) rWitness).1 1 1 = 0
      ∧ (kostantArrayOfRank (N := 2) rWitness).1 2 2 = 1 := by
  refine ⟨?_, ?_, ?_⟩ <;>
    · rw [kostantArrayOfRank_val, diff_apply]; decide

/-- Above the diagonal the Kostant array of `rWitness` is `m̄₀₁ = m̄₁₂ = 1`, `m̄₀₂ = 0` — completing
the interval-multiplicity partition `mWitness` on the support `i ≤ j`. -/
example :
    (kostantArrayOfRank (N := 2) rWitness).1 0 1 = 1
      ∧ (kostantArrayOfRank (N := 2) rWitness).1 1 2 = 1
      ∧ (kostantArrayOfRank (N := 2) rWitness).1 0 2 = 0 := by
  refine ⟨?_, ?_, ?_⟩ <;>
    · rw [kostantArrayOfRank_val, diff_apply]; decide

end Witness

end DLNFibre.Core
