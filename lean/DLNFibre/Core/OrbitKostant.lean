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
* `orbitDiffArrayEquiv d : Quotient (orbitSetoid d) ≃ RealizableDiffArray d` — orbits ↔ the
  **second-difference (multiplicity-array) form** of the realizable rank patterns,
  `⟦A⟧ ↦ diff (rankFn A)`. It composes `orbitKostantEquiv` with the abstract inversion
  `RankPattern.cumulDiffEquiv.symm = diff`, after embedding the `ℕ`-valued `Fin`-indexed rank
  pattern into the `ℤ`-indexed supported-array shape (`embedRank`). **On `i ≤ j` the image is
  exactly the paper's Kostant partition** (the interval multiplicities `m̄`, verified on the
  witness); below the diagonal it carries `rankFn`-convention artifacts (e.g. `-3`) — so the *full*
  array is the `diff`-form, not literally a Kostant partition. Restricting the codomain to a genuine
  nonnegative `i ≤ j` Kostant partition is roadmapped (needs the rank-pattern inequalities for
  nonnegativity). The realizing tuple is `⊕ M^{m̄}` (`Orbit.baseChange_normalForm`).

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

/-! ## One inversion further: the multiplicity-array form (towards Cor 2.9)

`orbitKostantEquiv` lands in **rank patterns**; the paper's Cor 2.9 phrases the bijection against
**Kostant partitions** — the multiplicity arrays `m̄ = diff r`. Composing with the abstract
inversion `RankPattern.cumulDiffEquiv` (whose `.symm` is `diff`) takes that step. The bridge is
`embedRank`: a finite `ℕ`-valued rank pattern `Fin (N+1) → Fin (N+1) → ℕ` cast into the `ℤ`-indexed
`ℤ`-valued supported-array shape `cumulDiffEquiv` operates on (zero outside the square `[0,N]²`, so
`Supported` holds by the guard, for free).

**Scope of the name.** The result is `orbitDiffArrayEquiv`, an `Equiv` onto the `diff`-image. On
`i ≤ j` this image is exactly the paper's Kostant partition (verified on the witness); below the
diagonal it carries artifacts of `rankFn`'s lower-triangle-zero convention, so the *full* array is
the `diff`-form, not literally a Kostant partition (which is nonnegative, supported on `i ≤ j`). The
genuinely-literal Cor 2.9 codomain — the nonnegative `i ≤ j` restriction — is roadmapped. -/

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

/-- The **second-difference array** `m̄ = diff r` of a rank pattern, via the abstract inversion
`cumulDiffEquiv.symm`. On the support `i ≤ j` (where Kostant partitions live) this is the paper's
interval-multiplicity partition; below the diagonal it carries `rankFn`-convention artifacts (see
the witness), so it is the `diff`-form, not literally a Kostant partition. -/
noncomputable def diffArrayOfRank {N : ℕ} (r : Fin (N + 1) → Fin (N + 1) → ℕ) :
    SuppArray (N : ℤ) ℤ :=
  (cumulDiffEquiv (R := ℤ) (N := (N : ℤ))).symm (embedRank r)

/-- `diffArrayOfRank r` is literally the second finite difference of the embedded pattern. -/
@[simp] theorem diffArrayOfRank_val {N : ℕ} (r : Fin (N + 1) → Fin (N + 1) → ℕ) :
    (diffArrayOfRank r).1 = diff (embedRank r).1 := rfl

/-- `diffArrayOfRank` is injective: it is `diff ∘ embedRank`, both injective (`diff` via
`cumulDiffEquiv`). The second-difference array is therefore a complete invariant of the rank
pattern. -/
theorem diffArrayOfRank_injective {N : ℕ} :
    Function.Injective (diffArrayOfRank (N := N)) := fun _ _ h =>
  embedRank_injective ((cumulDiffEquiv (R := ℤ) (N := (N : ℤ))).symm.injective h)

/-- The realizable second-difference arrays of `d`: the `diff`-image of the realizable rank
patterns. On `i ≤ j` each is the paper's Kostant partition (see `orbitDiffArrayEquiv`). -/
abbrev RealizableDiffArray (d : Fin (N + 1) → ℕ) :=
  ↥(diffArrayOfRank (N := N) '' Set.range (rankFn (k := k) d))

/-- Realizable rank patterns ↔ realizable second-difference arrays, by the corestriction of `diff`
(one inversion further than `orbitKostantEquiv`). -/
noncomputable def rankDiffArrayEquiv (d : Fin (N + 1) → ℕ) :
    RealizableRank (k := k) d ≃ RealizableDiffArray (k := k) d :=
  Equiv.Set.image (diffArrayOfRank (N := N)) (Set.range (rankFn (k := k) d))
    (diffArrayOfRank_injective (N := N))

/-- **Orbits ↔ the multiplicity-array form of realizable rank patterns (towards Cor 2.9).** The set
of `G_d`-orbits of `Tuple d` is in bijection with the realizable second-difference arrays of `d`,
via `⟦A⟧ ↦ diff (rankFn A)`. This is `orbitKostantEquiv` (orbits ↔ rank patterns) composed with
`cumulDiffEquiv.symm` (rank patterns ↔ second-difference arrays). **On `i ≤ j` the image is exactly
the paper's Kostant partition** (the interval multiplicities `m̄`, verified on the witness); below
the diagonal it carries `rankFn`-convention artifacts (the bijection is exact regardless — see
`diffArrayOfRank`). The genuinely-literal Cor 2.9 codomain (nonnegative `i ≤ j` restriction) is
roadmapped. -/
noncomputable def orbitDiffArrayEquiv (d : Fin (N + 1) → ℕ) :
    Quotient (orbitSetoid (k := k) d) ≃ RealizableDiffArray (k := k) d :=
  (orbitKostantEquiv d).trans (rankDiffArrayEquiv d)

/-- The bijection sends `⟦A⟧` to its second-difference array `diff (rankFn A)`. -/
@[simp] theorem orbitDiffArrayEquiv_mk {d : Fin (N + 1) → ℕ} (A : Tuple (k := k) d) :
    (orbitDiffArrayEquiv d (Quotient.mk _ A) : RealizableDiffArray (k := k) d).1
      = diffArrayOfRank (rankFn d A) := rfl

section Witness

/-! ## Non-vacuity witness

The bijection fires on the `(2,2,2)/ℚ` witness: the orbit of `tupleWitnessQ` maps to its rank
pattern. -/

/-- The bijection is non-vacuous: it sends `⟦tupleWitnessQ⟧` to `rankFn tupleWitnessQ`. -/
example :
    ((orbitKostantEquiv dWitness (Quotient.mk (orbitSetoid dWitness) tupleWitnessQ)
      : RealizableRank (k := ℚ) dWitness) : Fin 3 → Fin 3 → ℕ)
      = rankFn dWitness tupleWitnessQ := rfl

/-- The multiplicity-array bijection is non-vacuous: it sends `⟦tupleWitnessQ⟧` to the
second-difference array of its rank pattern. -/
example :
    (orbitDiffArrayEquiv dWitness (Quotient.mk (orbitSetoid dWitness) tupleWitnessQ)
      : RealizableDiffArray (k := ℚ) dWitness).1
      = diffArrayOfRank (rankFn dWitness tupleWitnessQ) := rfl

/-! ### Concrete multiplicity values, and the lower-triangle artifact

The paper's `(2,2,2)` rank pattern is `rWitness = [[2,1,0],[0,2,1],[0,0,2]]` (`rankFn`'s convention:
`r_{ij}` for `i ≤ j`, `0` below the diagonal). On the support `i ≤ j` — where Kostant partitions
live — `diffArrayOfRank rWitness = diff (embed rWitness)` reproduces the interval-multiplicity
partition `m̄₀₀ = m̄₀₁ = m̄₁₂ = m̄₂₂ = 1`, rest `0` (the paper's `mWitness`, last of the six
partitions of `(2,2,2)`; cf. `RankPattern.mWitness`). So on `i ≤ j` the array **is** the Kostant
partition.

Below the diagonal the array carries **artifacts** (here `(diff r)_{1,0} = -3`) from `rankFn`
zeroing the lower triangle rather than continuing the rank pattern there. A genuine Kostant
partition is nonnegative and supported on `i ≤ j`, so the *full* array is the `diff`-form, not
literally a Kostant partition — exhibited (with the negative entry) below. -/

/-- The paper's `(2,2,2)` witness rank pattern `[[2,1,0],[0,2,1],[0,0,2]]` (`rankFn` convention). -/
def rWitness : Fin 3 → Fin 3 → ℕ := ![![2, 1, 0], ![0, 2, 1], ![0, 0, 2]]

/-- On the diagonal the array of `rWitness` is `m̄₀₀ = m̄₂₂ = 1`, `m̄₁₁ = 0` (the paper's
`mWitness`). -/
example :
    (diffArrayOfRank (N := 2) rWitness).1 0 0 = 1
      ∧ (diffArrayOfRank (N := 2) rWitness).1 1 1 = 0
      ∧ (diffArrayOfRank (N := 2) rWitness).1 2 2 = 1 := by
  refine ⟨?_, ?_, ?_⟩ <;>
    · rw [diffArrayOfRank_val, diff_apply]; decide

/-- Above the diagonal the array of `rWitness` is `m̄₀₁ = m̄₁₂ = 1`, `m̄₀₂ = 0` — completing the
interval-multiplicity partition `mWitness` on the support `i ≤ j`. -/
example :
    (diffArrayOfRank (N := 2) rWitness).1 0 1 = 1
      ∧ (diffArrayOfRank (N := 2) rWitness).1 1 2 = 1
      ∧ (diffArrayOfRank (N := 2) rWitness).1 0 2 = 0 := by
  refine ⟨?_, ?_, ?_⟩ <;>
    · rw [diffArrayOfRank_val, diff_apply]; decide

/-- The lower-triangle artifact is real: `(diff r)_{1,0} = -3` is negative, so the full array is the
`diff`-form, not a (nonnegative, `i ≤ j`-supported) Kostant partition. -/
example : (diffArrayOfRank (N := 2) rWitness).1 1 0 = -3 := by
  rw [diffArrayOfRank_val, diff_apply]; decide

end Witness

end DLNFibre.Core
