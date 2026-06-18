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

Three forms of the bijection, each `⟦A⟧ ↦` a successively more literal encoding of the same datum:

* `orbitKostantEquiv d : Quotient (orbitSetoid d) ≃ RealizableRank d` — orbits ↔ realizable **rank
  patterns** (the honest building block; `⟦A⟧ ↦ rankFn A`).
* `orbitDiffArrayEquiv d : Quotient (orbitSetoid d) ≃ RealizableDiffArray d` — orbits ↔ the
  **second-difference (multiplicity-array) form** of the realizable rank patterns,
  `⟦A⟧ ↦ diff (rankFn A)`. It composes `orbitKostantEquiv` with the abstract inversion
  `RankPattern.cumulDiffEquiv.symm = diff`, after embedding the `ℕ`-valued `Fin`-indexed rank
  pattern into the `ℤ`-indexed supported-array shape (`embedRank`). **On `i ≤ j` the image is
  exactly the paper's Kostant partition** (the interval multiplicities `m̄`, verified on the
  witness); below the diagonal it carries `rankFn`-convention artifacts (e.g. `-3`) — so the *full*
  array is the `diff`-form, not literally a Kostant partition. The realizing tuple is `⊕ M^{m̄}`
  (`Orbit.baseChange_normalForm`).
* `orbitKostantPartitionEquiv d : Quotient (orbitSetoid d) ≃ KostantPartition d` — orbits ↔ the
  **literal Kostant partitions** (Le Halleur–Rimányi 2024, Cor 2.9): the realizable **nonnegative,
  `i ≤ j`-supported** multiplicity arrays, with no lower-triangle artifacts. The codomain carrier is
  `kostantArrayOfRank (rankFn A)` — `diff (rankFn A)` **truncated to `0` below the diagonal**. The
  bridge `kostantArrayOfRank_isKostant` identifies that truncation, for a realizable pattern, with
  the bar-multiplicity array `barMult` of a Gabriel decomposition (`Orbit.exists_cumul_barMult`),
  which is manifestly nonnegative (a sum of `singleDelta` indicators) and `i ≤ j`-supported
  (`birth ≤ death`). Truncation is invisible to `cumul` on the upper triangle, so the truncated
  array still determines the rank pattern (`kostantArrayOfRank_injOn`), and the equiv corestricts.
* `orbitCMPlusEquiv d : Quotient (orbitSetoid d) ≃ { m // CMPlus d m }` — orbits ↔ the **paper's
  independently-defined object** `CM⁺_d` (`CMPlus`): the nonnegative, `i ≤ j`-supported arrays
  satisfying the **dimension equations** `d_k = ∑_{i ≤ k ≤ j} m_{ij}`, with no reference to tuples
  or realizability. The image-coded carrier above and `CMPlus` coincide (`cMPlus_iff_mem_image`):
  realizable ⟹ CMPlus is `cMPlus_kostantArrayOfRank` (`r_{kk} = d_k`), and CMPlus ⟹ realizable is
  `kostantArrayOfRank_rankFn_realizer` (the explicit realizer `⊕ M^m` over `realizer`).

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
genuinely-literal Cor 2.9 codomain — the nonnegative `i ≤ j` restriction — is
`orbitKostantPartitionEquiv` below (carrier `kostantArrayOfRank`, the `diff`-array truncated to `0`
below the diagonal). -/

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
`orbitKostantPartitionEquiv` below. -/
noncomputable def orbitDiffArrayEquiv (d : Fin (N + 1) → ℕ) :
    Quotient (orbitSetoid (k := k) d) ≃ RealizableDiffArray (k := k) d :=
  (orbitKostantEquiv d).trans (rankDiffArrayEquiv d)

/-- The bijection sends `⟦A⟧` to its second-difference array `diff (rankFn A)`. -/
@[simp] theorem orbitDiffArrayEquiv_mk {d : Fin (N + 1) → ℕ} (A : Tuple (k := k) d) :
    (orbitDiffArrayEquiv d (Quotient.mk _ A) : RealizableDiffArray (k := k) d).1
      = diffArrayOfRank (rankFn d A) := rfl

/-! ## The literal Kostant-partition codomain (Cor 2.9)

`orbitDiffArrayEquiv` lands in the *full* `diff`-array, which below the diagonal carries
`rankFn`-convention artifacts (the `-3`). A genuine Kostant partition is **nonnegative** and
**supported on `i ≤ j`**. This section restricts the codomain to that literal object.

The carrier is `kostantArrayOfRank`: the `diff`-array **truncated to `0` below the diagonal**. The
bridge fact `kostantArrayOfRank_isKostant` identifies it, for a realizable rank pattern, with the
**bar-multiplicity array** `barMult` of a Gabriel decomposition (`Orbit.exists_cumul_barMult`),
which is manifestly nonnegative (a sum of `singleDelta` indicators) and `i ≤ j`-supported (bars have
`birth ≤ death`). Truncation is invisible to `cumul` on the upper triangle
(`cumul_truncBelow_of_le`), so the truncated array still determines the rank pattern — hence the map
stays injective and the bijection corestricts. -/

/-- A supported array is a **literal Kostant partition**: nonnegative and zero below the diagonal
(supported on `i ≤ j`), as Kostant partitions are. -/
def IsKostantArray {N : ℕ} (m : SuppArray (N : ℤ) ℤ) : Prop :=
  (∀ i j : ℤ, 0 ≤ m.1 i j) ∧ (∀ i j : ℤ, j < i → m.1 i j = 0)

/-- The `diff`-array of `r` **truncated to `0` below the diagonal** — the literal Kostant-partition
carrier (nonnegative, `i ≤ j`-supported once `r` is realizable; see
`kostantArrayOfRank_isKostant`). Agrees with `diffArrayOfRank r` on `i ≤ j`. -/
noncomputable def kostantArrayOfRank {N : ℕ} (r : Fin (N + 1) → Fin (N + 1) → ℕ) :
    SuppArray (N : ℤ) ℤ :=
  ⟨fun i j ↦ if i ≤ j then (diffArrayOfRank r).1 i j else 0, by
    refine ⟨fun i j hi ↦ ?_, fun i j hj ↦ ?_⟩ <;> dsimp only <;> split_ifs with h
    · exact (diffArrayOfRank r).2.1 i j hi
    · rfl
    · exact (diffArrayOfRank r).2.2 i j hj
    · rfl⟩

/-- On `i ≤ j` the truncated array is the full `diff`-array. -/
@[simp] theorem kostantArrayOfRank_of_le {N : ℕ} (r : Fin (N + 1) → Fin (N + 1) → ℕ) {i j : ℤ}
    (hij : i ≤ j) : (kostantArrayOfRank r).1 i j = (diffArrayOfRank r).1 i j := by
  simp [kostantArrayOfRank, hij]

/-- Below the diagonal the truncated array is `0`. -/
@[simp] theorem kostantArrayOfRank_of_gt {N : ℕ} (r : Fin (N + 1) → Fin (N + 1) → ℕ) {i j : ℤ}
    (hij : j < i) : (kostantArrayOfRank r).1 i j = 0 := by
  simp [kostantArrayOfRank, not_le.mpr hij]

/-- Truncating an array below the diagonal is invisible to `cumul` on the upper triangle: for
`i ≤ j`, `cumul` only sums entries `(a,b)` with `a ≤ i ≤ j ≤ b`, hence `a ≤ b`. -/
theorem cumul_truncBelow_of_le {N : ℤ} (f : ℤ → ℤ → ℤ) {i j : ℤ} (hij : i ≤ j) :
    cumul N (fun a b ↦ if a ≤ b then f a b else 0) i j = cumul N f i j := by
  rw [cumul_apply, cumul_apply]
  refine Finset.sum_congr rfl fun a ha ↦ Finset.sum_congr rfl fun b hb ↦ ?_
  rw [Finset.mem_Icc] at ha hb
  rw [if_pos (le_trans ha.2 (le_trans hij hb.1))]

/-- **The bridge fact.** For a realizable rank pattern `rankFn d A`, the truncated `diff`-array is
the bar-multiplicity array `barMult` of a Gabriel decomposition of `A`: nonnegative (sum of
`singleDelta` indicators) and `i ≤ j`-supported (bars have `birth ≤ death`). The truncated array is
therefore a literal Kostant partition. Uses `Orbit.exists_cumul_barMult` (the barcode bar-count =
rank-pattern identity) — no new barcode lemma; only the truncation/`diff` bookkeeping. -/
theorem kostantArrayOfRank_isKostant {d : Fin (N + 1) → ℕ} (A : Tuple (k := k) d) :
    IsKostantArray (kostantArrayOfRank (rankFn d A)) := by
  obtain ⟨M, birth, death, hbd, _hkost, hcum⟩ := exists_cumul_barMult A
  set mbar := barMult M birth death with hmbar
  -- `embedRank (rankFn d A)` agrees with `cumul N mbar` on the upper triangle `x ≤ y`.
  have hagree : ∀ x y : ℤ, x ≤ y →
      (embedRank (rankFn d A)).1 x y = cumul (N : ℤ) mbar x y := by
    intro x y hxy
    rcases lt_or_ge x 0 with hx | hx
    · rw [(embedRank (rankFn d A)).2.1 x y hx, (supported_cumul (N : ℤ) mbar).1 x y hx]
    rcases lt_or_ge (N : ℤ) y with hy | hy
    · rw [(embedRank (rankFn d A)).2.2 x y hy, (supported_cumul (N : ℤ) mbar).2 x y hy]
    have hy0 : 0 ≤ y := le_trans hx hxy
    have hxN : x ≤ (N : ℤ) := le_trans hxy hy
    obtain ⟨i, hi⟩ : ∃ i : Fin (N + 1), (i : ℤ) = x :=
      ⟨⟨x.toNat, by omega⟩, by simp [Int.toNat_of_nonneg hx]⟩
    obtain ⟨j, hj⟩ : ∃ j : Fin (N + 1), (j : ℤ) = y :=
      ⟨⟨y.toNat, by omega⟩, by simp [Int.toNat_of_nonneg hy0]⟩
    have hij : i ≤ j := by
      have : (i : ℤ) ≤ (j : ℤ) := by rw [hi, hj]; exact hxy
      exact_mod_cast this
    rw [← hi, ← hj, embedRank_apply_fin, ← hcum i j hij]
    simp [rankFn, hij]
  -- hence the full `diff`-array equals `mbar` on the upper triangle (all four `diff`-points have
  -- row ≤ col), and `mbar` is nonnegative and `i ≤ j`-supported.
  have hdiff : ∀ i j : ℤ, i ≤ j → (diffArrayOfRank (rankFn d A)).1 i j = mbar i j := by
    intro i j hij
    have hbarmult : diff (cumul (N : ℤ) mbar) i j = mbar i j :=
      congrFun (congrFun (diff_cumul (N : ℤ) mbar (supported_barMult M birth death).1
        (supported_barMult M birth death).2) i) j
    rw [diffArrayOfRank_val, diff_apply, hagree i j hij, hagree i (j + 1) (by omega),
      hagree (i - 1) j (by omega), hagree (i - 1) (j + 1) (by omega), ← diff_apply]
    exact hbarmult
  have hnonneg : ∀ a b : ℤ, 0 ≤ mbar a b := fun a b ↦ by
    rw [hmbar, barMult]
    exact Finset.sum_nonneg fun lam _ ↦ by rw [singleDelta]; split_ifs <;> norm_num
  refine ⟨fun i j ↦ ?_, fun i j hij ↦ ?_⟩
  · rcases le_or_gt i j with h | h
    · rw [kostantArrayOfRank_of_le _ h, hdiff i j h]; exact hnonneg i j
    · rw [kostantArrayOfRank_of_gt _ h]
  · rw [kostantArrayOfRank_of_gt _ hij]

/-- `cumul` of the truncated array recovers the embedded rank pattern on the upper triangle:
`cumul N (kostantArrayOfRank r) x y = (embedRank r) x y` for `x ≤ y`. The truncation is invisible to
`cumul` there (`cumul_truncBelow_of_le`), and `cumul` inverts `diff` on the supported `embedRank r`
(`cumul_diff`). The key to injectivity: the truncated array still determines the rank pattern. -/
theorem cumul_kostantArrayOfRank_of_le {N : ℕ} (r : Fin (N + 1) → Fin (N + 1) → ℕ) {x y : ℤ}
    (hxy : x ≤ y) :
    cumul (N : ℤ) (kostantArrayOfRank r).1 x y = (embedRank r).1 x y := by
  have htrunc : (kostantArrayOfRank r).1
      = fun a b ↦ if a ≤ b then (diff (embedRank r).1) a b else 0 := by
    funext a b; by_cases h : a ≤ b
    · rw [kostantArrayOfRank_of_le _ h, diffArrayOfRank_val, if_pos h]
    · rw [kostantArrayOfRank_of_gt _ (lt_of_not_ge h), if_neg h]
  rw [htrunc, cumul_truncBelow_of_le (diff (embedRank r).1) hxy,
    show cumul (N : ℤ) (diff (embedRank r).1) = (embedRank r).1 from
      cumul_diff (N : ℤ) (embedRank r).1 (embedRank r).2.1 (embedRank r).2.2]

/-- **The truncated array is a complete invariant of the rank pattern.** `kostantArrayOfRank` is
injective: it determines `embedRank r` on the upper triangle (`cumul_kostantArrayOfRank_of_le`),
hence `r` on `i ≤ j` (`embedRank_apply_fin`), and `r` is `0` below the diagonal by the `rankFn`
convention — but stated for any pattern with that convention, so injectivity is unconditional on the
realizable set. -/
theorem kostantArrayOfRank_injOn {d : Fin (N + 1) → ℕ} :
    Set.InjOn (kostantArrayOfRank (N := N)) (Set.range (rankFn (k := k) d)) := by
  rintro _ ⟨A, rfl⟩ _ ⟨B, rfl⟩ h
  -- upper triangle: `cumul` of the (equal) truncated arrays recovers `embedRank`
  have hemb : ∀ i j : Fin (N + 1), (i : ℤ) ≤ (j : ℤ) →
      (embedRank (rankFn d A)).1 (i : ℤ) (j : ℤ) = (embedRank (rankFn d B)).1 (i : ℤ) (j : ℤ) := by
    intro i j hij
    rw [← cumul_kostantArrayOfRank_of_le (rankFn d A) hij, h,
      cumul_kostantArrayOfRank_of_le (rankFn d B) hij]
  funext i j
  by_cases hij : i ≤ j
  · have hijZ : (i : ℤ) ≤ (j : ℤ) := by exact_mod_cast hij
    have := hemb i j hijZ
    rw [embedRank_apply_fin, embedRank_apply_fin] at this
    exact_mod_cast this
  · rw [rankFn, rankFn, dif_neg hij, dif_neg hij]

/-- **The literal Kostant-partition codomain (Le Halleur–Rimányi 2024, Cor 2.9).** The realizable,
**nonnegative, `i ≤ j`-supported** multiplicity arrays of `d`: the image of the realizable rank
patterns under `kostantArrayOfRank`, each certified `IsKostantArray` (the certificate is total by
`kostantArrayOfRank_isKostant`). The genuine paper-side object — no lower-triangle artifacts. -/
abbrev KostantPartition (d : Fin (N + 1) → ℕ) :=
  { m : SuppArray (N : ℤ) ℤ //
      m ∈ kostantArrayOfRank (N := N) '' Set.range (rankFn (k := k) d) ∧ IsKostantArray m }

/-- Realizable rank patterns ↔ literal Kostant partitions: `kostantArrayOfRank` corestricted onto
its image (injective by `kostantArrayOfRank_injOn`), then the `IsKostantArray` certificate attached
for free (`kostantArrayOfRank_isKostant`). -/
noncomputable def rankKostantPartitionEquiv (d : Fin (N + 1) → ℕ) :
    RealizableRank (k := k) d ≃ KostantPartition (k := k) d :=
  (Equiv.Set.imageOfInjOn (kostantArrayOfRank (N := N)) (Set.range (rankFn (k := k) d))
      kostantArrayOfRank_injOn).trans
    (Equiv.subtypeEquivRight fun m ↦
      ⟨fun hm ↦ ⟨hm, by
          obtain ⟨r, ⟨A, hA⟩, hrm⟩ := hm
          rw [← hrm, ← hA]
          exact kostantArrayOfRank_isKostant A⟩,
        fun hm ↦ hm.1⟩)

/-- **Orbits ↔ literal Kostant partitions (Le Halleur–Rimányi 2024, Cor 2.9).** The set of
`G_d`-orbits of `Tuple d` is in bijection with the realizable Kostant partitions of `d` — the
**nonnegative, `i ≤ j`-supported** multiplicity arrays — via `⟦A⟧ ↦` the truncated `diff (rankFn A)`
(the Kostant partition). This is `orbitKostantEquiv` (orbits ↔ rank patterns) composed with
`rankKostantPartitionEquiv`. The
literal-codomain form of `orbitDiffArrayEquiv`: same bijection, but the codomain is the genuine
paper-side Kostant partition (no lower-triangle artifacts). -/
noncomputable def orbitKostantPartitionEquiv (d : Fin (N + 1) → ℕ) :
    Quotient (orbitSetoid (k := k) d) ≃ KostantPartition (k := k) d :=
  (orbitKostantEquiv d).trans (rankKostantPartitionEquiv d)

/-- The bijection sends `⟦A⟧` to the truncated second-difference array
`kostantArrayOfRank (rankFn A)` (the literal Kostant partition of `A`). -/
@[simp] theorem orbitKostantPartitionEquiv_mk {d : Fin (N + 1) → ℕ} (A : Tuple (k := k) d) :
    (orbitKostantPartitionEquiv d (Quotient.mk _ A) : KostantPartition (k := k) d).1
      = kostantArrayOfRank (rankFn d A) := rfl

/-! ## The paper's predicate `CM⁺_d`, independently, and the realizability equivalence (Def, p.~8)

`KostantPartition d` above is **image-coded**: it bakes "realizable by a tuple" into the carrier.
The paper (Le Halleur–Rimányi 2024, p.~8) defines `CM⁺_d` *independently* as the upper-triangular
nonnegative multiplicity arrays satisfying the **dimension equations** `d_k = ∑_{i ≤ k ≤ j} m_{ij}`.
This section exposes that standalone predicate (`CMPlus`) and proves it coincides with
realizability, so the image-coded carrier and the genuine paper-side object agree.

The dimension-equation sum `∑_{i ≤ k ≤ j} m_{ij}` is exactly `cumul N m` on the **diagonal** `(k,k)`
(`cumul N m k k = ∑_{a ≤ k} ∑_{k ≤ b ≤ N} m_{ab} = ∑_{a ≤ k ≤ b} m_{ab}`), so `CMPlus` reads the
diagonal of `cumul`. -/

/-- **The paper's predicate `CM⁺_d` (Le Halleur–Rimányi 2024, p.~8), standalone.** A supported array
`m` is a **Kostant partition of `d`** when it is a nonnegative, `i ≤ j`-supported multiplicity array
(`IsKostantArray`) and satisfies the **dimension equations** `d_k = ∑_{i ≤ k ≤ j} m_{ij}` — the
diagonal of `cumul N m` (`cumul N m k k = ∑_{a ≤ k ≤ b} m_{ab}`). No reference to tuples or
realizability: the purely combinatorial paper definition. -/
def CMPlus (d : Fin (N + 1) → ℕ) (m : SuppArray (N : ℤ) ℤ) : Prop :=
  IsKostantArray m ∧ ∀ k : Fin (N + 1), (d k : ℤ) = cumul (N : ℤ) m.1 (k : ℤ) (k : ℤ)

/-! ### Realizable ⟹ CMPlus (the forward direction)

A realizable array `kostantArrayOfRank (rankFn d A)` is a Kostant partition: it is `IsKostantArray`
(`kostantArrayOfRank_isKostant`), and its diagonal `cumul` recovers `d_k`: `cumul` of the truncated
array on the diagonal is the embedded rank pattern there (`cumul_kostantArrayOfRank_of_le`), which
is `r_{kk} = d_k` (`rankPattern_self`). -/

/-- **Realizable ⟹ CMPlus.** Every realizable array satisfies the paper's dimension equations: the
diagonal of its `cumul` is `r_{kk} = d_k`. -/
theorem cMPlus_kostantArrayOfRank {d : Fin (N + 1) → ℕ} (A : Tuple (k := k) d) :
    CMPlus d (kostantArrayOfRank (rankFn d A)) := by
  refine ⟨kostantArrayOfRank_isKostant A, fun k ↦ ?_⟩
  rw [cumul_kostantArrayOfRank_of_le (rankFn d A) (le_refl (k : ℤ)), embedRank_apply_fin]
  rw [rankFn, dif_pos (le_refl k), rankPattern_self]

/-! ### CMPlus ⟹ realizable (the reverse direction, the substantive one)

A paper-style Kostant partition `m` (with `CMPlus d m`) is realized by an explicit tuple: the
interval direct sum `⊕_{(i,j)} M_{ij}^{m_{ij}}` carrying `m_{ij}` copies of the bar `M_{ij}`. We
encode the multiplicities as a **`CopyIndex`** — the finite sigma type with `(m_{ij}).toNat` copies
of each endpoint pair `(i,j)` — and read off a bar list `listOfArray m`. Its multiplicity array is
`m` (`multiplicityArray_listOfArray`, via the bar-count bridge `barMult_eq_card_fiber` and the fibre
equiv `Equiv.sigmaSubtype`), so `intervalDirectSum (listOfArray m)` has rank pattern `cumul m`
(`rankPattern_intervalDirectSum_eq_cumul`). The diagonal dimension equation pins `foldDim = d`, and
the upper-triangular rank pattern (pinned by `m` itself, *not* by the diagonal) feeds the assembly
`kostantArrayOfRank (rankFn d realizer) = m`. -/

/-- The copy-index of a multiplicity array: `(m_{ij}).toNat` copies of each endpoint pair `(i,j)`.
A `Fintype` (finite sigma), and the bar index set of the realizing direct sum. -/
abbrev CopyIndex (m : SuppArray (N : ℤ) ℤ) : Type :=
  Σ p : Fin (N + 1) × Fin (N + 1), Fin (m.1 (p.1 : ℤ) (p.2 : ℤ)).toNat

/-- The number of bars of the realizer: the total copy count `∑_{ij} (m_{ij}).toNat`. -/
noncomputable def copyCard (m : SuppArray (N : ℤ) ℤ) : ℕ := Fintype.card (CopyIndex m)

/-- The chosen labelling of the `copyCard m` bars by their endpoint pairs (via `Fintype.equivFin`).
`copyBar m lam = (i, j)` says bar `lam` is a copy of `M_{ij}`. -/
noncomputable def copyBar (m : SuppArray (N : ℤ) ℤ) (lam : Fin (copyCard m)) :
    Fin (N + 1) × Fin (N + 1) :=
  ((Fintype.equivFin (CopyIndex m)).symm lam).1

/-- The bar list of `m`: one entry `(i,j)` per copy. Its multiplicity array is `m`
(`multiplicityArray_listOfArray`). -/
noncomputable def listOfArray (m : SuppArray (N : ℤ) ℤ) :
    List (Fin (N + 1) × Fin (N + 1)) :=
  (List.finRange (copyCard m)).map (copyBar m)

/-- The `(birth,death) = (i,j)` fibre of the bar labelling has cardinality `(m_{ij}).toNat`: it is
the copy-index fibre over `(i,j)`, equivalent to `Fin (m_{ij}).toNat` via `Equiv.sigmaSubtype`. -/
theorem card_copyBar_fiber (m : SuppArray (N : ℤ) ℤ) (i j : Fin (N + 1)) :
    Fintype.card {lam // (copyBar m lam).1 = i ∧ (copyBar m lam).2 = j}
      = (m.1 (i : ℤ) (j : ℤ)).toNat := by
  classical
  -- `{lam // copyBar lam = (i,j)}` ≃ `{c : CopyIndex // c.1 = (i,j)}` ≃ `Fin (m_{ij}).toNat`
  have e₁ : {lam // (copyBar m lam).1 = i ∧ (copyBar m lam).2 = j}
      ≃ {lam // copyBar m lam = (i, j)} :=
    Equiv.subtypeEquivRight fun lam ↦ by rw [Prod.ext_iff]
  have e₂ : {lam // copyBar m lam = (i, j)}
      ≃ {c : CopyIndex m // c.1 = (i, j)} :=
    Equiv.subtypeEquivOfSubtype (p := fun c : CopyIndex m ↦ c.1 = (i, j))
      (Fintype.equivFin (CopyIndex m)).symm
  have e₃ : {c : CopyIndex m // c.1 = (i, j)} ≃ Fin (m.1 (i : ℤ) (j : ℤ)).toNat :=
    Equiv.sigmaSubtype (i, j)
  rw [Fintype.card_congr (e₁.trans (e₂.trans e₃)), Fintype.card_fin]

/-- **The realizer's multiplicity array is `m`.** `multiplicityArray (listOfArray m) = m.1`: the
list has `(m_{ij}).toNat = m_{ij}` copies of each `(i,j)` (`card_copyBar_fiber`, nonnegativity), and
vanishes off the `i ≤ j` support of `m` exactly as `barMult` does. -/
theorem multiplicityArray_listOfArray {d : Fin (N + 1) → ℕ} (m : SuppArray (N : ℤ) ℤ)
    (hm : CMPlus d m) :
    multiplicityArray (listOfArray m) = m.1 := by
  rw [listOfArray, multiplicityArray_map_finRange]
  set birth := fun lam ↦ (copyBar m lam).1 with hbirth
  set death := fun lam ↦ (copyBar m lam).2 with hdeath
  funext a b
  -- `barMult` vanishes off `[0,N]²`; on a cast pair `(i,j)` it is the fibre count `(m_{ij}).toNat`
  rcases lt_or_ge a 0 with ha | ha
  · rw [(supported_barMult _ birth death).1 a b ha, m.2.1 a b ha]
  rcases lt_or_ge (N : ℤ) b with hb | hb
  · rw [(supported_barMult _ birth death).2 a b hb, m.2.2 a b hb]
  -- below the diagonal `b < 0 ≤ a`: both `barMult` (death ≥ 0) and `m` (`IsKostantArray`) vanish
  rcases lt_or_ge b 0 with hb0 | hb0
  · rw [hm.1.2 a b (lt_of_lt_of_le hb0 ha), hbirth, hdeath, barMult]
    refine Finset.sum_eq_zero fun lam _ ↦ ?_
    rw [singleDelta, if_neg]
    rintro ⟨_, rfl⟩
    exact absurd hb0 (not_lt.mpr (by positivity))
  -- `a > N ≥ b`: below the diagonal again — both `barMult` (birth ≤ N) and `m` vanish
  rcases lt_or_ge (N : ℤ) a with haN | haN
  · rw [hm.1.2 a b (lt_of_le_of_lt hb haN), hbirth, hdeath, barMult]
    refine Finset.sum_eq_zero fun lam _ ↦ ?_
    rw [singleDelta, if_neg]
    rintro ⟨rfl, _⟩
    exact absurd haN (not_lt.mpr (by exact_mod_cast Nat.lt_succ_iff.mp (copyBar m lam).1.isLt))
  -- in range: name the `Fin (N+1)` indices `i, j`
  obtain ⟨i, hi⟩ : ∃ i : Fin (N + 1), (i : ℤ) = a :=
    ⟨⟨a.toNat, by omega⟩, by simp [Int.toNat_of_nonneg ha]⟩
  obtain ⟨j, hj⟩ : ∃ j : Fin (N + 1), (j : ℤ) = b :=
    ⟨⟨b.toNat, by omega⟩, by simp [Int.toNat_of_nonneg hb0]⟩
  subst hi hj
  rw [show barMult _ birth death (i : ℤ) (j : ℤ)
      = barMult _ birth death ((i, j).1 : ℤ) ((i, j).2 : ℤ) from rfl,
    barMult_eq_card_fiber _ birth death (i, j)]
  rw [card_copyBar_fiber m i j]
  -- `(m_{ij}).toNat = m_{ij}` since `m_{ij} ≥ 0`
  exact Int.toNat_of_nonneg (hm.1.1 (i : ℤ) (j : ℤ))

/-- **The dimension vector of the realizer is `d`.** `foldDim (listOfArray m) = d`: the diagonal
rank pattern `r_{kk} = foldDim` of the interval direct sum is `cumul (multiplicityArray) k k =
cumul m k k = d_k` by the dimension equation. The only place the diagonal `CMPlus` equation is
used. -/
theorem foldDim_listOfArray {d : Fin (N + 1) → ℕ} (m : SuppArray (N : ℤ) ℤ) (hm : CMPlus d m) :
    foldDim (listOfArray m) = d := by
  funext t
  -- `foldDim L t = r_{tt}(⊕ M^L) = cumul (mult L) t t = cumul m t t = d_t`; any field works for the
  -- middle rank identity (the multiplicity array is field-free), so we instantiate at `ℚ`.
  have hZ : (foldDim (listOfArray m) t : ℤ) = (d t : ℤ) := by
    have hself : (foldDim (listOfArray m) t : ℤ)
        = (rankPattern (foldDim (listOfArray m))
            (intervalDirectSum (k := ℚ) (listOfArray m)) t t le_rfl : ℤ) := by
      rw [rankPattern_self]
    rw [hself, rankPattern_intervalDirectSum_eq_cumul, multiplicityArray_listOfArray m hm,
      ← hm.2 t]
  exact_mod_cast hZ

/-- The explicit realizer of a Kostant partition `m`: the interval direct sum
`⊕_{(i,j)} M_{ij}^{m_{ij}}`, cast to live over `d` (its dimension vector is `d`,
`foldDim_listOfArray`). -/
noncomputable def realizer {d : Fin (N + 1) → ℕ} (m : SuppArray (N : ℤ) ℤ) (hm : CMPlus d m) :
    Tuple (k := k) d :=
  foldDim_listOfArray m hm ▸ intervalDirectSum (k := k) (listOfArray m)

/-- The realizer's rank pattern is `cumul m` on the upper triangle: `r_{ij}(realizer) = cumul N m`
(`rankPattern_intervalDirectSum_eq_cumul` + `multiplicityArray_listOfArray`, through the transport
`rankPattern_transport`). -/
theorem rankPattern_realizer {d : Fin (N + 1) → ℕ} (m : SuppArray (N : ℤ) ℤ) (hm : CMPlus d m)
    (i j : Fin (N + 1)) (hij : i ≤ j) :
    (rankPattern d (realizer (k := k) m hm) i j hij : ℤ)
      = cumul (N : ℤ) m.1 (i : ℤ) (j : ℤ) := by
  rw [realizer, rankPattern_transport (foldDim_listOfArray m hm)
    (intervalDirectSum (k := k) (listOfArray m)),
    rankPattern_intervalDirectSum_eq_cumul, multiplicityArray_listOfArray m hm]

/-- **CMPlus ⟹ realizable.** `kostantArrayOfRank (rankFn d (realizer m)) = m`: the realizer's rank
pattern is `cumul m` (`rankPattern_realizer`), so on the upper triangle `kostantArrayOfRank`
recovers `embedRank` of the rank pattern, which `diff`-inverts (`diff_cumul`) `m` back to `m`;
below the diagonal both sides are `0` (`kostantArrayOfRank_of_gt`, `IsKostantArray`). The whole
upper triangle is pinned by `m` itself (it *is* the multiplicity array), not by the diagonal
equation. -/
theorem kostantArrayOfRank_rankFn_realizer {d : Fin (N + 1) → ℕ} (m : SuppArray (N : ℤ) ℤ)
    (hm : CMPlus d m) :
    kostantArrayOfRank (rankFn d (realizer (k := k) m hm)) = m := by
  -- the truncated `diff`-array of the realizer's rank pattern agrees with `m` on the upper triangle
  set r := rankFn d (realizer (k := k) m hm) with hr
  -- `embedRank r` equals `cumul m` on the upper triangle (both supported; `embedRank r = cumul m`)
  have hembed : ∀ x y : ℤ, x ≤ y → (embedRank r).1 x y = cumul (N : ℤ) m.1 x y := by
    intro x y hxy
    rcases lt_or_ge x 0 with hx | hx
    · rw [(embedRank r).2.1 x y hx, (supported_cumul (N : ℤ) m.1).1 x y hx]
    rcases lt_or_ge (N : ℤ) y with hy | hy
    · rw [(embedRank r).2.2 x y hy, (supported_cumul (N : ℤ) m.1).2 x y hy]
    have hy0 : 0 ≤ y := le_trans hx hxy
    have hxN : x ≤ (N : ℤ) := le_trans hxy hy
    obtain ⟨i, hi⟩ : ∃ i : Fin (N + 1), (i : ℤ) = x :=
      ⟨⟨x.toNat, by omega⟩, by simp [Int.toNat_of_nonneg hx]⟩
    obtain ⟨j, hj⟩ : ∃ j : Fin (N + 1), (j : ℤ) = y :=
      ⟨⟨y.toNat, by omega⟩, by simp [Int.toNat_of_nonneg hy0]⟩
    have hij : i ≤ j := by
      have : (i : ℤ) ≤ (j : ℤ) := by rw [hi, hj]; exact hxy
      exact_mod_cast this
    rw [← hi, ← hj, embedRank_apply_fin, hr, rankFn, dif_pos hij]
    exact_mod_cast rankPattern_realizer (k := k) m hm i j hij
  -- `m = diff (cumul m)` (supported), so `cumul m` agrees with `m` after one `diff`
  have hdiffm : diff (cumul (N : ℤ) m.1) = m.1 := diff_cumul (N : ℤ) m.1 m.2.1 m.2.2
  apply Subtype.ext
  funext x y
  by_cases hxy : x ≤ y
  · rw [kostantArrayOfRank_of_le _ hxy, diffArrayOfRank_val, diff_apply,
      hembed x y hxy, hembed x (y + 1) (by omega), hembed (x - 1) y (by omega),
      hembed (x - 1) (y + 1) (by omega), ← diff_apply, hdiffm]
  · rw [kostantArrayOfRank_of_gt _ (lt_of_not_ge hxy), (hm.1.2 x y (lt_of_not_ge hxy)).symm]

/-! ### The realizability ↔ CMPlus equivalence (the two directions packaged)

The image-coded `KostantPartition d` carrier (`m ∈ kostantArrayOfRank '' Set.range (rankFn d) ∧
IsKostantArray m`) and the standalone paper predicate `CMPlus d m` define the same set. -/

/-- **Realizability characterizes the paper predicate.** A supported array is a realizable Kostant
array (image-coded) iff it satisfies the paper's standalone predicate `CMPlus d`. The forward
direction is `cMPlus_kostantArrayOfRank` (with `IsKostantArray` from the bridge), the reverse is the
realizer `kostantArrayOfRank_rankFn_realizer`. -/
theorem cMPlus_iff_mem_image {d : Fin (N + 1) → ℕ} (m : SuppArray (N : ℤ) ℤ) :
    CMPlus d m ↔
      (m ∈ kostantArrayOfRank (N := N) '' Set.range (rankFn (k := k) d) ∧ IsKostantArray m) := by
  constructor
  · intro hm
    exact ⟨⟨rankFn d (realizer (k := k) m hm), ⟨realizer (k := k) m hm, rfl⟩,
      kostantArrayOfRank_rankFn_realizer m hm⟩, hm.1⟩
  · rintro ⟨⟨_, ⟨A, rfl⟩, rfl⟩, _⟩
    exact cMPlus_kostantArrayOfRank A

/-- The image-coded Kostant-partition carrier coincides with the subtype of the paper predicate
`CMPlus d`: `KostantPartition d ≃ { m // CMPlus d m }`. The genuine paper-side object. -/
noncomputable def kostantPartitionCMPlusEquiv (d : Fin (N + 1) → ℕ) :
    KostantPartition (k := k) d ≃ { m : SuppArray (N : ℤ) ℤ // CMPlus d m } :=
  Equiv.subtypeEquivRight fun m ↦ (cMPlus_iff_mem_image (k := k) m).symm

/-- **Orbits ↔ Kostant partitions of `d`, paper predicate form (Le Halleur–Rimányi 2024, Cor 2.9).**
The set of `G_d`-orbits of `Tuple d` is in bijection with `{ m // CMPlus d m }` — the arrays
satisfying the paper's standalone dimension equations `d_k = ∑_{i ≤ k ≤ j} m_{ij}`, nonnegative and
`i ≤ j`-supported. The literal-codomain form of `orbitKostantPartitionEquiv`, retargeted onto the
independently-defined paper object. -/
noncomputable def orbitCMPlusEquiv (d : Fin (N + 1) → ℕ) :
    Quotient (orbitSetoid (k := k) d) ≃ { m : SuppArray (N : ℤ) ℤ // CMPlus d m } :=
  (orbitKostantPartitionEquiv d).trans (kostantPartitionCMPlusEquiv d)

/-- The bijection sends `⟦A⟧` to the (paper-predicate) Kostant partition
`kostantArrayOfRank (rankFn A)` of `A`. -/
@[simp] theorem orbitCMPlusEquiv_mk {d : Fin (N + 1) → ℕ} (A : Tuple (k := k) d) :
    (orbitCMPlusEquiv d (Quotient.mk _ A) : { m : SuppArray (N : ℤ) ℤ // CMPlus d m }).1
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

/-- The multiplicity-array bijection is non-vacuous: it sends `⟦tupleWitnessQ⟧` to the
second-difference array of its rank pattern. -/
example :
    (orbitDiffArrayEquiv dWitness (Quotient.mk (orbitSetoid dWitness) tupleWitnessQ)
      : RealizableDiffArray (k := ℚ) dWitness).1
      = diffArrayOfRank (rankFn dWitness tupleWitnessQ) := rfl

/-- The literal Kostant-partition bijection is non-vacuous: it sends `⟦tupleWitnessQ⟧` to the
literal Kostant partition `kostantArrayOfRank (rankFn tupleWitnessQ)` of the witness. -/
example :
    (orbitKostantPartitionEquiv dWitness (Quotient.mk (orbitSetoid dWitness) tupleWitnessQ)
      : KostantPartition (k := ℚ) dWitness).1
      = kostantArrayOfRank (rankFn dWitness tupleWitnessQ) := rfl

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

/-! ### The literal Kostant partition: the artifact is truncated away

`kostantArrayOfRank` truncates the lower triangle to `0`, so on the witness it lands **exactly** on
the paper's Kostant partition `RankPattern.mWitness` (`1` at `(0,0),(0,1),(1,2),(2,2)`, rest `0`) —
so the `-3` artifact is gone. The literal bijection `orbitKostantPartitionEquiv` fires here. -/

/-- The literal Kostant array of `rWitness` agrees with the full `diff`-array on `i ≤ j` (the six
upper-triangular multiplicities, the paper's `mWitness`). -/
example :
    (kostantArrayOfRank (N := 2) rWitness).1 0 0 = 1
      ∧ (kostantArrayOfRank (N := 2) rWitness).1 0 1 = 1
      ∧ (kostantArrayOfRank (N := 2) rWitness).1 1 1 = 0
      ∧ (kostantArrayOfRank (N := 2) rWitness).1 1 2 = 1
      ∧ (kostantArrayOfRank (N := 2) rWitness).1 0 2 = 0
      ∧ (kostantArrayOfRank (N := 2) rWitness).1 2 2 = 1 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    · rw [kostantArrayOfRank_of_le _ (by decide), diffArrayOfRank_val, diff_apply]; decide

/-- The artifact is **truncated away**: where the full `diff`-array had `-3`, the literal Kostant
array is `0`. So `kostantArrayOfRank rWitness` is nonnegative and `i ≤ j`-supported — a genuine
Kostant partition, not the `diff`-form. -/
example : (kostantArrayOfRank (N := 2) rWitness).1 1 0 = 0 :=
  kostantArrayOfRank_of_gt rWitness (by decide)

/-- The literal Kostant array of `rWitness` is the paper's Kostant partition `RankPattern.mWitness`
(the last of the six partitions of `(2,2,2)`) — exactly, on the whole `ℤ × ℤ` plane. Both sides are
supported on `i ≤ j`; there they are equal (`diff` of the witness rank pattern is `mWitness`), and
below the diagonal both are `0` (truncation vs. `mWitness`'s support). -/
example : (kostantArrayOfRank (N := 2) rWitness).1 = mWitness := by
  have hsupp : Supported (2 : ℤ) mWitness := supported_mWitness
  funext i j
  by_cases hij : i ≤ j
  · rw [kostantArrayOfRank_of_le _ hij, diffArrayOfRank_val,
      ← diff_cumul (2 : ℤ) mWitness hsupp.1 hsupp.2, diff_apply, diff_apply]
    have hpt : ∀ a b : ℤ, a ≤ b → (embedRank rWitness).1 a b = cumul (2 : ℤ) mWitness a b := by
      intro a b hab
      rcases lt_or_ge a 0 with ha | ha
      · rw [(embedRank rWitness).2.1 a b ha, (supported_cumul (2 : ℤ) mWitness).1 a b ha]
      rcases lt_or_ge (2 : ℤ) b with hb | hb
      · rw [(embedRank rWitness).2.2 a b hb, (supported_cumul (2 : ℤ) mWitness).2 a b hb]
      · have ha2 : a ≤ 2 := le_trans hab hb
        have hb0 : 0 ≤ b := le_trans ha hab
        interval_cases a <;> interval_cases b <;> first
          | omega
          | (simp only [embedRank, rWitness, cumul_apply, mWitness]; decide)
    rw [hpt i j hij, hpt i (j + 1) (by omega), hpt (i - 1) j (by omega),
      hpt (i - 1) (j + 1) (by omega)]
  · rw [kostantArrayOfRank_of_gt _ (lt_of_not_ge hij), mWitness,
      if_neg (by rintro ⟨_, h⟩; omega), if_neg (by rintro ⟨_, h⟩; omega),
      if_neg (by rintro ⟨h, _⟩; omega), if_neg (by rintro ⟨h, _⟩; omega)]

/-! ### The paper predicate `CMPlus` on the witness

`⟨mWitness, supported_mWitness⟩` (the paper's last partition of `(2,2,2)`, `m₀₀=m₀₁=m₁₂=m₂₂=1`)
satisfies the standalone `CMPlus dWitness`: it is nonnegative, `i ≤ j`-supported, and meets the
dimension equations `d_k = ∑_{i ≤ k ≤ j} m_{ij} = 2`. It is also the realized array of the
`(2,2,2)/ℚ` witness tuple (`= kostantArrayOfRank (rankFn dWitness tupleWitnessQ)`). -/

/-- The paper's `(2,2,2)` Kostant partition as a `SuppArray`. -/
def mWitnessSupp : SuppArray (2 : ℤ) ℤ := ⟨mWitness, supported_mWitness⟩

/-- **The paper predicate fires on the witness.** `mWitnessSupp` satisfies `CMPlus dWitness`: it is
a genuine Kostant partition of `(2,2,2)`. The dimension equations are `cumul 2 mWitness k k = 2`,
matching `d_k = 2` at each of the three diagonal vertices. -/
theorem cMPlus_mWitnessSupp : CMPlus dWitness mWitnessSupp := by
  refine ⟨⟨fun i j ↦ ?_, fun i j hij ↦ ?_⟩, fun k ↦ ?_⟩
  · -- nonnegative
    simp only [mWitnessSupp, mWitness]; split_ifs <;> norm_num
  · -- `i ≤ j`-supported (zero below the diagonal)
    simp only [mWitnessSupp, mWitness]; split_ifs with h₁ h₂ h₃ h₄ <;> omega
  · -- dimension equations `d_k = cumul 2 mWitness k k`, k = 0,1,2
    fin_cases k <;>
      · simp only [mWitnessSupp, dWitness]
        rw [cumul_apply]
        unfold mWitness
        decide

/-- The witness Kostant partition is **realized** — by its own `realizer` (`⊕ M^{mWitness}`):
`kostantArrayOfRank (rankFn dWitness (realizer mWitnessSupp _)) = mWitnessSupp`. So
`orbitCMPlusEquiv` lands on it from the orbit of that realizing tuple, confirming the reverse
direction concretely (over `ℚ`). -/
example :
    kostantArrayOfRank (rankFn dWitness (realizer (k := ℚ) mWitnessSupp cMPlus_mWitnessSupp))
      = mWitnessSupp :=
  kostantArrayOfRank_rankFn_realizer mWitnessSupp cMPlus_mWitnessSupp

end Witness

end DLNFibre.Core
