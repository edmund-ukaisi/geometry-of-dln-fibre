import DLNFibre.Core.OrbitCodim
import DLNFibre.Core.Orbit

/-!
# `DLNFibre.Core.SigmaStratification` — the orbit stratification of `Σ̄^r` (Phase G2)

The structural foundation of the `Σ^r`-geometry: the closed rank-`≤ r` product locus
`Σ̄^r = productRankLocusLE d r = {A | rank (mult A) ≤ r}` is the union of the orbit closures
`Ō_M = orbitRankLocus M` over the tuples `M` whose **corner** (the product rank `rank (mult M)`)
is `≤ r` (Le Halleur–Rimányi 2024, Cor 4.4 stratification, the `≤ r` / closure
convention — the genuine Zariski closure of `Σ^r`). This is the set-level equality

  `productRankLocusLE d r = ⋃ (M) (_ : (mult d M).rank ≤ r), orbitRankLocus M`,

and the equivalent membership characterisation `A ∈ Σ̄^r ↔ ∃ M, corner M ≤ r ∧ A ∈ Ō_M`.

**The two inclusions.**
* `⊇` is per-orbit (`orbitRankLocus_subset_productRankLocusLE`): if `A ∈ Ō_M` then
  `rank (mult A) = r_{0N}(A) ≤ r_{0N}(M) = rank (mult M) ≤ r`, the corner-entry monotonicity of the
  rank-pattern order that defines `orbitRankLocus`. The corner link `rank (mult A) = r_{0N}(A)` is
  `corner_rankPattern_eq_rank` below (G1).
* `⊆` is the trivial direction with this index — every `A ∈ Σ̄^r` lies in its **own** orbit closure
  `Ō_A` (`self_mem_orbitRankLocus`), whose corner is exactly `rank (mult A) ≤ r`. The bare set
  equality therefore needs **no** Gabriel/normal-form machinery; the genuine Gabriel content — that
  `A` lies in the orbit closure of a *canonical* normal form with the same rank pattern — is
  delivered separately as `exists_orbitRankLocus_mem_rankPattern_eq` (the brick a later thread uses
  to replace arbitrary tuples by Kostant/normal-form representatives and collapse the union to a
  finite distinct family via `orbitRankLocus_eq_of_rankPattern_eq`).

This closes step (ii) of the aggregate-reading roadmap recorded in `Core.CThetaGeometric`
("its orbit stratification `Σ^r = ⋃_M Ō_M`"); the per-orbit geometric codimension (deliverables 1,
2 there) feeds the downstream component / `θ` count (Phase G3 / θ), which consumes the union form
and the rank-pattern collapse lemma below.

**Typeclass.** `Field k` (the Gabriel normal-form existence `baseChange_normalForm` needs it; the
union equality and the per-orbit inclusion themselves use only the rank-pattern order, but the
module's headline keeps the uniform `Field` for the normal-form brick). No `IsAlgClosed`/`CharZero`:
this is a SET equality of determinantal loci, not a codimension statement. **Dependency rule:**
`Core` only — never import `DLNFibre.DLN`.
-/

namespace DLNFibre.Core

open Matrix

universe u

variable {k : Type u} [Field k] {N : ℕ}

/-! ## G1 — the corner rank-pattern entry is the product rank -/

/-- **G1.** The corner entry of the rank pattern is the rank of the full product:
`r_{0N}(A) = rank (mult A)`. The full product `mult d A` is the `[0, N]` interval sub-product
(`Submult.mult_eq_submult`), and `rankPattern d A 0 (last N)` is its rank by definition. -/
theorem corner_rankPattern_eq_rank (d : Fin (N + 1) → ℕ) (A : Tuple (k := k) d) :
    rankPattern d A 0 (Fin.last N) (Fin.zero_le _) = (mult d A).rank := by
  rw [rankPattern, ← mult_eq_submult]

/-! ## The per-orbit inclusion `Ō_M ⊆ Σ̄^r` (the `⊇` direction) -/

/-- The orbit closure `Ō_M = orbitRankLocus M` is contained in `Σ̄^r = productRankLocusLE d r` as
soon as its corner `rank (mult M) ≤ r`: for `A ∈ Ō_M` the corner-entry rank-pattern inequality gives
`rank (mult A) = r_{0N}(A) ≤ r_{0N}(M) = rank (mult M) ≤ r`. The `⊇` half of the stratification. -/
theorem orbitRankLocus_subset_productRankLocusLE (d : Fin (N + 1) → ℕ) {r : ℕ}
    {M : Tuple (k := k) d} (hM : (mult d M).rank ≤ r) :
    orbitRankLocus M ⊆ productRankLocusLE d r := by
  intro A hA
  rw [mem_productRankLocusLE, ← corner_rankPattern_eq_rank d A]
  exact (hA 0 (Fin.last N) (Fin.zero_le _)).trans
    ((corner_rankPattern_eq_rank d M).le.trans hM)

/-! ## The Gabriel set-membership brick (the canonical-representative content)

The bare union equality below takes `M := A`, so it does not need normal forms. The genuine Gabriel
content — that every tuple lies in the orbit closure of a *normal form* with the same rank pattern —
is this separate brick, the input a later thread uses to pass to canonical Kostant reps. -/

/-- **Gabriel set-membership.** Every tuple `A` lies in the orbit closure `Ō_M = orbitRankLocus M`
of a normal form `M` (a reindexed interval direct sum `⊕ M_{ab}`, `baseChange_normalForm`) with the
**same rank pattern** as `A`. Since `A` is `G_d`-equivalent to `M`, the rank patterns agree at every
`(i, j)` (`rankPattern_eq_of_smul`), so `A ∈ Ō_M` with equal corner entries (not merely `≤`). -/
theorem exists_orbitRankLocus_mem_rankPattern_eq (d : Fin (N + 1) → ℕ) (A : Tuple (k := k) d) :
    ∃ M : Tuple (k := k) d,
      (∀ (i j : Fin (N + 1)) (hij : i ≤ j), rankPattern d A i j hij = rankPattern d M i j hij)
        ∧ A ∈ orbitRankLocus M := by
  obtain ⟨L, h, P, hP, _, _⟩ := baseChange_normalForm A
  refine ⟨h ▸ intervalDirectSum (k := k) L, fun i j hij ↦ rankPattern_eq_of_smul P hP i j hij,
    fun i j hij ↦ le_of_eq (rankPattern_eq_of_smul P hP i j hij)⟩

/-! ## The rank-pattern collapse (for the downstream finite-family / component count)

`orbitRankLocus M` depends only on `rankPattern M`, so the all-`M` union below collapses onto the
finite set of *distinct* orbit closures. This is the equality a component argument uses to identify
`Ō_M` across different representatives of the same Kostant partition. -/

/-- The orbit closure depends only on the rank pattern: equal rank patterns give the same locus. The
collapse lemma the downstream component count uses to replace the all-`M` union by a finite distinct
family of orbit closures. -/
theorem orbitRankLocus_eq_of_rankPattern_eq {d : Fin (N + 1) → ℕ} {M M' : Tuple (k := k) d}
    (h : ∀ (i j : Fin (N + 1)) (hij : i ≤ j), rankPattern d M i j hij = rankPattern d M' i j hij) :
    orbitRankLocus M = orbitRankLocus M' := by
  ext A
  simp only [orbitRankLocus, Set.mem_setOf_eq]
  exact ⟨fun hA i j hij ↦ (h i j hij) ▸ hA i j hij, fun hA i j hij ↦ (h i j hij).symm ▸ hA i j hij⟩

/-! ## G2 — the stratification, membership and union forms -/

/-- **G2 (membership form).** `A` lies in the rank-`≤ r` product locus `Σ̄^r` iff it lies in some
orbit closure `Ō_M` whose corner `rank (mult M) ≤ r`. The `←` is
`orbitRankLocus_subset_productRankLocusLE`; the `→` takes `M := A` (`self_mem_orbitRankLocus`,
corner `rank (mult A) ≤ r`). -/
theorem mem_productRankLocusLE_iff_exists_mem_orbitRankLocus (d : Fin (N + 1) → ℕ) (r : ℕ)
    (A : Tuple (k := k) d) :
    A ∈ productRankLocusLE d r
      ↔ ∃ M : Tuple (k := k) d, (mult d M).rank ≤ r ∧ A ∈ orbitRankLocus M := by
  constructor
  · intro hA
    exact ⟨A, mem_productRankLocusLE.mp hA, self_mem_orbitRankLocus A⟩
  · rintro ⟨M, hM, hAM⟩
    exact orbitRankLocus_subset_productRankLocusLE d hM hAM

/-- **G2 (the stratification, union form).** The closed rank-`≤ r` product locus `Σ̄^r` is the union
of the orbit closures `Ō_M = orbitRankLocus M` over all tuples `M` whose corner `rank (mult M) ≤ r`
(Le Halleur–Rimányi 2024, Cor 4.4). `⊇` is `orbitRankLocus_subset_productRankLocusLE`; `⊆` places
`A` in its own orbit closure `Ō_A`. The union ranges over all corner-`≤ r` tuples; it collapses
onto a finite family of distinct orbit closures by `orbitRankLocus_eq_of_rankPattern_eq` (the form a
component count consumes). -/
theorem productRankLocusLE_eq_iUnion_orbitRankLocus (d : Fin (N + 1) → ℕ) (r : ℕ) :
    productRankLocusLE d r
      = ⋃ (M : Tuple (k := k) d) (_ : (mult d M).rank ≤ r), orbitRankLocus M := by
  ext A
  rw [Set.mem_iUnion₂, mem_productRankLocusLE_iff_exists_mem_orbitRankLocus]
  exact ⟨fun ⟨M, hM, hAM⟩ ↦ ⟨M, hM, hAM⟩, fun ⟨M, hM, hAM⟩ ↦ ⟨M, hM, hAM⟩⟩

section Witness

/-! ## Non-vacuity witness

`N = 2`, dimension vector `(2, 2, 2)`, over `ℚ` (a field — `baseChange_normalForm` needs `Field`).
With `A₁ = [[1,2],[0,1]]`, `A₂ = [[1,0],[3,1]]` the product `mult = A₂ A₁ = [[1,2],[3,7]]` is a
`2 × 2` matrix, so its rank is `≤ 2` and the tuple lies in `Σ̄^2`. The stratification and the
Gabriel membership brick fire on it: it lies in its own orbit closure `Ō_A` with corner `≤ 2`. -/

/-- Witness tuple `(A₁, A₂)` over `ℚ` (the `ℤ` witness cast into a field). -/
def tupleWitnessStratQ : Tuple (k := ℚ) dWitness := fun i ↦
  match i with
  | 0 => !![1, 2; 0, 1]
  | 1 => !![1, 0; 3, 1]

/-- The witness product has rank `≤ 2` (it is a `2 × 2` matrix), so the tuple lies in `Σ̄^2`. -/
theorem rank_mult_tupleWitnessStratQ_le : (mult dWitness tupleWitnessStratQ).rank ≤ 2 :=
  le_trans (Matrix.rank_le_height _) (by decide)

/-- The stratification fires on the witness: it lies in `Σ̄^2`, hence in some corner-`≤ 2` orbit
closure (its own). -/
example : tupleWitnessStratQ ∈ productRankLocusLE dWitness 2 := by
  rw [productRankLocusLE_eq_iUnion_orbitRankLocus, Set.mem_iUnion₂]
  exact ⟨tupleWitnessStratQ, rank_mult_tupleWitnessStratQ_le,
    self_mem_orbitRankLocus tupleWitnessStratQ⟩

/-- The Gabriel set-membership brick fires on the witness: it lies in the orbit closure of a normal
form with the same rank pattern. -/
example : ∃ M : Tuple (k := ℚ) dWitness,
    (∀ (i j : Fin 3) (hij : i ≤ j),
      rankPattern dWitness tupleWitnessStratQ i j hij = rankPattern dWitness M i j hij)
      ∧ tupleWitnessStratQ ∈ orbitRankLocus M :=
  exists_orbitRankLocus_mem_rankPattern_eq dWitness tupleWitnessStratQ

end Witness

end DLNFibre.Core
