import DLNFibre.Core.Gabriel
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Logic.Equiv.Sum

/-!
# `DLNFibre.Core.Orbit` — the complete `G_d`-invariant and the orbit ↔ Kostant bijection (Cor 2.9)

The capstone of rung 4 (Le Halleur–Rimányi 2024, Cor 2.9): the rank pattern is a **complete**
`G_d`-invariant on `Tuple d`, and `G_d`-orbits are in bijection with the realizable Kostant
partitions via `A ↦ diff (rankPattern A)`.

* `rankPattern_eq_of_smul` — the easy direction (orbit-invariance): `g • A = B ⟹` equal patterns.
* `orbit_of_rankPattern_eq` — **the crux**: equal rank patterns `⟹ ∃ g, g • A = B`. Built from the
  two tuples' barcodes (`hasBarcode_tuple`): equal rank patterns force equal bar
  multiplicities (`diff_cumul`), hence a birth/death-preserving relabelling `σ` of the bars; the
  barcode bases at each vertex then `Basis.equiv`-transport into an intertwiner `φ_t` of the chains,
  which `LinearMap.toMatrix'` turns into a base-change `P` with `P • A = B`.
* `rankPattern_eq_iff_orbit` — **the complete invariant**: `rankPattern A = rankPattern B ↔
  ∃ g, g • A = B`.
* `baseChange_normalForm` — **the Gabriel normal-form object** (cast-free): every tuple is
  `G_d`-equivalent to a reindexing of the interval direct sum `⊕ M^{m̄}` of its own bars.
The orbit ↔ Kostant bijection as a single `Equiv` object is packaged in `Core.OrbitKostant`
(`orbitKostantPartitionEquiv`, `orbitCMPlusEquiv`): the complete invariant above +
`RankPattern.cumulDiffEquiv` + the realizability in `baseChange_normalForm` assemble into a genuine
`Quotient (orbitSetoid d) ≃ KostantPartition d`.

**Typeclass.** `Field k` (the barcode existence; `Tuple`/`baseChange` themselves only need
`CommRing`). **Dependency rule:** never import `DLNFibre.DLN`.
-/

namespace DLNFibre.Core

open Matrix

universe u

variable {k : Type u} [Field k] {N : ℕ}

/-! ## The easy direction: the rank pattern is a `G_d`-invariant -/

/-- **Orbit-invariance of the rank pattern.** If `B = g • A` then `A` and `B` have the same rank
pattern at every `(i,j)`. The `←` half of the complete invariant; immediate from
`rankPattern_smul`. -/
theorem rankPattern_eq_of_smul {d : Fin (N + 1) → ℕ} {A B : Tuple (k := k) d}
    (P : BaseChangeGroup (k := k) d) (h : P • A = B) (i j : Fin (N + 1)) (hij : i ≤ j) :
    rankPattern d A i j hij = rankPattern d B i j hij := by
  rw [← h, rankPattern_smul]

/-! ## A birth/death-preserving relabelling of bars from equal multiplicities

Two Gabriel decompositions with the same bar-multiplicity array `barMult` (equivalently, the same
rank pattern, via `diff_cumul`) have the same number of bars of each `(birth, death)` type, so their
bar sets are related by a bijection `σ` preserving `(birth, death)`. Built from
`Equiv.sigmaFiberEquiv` over the `(birth, death)` fibres and `Fintype.equivOfCardEq` per fibre. -/

/-- Equality of `Fin (N+1)` after the `ℤ`-coercion is equality of the indices. -/
theorem fin_castInt_inj {x y : Fin (N + 1)} (h : (x : ℤ) = (y : ℤ)) : x = y :=
  Fin.val_injective (by exact_mod_cast h)

/-- `barMult` at a cast pair `(p.1, p.2)` counts the bars with that exact `(birth, death)`.
The bridge from the integer `barMult` array to a fintype cardinality of bars. -/
theorem barMult_eq_card_fiber (M : ℕ) (birth death : Fin M → Fin (N + 1))
    (p : Fin (N + 1) × Fin (N + 1)) :
    barMult M birth death (p.1 : ℤ) (p.2 : ℤ)
      = (Fintype.card {lam // birth lam = p.1 ∧ death lam = p.2} : ℤ) := by
  classical
  rw [barMult, Fintype.card_subtype, Finset.card_filter, Nat.cast_sum]
  refine Finset.sum_congr rfl fun lam _ ↦ ?_
  rw [singleDelta]
  by_cases h : birth lam = p.1 ∧ death lam = p.2
  · rw [if_pos ⟨by rw [h.1], by rw [h.2]⟩, if_pos h, Nat.cast_one]
  · rw [if_neg ?_, if_neg h, Nat.cast_zero]
    rintro ⟨h1, h2⟩
    exact h ⟨(fin_castInt_inj h1).symm, (fin_castInt_inj h2).symm⟩

/-- **The bar relabelling.** Two Gabriel decompositions with equal bar-multiplicity arrays have a
bijection `σ` of their bar index sets preserving `birth` and `death`. From `Equiv.ofFiberEquiv` over
the `(birth, death)` fibres (equal cardinalities by `barMult_eq_card_fiber`). -/
theorem exists_barEquiv {M₁ M₂ : ℕ} (b₁ e₁ : Fin M₁ → Fin (N + 1)) (b₂ e₂ : Fin M₂ → Fin (N + 1))
    (h : ∀ a b : Fin (N + 1),
      barMult M₁ b₁ e₁ (a : ℤ) (b : ℤ) = barMult M₂ b₂ e₂ (a : ℤ) (b : ℤ)) :
    ∃ σ : Fin M₁ ≃ Fin M₂, ∀ lam, b₂ (σ lam) = b₁ lam ∧ e₂ (σ lam) = e₁ lam := by
  classical
  set F₁ : Fin M₁ → Fin (N + 1) × Fin (N + 1) := fun lam ↦ (b₁ lam, e₁ lam) with hF₁
  set F₂ : Fin M₂ → Fin (N + 1) × Fin (N + 1) := fun lam ↦ (b₂ lam, e₂ lam) with hF₂
  have hcard : ∀ p, Fintype.card {lam // F₁ lam = p} = Fintype.card {lam // F₂ lam = p} := by
    intro p
    have e1 : {lam // F₁ lam = p} ≃ {lam // b₁ lam = p.1 ∧ e₁ lam = p.2} :=
      Equiv.subtypeEquivRight (fun lam ↦ by rw [hF₁, Prod.ext_iff])
    have e2 : {lam // F₂ lam = p} ≃ {lam // b₂ lam = p.1 ∧ e₂ lam = p.2} :=
      Equiv.subtypeEquivRight (fun lam ↦ by rw [hF₂, Prod.ext_iff])
    have hz : (Fintype.card {lam // b₁ lam = p.1 ∧ e₁ lam = p.2} : ℤ)
        = (Fintype.card {lam // b₂ lam = p.1 ∧ e₂ lam = p.2} : ℤ) := by
      rw [← barMult_eq_card_fiber, ← barMult_eq_card_fiber]; exact h p.1 p.2
    rw [Fintype.card_congr e1, Fintype.card_congr e2]
    exact_mod_cast hz
  refine ⟨Equiv.ofFiberEquiv (fun p ↦ Fintype.equivOfCardEq (hcard p)), fun lam ↦ ?_⟩
  have hF : F₂ (Equiv.ofFiberEquiv (fun p ↦ Fintype.equivOfCardEq (hcard p)) lam) = F₁ lam :=
    Equiv.ofFiberEquiv_map _ lam
  exact Prod.ext_iff.mp hF

/-! ## From an intertwiner of the chains to a base change

A family of linear automorphisms `φ_t : k^{d_t} ≃ₗ k^{d_t}` intertwining the `mulVecLin` chains of
`A` and `B` (`φ_{t+1} ∘ A_t = B_t ∘ φ_t`) is exactly a `G_d` base change carrying `A` to `B`:
`LinearMap.toMatrix'` turns the `φ_t` into invertible matrices `P_t`, and the intertwining identity
becomes `P_{t+1} A_t = B_t P_t`, i.e. `B_t = P_{t+1} A_t P_t⁻¹`. -/

/-- The invertible matrix of a linear automorphism of `k^m` (`toMatrix'` of the equiv, with the
inverse equiv as its matrix inverse). The bridge from `≃ₗ` to a `GLₘ = (Matrix _ _ k)ˣ` element. -/
def unitOfLinearEquiv {m : ℕ} (φ : (Fin m → k) ≃ₗ[k] (Fin m → k)) :
    (Matrix (Fin m) (Fin m) k)ˣ where
  val := LinearMap.toMatrix' φ.toLinearMap
  inv := LinearMap.toMatrix' φ.symm.toLinearMap
  val_inv := by
    rw [← LinearMap.toMatrix'_comp,
      show φ.toLinearMap ∘ₗ φ.symm.toLinearMap = LinearMap.id from by ext x; simp,
      LinearMap.toMatrix'_id]
  inv_val := by
    rw [← LinearMap.toMatrix'_comp,
      show φ.symm.toLinearMap ∘ₗ φ.toLinearMap = LinearMap.id from by ext x; simp,
      LinearMap.toMatrix'_id]

@[simp] theorem unitOfLinearEquiv_val {m : ℕ} (φ : (Fin m → k) ≃ₗ[k] (Fin m → k)) :
    (unitOfLinearEquiv φ).val = LinearMap.toMatrix' φ.toLinearMap := rfl

/-- **Intertwiner ⟹ base change.** If `φ_t : k^{d_t} ≃ₗ k^{d_t}` satisfy
`φ_{e.succ} ∘ (A_e)·lin = (B_e)·lin ∘ φ_{e.castSucc}` at every edge, then there is a `G_d` base
change `P` with `P • A = B` (`P_t := toMatrix' φ_t`). -/
theorem baseChange_of_intertwine {d : Fin (N + 1) → ℕ} (A B : Tuple (k := k) d)
    (φ : ∀ t, (Fin (d t) → k) ≃ₗ[k] (Fin (d t) → k))
    (hφ : ∀ e : Fin N, (φ e.succ).toLinearMap ∘ₗ (A e).mulVecLin
      = (B e).mulVecLin ∘ₗ (φ e.castSucc).toLinearMap) :
    ∃ P : BaseChangeGroup (k := k) d, P • A = B := by
  classical
  refine ⟨fun t ↦ unitOfLinearEquiv (φ t), ?_⟩
  funext e
  have key : (unitOfLinearEquiv (φ e.succ)).val * A e
      = B e * (unitOfLinearEquiv (φ e.castSucc)).val := by
    have hc := congrArg LinearMap.toMatrix' (hφ e)
    rw [LinearMap.toMatrix'_comp, LinearMap.toMatrix'_comp,
      ← Matrix.toLin'_apply', LinearMap.toMatrix'_toLin',
      ← Matrix.toLin'_apply', LinearMap.toMatrix'_toLin'] at hc
    simpa only [unitOfLinearEquiv_val] using hc
  rw [smul_eq_baseChange, baseChange_apply]
  calc (unitOfLinearEquiv (φ e.succ)).val * A e * Units.val ((unitOfLinearEquiv (φ e.castSucc))⁻¹)
      = B e * (unitOfLinearEquiv (φ e.castSucc)).val
          * Units.val ((unitOfLinearEquiv (φ e.castSucc))⁻¹) := by rw [key]
    _ = B e * ((unitOfLinearEquiv (φ e.castSucc)).val
          * Units.val ((unitOfLinearEquiv (φ e.castSucc))⁻¹)) := by rw [Matrix.mul_assoc]
    _ = B e * (1 : Matrix (Fin (d e.castSucc)) (Fin (d e.castSucc)) k) := by rw [Units.mul_inv]
    _ = B e := Matrix.mul_one _

/-! ## The crux: equal rank patterns ⟹ same orbit -/

/-- **Equal rank patterns ⟹ same `G_d`-orbit (Cor 2.9, hard direction).** Two tuples with equal
rank patterns lie in the same `G_d`-orbit. Both have a barcode (`hasBarcode_tuple`); equal rank
patterns force equal bar-multiplicity arrays (via the inversion `diff_cumul`), so a
`(birth, death)`-preserving relabelling `σ` of their bars exists (`exists_barEquiv`). The barcode
bases at each vertex (`barcodeVertexBasis`) then transport, through `Basis.equiv` along `σ`, into an
intertwiner `φ_t` of the two `mulVecLin` chains, which `baseChange_of_intertwine` turns into the
base change `P` with `P • A = B`. -/
theorem orbit_of_rankPattern_eq {d : Fin (N + 1) → ℕ} (A B : Tuple (k := k) d)
    (h : ∀ (i j : Fin (N + 1)) (hij : i ≤ j),
      rankPattern d A i j hij = rankPattern d B i j hij) :
    ∃ P : BaseChangeGroup (k := k) d, P • A = B := by
  classical
  obtain ⟨MA, bA, eA, lineA, hbdA, hsuppA, hnzA, htrajA, hdeathA, hindepA, hspanA⟩ :=
    hasBarcode_tuple d A
  obtain ⟨MB, bB, eB, lineB, hbdB, hsuppB, hnzB, htrajB, hdeathB, hindepB, hspanB⟩ :=
    hasBarcode_tuple d B
  -- the cumulative bar-multiplicity is the rank pattern, for each tuple
  have hcumA : ∀ (i j : Fin (N + 1)) (hij : i ≤ j),
      (rankPattern d A i j hij : ℤ) = cumul (N : ℤ) (barMult MA bA eA) (i : ℤ) (j : ℤ) := by
    intro i j hij
    rw [cumul_barMult_eq_card, rankPattern_eq_finrank_range_compMap]
    exact_mod_cast finrank_range_compMap_eq_card (chainSpace k d) (chainEdge d A)
      MA bA eA lineA hsuppA hnzA htrajA hdeathA hindepA hspanA i j hij
  have hcumB : ∀ (i j : Fin (N + 1)) (hij : i ≤ j),
      (rankPattern d B i j hij : ℤ) = cumul (N : ℤ) (barMult MB bB eB) (i : ℤ) (j : ℤ) := by
    intro i j hij
    rw [cumul_barMult_eq_card, rankPattern_eq_finrank_range_compMap]
    exact_mod_cast finrank_range_compMap_eq_card (chainSpace k d) (chainEdge d B)
      MB bB eB lineB hsuppB hnzB htrajB hdeathB hindepB hspanB i j hij
  -- the cumulative bar-multiplicities agree on the lower triangle
  -- (out-of-range ⟹ 0 by support; in-range ⟹ rankPattern, equal by hypothesis)
  have hRA : ∀ x y : ℤ, x ≤ y →
      cumul (N : ℤ) (barMult MA bA eA) x y = cumul (N : ℤ) (barMult MB bB eB) x y := by
    intro x y hxy
    rcases lt_or_ge x 0 with hx | hx
    · rw [(supported_cumul (N : ℤ) (barMult MA bA eA)).1 x y hx,
          (supported_cumul (N : ℤ) (barMult MB bB eB)).1 x y hx]
    rcases lt_or_ge (N : ℤ) y with hy | hy
    · rw [(supported_cumul (N : ℤ) (barMult MA bA eA)).2 x y hy,
          (supported_cumul (N : ℤ) (barMult MB bB eB)).2 x y hy]
    have hxN : x ≤ (N : ℤ) := le_trans hxy hy
    have hy0 : 0 ≤ y := le_trans hx hxy
    obtain ⟨i, hi⟩ : ∃ i : Fin (N + 1), (i : ℤ) = x :=
      ⟨⟨x.toNat, by omega⟩, by simp [Int.toNat_of_nonneg hx]⟩
    obtain ⟨j, hj⟩ : ∃ j : Fin (N + 1), (j : ℤ) = y :=
      ⟨⟨y.toNat, by omega⟩, by simp [Int.toNat_of_nonneg hy0]⟩
    have hij : i ≤ j := by have : (i : ℤ) ≤ (j : ℤ) := by rw [hi, hj]; exact hxy
                           exact_mod_cast this
    rw [← hi, ← hj, ← hcumA i j hij, ← hcumB i j hij, h i j hij]
  -- equal bar-multiplicity arrays on every (birth, death) pair
  have hbarMult : ∀ a b : Fin (N + 1),
      barMult MA bA eA (a : ℤ) (b : ℤ) = barMult MB bB eB (a : ℤ) (b : ℤ) := by
    intro a b
    by_cases hab : (a : ℤ) ≤ (b : ℤ)
    · rw [← diff_cumul (N : ℤ) (barMult MA bA eA) (supported_barMult MA bA eA).1
            (supported_barMult MA bA eA).2,
          ← diff_cumul (N : ℤ) (barMult MB bB eB) (supported_barMult MB bB eB).1
            (supported_barMult MB bB eB).2,
          diff_apply, diff_apply, hRA (a : ℤ) (b : ℤ) hab, hRA (a : ℤ) (b + 1) (by omega),
          hRA ((a : ℤ) - 1) (b : ℤ) (by omega), hRA ((a : ℤ) - 1) (b + 1) (by omega)]
    · have hempty : ∀ {M' : ℕ} (b' e' : Fin M' → Fin (N + 1)), (∀ lam, b' lam ≤ e' lam) →
          barMult M' b' e' (a : ℤ) (b : ℤ) = 0 := by
        intro M' b' e' hbd'
        rw [barMult]
        refine Finset.sum_eq_zero fun lam _ ↦ ?_
        rw [singleDelta, if_neg]
        rintro ⟨h1, h2⟩
        exact hab (by rw [h1, h2]; exact_mod_cast hbd' lam)
      rw [hempty bA eA hbdA, hempty bB eB hbdB]
  obtain ⟨σ, hσ⟩ := exists_barEquiv bA eA bB eB hbarMult
  -- the barcode bases at each vertex, and the apply lemmas
  set bvA : (t : Fin (N + 1)) → Module.Basis {lam // bA lam ≤ t ∧ t ≤ eA lam} k (Fin (d t) → k) :=
    fun t ↦ barcodeVertexBasis (chainSpace k d)
      MA bA eA lineA hsuppA hnzA hindepA hspanA t with hbvA
  set bvB : (t : Fin (N + 1)) → Module.Basis {lam // bB lam ≤ t ∧ t ≤ eB lam} k (Fin (d t) → k) :=
    fun t ↦ barcodeVertexBasis (chainSpace k d)
      MB bB eB lineB hsuppB hnzB hindepB hspanB t with hbvB
  have bvA_apply : ∀ (t : Fin (N + 1)) (s : {lam // bA lam ≤ t ∧ t ≤ eA lam}),
      bvA t s = lineA s.1 t := fun t s ↦ by
    rw [hbvA]; exact barcodeVertexBasis_apply (chainSpace k d)
      MA bA eA lineA hsuppA hnzA hindepA hspanA t s
  have bvB_apply : ∀ (t : Fin (N + 1)) (s : {lam // bB lam ≤ t ∧ t ≤ eB lam}),
      bvB t s = lineB s.1 t := fun t s ↦ by
    rw [hbvB]; exact barcodeVertexBasis_apply (chainSpace k d)
      MB bB eB lineB hsuppB hnzB hindepB hspanB t s
  -- the intertwiner: transport the barcode basis along σ at each vertex
  set φ : (t : Fin (N + 1)) → (Fin (d t) → k) ≃ₗ[k] (Fin (d t) → k) :=
    fun t ↦ (bvA t).equiv (bvB t) (σ.subtypeEquiv (fun lam ↦ by rw [(hσ lam).1, (hσ lam).2]))
    with hφdef
  have hφapply : ∀ (t : Fin (N + 1)) (lam : Fin MA) (hlam : bA lam ≤ t ∧ t ≤ eA lam),
      φ t (lineA lam t) = lineB (σ lam) t := by
    intro t lam hlam
    rw [hφdef, ← bvA_apply t ⟨lam, hlam⟩, Module.Basis.equiv_apply, bvB_apply]
    rfl
  refine baseChange_of_intertwine A B φ (fun e ↦ (bvA e.castSucc).ext (fun s ↦ ?_))
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
  rw [bvA_apply, hφapply e.castSucc s.1 s.2, ← chainEdge_apply, ← chainEdge_apply]
  by_cases hsj : e.succ ≤ eA s.1
  · rw [htrajA s.1 e s.2.1 hsj,
        hφapply e.succ s.1 ⟨le_trans s.2.1 (Fin.castSucc_le_succ e), hsj⟩,
        htrajB (σ s.1) e (by rw [(hσ s.1).1]; exact s.2.1) (by rw [(hσ s.1).2]; exact hsj)]
  · replace hsj := not_le.mp hsj
    rw [hdeathA s.1 e hsj, map_zero, hdeathB (σ s.1) e (by rw [(hσ s.1).2]; exact hsj)]

/-! ## The complete invariant (Cor 2.9) -/

/-- **The complete `G_d`-invariant (Le Halleur–Rimányi 2024, Cor 2.9).** Two tuples have the same
rank pattern iff they lie in the same `G_d`-orbit: `rankPattern A = rankPattern B ↔ ∃ g, g • A = B`.
The `←` is orbit-invariance (`rankPattern_eq_of_smul`), the `→` the barcode/`Basis.equiv`
construction (`orbit_of_rankPattern_eq`). The rank pattern is thus a *complete* isomorphism
invariant of type-A representations. -/
theorem rankPattern_eq_iff_orbit {d : Fin (N + 1) → ℕ} (A B : Tuple (k := k) d) :
    (∀ (i j : Fin (N + 1)) (hij : i ≤ j), rankPattern d A i j hij = rankPattern d B i j hij)
      ↔ ∃ P : BaseChangeGroup (k := k) d, P • A = B :=
  ⟨orbit_of_rankPattern_eq A B, fun ⟨P, hP⟩ i j hij ↦ rankPattern_eq_of_smul P hP i j hij⟩

/-! ## The Gabriel normal-form object

Every tuple is `G_d`-equivalent to a reindexing of the interval direct sum `⊕ M^{m̄}` of its own
bars — the genuine orbit normal form. The `foldDim`-cast is handled by a transport, kept off the
statement of the rank-pattern lemma it feeds. -/

/-- Transporting a tuple along a dimension-vector equality preserves the rank pattern. -/
theorem rankPattern_transport {d₀ d : Fin (N + 1) → ℕ} (h : d₀ = d) (X : Tuple (k := k) d₀)
    (i j : Fin (N + 1)) (hij : i ≤ j) :
    rankPattern d (h ▸ X) i j hij = rankPattern d₀ X i j hij := by
  subst h; rfl

/-- `foldDim` of a list is the pointwise sum of the interval dimension vectors. -/
theorem foldDim_eq_sum (L : List (Fin (N + 1) × Fin (N + 1))) (t : Fin (N + 1)) :
    foldDim L t = (L.map (fun p ↦ intervalDim p.1 p.2 t)).sum := by
  induction L with
  | nil => simp [foldDim]
  | cons p ps ih => simp [foldDim, ih]

/-- The dimension vector of the bar list `(birth, death)` of a barcode is the alive-bar count. -/
theorem foldDim_map_finRange (M : ℕ) (birth death : Fin M → Fin (N + 1)) (t : Fin (N + 1)) :
    foldDim ((List.finRange M).map (fun lam ↦ (birth lam, death lam))) t
      = (Finset.univ.filter (fun lam ↦ birth lam ≤ t ∧ t ≤ death lam)).card := by
  rw [foldDim_eq_sum, List.map_map, ← List.ofFn_eq_map, List.sum_ofFn, Finset.card_filter]
  refine Finset.sum_congr rfl fun lam _ ↦ ?_
  rw [Function.comp_apply, intervalDim]

/-- The list multiplicity array of the bar list `(birth, death)` is the barcode's `barMult`. -/
theorem multiplicityArray_map_finRange (M : ℕ) (birth death : Fin M → Fin (N + 1)) :
    multiplicityArray ((List.finRange M).map (fun lam ↦ (birth lam, death lam)))
      = barMult M birth death := by
  funext a b
  rw [multiplicityArray, barMult, List.map_map, ← List.ofFn_eq_map, List.sum_ofFn]
  refine Finset.sum_congr rfl fun lam _ ↦ ?_
  rw [Function.comp_apply, singleDelta]

/-- **Barcode ⟹ cumulative `barMult` = rank pattern.** Every tuple has a Gabriel decomposition
whose alive-bar count is the dimension vector (Kostant constraint) and whose cumulative
bar-multiplicity array is the rank pattern. The reusable barcode-to-`barMult` interface. -/
theorem exists_cumul_barMult {d : Fin (N + 1) → ℕ} (A : Tuple (k := k) d) :
    ∃ (M : ℕ) (birth death : Fin M → Fin (N + 1)),
      (∀ lam, birth lam ≤ death lam) ∧
      (∀ t, (Finset.univ.filter (fun lam ↦ birth lam ≤ t ∧ t ≤ death lam)).card = d t) ∧
      ∀ (i j : Fin (N + 1)) (hij : i ≤ j),
        (rankPattern d A i j hij : ℤ) = cumul (N : ℤ) (barMult M birth death) (i : ℤ) (j : ℤ) := by
  obtain ⟨M, birth, death, line, hbd, hsupp, hnz, htraj, hdeath, hindep, hspan⟩ :=
    hasBarcode_tuple d A
  have hcount : ∀ (i j : Fin (N + 1)) (hij : i ≤ j),
      rankPattern d A i j hij
        = (Finset.univ.filter (fun lam ↦ birth lam ≤ i ∧ j ≤ death lam)).card := fun i j hij ↦ by
    rw [rankPattern_eq_finrank_range_compMap]
    exact finrank_range_compMap_eq_card (chainSpace k d) (chainEdge d A)
      M birth death line hsupp hnz htraj hdeath hindep hspan i j hij
  refine ⟨M, birth, death, hbd, fun t ↦ ?_, fun i j hij ↦ ?_⟩
  · have ht := hcount t t le_rfl; rw [rankPattern_self] at ht; exact ht.symm
  · rw [cumul_barMult_eq_card, hcount i j hij]

/-- **The Gabriel normal-form object (rung 4, the orbit normal form).** Every tuple `A : Tuple d` is
`G_d`-equivalent to (a reindexing along `foldDim L = d` of) the interval direct sum `⊕_{(a,b) ∈ L}
M_{ab}` of its own bars — i.e. `∃ L (h : foldDim L = d) P, P • A = h ▸ intervalDirectSum L`. This is
the genuine Gabriel normal form (Le Halleur–Rimányi 2024, Thm 2.5 / Cor 2.9): the right-hand side is
manifestly a direct sum of interval modules, and on the upper triangle `i ≤ j` the cumulative count
of `L`'s multiplicity array recovers the rank pattern,
`(r_{ij} : ℤ) = cumul N (multiplicityArray L)`.
The multiplicities `multiplicityArray L` are therefore `diff` of that cumulative array
(`multiplicityArray_normalForm_eq_diff`, the `diff_cumul` inversion), pinning `L` from `A`'s rank
pattern. Proved from the complete invariant (`orbit_of_rankPattern_eq`) by exhibiting the interval
direct sum as a tuple with the same rank pattern as `A`. -/
theorem baseChange_normalForm {d : Fin (N + 1) → ℕ} (A : Tuple (k := k) d) :
    ∃ (L : List (Fin (N + 1) × Fin (N + 1))) (h : foldDim L = d) (P : BaseChangeGroup (k := k) d),
      P • A = h ▸ intervalDirectSum L ∧ (∀ p ∈ L, p.1 ≤ p.2) ∧
      ∀ (i j : Fin (N + 1)) (hij : i ≤ j),
        (rankPattern d A i j hij : ℤ) = cumul (N : ℤ) (multiplicityArray L) (i : ℤ) (j : ℤ) := by
  obtain ⟨M, birth, death, hbd, hkost, hcum⟩ := exists_cumul_barMult A
  set L : List (Fin (N + 1) × Fin (N + 1)) :=
    (List.finRange M).map (fun lam ↦ (birth lam, death lam)) with hL
  have hfold : foldDim L = d :=
    funext fun t ↦ (foldDim_map_finRange M birth death t).trans (hkost t)
  have hmult : multiplicityArray L = barMult M birth death := by
    rw [hL]; exact multiplicityArray_map_finRange M birth death
  have hrank : ∀ (i j : Fin (N + 1)) (hij : i ≤ j),
      rankPattern d A i j hij = rankPattern d (hfold ▸ intervalDirectSum (k := k) L) i j hij := by
    intro i j hij
    have hz : (rankPattern d A i j hij : ℤ)
        = (rankPattern d (hfold ▸ intervalDirectSum (k := k) L) i j hij : ℤ) := by
      rw [hcum i j hij, rankPattern_transport hfold (intervalDirectSum (k := k) L),
        rankPattern_intervalDirectSum_eq_cumul (K := k) L i j hij, hmult]
    exact_mod_cast hz
  obtain ⟨P, hP⟩ := orbit_of_rankPattern_eq A (hfold ▸ intervalDirectSum (k := k) L) hrank
  refine ⟨L, hfold, P, hP, ?_, fun i j hij ↦ ?_⟩
  · intro p hp
    rw [hL, List.mem_map] at hp
    obtain ⟨lam, _, rfl⟩ := hp
    exact hbd lam
  · rw [hcum i j hij, hmult]

/-- **The normal-form multiplicities are `diff` of the rank pattern (uniqueness, Cor 2.9).** The bar
list `L` of `baseChange_normalForm` has its multiplicity array pinned by `A`'s rank pattern: there
is a supported array `r` (the cumulative count `cumul N (multiplicityArray L)`) that equals the rank
pattern on the upper triangle `i ≤ j` and whose second finite difference is exactly
`multiplicityArray L` — so `multiplicityArray L = diff r` with `r = (rankPattern A)` on `i ≤ j`. The
`diff_cumul` inversion of the cumulative equality in `baseChange_normalForm`; makes the
"multiplicity array is `diff (rankPattern A)`" reading literal. -/
theorem multiplicityArray_normalForm_eq_diff {d : Fin (N + 1) → ℕ} (A : Tuple (k := k) d) :
    ∃ (L : List (Fin (N + 1) × Fin (N + 1))) (h : foldDim L = d) (P : BaseChangeGroup (k := k) d)
      (r : ℤ → ℤ → ℤ),
      P • A = h ▸ intervalDirectSum L ∧ (∀ p ∈ L, p.1 ≤ p.2) ∧
      Supported (N : ℤ) r ∧ diff r = multiplicityArray L ∧
      ∀ (i j : Fin (N + 1)) (hij : i ≤ j), r (i : ℤ) (j : ℤ) = (rankPattern d A i j hij : ℤ) := by
  obtain ⟨L, h, P, hP, hbd, hcum⟩ := baseChange_normalForm A
  refine ⟨L, h, P, cumul (N : ℤ) (multiplicityArray L), hP, hbd,
    supported_cumul (N : ℤ) (multiplicityArray L), ?_, fun i j hij ↦ (hcum i j hij).symm⟩
  -- `multiplicityArray L` is supported (it counts a finite bar list), so `cumul` inverts to it
  refine diff_cumul (N : ℤ) (multiplicityArray L) ?_ ?_
  · intro a b ha
    refine List.sum_eq_zero fun x hx ↦ ?_
    obtain ⟨p, _, rfl⟩ := List.mem_map.mp hx
    rw [if_neg]; rintro ⟨rfl, _⟩; exact absurd ha (not_lt.mpr (by positivity))
  · intro a b hb
    refine List.sum_eq_zero fun x hx ↦ ?_
    obtain ⟨p, _, rfl⟩ := List.mem_map.mp hx
    rw [if_neg]
    rintro ⟨_, rfl⟩
    exact absurd hb (not_lt.mpr (by exact_mod_cast Nat.lt_succ_iff.mp p.2.isLt))

section Witness

/-! ## Non-vacuity witnesses

The `(2,2,2)` tuple over `ℚ` (`Gabriel.tupleWitnessQ`). The crux `orbit_of_rankPattern_eq` fires on
a concrete pair (a genuine non-identity `GL₂(ℚ)` base change of the witness), and the normal-form
object `baseChange_normalForm` fires on the witness — so the complete invariant and the Gabriel
normal form are non-vacuous on concrete matrix tuples. -/

/-- A concrete `GL₂(ℚ)` element `!![1,1;0,1]` (determinant `1`), with explicit inverse. -/
def witnessUnitQ : (Matrix (Fin 2) (Fin 2) ℚ)ˣ where
  val := !![1, 1; 0, 1]
  inv := !![1, -1; 0, 1]
  val_inv := by ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  inv_val := by ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

/-- A concrete non-identity base change of the `(2,2,2)/ℚ` witness, at every vertex. -/
def witnessBaseChangeQ : BaseChangeGroup (k := ℚ) dWitness :=
  fun v ↦ match v with
    | 0 => witnessUnitQ
    | 1 => witnessUnitQ
    | 2 => witnessUnitQ

/-- The crux fires on a concrete pair: the witness and its non-identity base change have equal rank
patterns (`rankPattern_eq_of_smul`), so `orbit_of_rankPattern_eq` produces a base change between
them. -/
example : ∃ Q : BaseChangeGroup (k := ℚ) dWitness,
    Q • tupleWitnessQ = witnessBaseChangeQ • tupleWitnessQ :=
  orbit_of_rankPattern_eq tupleWitnessQ (witnessBaseChangeQ • tupleWitnessQ)
    (fun i j hij ↦ rankPattern_eq_of_smul witnessBaseChangeQ rfl i j hij)

/-- The complete invariant fires on the witness: equal rank patterns ↔ same orbit. -/
example : (∀ (i j : Fin 3) (hij : i ≤ j),
      rankPattern dWitness tupleWitnessQ i j hij
        = rankPattern dWitness (witnessBaseChangeQ • tupleWitnessQ) i j hij)
    ↔ ∃ Q : BaseChangeGroup (k := ℚ) dWitness,
        Q • tupleWitnessQ = witnessBaseChangeQ • tupleWitnessQ :=
  rankPattern_eq_iff_orbit tupleWitnessQ (witnessBaseChangeQ • tupleWitnessQ)

/-! ### A rank-one zero-product witness

The exposition's running rank-one example (Example 2.6): `(2,2,2)/ℚ` with edge factors
`A = diag(1,0)` and `B = diag(0,1)`, so `B·A = 0` and both factors have rank `1`. This is a
genuinely **degenerate** pair (`tupleWitnessQ` above is the invertible/full-rank pair). Its rank
pattern is `r_{01} = r_{12} = 1`, `r_{02} = 0`, diagonal `r_{kk} = 2`. -/

/-- The `(2,2,2)/ℚ` **rank-one zero-product** tuple: edge `0` is `diag(1,0) = !![1,0;0,0]`, edge `1`
is `diag(0,1) = !![0,0;0,1]`, so the product `B·A = 0` and each factor is rank `1` (the exposition's
Example 2.6). -/
def tupleWitnessRankOneQ : Tuple (k := ℚ) dWitness := fun i ↦
  match i with
  | 0 => !![1, 0; 0, 0]
  | 1 => !![0, 0; 0, 1]

/-- The first factor (`submult 0 1`) of the rank-one witness is `A = !![1,0;0,0]` (`multPrefix`
bridge: `submult 0 1 = A 0 · 1 = A 0`). -/
theorem submult_tupleWitnessRankOneQ_zero_one :
    submult dWitness tupleWitnessRankOneQ 0 (Fin.succ 0) (Fin.zero_le _) = !![1, 0; 0, 0] := by
  rw [submult_succ dWitness tupleWitnessRankOneQ 0 0 (Fin.zero_le _)]
  convert Matrix.mul_one (tupleWitnessRankOneQ 0) using 2

/-- The second factor (`submult 1 2`) of the rank-one witness is `B = !![0,0;0,1]`, a genuine
`i ≠ 0` slice via the composition step `submult_succ` and the diagonal `submult_self`. -/
theorem submult_tupleWitnessRankOneQ_one_two :
    submult dWitness tupleWitnessRankOneQ 1 (Fin.succ 1) (by decide) = !![0, 0; 0, 1] := by
  rw [submult_succ dWitness tupleWitnessRankOneQ 1 1 le_rfl]
  convert Matrix.mul_one (tupleWitnessRankOneQ 1) using 2

/-- The whole-chain product (`submult 0 2 = B·A`) of the rank-one witness is the zero matrix:
`!![0,0;0,1] · !![1,0;0,0] = 0`. The zero-product condition `B·A = 0`. -/
theorem submult_tupleWitnessRankOneQ_zero_two :
    submult dWitness tupleWitnessRankOneQ 0 (Fin.succ 1) (Fin.zero_le _) = 0 := by
  rw [submult_succ dWitness tupleWitnessRankOneQ 0 1 (by decide),
    show submult dWitness tupleWitnessRankOneQ 0 (Fin.castSucc 1) (by decide)
      = submult dWitness tupleWitnessRankOneQ 0 (Fin.succ 0) (Fin.zero_le _) from rfl,
    submult_tupleWitnessRankOneQ_zero_one]
  convert_to (!![0, 0; 0, 1] : Matrix (Fin 2) (Fin 2) ℚ) * !![1, 0; 0, 0] = 0 using 2
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two]

/-- `!![1,0;0,0]` has rank `1` (one nonzero diagonal entry), via `rank_diagonal`. -/
theorem rank_matWitnessA : (!![1, 0; 0, 0] : Matrix (Fin 2) (Fin 2) ℚ).rank = 1 := by
  rw [show (!![1, 0; 0, 0] : Matrix (Fin 2) (Fin 2) ℚ) = Matrix.diagonal ![1, 0] from by
    funext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.diagonal], Matrix.rank_diagonal,
    Fintype.card_congr (Equiv.subtypeEquivRight (q := fun i ↦ i = 0)
      (fun i ↦ by fin_cases i <;> simp)), Fintype.card_subtype_eq]

/-- `!![0,0;0,1]` has rank `1` (one nonzero diagonal entry), via `rank_diagonal`. -/
theorem rank_matWitnessB : (!![0, 0; 0, 1] : Matrix (Fin 2) (Fin 2) ℚ).rank = 1 := by
  rw [show (!![0, 0; 0, 1] : Matrix (Fin 2) (Fin 2) ℚ) = Matrix.diagonal ![0, 1] from by
    funext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.diagonal], Matrix.rank_diagonal,
    Fintype.card_congr (Equiv.subtypeEquivRight (q := fun i ↦ i = 1)
      (fun i ↦ by fin_cases i <;> simp)), Fintype.card_subtype_eq]

/-- **The rank-one witness rank pattern.** `r_{01} = r_{12} = 1` (each factor has one nonzero
diagonal entry), `r_{02} = 0` (`B·A = 0`), and the diagonal `r_{kk} = 2`. A genuinely degenerate
zero-product pair, distinct from the full-rank `tupleWitnessQ`. -/
theorem rankPattern_tupleWitnessRankOneQ :
    rankPattern dWitness tupleWitnessRankOneQ 0 1 (by decide) = 1
      ∧ rankPattern dWitness tupleWitnessRankOneQ 1 2 (by decide) = 1
      ∧ rankPattern dWitness tupleWitnessRankOneQ 0 2 (by decide) = 0
      ∧ rankPattern dWitness tupleWitnessRankOneQ 0 0 le_rfl = 2
      ∧ rankPattern dWitness tupleWitnessRankOneQ 1 1 le_rfl = 2
      ∧ rankPattern dWitness tupleWitnessRankOneQ 2 2 le_rfl = 2 := by
  refine ⟨?_, ?_, ?_, rankPattern_self dWitness tupleWitnessRankOneQ 0,
    rankPattern_self dWitness tupleWitnessRankOneQ 1,
    rankPattern_self dWitness tupleWitnessRankOneQ 2⟩
  · rw [show rankPattern dWitness tupleWitnessRankOneQ 0 1 (by decide)
        = rankPattern dWitness tupleWitnessRankOneQ 0 (Fin.succ 0) (Fin.zero_le _) from rfl,
      rankPattern, submult_tupleWitnessRankOneQ_zero_one]; exact rank_matWitnessA
  · rw [show rankPattern dWitness tupleWitnessRankOneQ 1 2 (by decide)
        = rankPattern dWitness tupleWitnessRankOneQ 1 (Fin.succ 1) (by decide) from rfl,
      rankPattern, submult_tupleWitnessRankOneQ_one_two]; exact rank_matWitnessB
  · rw [show rankPattern dWitness tupleWitnessRankOneQ 0 2 (by decide)
        = rankPattern dWitness tupleWitnessRankOneQ 0 (Fin.succ 1) (Fin.zero_le _) from rfl,
      rankPattern, submult_tupleWitnessRankOneQ_zero_two, Matrix.rank_zero]

/-- The Gabriel normal form fires on the **rank-one** witness too: the degenerate zero-product pair
is `G_d`-equivalent to a reindexing of the interval direct sum of its own bars (here the bars
`M_{00}, M_{01}, M_{12}, M_{22}` forced by its rank pattern). The complete invariant is non-vacuous
on a genuinely degenerate tuple, not only the full-rank `tupleWitnessQ`. -/
example : ∃ (L : List (Fin 3 × Fin 3)) (h : foldDim L = dWitness)
    (P : BaseChangeGroup (k := ℚ) dWitness),
      P • tupleWitnessRankOneQ = h ▸ intervalDirectSum L := by
  obtain ⟨L, h, P, hP, _, _⟩ := baseChange_normalForm tupleWitnessRankOneQ
  exact ⟨L, h, P, hP⟩

/-- The Gabriel normal-form object fires on the witness: `tupleWitnessQ` is `G_d`-equivalent to a
reindexing of an interval direct sum of its own bars. -/
example : ∃ (L : List (Fin 3 × Fin 3)) (h : foldDim L = dWitness)
    (P : BaseChangeGroup (k := ℚ) dWitness), P • tupleWitnessQ = h ▸ intervalDirectSum L := by
  obtain ⟨L, h, P, hP, _, _⟩ := baseChange_normalForm tupleWitnessQ
  exact ⟨L, h, P, hP⟩

end Witness

end DLNFibre.Core
