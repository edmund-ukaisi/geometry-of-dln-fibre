import DLNFibre.Core.Barcode
import DLNFibre.Core.BaseChange
import DLNFibre.Core.IntervalModule
import Mathlib.LinearAlgebra.Matrix.ToLin

/-!
# `DLNFibre.Core.Gabriel` — the barcode existence carried to concrete `Tuple`s (rung 4 completion)

The abstract-chain barcode existence theorem (`Core.Barcode.hasBarcode_top`, the existence half of
type-A Gabriel) instantiated at the **concrete chain attached to a matrix tuple**:

* `chainSpace k d t := Fin (d t) → k` — the vertex spaces `k^{d_t}`;
* `chainEdge d A t := (A t).mulVecLin` — the edge maps, the linear map of each matrix factor.

The bridge `compMap_chainEdge` identifies the abstract composite `compMap` with
`(submult d A i j).mulVecLin` (the matrix sub-product turned into a linear map), so the abstract
machinery and the `Setup`/`Submult`/`BaseChange` matrix API speak about the same maps.

**Headlines.**
- `compMap_chainEdge` — the composite of the concrete chain is the `mulVecLin` of the matrix
  sub-product `submult d A i j`. The cast-free bridge between the two encodings.
- `hasBarcode_tuple` — **every `Tuple` over a field has a barcode**: the existence half of type-A
  Gabriel (Le Halleur–Rimányi 2024, Thm 2.5) realised on the concrete chain of a matrix tuple.
- `rankPattern_eq_finrank_range_compMap` — the matrix rank pattern `r_{ij}` equals the finrank of
  the range of the abstract composite; ties `rankPattern` (Submult) to the barcode world.

**Scope.** This is the **existence** content (and its bridge to `rankPattern`). Uniqueness of the
multiplicities and the explicit `g·A = ⊕ M^m` change-of-basis object are separate steps; see the
thread findings for what lands here.

**Typeclass.** `Field k` (the barcode existence needs the splitting fact's `NoZeroSMulDivisors`).
**Dependency rule:** never import `DLNFibre.DLN`.
-/

namespace DLNFibre.Core

open Matrix

universe u

variable {k : Type u} [Field k] {N : ℕ}

/-! ## The concrete chain attached to a `Tuple`

A tuple `A : Tuple d` is a chain of finite-dimensional `k`-vector spaces `k^{d_0} → … → k^{d_N}`
with edge maps the `mulVecLin` of each matrix factor. This is the `V_i := Fin (d i) → k`,
`f_i := mulVecLin (A i)` instantiation of the abstract chain of `Core.Barcode`. -/

/-- Vertex spaces of the concrete chain of a tuple over `d`: `k^{d_t}` at vertex `t`. -/
abbrev chainSpace (k : Type u) [Field k] (d : Fin (N + 1) → ℕ) : Fin (N + 1) → Type u :=
  fun t ↦ Fin (d t) → k

/-- Edge maps of the concrete chain: `f_t = mulVecLin (A_t)`, the linear map of the matrix `A_t`. -/
def chainEdge (d : Fin (N + 1) → ℕ) (A : Tuple (k := k) d) :
    ∀ t : Fin N, chainSpace k d t.castSucc →ₗ[k] chainSpace k d t.succ :=
  fun t ↦ (A t).mulVecLin

/-- The edge map of the concrete chain is the matrix's `mulVecLin` (definitional unfolding). -/
theorem chainEdge_apply (d : Fin (N + 1) → ℕ) (A : Tuple (k := k) d) (t : Fin N) :
    chainEdge d A t = (A t).mulVecLin := rfl

/-- **The bridge.** The abstract composite of the concrete chain equals the `mulVecLin` of the
matrix sub-product: `compMap (chainSpace) (chainEdge) i j = (submult d A i j).mulVecLin`. Proved by
induction on the upper index `j` through `compMap_succ`/`submult_succ` and `Matrix.mulVecLin_mul`.
The cast-free identification of the abstract-chain and matrix encodings of the sub-product. -/
theorem compMap_chainEdge (d : Fin (N + 1) → ℕ) (A : Tuple (k := k) d) (i j : Fin (N + 1))
    (hij : i ≤ j) :
    compMap (chainSpace k d) (chainEdge d A) i j hij = (submult d A i j hij).mulVecLin := by
  induction j using Fin.induction with
  | zero =>
    obtain rfl : i = 0 := Fin.le_zero_iff.mp hij
    rw [compMap_self, submult_self, Matrix.mulVecLin_one]
  | succ p ih =>
    rcases eq_or_lt_of_le hij with rfl | hlt
    · rw [compMap_self, submult_self, Matrix.mulVecLin_one]
    · have hip : i ≤ p.castSucc := Fin.le_castSucc_iff.mpr hlt
      rw [compMap_succ (chainSpace k d) (chainEdge d A) i p hip, ih hip,
        submult_succ d A i p hip, Matrix.mulVecLin_mul]
      rfl

/-! ## The barcode existence theorem on a `Tuple` -/

/-- **The barcode existence theorem on a `Tuple` (rung 4 completion).** Every matrix tuple over a
field, viewed as the concrete chain `k^{d_0} → … → k^{d_N}` of `mulVecLin` maps, has a barcode: an
internal direct sum of interval-module lines at every vertex (`Core.Barcode.HasBarcode`). This is
the **existence** half of type-A Gabriel (Le Halleur–Rimányi 2024, Thm 2.5) carried from the
abstract chain down to the concrete `Tuple` encoding. Existence only — uniqueness of the
multiplicities and the explicit `g·A = ⊕ M^m` object are separate. -/
theorem hasBarcode_tuple (d : Fin (N + 1) → ℕ) (A : Tuple (k := k) d) :
    HasBarcode (chainSpace k d) (chainEdge d A) (fun _ ↦ ⊤) :=
  hasBarcode_top (chainSpace k d) (chainEdge d A)

/-! ## Bridge to the matrix rank pattern -/

/-- **The rank pattern is the range-rank of the abstract composite.** The matrix rank pattern
`r_{ij} = rank (submult d A i j)` equals the finrank of the range of the abstract chain's composite
`compMap i j`. Immediate from the bridge `compMap_chainEdge` and the definition of `Matrix.rank`.
Ties `Submult.rankPattern` to the barcode world (`Core.Barcode`). -/
theorem rankPattern_eq_finrank_range_compMap (d : Fin (N + 1) → ℕ) (A : Tuple (k := k) d)
    (i j : Fin (N + 1)) (hij : i ≤ j) :
    rankPattern d A i j hij
      = Module.finrank k (LinearMap.range (compMap (chainSpace k d) (chainEdge d A) i j hij)) := by
  rw [rankPattern, Matrix.rank, compMap_chainEdge]

/-! ## The range-rank of a composite is the number of bars alive across `[i,j]`

The barcode's geometric payload for the rank pattern (the *completeness* direction of Prop 3.1b,
disclaimed as out of scope in `IntervalModule`): for a chain carrying a barcode, the rank of the
composite `compMap i j` — equivalently `rankPattern d A i j` for a tuple — counts exactly the bars
`λ` with `birth λ ≤ i` and `j ≤ death λ` (those alive at `i` and surviving to `j`). This works
purely from the `HasBarcode` data, with no change-of-basis matrix. -/

section AbstractRank

variable {k : Type u} [Field k] {N : ℕ}
  (V : Fin (N + 1) → Type u) [∀ t, AddCommGroup (V t)] [∀ t, Module k (V t)]
  (f : ∀ t : Fin N, V t.castSucc →ₗ[k] V t.succ)

/-- A single barcode line spans a **subrepresentation** `t ↦ k·(line t)`: each edge sends the line
to a scalar multiple of the next line (its multiple `line e.succ` on an active edge by `htraj`, or
`0` past death by `hdeath`, or `0` from a vanishing source off the bar). The structural fact behind
"the image of a line stays on its own bar". -/
theorem lineFamily_isSubrep (b e : Fin (N + 1)) (ln : ∀ t, V t)
    (hsupp : ∀ t, ¬ (b ≤ t ∧ t ≤ e) → ln t = 0)
    (htraj : ∀ edge : Fin N, b ≤ edge.castSucc → edge.succ ≤ e →
      f edge (ln edge.castSucc) = ln edge.succ)
    (hdeath : ∀ edge : Fin N, e < edge.succ → f edge (ln edge.castSucc) = 0) :
    IsSubrep V f (fun t ↦ k ∙ ln t) := by
  intro edge
  rw [Submodule.map_le_iff_le_comap]
  intro x hx
  obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hx
  rw [Submodule.mem_comap, map_smul]
  refine Submodule.smul_mem _ _ ?_
  by_cases hed : e < edge.succ
  · rw [hdeath edge hed]; exact Submodule.zero_mem _
  · by_cases hbe : b ≤ edge.castSucc
    · rw [htraj edge hbe (not_lt.mp hed)]; exact Submodule.mem_span_singleton_self _
    · rw [hsupp edge.castSucc (by rw [not_and_or]; exact Or.inl hbe), map_zero]
      exact Submodule.zero_mem _

/-- **Transport along a bar.** Inside its interval (`b ≤ i ≤ t ≤ e`), the composite carries the line
forward: `compMap i t (ln i) = ln t`. The forward trajectory of the bar; induction on `t` through
`compMap_succ` and the active-edge clause `htraj`. -/
theorem compMap_line_eq_of_alive (b e : Fin (N + 1)) (ln : ∀ t, V t)
    (htraj : ∀ edge : Fin N, b ≤ edge.castSucc → edge.succ ≤ e →
      f edge (ln edge.castSucc) = ln edge.succ)
    {i : Fin (N + 1)} (hbi : b ≤ i) :
    ∀ {t : Fin (N + 1)} (hit : i ≤ t), t ≤ e → compMap V f i t hit (ln i) = ln t := by
  intro t
  induction t using Fin.induction with
  | zero =>
    intro hit _
    obtain rfl : i = 0 := Fin.le_zero_iff.mp hit
    rw [show compMap V f 0 0 hit = LinearMap.id from compMap_self V f 0]; rfl
  | succ p ih =>
    intro hit hte
    rcases eq_or_lt_of_le hit with rfl | hlt
    · rw [show compMap V f p.succ p.succ hit = LinearMap.id from compMap_self V f p.succ]; rfl
    · have hip : i ≤ p.castSucc := Fin.le_castSucc_iff.mpr hlt
      rw [compMap_succ V f i p hip, LinearMap.comp_apply,
        ih hip (le_trans (Fin.castSucc_le_succ p) hte)]
      exact htraj p (le_trans hbi hip) hte

/-- **The range-rank of a composite is the number of bars alive across `[i,j]`.** For a chain
carrying a barcode (the `HasBarcode (fun _ ↦ ⊤)` data, here taken as explicit hypotheses), the
finrank of the range of `compMap i j` equals the number of bars `λ` with `birth λ ≤ i` and
`j ≤ death λ`. The bars surviving the whole interval contribute their (independent) lines to the
image; the others map to zero (off-support source, or killed past death via the single-line
subrep). The geometric content behind `r_{ij} = cumul m` for an arbitrary tuple. -/
theorem finrank_range_compMap_eq_card [∀ t, FiniteDimensional k (V t)]
    (M : ℕ) (birth death : Fin M → Fin (N + 1)) (line : Fin M → ∀ t, V t)
    (hsupp : ∀ lam t, ¬ (birth lam ≤ t ∧ t ≤ death lam) → line lam t = 0)
    (hnz : ∀ lam t, birth lam ≤ t → t ≤ death lam → line lam t ≠ 0)
    (htraj : ∀ lam (edge : Fin N), birth lam ≤ edge.castSucc → edge.succ ≤ death lam →
      f edge (line lam edge.castSucc) = line lam edge.succ)
    (hdeath : ∀ lam (edge : Fin N), death lam < edge.succ → f edge (line lam edge.castSucc) = 0)
    (hindep : ∀ t, iSupIndep (fun lam ↦ k ∙ line lam t))
    (hspan : ∀ t, ⨆ lam, k ∙ line lam t = ⊤)
    (i j : Fin (N + 1)) (hij : i ≤ j) :
    Module.finrank k (LinearMap.range (compMap V f i j hij))
      = (Finset.univ.filter (fun lam ↦ birth lam ≤ i ∧ j ≤ death lam)).card := by
  classical
  -- The image of each surviving bar's source line is its line at `j`.
  have g_eq : ∀ lam, birth lam ≤ i → j ≤ death lam →
      compMap V f i j hij (line lam i) = line lam j := fun lam hbi hjd =>
    compMap_line_eq_of_alive V f (birth lam) (death lam) (line lam) (htraj lam) hbi hij hjd
  -- Every other bar maps its source line to zero.
  have g_zero : ∀ lam, ¬ (birth lam ≤ i ∧ j ≤ death lam) →
      compMap V f i j hij (line lam i) = 0 := by
    intro lam hlam
    rcases not_and_or.mp hlam with hbi | hjd
    · -- not yet born at `i`: the source line is already zero
      rw [hsupp lam i (fun h => hbi h.1), map_zero]
    · -- dead before `j`: the image lands in `k ∙ line lam j` with `line lam j = 0`
      have hsub : IsSubrep V f (fun t ↦ k ∙ line lam t) :=
        lineFamily_isSubrep V f (birth lam) (death lam) (line lam) (hsupp lam) (htraj lam)
          (hdeath lam)
      have hmem : compMap V f i j hij (line lam i) ∈ (k ∙ line lam j) :=
        compMap_mem V f hsub hij (Submodule.mem_span_singleton_self _)
      rw [hsupp lam j (fun h => hjd h.2), Submodule.span_zero_singleton] at hmem
      exact Submodule.mem_bot k |>.mp hmem
  -- map of a span singleton through the composite
  have hmap_sing : ∀ v : V i,
      Submodule.map (compMap V f i j hij) (k ∙ v) = k ∙ (compMap V f i j hij v) := by
    intro v; rw [Submodule.map_span, Set.image_singleton]
  -- the range is the span of the surviving lines at `j`
  have hrange : LinearMap.range (compMap V f i j hij)
      = Submodule.span k (Set.range (fun s : {lam // birth lam ≤ i ∧ j ≤ death lam} ↦
          line s.1 j)) := by
    rw [LinearMap.range_eq_map, ← hspan i, Submodule.map_iSup]
    simp only [hmap_sing]
    apply le_antisymm
    · refine iSup_le fun lam => ?_
      by_cases hlam : birth lam ≤ i ∧ j ≤ death lam
      · rw [g_eq lam hlam.1 hlam.2, Submodule.span_singleton_le_iff_mem]
        exact Submodule.subset_span ⟨⟨lam, hlam⟩, rfl⟩
      · rw [g_zero lam hlam, Submodule.span_zero_singleton]; exact bot_le
    · rw [Submodule.span_le]
      rintro _ ⟨s, rfl⟩
      refine Submodule.mem_iSup_of_mem s.1 ?_
      rw [g_eq s.1 s.2.1 s.2.2]
      exact Submodule.mem_span_singleton_self _
  -- the surviving lines are linearly independent (a sub-family of the independent family at `j`)
  have hli : LinearIndependent k (fun s : {lam // birth lam ≤ i ∧ j ≤ death lam} ↦ line s.1 j) :=
    iSupIndep.linearIndependent _ ((hindep j).comp Subtype.val_injective)
      (fun s => Submodule.mem_span_singleton_self _)
      (fun s => hnz s.1 j (le_trans s.2.1 hij) s.2.2)
  rw [hrange, finrank_span_eq_card hli, Fintype.card_subtype]

/-- **The barcode lines alive at a vertex form a basis of `V_t`.** Indexed by the bars `λ` alive at
`t` (`birth λ ≤ t ≤ death λ`), the lines `line λ t` are independent (a sub-family of the vertex-`t`
independent family) and span `V_t` (the dead lines vanish, so the alive ones still span `⊤`). The
change-of-basis datum of the Gabriel normal form (design §1.1, "the lines at each vertex form a
basis") — the columns of the per-vertex base-change matrix `Q_t`. -/
noncomputable def barcodeVertexBasis
    (M : ℕ) (birth death : Fin M → Fin (N + 1)) (line : Fin M → ∀ t, V t)
    (hsupp : ∀ lam t, ¬ (birth lam ≤ t ∧ t ≤ death lam) → line lam t = 0)
    (hnz : ∀ lam t, birth lam ≤ t → t ≤ death lam → line lam t ≠ 0)
    (hindep : ∀ t, iSupIndep (fun lam ↦ k ∙ line lam t))
    (hspan : ∀ t, ⨆ lam, k ∙ line lam t = ⊤) (t : Fin (N + 1)) :
    Module.Basis {lam // birth lam ≤ t ∧ t ≤ death lam} k (V t) :=
  Module.Basis.mk
    (iSupIndep.linearIndependent _ ((hindep t).comp Subtype.val_injective)
      (fun _ ↦ Submodule.mem_span_singleton_self _) (fun s ↦ hnz s.1 t s.2.1 s.2.2))
    (by
      rw [← hspan t]
      refine iSup_le fun lam ↦ ?_
      by_cases hlam : birth lam ≤ t ∧ t ≤ death lam
      · rw [Submodule.span_singleton_le_iff_mem]
        exact Submodule.subset_span ⟨⟨lam, hlam⟩, rfl⟩
      · rw [hsupp lam t hlam, Submodule.span_zero_singleton]; exact bot_le)

/-- The basis vector at bar `s` is exactly that bar's line at `t` (`Basis.mk` unfolding). -/
theorem barcodeVertexBasis_apply
    (M : ℕ) (birth death : Fin M → Fin (N + 1)) (line : Fin M → ∀ t, V t)
    (hsupp : ∀ lam t, ¬ (birth lam ≤ t ∧ t ≤ death lam) → line lam t = 0)
    (hnz : ∀ lam t, birth lam ≤ t → t ≤ death lam → line lam t ≠ 0)
    (hindep : ∀ t, iSupIndep (fun lam ↦ k ∙ line lam t))
    (hspan : ∀ t, ⨆ lam, k ∙ line lam t = ⊤) (t : Fin (N + 1))
    (s : {lam // birth lam ≤ t ∧ t ≤ death lam}) :
    barcodeVertexBasis V M birth death line hsupp hnz hindep hspan t s = line s.1 t :=
  Module.Basis.mk_apply _ _ _

end AbstractRank

/-- **The rank pattern is the bar-count of a Gabriel decomposition (completeness of Prop 3.1b).**
Every tuple over a field admits a Gabriel decomposition — a finite family of bars `(birth, death)`
with `birth ≤ death` — whose rank pattern is recovered as a bar count at *every* `(i,j)`:
`r_{ij} = #{λ : birth λ ≤ i ∧ j ≤ death λ}`. This is the *completeness* direction of
Le Halleur–Rimányi 2024, Prop 3.1b — the statement that an **arbitrary** tuple's rank pattern is the
cumulative count of its Gabriel multiplicities, disclaimed as out of scope in `IntervalModule`
(which only does the constructed-direct-sum side). Read off the barcode (`hasBarcode_tuple`) via the
range-rank/bar-count identity; no change-of-basis matrix. -/
theorem exists_barcode_rankPattern (d : Fin (N + 1) → ℕ) (A : Tuple (k := k) d) :
    ∃ (M : ℕ) (birth death : Fin M → Fin (N + 1)),
      (∀ lam, birth lam ≤ death lam) ∧
      (∀ t, (Finset.univ.filter (fun lam ↦ birth lam ≤ t ∧ t ≤ death lam)).card = d t) ∧
      ∀ (i j : Fin (N + 1)) (hij : i ≤ j),
        rankPattern d A i j hij
          = (Finset.univ.filter (fun lam ↦ birth lam ≤ i ∧ j ≤ death lam)).card := by
  obtain ⟨M, birth, death, line, hbd, hsupp, hnz, htraj, hdeath, hindep, hspan⟩ :=
    hasBarcode_tuple d A
  have hrk : ∀ (i j : Fin (N + 1)) (hij : i ≤ j),
      rankPattern d A i j hij
        = (Finset.univ.filter (fun lam ↦ birth lam ≤ i ∧ j ≤ death lam)).card := by
    intro i j hij
    rw [rankPattern_eq_finrank_range_compMap]
    exact finrank_range_compMap_eq_card (chainSpace k d) (chainEdge d A) M birth death line
      hsupp hnz htraj hdeath hindep hspan i j hij
  refine ⟨M, birth, death, hbd, fun t => ?_, hrk⟩
  -- the Kostant dimension constraint: at `(t,t)` the bar count is `r_{tt} = d_t`
  have := (hrk t t le_rfl).symm
  rwa [rankPattern_self] at this

/-! ## Uniqueness: the multiplicities are forced by the rank pattern

The bar count `r_{ij} = #{λ : birth λ ≤ i ∧ j ≤ death λ}` is `cumul N` of the **bar-multiplicity
array** `m̄_{ab} = #{λ : birth λ = a ∧ death λ = b}` (the Gabriel multiplicities). Feeding this into
the already-formalised inversion `RankPattern.diff_cumul` forces `m̄ = diff (rank pattern)`: the
multiplicities are a function of the rank pattern (Le Halleur–Rimányi 2024, the uniqueness half of
Cor 2.9). Pure combinatorics on `birth`/`death`; reuses `IntervalModule.singleDelta` /
`cumul_singleDelta`. -/

/-- `cumul N` commutes with a finite sum of arrays (it is a double `Finset.sum`). -/
theorem cumul_finsetSum {ι : Type*} (s : Finset ι) (g : ι → ℤ → ℤ → ℤ) (i j : ℤ) :
    cumul (N : ℤ) (fun a b ↦ ∑ x ∈ s, g x a b) i j = ∑ x ∈ s, cumul (N : ℤ) (g x) i j := by
  simp only [cumul_apply]
  rw [Finset.sum_congr rfl (fun k _ ↦ Finset.sum_comm
    (s := Finset.Icc j (N : ℤ)) (t := s) (f := fun l x ↦ g x k l)), Finset.sum_comm]

/-- The **bar-multiplicity array** of a Gabriel decomposition: at `(a,b)`, the number of bars born
at `a` and dying at `b`, encoded as the ℤ-array `∑_λ δ_{(birth λ, death λ)}`. -/
def barMult (M : ℕ) (birth death : Fin M → Fin (N + 1)) : ℤ → ℤ → ℤ :=
  fun a b ↦ ∑ lam : Fin M, singleDelta (birth lam) (death lam) a b

/-- The bar-multiplicity array is supported (`0 ≤ birth λ` and `death λ ≤ N` for every bar). -/
theorem supported_barMult (M : ℕ) (birth death : Fin M → Fin (N + 1)) :
    Supported (N : ℤ) (barMult M birth death) := by
  refine ⟨fun a b ha ↦ ?_, fun a b hb ↦ ?_⟩
  · simp only [barMult]
    refine Finset.sum_eq_zero fun lam _ ↦ ?_
    rw [singleDelta, if_neg]
    rintro ⟨rfl, _⟩
    exact absurd ha (not_lt.mpr (by positivity))
  · simp only [barMult]
    refine Finset.sum_eq_zero fun lam _ ↦ ?_
    rw [singleDelta, if_neg]
    rintro ⟨_, rfl⟩
    exact absurd hb (not_lt.mpr (by exact_mod_cast Nat.lt_succ_iff.mp (death lam).isLt))

/-- **The bar count is `cumul` of the bar-multiplicity array.** Combined with
`exists_barcode_rankPattern`, this is `r_{ij} = cumul N m̄ i j` — the cumulative form of Prop 3.1b.
Each bar's single delta contributes its containment indicator (`cumul_singleDelta`). -/
theorem cumul_barMult_eq_card (M : ℕ) (birth death : Fin M → Fin (N + 1)) (i j : Fin (N + 1)) :
    cumul (N : ℤ) (barMult M birth death) (i : ℤ) (j : ℤ)
      = ((Finset.univ.filter (fun lam ↦ birth lam ≤ i ∧ j ≤ death lam)).card : ℤ) := by
  unfold barMult
  rw [cumul_finsetSum Finset.univ (fun lam ↦ singleDelta (birth lam) (death lam))]
  simp_rw [cumul_singleDelta]
  rw [Finset.card_filter, Nat.cast_sum]
  refine Finset.sum_congr rfl fun lam _ ↦ ?_
  rw [apply_ite (Nat.cast : ℕ → ℤ), Nat.cast_one, Nat.cast_zero]

/-- **Uniqueness of the Gabriel multiplicities (forced by the rank pattern).** Every tuple over a
field has a Gabriel decomposition whose bar-multiplicity array `m̄` is supported, satisfies
`m̄ = diff (cumul N m̄)` (the finite-difference inversion of `RankPattern`), and whose cumulative
form `cumul N m̄` *is* the rank pattern: `(r_{ij} : ℤ) = cumul N m̄ i j` for every `i ≤ j`. So
`m̄ = diff (rank pattern)` — the multiplicities are a function of the rank pattern alone (uniqueness
half of Le Halleur–Rimányi 2024, Cor 2.9), via the already-formalised `diff_cumul`. -/
theorem rankPattern_eq_cumul_barMult (d : Fin (N + 1) → ℕ) (A : Tuple (k := k) d) :
    ∃ (M : ℕ) (birth death : Fin M → Fin (N + 1)),
      Supported (N : ℤ) (barMult M birth death) ∧
      diff (cumul (N : ℤ) (barMult M birth death)) = barMult M birth death ∧
      ∀ (i j : Fin (N + 1)) (hij : i ≤ j),
        (rankPattern d A i j hij : ℤ)
          = cumul (N : ℤ) (barMult M birth death) (i : ℤ) (j : ℤ) := by
  obtain ⟨M, birth, death, _, _, hrk⟩ := exists_barcode_rankPattern d A
  refine ⟨M, birth, death, supported_barMult M birth death,
    diff_cumul (N : ℤ) _ (supported_barMult M birth death).1 (supported_barMult M birth death).2,
    fun i j hij ↦ ?_⟩
  rw [hrk i j hij, cumul_barMult_eq_card]

section Witness

/-! ## Non-vacuity witness

The `(2,2,2)` tuple over `ℚ` (a field, where the barcode existence applies): `A₁ = [[1,2],[0,1]]`,
`A₂ = [[1,0],[3,1]]` — the rational version of `Setup.tupleWitness`. Its concrete chain has a
barcode (`hasBarcode_tuple` fires), and the rank-pattern bridge holds. (Both factors are invertible
here, so its barcode is the single-orbit `2·M₀₂`; the genuinely degenerate `(2,2,2)` orbits are
exercised on the matrix side in `RankPattern`/`IntervalModule`.) -/

/-- The `(2,2,2)` witness tuple over `ℚ`. -/
def tupleWitnessQ : Tuple (k := ℚ) dWitness := fun i ↦
  match i with
  | 0 => !![1, 2; 0, 1]
  | 1 => !![1, 0; 3, 1]

/-- `hasBarcode_tuple` fires on the concrete chain of the `(2,2,2)` witness over `ℚ` — the existence
theorem is non-vacuous on a concrete matrix tuple. -/
example : HasBarcode (chainSpace ℚ dWitness) (chainEdge dWitness tupleWitnessQ) (fun _ ↦ ⊤) :=
  hasBarcode_tuple dWitness tupleWitnessQ

/-- The rank-pattern bridge holds on the witness at `(0,2)`: `r_{02}` is the range-rank of the
composite of the whole chain. -/
example :
    rankPattern dWitness tupleWitnessQ 0 2 (by decide)
      = Module.finrank ℚ
          (LinearMap.range (compMap (chainSpace ℚ dWitness) (chainEdge dWitness tupleWitnessQ)
            0 2 (by decide))) :=
  rankPattern_eq_finrank_range_compMap dWitness tupleWitnessQ 0 2 (by decide)

/-- The completeness direction (Prop 3.1b) is non-vacuous: the `(2,2,2)` witness has a Gabriel
decomposition whose bar count recovers the rank pattern, with the Kostant dimension constraint. -/
example : ∃ (M : ℕ) (birth death : Fin M → Fin 3),
    (∀ lam, birth lam ≤ death lam) ∧
    (∀ t, (Finset.univ.filter (fun lam ↦ birth lam ≤ t ∧ t ≤ death lam)).card = dWitness t) ∧
    ∀ (i j : Fin 3) (hij : i ≤ j),
      rankPattern dWitness tupleWitnessQ i j hij
        = (Finset.univ.filter (fun lam ↦ birth lam ≤ i ∧ j ≤ death lam)).card :=
  exists_barcode_rankPattern dWitness tupleWitnessQ

/-- The uniqueness headline fires on the `(2,2,2)` witness: its Gabriel multiplicities are forced as
`diff` of the (cumulative) rank pattern. -/
example : ∃ (M : ℕ) (birth death : Fin M → Fin 3),
    Supported (2 : ℤ) (barMult M birth death) ∧
    diff (cumul (2 : ℤ) (barMult M birth death)) = barMult M birth death ∧
    ∀ (i j : Fin 3) (hij : i ≤ j),
      (rankPattern dWitness tupleWitnessQ i j hij : ℤ)
        = cumul (2 : ℤ) (barMult M birth death) (i : ℤ) (j : ℤ) :=
  rankPattern_eq_cumul_barMult dWitness tupleWitnessQ

end Witness

end DLNFibre.Core
