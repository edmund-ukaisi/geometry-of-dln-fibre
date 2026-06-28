import DLNFibre.Core.OrbitVariety
import DLNFibre.Core.Orbit
import DLNFibre.Core.GenericTuple
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-!
# `DLNFibre.Core.RankLocusClosed` — the rank locus is Zariski-closed (L6.3, easy direction)

The Zariski-closedness of `orbitRankLocus M ⊆ Rep_d` — the determinantal locus cut out by the
rank conditions `rankPattern A ≤ rankPattern M` (Lehalleur–Rimányi 2024 Thm 3.8 says this set *is*
the orbit closure `Ō_M`; that identification is L6.1/L6.2, NOT here). This module proves the
**topological** content of the easy inclusion `Ō_M ⊆ orbitRankLocus M`: the rank locus is closed,
so the closure of the orbit `O_M` stays inside it once `O_M ⊆ orbitRankLocus M`. Two pieces:

1. **The determinantal-rank bridge** (`rank_le_iff_forall_submatrix_det_eq_zero`, built here —
   Mathlib v4.29 has no packaged version): over a field, `A.rank ≤ r` iff every `(r+1)×(r+1)`
   submatrix of `A` has determinant `0`. The `→` is `cRank_submatrix_le` + "non-full-rank square
   ⟹ `det = 0`"; the `←` is the column/row independent-subfamily extraction
   (`exists_linearIndependent'` + `LinearIndependent.rank_matrix` +
   `linearIndependent_cols_iff_isUnit`).
2. **Closedness** (`isZariskiClosed_orbitRankLocus`): the entries of `submult d A i j` are
   polynomials in the matrix entries (the **generic tuple** `genericTuple`, entries = coordinate
   variables, evaluated at `canonicalCoord A`), so each `(r+1)`-minor is a polynomial `minorPoly`.
   The bridge writes `canonicalCoord '' orbitRankLocus M` as the `zeroLocus` of the ideal generated
   by the minor polynomials, and a `zeroLocus` is Zariski-closed (Galois-connection `l_u_l_eq_l`).

Plus the easy orbit inclusion `O_M ⊆ orbitRankLocus M` (`orbitSet_subset_orbitRankLocus`,
`rankPattern`-invariance, `rankPattern_eq_iff_orbit`) and the resulting ideal inclusion. No field
algebraic-closedness is needed for closedness; `[Field k]` suffices.

**Dependency rule:** `Core` only — never import `DLNFibre.DLN`.
-/

namespace DLNFibre.Core

open Matrix MvPolynomial Submodule Module

universe u

variable {k : Type u} [Field k]

/-! ## The determinantal-rank bridge (pure matrix lemma, network-free) -/

/-- A square submatrix has rank at most the rank of the full matrix (general index maps over a
field). From `Matrix.cRank_submatrix_le`, cast `Cardinal → ℕ`. -/
theorem rank_submatrix_le_rank {p q : ℕ} (A : Matrix (Fin p) (Fin q) k) {a b : ℕ}
    (f : Fin a → Fin p) (g : Fin b → Fin q) :
    (A.submatrix f g).rank ≤ A.rank := by
  have hc := Matrix.cRank_submatrix_le A f g
  rw [← Matrix.cRank_toNat_eq_rank (A.submatrix f g), ← Matrix.cRank_toNat_eq_rank A]
  exact Cardinal.toNat_le_toNat hc ((A.cRank_le_card_width).trans_lt Cardinal.natCast_lt_aleph0)

/-- A square matrix whose rank is below its size has determinant `0` (over a field): otherwise it
would be a unit of full rank. -/
theorem det_eq_zero_of_rank_lt {p : ℕ} (A : Matrix (Fin p) (Fin p) k) (h : A.rank < p) :
    A.det = 0 := by
  by_contra hdet
  have hu : IsUnit A := (Matrix.isUnit_iff_isUnit_det A).mpr (Ne.isUnit hdet)
  have := Matrix.rank_of_isUnit A hu
  rw [Fintype.card_fin] at this; omega

/-- **Direction A** (`rank ≤ r ⟹ minors vanish`). If `A.rank ≤ r` then every `(r+1)×(r+1)`
submatrix of `A` has determinant `0`: the submatrix has rank `≤ A.rank ≤ r < r+1`, so it is not
full rank. -/
theorem submatrix_det_eq_zero_of_rank_le {p q r : ℕ} {A : Matrix (Fin p) (Fin q) k}
    (hr : A.rank ≤ r) (er : Fin (r + 1) → Fin p) (ec : Fin (r + 1) → Fin q) :
    (A.submatrix er ec).det = 0 :=
  det_eq_zero_of_rank_lt _ (lt_of_le_of_lt (rank_submatrix_le_rank A er ec) (by omega))

/-! ## Independent-subfamily extraction (the engine of Direction B)

From `s ≤ A.rank`, extract an injective family of `s` row indices whose rows are linearly
independent — `exists_linearIndependent'` gives a maximal independent subfamily of the rows, of
cardinality `= A.rank` (by `LinearIndependent.rank_matrix`-style counting), and `s ≤` that card
gives a `Fin s` slice. -/

/-- From `s ≤ A.rank`, an injective row-index family `er : Fin s → Fin p` whose selected rows are
linearly independent. The selected `s × q` submatrix then has full row rank `s`. -/
theorem exists_injective_linearIndependent_rows {p q : ℕ} (A : Matrix (Fin p) (Fin q) k) {s : ℕ}
    (hs : s ≤ A.rank) :
    ∃ er : Fin s → Fin p, Function.Injective er ∧
      LinearIndependent k (fun i ↦ A.row (er i)) := by
  classical
  -- maximal independent subfamily of the rows, indexed by `κ` with an injection `a : κ → Fin p`
  obtain ⟨κ, a, ha_inj, ha_span, ha_li⟩ := exists_linearIndependent' k A.row
  haveI : Module.Finite k (Fin p → k) := inferInstance
  haveI : Finite κ := ha_li.finite
  haveI : Fintype κ := Fintype.ofFinite κ
  -- `Fintype.card κ = A.rank`: independent family spanning the row span of finrank `A.rank`
  have hcard : Fintype.card κ = A.rank := by
    have h1 : finrank k (span k (Set.range (A.row ∘ a))) = Fintype.card κ :=
      finrank_span_eq_card ha_li
    rw [ha_span] at h1
    rw [A.rank_eq_finrank_span_row, ← h1]
  -- choose an injection `Fin s ↪ κ` (since `s ≤ card κ`), compose with `a`
  have hsle : s ≤ Fintype.card κ := by rw [hcard]; exact hs
  obtain ⟨ι⟩ := Function.Embedding.nonempty_of_card_le (β := κ) (α := Fin s)
    (by rw [Fintype.card_fin]; exact hsle)
  have hιinj : Function.Injective (ι : Fin s → κ) := Function.Embedding.injective ι
  refine ⟨fun i ↦ a (ι i), ?_, ?_⟩
  · exact fun i j hij ↦ hιinj (ha_inj hij)
  · have hcomp : (fun i ↦ A.row (a (ι i))) = (A.row ∘ a) ∘ (ι : Fin s → κ) := rfl
    rw [hcomp]
    exact ha_li.comp (ι : Fin s → κ) hιinj

/-- **Direction B** (`minors vanish ⟹ rank ≤ r`, contrapositive form). If `r + 1 ≤ A.rank` then some
`(r+1)×(r+1)` submatrix has non-zero determinant: extract `r+1` independent rows, then `r+1`
independent columns of that sub-block; the resulting square block has independent columns, hence is
a unit, hence has non-zero determinant. -/
theorem exists_submatrix_det_ne_zero_of_le_rank {p q r : ℕ} (A : Matrix (Fin p) (Fin q) k)
    (hr : r + 1 ≤ A.rank) :
    ∃ (er : Fin (r + 1) → Fin p) (ec : Fin (r + 1) → Fin q),
      Function.Injective er ∧ Function.Injective ec ∧ (A.submatrix er ec).det ≠ 0 := by
  classical
  -- (1) extract `r+1` independent rows of `A`
  obtain ⟨er, her_inj, her_li⟩ := exists_injective_linearIndependent_rows A hr
  set B : Matrix (Fin (r + 1)) (Fin q) k := A.submatrix er id with hB
  -- the rows of `B` are exactly the selected rows, so they are independent and `B.rank = r+1`
  have hBrow : B.row = fun i ↦ A.row (er i) := by
    funext i; rfl
  have hBli : LinearIndependent k B.row := by rw [hBrow]; exact her_li
  have hBrank : B.rank = r + 1 := by
    have := hBli.rank_matrix; rwa [Fintype.card_fin] at this
  -- (2) extract `r+1` independent rows of `Bᵀ` = `r+1` independent columns of `B`
  have hBTrank : (r + 1) ≤ Bᵀ.rank := by rw [Matrix.rank_transpose, hBrank]
  obtain ⟨ec, hec_inj, hec_li⟩ := exists_injective_linearIndependent_rows Bᵀ hBTrank
  -- (3) the square block `C = A.submatrix er ec` has independent columns, hence is a unit
  set C : Matrix (Fin (r + 1)) (Fin (r + 1)) k := A.submatrix er ec with hC
  have hCcol : C.col = fun i ↦ Bᵀ.row (ec i) := by
    funext i j; simp [hC, hB, Matrix.col_apply, Matrix.row_apply, Matrix.transpose_apply,
      Matrix.submatrix_apply]
  have hCli : LinearIndependent k C.col := by rw [hCcol]; exact hec_li
  have hCunit : IsUnit C := Matrix.linearIndependent_cols_iff_isUnit.mp hCli
  refine ⟨er, ec, her_inj, hec_inj, ?_⟩
  exact Matrix.isUnit_iff_isUnit_det C |>.mp hCunit |>.ne_zero

/-- **The determinantal-rank bridge.** Over a field, `A.rank ≤ r` iff every `(r+1)×(r+1)` submatrix
of `A` (selected by *any* index maps `er, ec`) has determinant `0`. The `→` is
`submatrix_det_eq_zero_of_rank_le`; the `←` is the contrapositive via
`exists_submatrix_det_ne_zero_of_le_rank`. Mathlib v4.29 has no packaged version. -/
theorem rank_le_iff_forall_submatrix_det_eq_zero {p q r : ℕ} (A : Matrix (Fin p) (Fin q) k) :
    A.rank ≤ r ↔ ∀ (er : Fin (r + 1) → Fin p) (ec : Fin (r + 1) → Fin q),
      (A.submatrix er ec).det = 0 := by
  constructor
  · exact fun hr er ec ↦ submatrix_det_eq_zero_of_rank_le hr er ec
  · intro hall
    by_contra hlt
    obtain ⟨er, ec, _, _, hne⟩ :=
      exists_submatrix_det_ne_zero_of_le_rank A (Nat.succ_le_of_lt (Nat.not_le.mp hlt))
    exact hne (hall er ec)

/-! ## Polynomialization: the rank-pattern minors as coordinate polynomials

The entries of `submult d A i j` are polynomials in the matrix entries of `A`. We realise this with
the **generic tuple** `genericTuple d`, the tuple over the coordinate ring whose `(i, r, c)` entry
is the variable `X ⟨i, r, c⟩`; evaluating at the point `canonicalCoord d A` recovers `A`. Then
`submult` of the generic tuple, evaluated, is `submult` of `A` (matrix multiplication commutes with
the ring hom `eval`), and each `(s)`-minor of the generic `submult` is a polynomial whose value at
`canonicalCoord d A` is the corresponding numerical minor of `submult d A i j`. -/

variable {N : ℕ}

-- `genericTuple` and `eval_genericTuple` now live in `Core.GenericTuple` (over any `CommRing`, the
-- weakest hypothesis), reused here and by `Core.MultComorphism`.

/-- Evaluating the generic interval sub-product at `canonicalCoord d A` recovers `submult d A i j`:
matrix multiplication commutes with the ring hom `eval`, and the generic factors evaluate to the
factors of `A` (`eval_genericTuple`). By induction on the upper index through `submult_succ`. -/
theorem eval_submult_genericTuple {d : Fin (N + 1) → ℕ} (A : Tuple (k := k) d)
    (i j : Fin (N + 1)) (hij : i ≤ j) :
    (submult d (genericTuple (k := k) d) i j hij).map (MvPolynomial.eval (canonicalCoord d A))
      = submult d A i j hij := by
  induction j using Fin.induction with
  | zero =>
    obtain rfl : i = 0 := le_antisymm hij (Fin.zero_le i)
    rw [submult_self, submult_self, Matrix.map_one _ (map_zero _) (map_one _)]
  | succ p ih =>
    rcases eq_or_lt_of_le hij with heq | hlt
    · subst heq
      rw [submult_self, submult_self, Matrix.map_one _ (map_zero _) (map_one _)]
    · have hip : i ≤ p.castSucc := by
        rw [Fin.le_castSucc_iff]; exact hlt
      rw [submult_succ d (genericTuple (k := k) d) i p hip, submult_succ d A i p hip,
        Matrix.map_mul, eval_genericTuple A p, ih hip]

/-- The **minor polynomial**: the determinant of an `(s)×(s)` submatrix of the generic interval
sub-product `submult d (genericTuple d) i j`, a polynomial in the coordinate ring. Its value at
`canonicalCoord d A` is the corresponding numerical minor of `submult d A i j`
(`eval_minorPoly`). -/
noncomputable def minorPoly {d : Fin (N + 1) → ℕ} (i j : Fin (N + 1)) (hij : i ≤ j) {s : ℕ}
    (er : Fin s → Fin (d j)) (ec : Fin s → Fin (d i)) : MvPolynomial (RepCoord d) k :=
  ((submult d (genericTuple (k := k) d) i j hij).submatrix er ec).det

/-- Evaluating `minorPoly` at the point `canonicalCoord d A` yields the numerical `(s)`-minor of
`submult d A i j`: determinant commutes with the ring hom `eval` (`RingHom.map_det`), evaluation
commutes with `submatrix` (`Matrix.submatrix_map`), and the generic sub-product evaluates to
`submult d A i j` (`eval_submult_genericTuple`). -/
theorem eval_minorPoly {d : Fin (N + 1) → ℕ} (A : Tuple (k := k) d) (i j : Fin (N + 1))
    (hij : i ≤ j) {s : ℕ} (er : Fin s → Fin (d j)) (ec : Fin s → Fin (d i)) :
    MvPolynomial.eval (canonicalCoord d A) (minorPoly i j hij er ec)
      = ((submult d A i j hij).submatrix er ec).det := by
  rw [minorPoly, RingHom.map_det, RingHom.mapMatrix_apply, ← Matrix.submatrix_map,
    eval_submult_genericTuple A i j hij]

/-! ## The rank locus is Zariski-closed -/

/-- The set of **defining minor polynomials** of `orbitRankLocus M`: for each `(i, j)` with `i ≤ j`
and each pair of index maps `er, ec` of size `rankPattern M i j hij + 1`, the minor polynomial
`minorPoly i j hij er ec`. Its common zero locus is exactly `canonicalCoord '' orbitRankLocus M`. -/
def rankMinorSet {d : Fin (N + 1) → ℕ} (M : Tuple (k := k) d) :
    Set (MvPolynomial (RepCoord d) k) :=
  {p | ∃ (i j : Fin (N + 1)) (hij : i ≤ j)
      (er : Fin (rankPattern d M i j hij + 1) → Fin (d j))
      (ec : Fin (rankPattern d M i j hij + 1) → Fin (d i)), p = minorPoly i j hij er ec}

/-- A point `x` is a common zero of `rankMinorSet M` iff the tuple `A = canonicalCoord.symm x`
satisfies every rank bound `rankPattern A i j ≤ rankPattern M i j` — by the determinantal-rank
bridge applied to `submult d A i j`. -/
theorem mem_zeroLocus_rankMinorSet_iff {d : Fin (N + 1) → ℕ} (M : Tuple (k := k) d)
    (x : RepCoord d → k) :
    (∀ p ∈ rankMinorSet M, MvPolynomial.eval x p = 0) ↔
      (canonicalCoord d).symm x ∈ orbitRankLocus M := by
  set A := (canonicalCoord d).symm x with hA
  have hxA : x = canonicalCoord d A := by rw [hA, Equiv.apply_symm_apply]
  rw [orbitRankLocus, Set.mem_setOf_eq]
  constructor
  · -- common zero ⟹ all rank bounds hold
    intro hzero i j hij
    rw [show rankPattern d A i j hij = (submult d A i j hij).rank from rfl,
      rank_le_iff_forall_submatrix_det_eq_zero (submult d A i j hij)]
    intro er ec
    have hmem : minorPoly i j hij er ec ∈ rankMinorSet M := ⟨i, j, hij, er, ec, rfl⟩
    have := hzero _ hmem
    rw [hxA, eval_minorPoly A i j hij er ec] at this
    exact this
  · -- all rank bounds hold ⟹ common zero
    intro hrank p hp
    obtain ⟨i, j, hij, er, ec, rfl⟩ := hp
    rw [hxA, eval_minorPoly A i j hij er ec]
    have hle : (submult d A i j hij).rank ≤ rankPattern d M i j hij := hrank i j hij
    rw [rank_le_iff_forall_submatrix_det_eq_zero (submult d A i j hij)] at hle
    exact hle er ec

/-- `canonicalCoord '' orbitRankLocus M` is the zero locus of the minor ideal `span (rankMinorSet
M)`: it is cut out by the defining minor polynomials. -/
theorem image_orbitRankLocus_eq_zeroLocus {d : Fin (N + 1) → ℕ} (M : Tuple (k := k) d) :
    canonicalCoord d '' orbitRankLocus M
      = MvPolynomial.zeroLocus k (Ideal.span (rankMinorSet M)) := by
  rw [MvPolynomial.zeroLocus_span]
  ext x
  rw [Set.mem_setOf_eq]
  have heval : (∀ p ∈ rankMinorSet M, (MvPolynomial.aeval x) p = 0)
      ↔ (∀ p ∈ rankMinorSet M, MvPolynomial.eval x p = 0) := by
    simp only [MvPolynomial.aeval_eq_eval]
  rw [heval, mem_zeroLocus_rankMinorSet_iff M x]
  constructor
  · rintro ⟨A, hA, rfl⟩; rwa [Equiv.symm_apply_apply]
  · intro hx; exact ⟨(canonicalCoord d).symm x, hx, (canonicalCoord d).apply_symm_apply x⟩

/-- **The rank locus is Zariski-closed (L6.3).** `canonicalCoord '' orbitRankLocus M` equals the
zero locus of its own vanishing ideal — it is cut out by the determinantal minor polynomials
(`image_orbitRankLocus_eq_zeroLocus`), and any zero locus is Zariski-closed (the Galois-connection
fact `zeroLocus (vanishingIdeal (zeroLocus I)) = zeroLocus I`). This is the topological content of
the easy orbit-closure inclusion `Ō_M ⊆ orbitRankLocus M`. -/
theorem isZariskiClosed_orbitRankLocus {d : Fin (N + 1) → ℕ} (M : Tuple (k := k) d) :
    IsZariskiClosed (canonicalCoord d '' orbitRankLocus M) := by
  rw [IsZariskiClosed, image_orbitRankLocus_eq_zeroLocus M]
  exact (MvPolynomial.zeroLocus_vanishingIdeal_galoisConnection
    (σ := RepCoord d) (k := k) (K := k)).l_u_l_eq_l _ |>.symm

/-! ## The easy orbit inclusion `O_M ⊆ orbitRankLocus M` -/

/-- Every tuple in the orbit of `M` lies in `orbitRankLocus M`: a base change preserves the rank
pattern (`rankPattern_eq_of_smul`), so `rankPattern (P • M) = rankPattern M ≤ rankPattern M`. The
orbit (before flattening) is contained in the rank locus — the easy half of Thm 3.8. -/
theorem orbit_subset_orbitRankLocus {d : Fin (N + 1) → ℕ} (M : Tuple (k := k) d) :
    {A | ∃ P : BaseChangeGroup (k := k) d, P • M = A} ⊆ orbitRankLocus M := by
  rintro A ⟨P, rfl⟩ i j hij
  exact (rankPattern_eq_of_smul P rfl i j hij).symm.le

/-- **The orbit is contained in the rank locus (L6.3, flattened form).** `O_M = canonicalCoord ''
(orbit of M) ⊆ canonicalCoord '' orbitRankLocus M`: the orbit-invariance of the rank pattern places
every orbit point in the determinantal locus. With `isZariskiClosed_orbitRankLocus`, the Zariski
closure of `O_M` stays inside `orbitRankLocus M` — the easy inclusion `Ō_M ⊆ orbitRankLocus M`. -/
theorem orbitSet_subset_orbitRankLocus {d : Fin (N + 1) → ℕ} (M : Tuple (k := k) d) :
    orbitSet M ⊆ canonicalCoord d '' orbitRankLocus M :=
  Set.image_mono (orbit_subset_orbitRankLocus M)

/-- **The easy ideal inclusion.** `vanishingIdeal (canonicalCoord '' orbitRankLocus M) ≤
vanishingIdeal (O_M)`: at the ideal level the easy orbit inclusion `O_M ⊆ orbitRankLocus M` is the
*trivial* containment of vanishing ideals (`vanishingIdeal` is order-reversing). The genuine content
of L6.3 is the closedness `isZariskiClosed_orbitRankLocus`; this is the ideal-side shadow. -/
theorem vanishingIdeal_orbitRankLocus_le_orbitSet {d : Fin (N + 1) → ℕ} (M : Tuple (k := k) d) :
    MvPolynomial.vanishingIdeal k (canonicalCoord d '' orbitRankLocus M)
      ≤ MvPolynomial.vanishingIdeal k (orbitSet M) :=
  MvPolynomial.vanishingIdeal_anti_mono (orbitSet_subset_orbitRankLocus M)

section Witness

/-! ## Non-vacuity witnesses

The determinantal-rank bridge fires on a concrete rank-1 matrix; the rank locus is inhabited (every
`M` is in its own); the orbit inclusion is exercised on the `(2,2,2)/ℚ` orbit witness. -/

/-- The bridge fires concretely: the `2×2` zero matrix over `ℚ` has rank `≤ 0`, witnessed through
the bridge by every `1×1` minor (an entry) being `0`. -/
example : (0 : Matrix (Fin 2) (Fin 2) ℚ).rank ≤ 0 := by
  rw [rank_le_iff_forall_submatrix_det_eq_zero]
  intro er ec
  rw [Matrix.det_fin_one]
  simp

/-- Direction B fires concretely: the `2×2` identity over `ℚ` does not have rank `≤ 1` — its single
`2×2` minor (its determinant `1`) is nonzero. -/
example : ¬ (1 : Matrix (Fin 2) (Fin 2) ℚ).rank ≤ 1 := by
  rw [rank_le_iff_forall_submatrix_det_eq_zero]
  intro h
  have := h id id
  rw [Matrix.submatrix_id_id, Matrix.det_one] at this
  exact one_ne_zero this

/-- The rank locus is inhabited: every `M` lies in its own flattened rank locus. -/
example {d : Fin (N + 1) → ℕ} (M : Tuple (k := k) d) :
    canonicalCoord d M ∈ canonicalCoord d '' orbitRankLocus M :=
  ⟨M, self_mem_orbitRankLocus M, rfl⟩

/-- The orbit inclusion is non-vacuous: the `(2,2,2)/ℚ` orbit point `canonicalCoord tupleWitnessQ`
lies in `canonicalCoord '' orbitRankLocus tupleWitnessQ`. -/
example : canonicalCoord dWitness tupleWitnessQ
    ∈ canonicalCoord dWitness '' orbitRankLocus tupleWitnessQ :=
  orbitSet_subset_orbitRankLocus tupleWitnessQ
    ⟨tupleWitnessQ, ⟨1, one_smul _ _⟩, rfl⟩

end Witness

end DLNFibre.Core

/-! ## Rank base-change under an injective field hom (top-level `Matrix` lemma)

Stated outside `DLNFibre.Core` so the name lands in the genuine `Matrix` namespace (declaring a
`Matrix.…` lemma *inside* `DLNFibre.Core` would shadow the top-level `Matrix` namespace for every
downstream Core file). -/

namespace Matrix

/-- **Matrix rank is preserved by an injective ring hom (between fields).** For an injective
`ι : R →+* S` between fields, the entrywise map `B ↦ B.map ι` preserves rank. Proof: via the
determinantal-rank bridge `DLNFibre.Core.rank_le_iff_forall_submatrix_det_eq_zero`,
`(B.map ι).rank ≤ r ↔ B.rank ≤ r` for every `r`, because each `(r+1)×(r+1)` minor satisfies
`det ((B.map ι).submatrix er ec) = ι (det (B.submatrix er ec))` (`Matrix.submatrix_map` +
`RingHom.map_det`), and `ι` injective gives `ι x = 0 ↔ x = 0`. The rank base-change micro-lemma the
real↔complex codim transfer rests on. -/
theorem rank_map_eq_of_injective {R S : Type*} [Field R] [Field S]
    {p q : ℕ} (B : Matrix (Fin p) (Fin q) R) (ι : R →+* S) (hι : Function.Injective ι) :
    (B.map ι).rank = B.rank := by
  have hiff : ∀ r : ℕ, (B.map ι).rank ≤ r ↔ B.rank ≤ r := by
    intro r
    rw [DLNFibre.Core.rank_le_iff_forall_submatrix_det_eq_zero (B.map ι),
      DLNFibre.Core.rank_le_iff_forall_submatrix_det_eq_zero B]
    refine forall₂_congr (fun er ec ↦ ?_)
    rw [Matrix.submatrix_map, ← RingHom.mapMatrix_apply, ← RingHom.map_det]
    exact map_eq_zero_iff ι hι
  exact le_antisymm ((hiff _).2 le_rfl) ((hiff _).1 le_rfl)

end Matrix
