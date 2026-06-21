<task>
Lean 4 + Mathlib (pin v4.29.0) formalisation. I must prove a determinantal-rank
locus is Zariski-closed. Help me pick the cheapest viable proof route and size it.

CONTEXT (defs, all already in the project):
- `Tuple d := ∀ i : Fin N, Matrix (Fin (d i.succ)) (Fin (d i.castSucc)) k`  [k : Field]
- `submult d A i j (hij : i ≤ j) : Matrix (Fin (d j)) (Fin (d i)) k` is an interval matrix
  PRODUCT `A_j ⋯ A_{i+1}` (identity at i=j). Its entries are POLYNOMIALS in the entries of the
  factors A_i (a product of finitely many matrices, so each entry is a polynomial of degree ≤ #factors).
- `rankPattern d A i j hij := (submult d A i j hij).rank`   (Matrix.rank, the column-span finrank, ℕ-valued)
- `orbitRankLocus M := {A | ∀ i j (h : i ≤ j), rankPattern d A i j h ≤ rankPattern d M i j h}`
- `RepCoord d := Σ i : Fin N, Fin (d i.succ) × Fin (d i.castSucc)`  (one coordinate per matrix entry; Finite)
- `canonicalCoord d : Tuple d ≃ (RepCoord d → k)`, the entry-flattening: (canonicalCoord A) ⟨i,r,c⟩ = (A i) r c.
- `MvPolynomial.zeroLocus k (I : Ideal (MvPolynomial σ k)) : Set (σ → k)` and
  `MvPolynomial.vanishingIdeal k (V : Set (σ → k)) : Ideal (MvPolynomial σ k)` (Mathlib's, σ = RepCoord d).
- `IsZariskiClosed (Z : Set (σ → k)) : Prop := Z = zeroLocus k (vanishingIdeal k Z)`  (project def).

GOAL: `IsZariskiClosed (canonicalCoord d '' orbitRankLocus M)`.

KNOWN MATHLIB GAP (verified by grep of the v4.29 pin): there is NO packaged lemma
"Matrix.rank N ≤ r ↔ all (r+1)×(r+1) minors (determinants of (r+1)-square submatrices) vanish".
`Mathlib.LinearAlgebra.Matrix.Rank` has rank = finrank of column span, rank_submatrix_le,
rank_eq_finrank_span_cols, cRank, eRank, but no determinantal/minor characterization.

WHAT I ALREADY KNOW:
- `IsZariskiClosed Z` reduces (⊆ is free via `zeroLocus_vanishingIdeal_le`) to: `zeroLocus(vanishingIdeal Z) ⊆ Z`.
- The slick route is: exhibit an explicit polynomial set S with `zeroLocus(span S) = Z`; then
  Z is closed because `zeroLocus(vanishingIdeal(zeroLocus J)) = zeroLocus J` (a Galois-connection fact,
  `zeroLocus_vanishingIdeal_zeroLocus` style). So it suffices to write Z AS a zeroLocus of an explicit ideal.
- For that I need set-equality `Z = zeroLocus(I_minors)`, which needs BOTH directions of the
  minor bridge over a field:
    (A) rank N ≤ r  →  every (r+1)-minor of N is 0   [easy direction; multilinear/columns dependent]
    (B) every (r+1)-minor of N is 0  →  rank N ≤ r   [hard direction; pivot/echelon argument]
  Both are entry-polynomial conditions, so the locus is a zeroLocus.

QUESTIONS:
1. Is there a route to `IsZariskiClosed (canonicalCoord '' orbitRankLocus M)` that AVOIDS the full
   bidirectional minor bridge? E.g. some closure-of-image lemma, or expressing rankPattern ≤ via a
   different polynomial condition Mathlib already has? Be concrete about Mathlib v4.29 lemma names.
2. If the minor bridge is genuinely required: which direction is the bottleneck, what is the minimal
   Mathlib-idiomatic proof of EACH direction (name the lemmas: det of submatrix, linearIndependent of
   columns, finrank, `Matrix.rank_eq_finrank_span_cols`, `Module.finrank_le`, `Matrix.exists_...`,
   `Fintype.card`, the (r+1)-subset enumeration as `n_0 ↪ n` embeddings), and an honest LINE-COUNT
   sizing (small <80, medium 80–200, large >200) for a self-contained minimal `rank N ≤ r ↔ minors vanish`
   over a Field. NOTE the matrices here are `Fin p × Fin q`.
3. Subtle point: `submult` entries are polynomials in the RepCoord variables, but `canonicalCoord A` is
   a POINT (RepCoord → k), and the minor of `submult d A i j` is a polynomial EVALUATED at that point.
   How do I cleanly say "the (r+1)-minor, as a polynomial in MvPolynomial (RepCoord d) k, vanishes at
   canonicalCoord A iff the corresponding numerical minor of submult d A i j is 0"? I.e. I need a
   polynomial `P_minor` with `eval (canonicalCoord A) P_minor = det((submult d A i j).submatrix ...)`.
   Is there a clean "generic matrix" pattern (each entry = an MvPolynomial in the coordinate ring,
   matrix multiplication of generic matrices, then det) — `Matrix.map`, `RingHom.map_det`,
   `MvPolynomial.eval` — to get this evaluation-commutes fact without per-entry blowup? The project
   already has `genericMat`/`RingHom.map_det`/`eval_genericMat` patterns in OrbitVariety.lean.
4. If the full bridge balloons past ~200 lines, what is the cleanest REDUCED deliverable that still
   banks real content (e.g. each single `rankPattern ≤ k` slice closed, or the easy ideal inclusion
   `vanishingIdeal(orbitRankLocus) ⊆ vanishingIdeal(O_M)` standalone), and how do I state the gap honestly?
</task>

<output_contract>
  Four numbered sections matching the four questions. For Q2 give a concrete proof sketch with
  Mathlib v4.29 lemma names and a line-count band per direction. For Q3 give the exact "generic
  matrix / map_det / eval" lemma chain. Keep it tight — sketch + names, not full Lean. End with a
  one-line VERDICT: "full bridge" vs "reduced deliverable X", with the reason.
</output_contract>

<grounding_rules>
  Mathlib changes fast; you may be wrong about exact v4.29 lemma names. Flag any lemma name you are
  NOT confident exists in v4.29 as "(verify)". Distinguish "this lemma exists" (assertion) from "a
  lemma of roughly this shape should exist" (inference). Do not invent a `Matrix.rank_le_iff_minors`
  — I have verified it is absent.
</grounding_rules>
