1. **Avoiding The Full Minor Bridge**

No genuinely cheaper Mathlib-v4.29 route is visible for the exact goal.

`canonicalCoord` is an equivalence, so the problem is exactly that `orbitRankLocus M` is defined by rank inequalities. Mathlib has no closedness theorem for rank loci, no packaged upper semicontinuity of rank, and no affine-image shortcut that applies. Polynomial images are not generally closed, and expressing `rank ≤ r` by factorisation through `k^r` would introduce an existential image problem that is harder than minors.

The viable route is still:

```lean
Z = MvPolynomial.zeroLocus k I_minors
```

then conclude closed using the Galois-connection API:

- `MvPolynomial.zeroLocus_span`
- `MvPolynomial.mem_zeroLocus_iff`
- `MvPolynomial.mem_vanishingIdeal_iff`
- `MvPolynomial.zeroLocus_vanishingIdeal_galoisConnection`
- `MvPolynomial.zeroLocus_vanishingIdeal_le`
- `MvPolynomial.le_vanishingIdeal_zeroLocus`

There is no `Matrix.rank_le_iff_minors` in the pin, as you said, and I found no alternative packaged polynomial rank condition.

2. **Minor Bridge Sizing**

State the bridge with embeddings:

```lean
A.rank ≤ r ↔
  ∀ er : Fin (r + 1) ↪ Fin p,
  ∀ ec : Fin (r + 1) ↪ Fin q,
    (A.submatrix er ec).det = 0
```

Direction A, `rank ≤ r → minors vanish`, is small: about 40-70 lines.

Proof route:

- Let `B := A.submatrix er ec`.
- Use `Matrix.cRank_submatrix_le` plus `[simp] Matrix.cRank_toNat_eq_rank` to get `B.rank ≤ A.rank`. The exact cardinal-to-nat monotonic cast lemma may need checking, but the rank API is there.
- Then `B.rank ≤ r`.
- If `B.det ≠ 0`, get full rank:
  - either `Matrix.linearIndependent_cols_of_det_ne_zero`,
  - then `linearIndependent_iff_card_le_finrank_span`,
  - `Matrix.rank_eq_finrank_span_cols`,
  - `Fintype.card_fin`;
  - contradiction `r + 1 ≤ r`.
- Or use `Ne.isUnit`, `Matrix.isUnit_iff_isUnit_det`, `Matrix.rank_of_isUnit`, `Fintype.card_fin`.

Direction B, all minors vanish → `rank ≤ r`, is the bottleneck, but the cheapest route is not pivot/echelon. Use a nonzero-minor existence lemma by selecting actual independent rows and columns from spans. Size: medium, about 110-180 lines if cleanly factored.

Contrapositive lemma:

```lean
A.rank ≥ s →
  ∃ er : Fin s ↪ Fin p, ∃ ec : Fin s ↪ Fin q,
    (A.submatrix er ec).det ≠ 0
```

Proof route:

- Rewrite rank as row-span dimension:
  - `Matrix.rank_eq_finrank_span_row`.
- Use:
  - `Submodule.exists_fun_fin_finrank_span_eq`
  to choose a basis subfamily of actual rows from `Set.range A.row`.
- Restrict from `Fin A.rank` to `Fin s` using `Fin.castLE` / `Fin.castLEEmb`.
- Preserve independence with:
  - `LinearIndependent.comp`
  - `Fin.castLE_injective`
- Extract row indices from `Set.range A.row`, then bundle them as `er : Fin s ↪ Fin p`.
  - Injectivity follows from `LinearIndependent.injective`.
- Let `B := A.submatrix er id`; its rows are linearly independent.
- Use:
  - `LinearIndependent.rank_matrix`
  to get `B.rank = s`.
- Now repeat on columns of `B`:
  - `Matrix.rank_eq_finrank_span_cols`
  - `Submodule.exists_fun_fin_finrank_span_eq`
  - `LinearIndependent.comp` or reindex by `finCongr`
  - extract `ec : Fin s ↪ Fin q`
  - injectivity again by `LinearIndependent.injective`.
- The square matrix `B.submatrix id ec`, hence `A.submatrix er ec` by `Matrix.submatrix_submatrix`, has linearly independent columns.
- Convert LI columns to nonzero determinant using:
  - `Matrix.linearIndependent_cols_iff_isUnit`
  - `Matrix.isUnit_iff_isUnit_det`
  - field fact `IsUnit ↔ ≠ 0`, usually via `Ne.isUnit`.

`Matrix.exists_mulVec_eq_zero_iff` exists, but I would not base this bridge on it. It is square singularity/kernal API, not the rectangular rank-to-nonzero-minor extraction you need.

Full self-contained theorem: budget medium-to-large, roughly 170-240 lines. I would plan for just over 200 on the first implementation because the `Set.range` extraction, `Fin` casts, and `submatrix_submatrix` rewrites are the real Lean cost.

3. **Generic Matrix / Eval Chain**

Use the existing `OrbitVariety.lean` pattern.

Define the generic tuple over the coordinate ring:

```lean
noncomputable def genericTuple (d) :
    Tuple (k := MvPolynomial (RepCoord d) k) d :=
  fun i r c => MvPolynomial.X ⟨i, r, c⟩
```

Evaluation lemma:

```lean
theorem eval_genericTuple (A : Tuple (k := k) d) (i) :
    (genericTuple d i).map (MvPolynomial.eval (canonicalCoord d A)) = A i
```

Proof is by extensionality and:

- `Matrix.map_apply`
- `MvPolynomial.eval_X`
- `canonicalCoord_apply`

Then prove generic submultiplication evaluates correctly:

```lean
theorem eval_submult_genericTuple (A) i j hij :
    (submult d (genericTuple d) i j hij).map
        (MvPolynomial.eval (canonicalCoord d A))
      = submult d A i j hij
```

Use the existing recursion lemmas for `submult`, probably:

- `submult_self`
- `submult_succ`
- `Matrix.map_mul`
- `Matrix.map_one`

Then define the minor polynomial:

```lean
noncomputable def minorPoly d i j hij
    (s : ℕ)
    (er : Fin s ↪ Fin (d j))
    (ec : Fin s ↪ Fin (d i)) :
    MvPolynomial (RepCoord d) k :=
  ((submult d (genericTuple d) i j hij).submatrix er ec).det
```

Evaluation chain:

```lean
MvPolynomial.eval (canonicalCoord d A) (minorPoly d i j hij s er ec)
= ((submult d A i j hij).submatrix er ec).det
```

Lean chain:

- unfold `minorPoly`;
- rewrite determinant through evaluation with `RingHom.map_det`;
- commute evaluation with submatrix using `Matrix.submatrix_map`;
- rewrite the whole generic interval product using `eval_submult_genericTuple`;
- finish by extensionality/simp.

For `zeroLocus`, remember Mathlib defines it with `aeval`; use `MvPolynomial.aeval_eq_eval` when moving between `aeval x P = 0` and `MvPolynomial.eval x P = 0`.

4. **Reduced Deliverable If Bridge Bloats**

Best reduced deliverable: bank the polynomialization layer, not a weak Zariski statement.

Concretely:

- define `genericTuple`;
- prove `eval_genericTuple`;
- prove `eval_submult_genericTuple`;
- define `minorPoly`;
- prove `eval_minorPoly`;
- define `I_minors`;
- prove the closedness theorem conditional on a rank-minor bridge hypothesis.

Then the honest gap is exactly:

```lean
∀ A, rankPattern d A i j hij ≤ rankPattern d M i j hij
  ↔ ∀ er ec, eval (canonicalCoord d A) (minorPoly ...) = 0
```

If you also implement the easy direction, the real inclusion is:

```lean
I_minors ≤ MvPolynomial.vanishingIdeal k (canonicalCoord d '' orbitRankLocus M)
```

not the reverse, because `vanishingIdeal` reverses inclusions.

VERDICT: **full bridge**, but use the double span-subfamily selection proof; it is the cheapest viable route and avoids a large pivot/Cauchy-Binet development.