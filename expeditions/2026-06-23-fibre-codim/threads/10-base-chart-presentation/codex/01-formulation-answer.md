**Recommendation**
Use **abstract `m ⊕ l` / `m ⊕ n` block indices for the core Schur lemmas**, then add a thin `Fin r` wrapper by `reindex` for the global `Fin p × Fin q` coordinate convention. Do not make the main theorem carry `p - r` arithmetic.

The core statement I’d commit to is:

```lean
theorem Matrix.rank_fromBlocks_eq_card_left_iff_schur
    {k : Type u} [Field k]
    {m l n : Type*}
    [Fintype m] [Fintype l] [Fintype n]
    [DecidableEq m] [DecidableEq l] [DecidableEq n]
    (Δ : Matrix m m k) (B12 : Matrix m n k)
    (B21 : Matrix l m k) (B22 : Matrix l n k)
    [Invertible Δ] :
    (Matrix.fromBlocks Δ B12 B21 B22).rank = Fintype.card m ↔
      B22 = B21 * ⅟Δ * B12
```

Then the point chart should be determinant-open, not unit-object-first:

```lean
def PivotRankChart (k : Type u) [Field k]
    (m l n : Type*) [Fintype m] [Fintype l] [Fintype n]
    [DecidableEq m] [DecidableEq l] [DecidableEq n] :
    Set (Matrix (m ⊕ l) (m ⊕ n) k) :=
  { M | M.rank = Fintype.card m ∧ IsUnit M.toBlocks₁₁.det }

noncomputable def pivotRankChartEquiv :
    { M // M ∈ PivotRankChart k m l n } ≃
      { Δ : Matrix m m k // IsUnit Δ.det } × Matrix m n k × Matrix l m k
```

Use `{Δ // IsUnit Δ.det}` rather than `(Matrix m m k)ˣ` for this chart API. It matches the localization element `det Δ` directly; you can locally set `letI : Invertible Δ := Matrix.invertibleOfIsUnitDet Δ hΔ`.

**Rank Reduction**
Prove block-diagonal rank additivity. It is the cleanest reusable brick.

```lean
theorem Matrix.rank_fromBlocks_zero₁₂_zero₂₁
    {k : Type u} [Field k]
    {m n l o : Type*}
    [Fintype m] [Fintype n] [Fintype l] [Fintype o]
    (A : Matrix m n k) (D : Matrix l o k) :
    (Matrix.fromBlocks A 0 0 D).rank = A.rank + D.rank
```

Proof route: conjugate `mulVecLin` through

```lean
LinearEquiv.sumArrowLequivProdArrow _ _ k k
```

so the block-diagonal map becomes

```lean
A.mulVecLin.prodMap D.mulVecLin
```

Then use `LinearMap.range_prodMap` and `Module.finrank_prod`. This is less friction than a custom “just the iff” argument, and it gives you the lemma Mathlib is missing.

Then add:

```lean
theorem Matrix.rank_eq_zero_iff
    {k : Type u} [Field k]
    {m n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix m n k) :
    A.rank = 0 ↔ A = 0
```

The Schur proof becomes: LDU factorization, rank preserved by the two unipotent factors, block-diagonal additivity, `rank Δ = card m`, and `rank S = 0 ↔ S = 0`.

**Coordinate Ring**
A point-set `Equiv` is **not enough** for G2-3. It is good supporting API, but the downstream flatness route consumes a localized `AlgEquiv`, not a bijection of `k`-points. The repo already records this exact wall: the Schur trivialization needs explicit exact-rank quotient presentations, not opaque `vanishingIdeal`s, in [ChartFlatnessProbe.lean](/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/ChartFlatnessProbe.lean:22).

The algebraic target should eventually be shaped like:

```lean
noncomputable def pivotChartAlgEquiv :
    Localization.Away
      (Ideal.Quotient.mk (rankLEIdeal k (m ⊕ l) (m ⊕ n) (Fintype.card m)) pivotMinor)
      (MvPolynomial ((m ⊕ l) × (m ⊕ n)) k ⧸
        rankLEIdeal k (m ⊕ l) (m ⊕ n) (Fintype.card m))
      ≃ₐ[k]
    Localization.Away freePivotMinor
      (MvPolynomial ((m × m) ⊕ ((m × n) ⊕ (l × m))) k)
```

So: land the matrix-level Schur theorem first, but don’t call the feeder complete until you have at least the localized Schur presentation as `AlgHom`s or an `AlgEquiv`.

**Landmines**
Use `mulVecLin` for the block-diagonal proof; avoid basis-heavy `toLin'` unless needed. Put `classical` near `Sum`/matrix ext work. For `Fin p`, keep all arithmetic in a wrapper using `rank_reindex` and `MvPolynomial.renameEquiv`. Be careful that `⅟Δ` depends on the local `[Invertible Δ]` instance; create it once from `IsUnit Δ.det` and keep expressions under that instance.