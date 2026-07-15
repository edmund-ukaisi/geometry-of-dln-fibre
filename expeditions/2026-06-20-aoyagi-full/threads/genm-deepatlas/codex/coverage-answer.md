## 1. The statement

Your framing is slightly wrong: chart coverage is not the clean public statement of “CRrec = geometric κ”. The correct invariant is exact algebraic codimension, not set coverage or measure coverage.

Also, the actual banked `minAdmRec` is a zero-target recursion on residual widths. Thus define mathematically

```lean
CR H s := minAdmRec (Core.dminus H s)
-- dminus H s i = H i - s
```

The clean theorem is:

```lean
namespace DLNFibre.DLN.RLCT

open DLNFibre.Core

theorem codimRepCanonical_productRankLocusLE_eq_minAdmRec
    {K : Type*} [Field K] [IsAlgClosed K] [CharZero K]
    {L : ℕ} (H : Fin (L + 1) → ℕ) (s : ℕ)
    (hL : 1 ≤ L) (hs : ∀ i, s ≤ H i) :
    codimRepCanonical (productRankLocusLE (k := K) H s)
      = (minAdmRec (dminus H s) : ℕ∞) := by
  ...
```

Then κ is the specialization `s := ρ - k`.

This is:

- non-vacuous;
- an exact equality, not a cover;
- exactly “geometric codimension = CR recursion”;
- reachable almost entirely by composition of banked theorems.

Do not name this `charts_exhaust`; its proof no longer depends on charts. The repository already has an independent quiver/orbit-closure proof of the geometric side.

Important scope correction: `codimRepCanonical` currently applies to `Core.Tuple`, over an algebraically closed field. The natural specialization is `K := ℂ`. Your analytic `Params H` is hard-coded over `ℝ`, and the repo currently has no proved real/complex codimension bridge for this locus. The transpose map

```lean
A ↦ fun i ↦ (A i)ᵀ
```

sends your product to the transpose of `Core.mult`, but formalizing this coordinate equivalence does not by itself prove the missing real-to-complex codimension statement.

A Lebesgue-measure statement is not the substitute: when the codimension is positive, `S_s` itself is ambient-null, so even an empty chart family could satisfy an a.e.-coverage claim about `S_s`.

## 2. Decomposition

For the recommended codimension theorem:

1. Banked:

```lean
kostantPartitions_nonempty_of_le hL hs :
  (kostantPartitions H s).Nonempty
```

2. Banked:

```lean
kostantPartitions_zero_nonempty (e := dminus H s) hL :
  (kostantPartitions (dminus H s) 0).Nonempty
```

3. Banked in [SigmaCodim.lean](/home/ubuntu/workspace/deepatlasA-wt/lean/DLNFibre/Core/SigmaCodim.lean:82):

```lean
codimRepCanonical_productRankLocusLE_eq_cCodim_enat
```

4. Banked:

```lean
cCodim_rankShift hs hzero hsRank :
  cCodim (dminus H s) 0 hzero = cCodim H s hsRank
```

5. Banked in [MinAdmCCodim.lean](/home/ubuntu/workspace/deepatlasA-wt/lean/DLNFibre/DLN/RLCT/Validate/MinAdmCCodim.lean:315):

```lean
minAdm_eq_cCodim (dminus H s) hL hzero :
  (minAdm (dminus H s) : ℤ) = cCodim (dminus H s) 0 hzero
```

6. Banked in [RouteMLayerSplit.lean](/home/ubuntu/workspace/deepatlasA-wt/lean/DLNFibre/DLN/RLCT/Validate/RouteMLayerSplit.lean:395):

```lean
minAdmRec_eq_minAdm (dminus H s)
```

7. New: a short cast/rewriting assembly proving the displayed theorem.

If the chart proof itself must independently be certified, the decomposition is longer:

1. New exact-rank cells:

```lean
def lastRankCell (H) (s r) :=
  {A | (lastLayer H A).rank = r ∧ (prod H A).rank ≤ s}
```

2. New, using the banked pivot cover and Schur iff:

```lean
rankEqLocus_eq_iUnion_pivotSchurZero :
  {M | M.rank = r}
    = ⋃ ρ κ, {M | IsUnit (M.submatrix ρ κ).det ∧ schurBlock M ρ κ = 0}
```

This is already non-vacuous at `r = 0`: the Schur-zero condition becomes `M = 0`.

3. New wrapper around banked `deepReduce_rank`:

```lean
exactRank_block_reduction :
  IsUnit M.toBlocks₁₁.det → M.rank = r →
  (X * M).rank
    = (X * fromRows M.toBlocks₁₁ M.toBlocks₂₁ * M.toBlocks₁₁⁻¹).rank
```

4. New general-pivot reindexing wrapper:

```lean
generalPivot_exactRank_reduction :
  IsUnit (M.submatrix ρ κ).det → M.rank = r → ...
```

Most permutation infrastructure is already present: `blockSplitEquiv`, `pivotBlock_reindex_eq_submatrix`, and `Matrix.rank_reindex` are used in the repo.

5. New exact stratification:

```lean
productRankLocusLE_eq_iUnion_lastRankCell :
  {A | (prod H A).rank ≤ s}
    = ⋃ r : Fin (min m n + 1), lastRankCell H s r
```

6. New local chart equivalence identifying each cell with free coordinates, a zero Schur block of size `(m-r)×(n-r)`, and a reduced product-rank locus.

7. New — hardest:

```lean
codimRepCanonical_lastRankCell :
  codimRepCanonical (lastRankCell H s r)
    = ((m - r) * (n - r) : ℕ∞)
      + codimRepCanonical (productRankLocusLE (lastRed H r) s)
```

This requires a principal-open algebraic equivalence/localization argument. The banked measure-preserving shears do not prove algebraic codimension additivity.

8. New finite-union codimension minimum, followed by induction on depth.

A flat finite `CRPath` type is optional. Induction with nested finite unions is cleaner; flatten paths only if a downstream API strictly requires one `Fintype` index.

## 3. Recursion shape

You can avoid constructing reduced `Params`.

Carry an effective-product state:

```lean
structure EffectiveState (H : Fin (L + 1) → ℕ) (A : Params H)
    (j : ℕ) (hj : j ≤ L) where
  q : ℕ
  Q : Matrix (Fin (H ⟨j, by omega⟩)) (Fin q) ℝ
  fullRank : Q.rank = q
```

Its represented product is

```lean
prodAux H A j ... * Q
```

Start with `j = L`, `q = H (Fin.last L)`, and `Q = 1`.

When `j > 0`, form the effective last layer

```lean
M := reindex (A ⟨j - 1, ...⟩) * Q
```

choose `r := M.rank`, choose an invertible `r×r` pivot, and set

```lean
Q' := pivotColumns M * Δ⁻¹.
```

The banked reduction gives

```lean
rank (prodAux j * Q) = rank (prodAux (j - 1) * Q').
```

Thus the state descends from `(j,q)` to `(j-1,r)`, exactly realizing the last-peel recurrence, without dependent-width tuple surgery.

For the coordinate/codimension proof, strengthen `fullRank` to carry a square completion of `Q` whose determinant is a unit, preferably absolute determinant `1`. That is what makes the preceding layer split into reduced and spectator coordinates.

## 4. Reachability

- Exact complex-algebraic codimension theorem above: immediately reachable, roughly 30–80 LoC.
- Add a generic `ParamsK`/transpose bridge to the Core orientation: roughly 150–350 LoC.
- One-step exact-rank pivot/Schur/reduction theorem: roughly 100–250 LoC.
- Full independent chart-atlas codimension proof: roughly 1,500–3,000 LoC.
- A genuine theorem directly about real algebraic codimension of the hard-coded `Params H`: additional and currently uncertain because of the unproved real/complex bridge.

The cheapest genuine theorem to land is the displayed codimension wrapper: it directly closes “CRrec = geometric κ”.

If the review specifically demands chart evidence, the cheapest first chart theorem is `rankEqLocus_eq_iUnion_pivotSchurZero`. It fixes the rank-zero defect before any recursive machinery is built.

## 5. Triviality check

Your claim is correct.

At `t = 0`, `Fin 0` has the empty row/column embeddings, the `0×0` determinant is `1`, and hence the pivot chart is all matrices. Indeed, the banked theorem at `t = 0` reads

```lean
{M | 0 ≤ M.rank} = ⋃ ρ κ, pivotChart ρ κ
```

whose left side is `Set.univ`.

Non-vacuity comes from one of these stronger requirements:

- use exact-rank cells `M.rank = r`;
- equivalently, on an invertible `r`-pivot chart require the Schur coordinate `E = 0`;
- prove the per-cell codimension formula;
- finally prove that the codimension of the finite union is the minimum prescribed by the CR recursion.

Bare inclusion, and even a measure cover of `S_s`, contains none of that information.