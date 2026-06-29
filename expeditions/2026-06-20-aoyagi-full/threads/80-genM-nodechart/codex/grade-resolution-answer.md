**1. Commit**

No. `Fin N → Fin N` fixes the square-matrix bookkeeping, but `one bLayer = output layer = input boundary` hits the same wall. The real resolution is:

`single Fin N endomorphism + one frameB-style dependency grading`

not

`single Fin N endomorphism + raw layer grading`.

**2. What `frameB` Is**

`frameB : Fin 27 → ℕ` should be understood as an ordered dependency/SCC grading on the shared coordinate index set.

For row `i`, column `j`, draw an edge `j → i` when the derivative entry can be nonzero. The needed theorem is exactly:

```lean
frameB j > frameB i → DFrame i j = 0
-- equivalently:
DFrame i j ≠ 0 → frameB j ≤ frameB i
```

So `frameB` is not merely the output `[9,9,9]` layer grading, and not merely the input `[12,12,3]` boundary grading. It may be a common refinement/interleaving of both, plus further splitting by within-layer role/SCC structure. The 13 blocks are allowed not to visibly align with either raw partition because their job is to topologically order dependencies, not to restate layers.

What makes `frameB i` and `frameB j` comparable is the shared `Fin 27` identification. The semantic proof still talks about “output layer of row `i`” and “input boundary of column `j`”, but the determinant proof compares only the dependency rank `frameB`.

**3. Opaque-Width Design**

Use a single grading, but not the naive output `bLayer`.

Minimal data for the grading author:

```lean
outLayer    : Fin N → Layer      -- via output reshape e / FlatIdx
inBoundary  : Fin N → Boundary   -- via input chart reading / ChartIdx
frameB      : Fin N → Block
```

plus the bridge theorem:

```lean
DFrame i j ≠ 0 → frameB j ≤ frameB i
```

proved from:

```lean
DFrame i j ≠ 0 → inBoundary j ≤ outLayer i
```

together with the within-layer/role/SCC analysis.

Two independent row/column reindexings into matched blocks are more general but less clean: then every diagonal block needs an explicit equal-cardinality proof. With one shared `Fin N` and one `frameB`, square blocks are automatic.

**4. Cheapest `#eval` Check**

Before building the general proof, run the support-violation check on `(3,3,3,3)`:

```lean
#eval ((List.finRange 27).bind fun i =>
  (List.finRange 27).filterMap fun j =>
    if frameB j > frameB i ∧ DFrame3333 i j != 0 then
      some (i, j, frameB i, frameB j, DFrame3333 i j)
    else
      none)
-- expected: []
```

Also print block sizes:

```lean
#eval frameBBlockSizes
-- expected: [1,1,3,3,3,3,1,1,1,7,1,1,1]
```

The first check is the decisive one. Alignment tables with `[12,12,3]` and `[9,9,9]` are diagnostic; vanishing above `frameB` is the proof target.