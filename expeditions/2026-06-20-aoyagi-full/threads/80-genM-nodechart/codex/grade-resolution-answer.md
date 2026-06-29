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
---

## SUPERSEDED (2026-06-29): single-global-frameB is M-NON-UNIFORM

genm-interior's deeper check WALLS the single-global-frameB-SCC resolution above: the SCC block
STRUCTURE is M-DEPENDENT. sympy on T3333's actual SCC = 11 blocks [1×6, 3×4, 9] ≠ frameB's hand-tuned
13; the K-coupling block size depends on the per-boundary K-core dim t_s, which varies with M. The
(3,3,3,3) #eval validated frameB for THAT ONE M — but there is NO uniform opaque-width frameB. LESSON:
validate a candidate grading across MULTIPLE M (the #eval-at-one-M caught the layer mismatch but missed
M-uniformity).

TRACTABLE ROUTE (genm-interior re-speccing, gated): det_comp PER-PIECE — DFrame_M = ∏ non-disjoint
TRIANGULAR pieces via listProd_clm_abs_det + LOCAL uniform per-piece det lemmas, ordered by b-0's
one-sided locality. NOT a global grading (sidesteps M-dependence). b-0 capstone + reader/block-locality
feed it. Validate per-piece det uniformity at a 2nd M (2,3,2): flatDim 12, L=2, distinct K-core dims —
a good decorrelated second node from (3,3,3,3)'s L=3.
