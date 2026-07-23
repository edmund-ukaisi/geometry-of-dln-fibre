Verdict: use (b) as the public lemma, proved by the concrete unfolding/induction of (a). Do not expose an abstract theorem deriving it from `hslot`.

The current statement still quantifies over arbitrary `e` in [Case1Wire.lean:386](/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/aoyagi-engine/L4D/lean/DLNFibre/DLN/Aoyagi/Case1Wire.lean:386). A concrete proof therefore first requires `e = canonFlatten d`, or an explicit root chart-frame hypothesis. `IsLinearMap e` is insufficient.

Why a direct (a) proof is risky:

- The outgoing case-11 shear being `id` only means it does not destroy the factor. It does not create it; the factor originates at the reused divisor’s earlier birth.
- `foldResid p` is not definitionally `coreGen ∘ foldG`: δ=1 steps use `blockBlowupCoordQuot`, replacing a pivot by `1` [MonumentAtlas.lean:474](/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/aoyagi-engine/L4D/lean/DLNFibre/DLN/Aoyagi/MonumentAtlas.lean:474). A one-shot product expansion can accidentally factor the unnormalised product or a factor already absorbed into `foldB`.
- Consequently, unfolding the whole prefix requires an inductive normal form anyway—effectively route (b).

A safe intermediate predicate is:

```lean
MergeBoostSplit resid e₂ partial extra center :=
  ∀ j, ∃ α β,
    Continuous α ∧ Continuous β ∧
    IgnoresCenter α center ∧ IgnoresCenter β center ∧
    ∀ u,
      resid j u =
        ∑ i ∈ partial, α i u * u i +
        u e₂ * ∑ i ∈ extra, β i u * u i
```

Then prove two separate results:

1. `foldResid_case11_mergeBoostSplit_canon`: about the actual
   `foldResid d (canonFlatten d) p`, canonical real branch, and canonical case-11 center.
2. `MergeBoostSplit.deg1SupportedOn`: purely algebraic assembly of the desired coefficients.

Natural supporting lemmas are:

- Center geometry:
  `supportAt = partial ⊔ extra`,
  `ed.center = {e₂} ⊔ partial`,
  `extra ∩ ed.center = ∅`, and `e₂` is cross-layer.
- Root frame: matrix-entry expansion for `coreGen d (canonFlatten d)`.
- Birth step: the selected divisor introduces exactly one `e₂` factor on the appropriate complementary rows.
- Suffix transport: intervening canonical steps preserve both the factor and coefficient independence.
- Threshold split: partial weights contain no `e₂`; extra weights are exactly `e₂ * remainder`, with the remainder independent of `e₂`.
- Closure lemmas for `Continuous` and `IgnoresCoords` under finite sums, products, and projections outside the center.

Continuity is genuine without division if the factor is exposed syntactically. `blockBlowupCoordQuot` is `1` at the pivot and the original coordinate elsewhere—there is no `/ e₂` [BlockDivision.lean:30](/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/aoyagi-engine/L4D/lean/DLNFibre/Core/Aoyagi/BlockDivision.lean:30). Avoid defining the coefficient as `F/e₂` or as a field-theoretic `b_i/b_j`; construct the residual tail product directly.

`IgnoresCoords` is the harder condition and is not automatic from literal divisibility. You must prove:

- partial coefficients do not read `e₂` or any partial coordinate;
- each `β_i` ignores the entire center;
- every extra coordinate lies outside the center.

Then the pivot coefficient

```lean
c e₂ u := ∑ i ∈ extra, β i u * u i
```

is continuous and ignores the center. A literal factor alone is insufficient: `e₂ * (e₂ + u_i)` is divisible by `e₂` but fails `IgnoresCoords`. Likewise, per-layer affine degree does not exclude the cross-layer term `e₂ * u_partial`, which has two center factors.

Finally, Aoyagi’s ideal equality after regular row/column operations is not by itself enough. The chart-frame lemma must give a pointwise identity for the actual `foldResid`, or transport through cofactors proved to ignore the center. Otherwise route (b) merely repackages another false generality.
tokens used
174,713
Verdict: use (b) as the public lemma, proved by the concrete unfolding/induction of (a). Do not expose an abstract theorem deriving it from `hslot`.

The current statement still quantifies over arbitrary `e` in [Case1Wire.lean:386](/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/aoyagi-engine/L4D/lean/DLNFibre/DLN/Aoyagi/Case1Wire.lean:386). A concrete proof therefore first requires `e = canonFlatten d`, or an explicit root chart-frame hypothesis. `IsLinearMap e` is insufficient.

Why a direct (a) proof is risky:

- The outgoing case-11 shear being `id` only means it does not destroy the factor. It does not create it; the factor originates at the reused divisor’s earlier birth.
- `foldResid p` is not definitionally `coreGen ∘ foldG`: δ=1 steps use `blockBlowupCoordQuot`, replacing a pivot by `1` [MonumentAtlas.lean:474](/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/aoyagi-engine/L4D/lean/DLNFibre/DLN/Aoyagi/MonumentAtlas.lean:474). A one-shot product expansion can accidentally factor the unnormalised product or a factor already absorbed into `foldB`.
- Consequently, unfolding the whole prefix requires an inductive normal form anyway—effectively route (b).

A safe intermediate predicate is:

```lean
MergeBoostSplit resid e₂ partial extra center :=
  ∀ j, ∃ α β,
    Continuous α ∧ Continuous β ∧
    IgnoresCenter α center ∧ IgnoresCenter β center ∧
    ∀ u,
      resid j u =
        ∑ i ∈ partial, α i u * u i +
        u e₂ * ∑ i ∈ extra, β i u * u i
```

Then prove two separate results:

1. `foldResid_case11_mergeBoostSplit_canon`: about the actual
   `foldResid d (canonFlatten d) p`, canonical real branch, and canonical case-11 center.
2. `MergeBoostSplit.deg1SupportedOn`: purely algebraic assembly of the desired coefficients.


- Center geometry:
  `supportAt = partial ⊔ extra`,
  `ed.center = {e₂} ⊔ partial`,
  `extra ∩ ed.center = ∅`, and `e₂` is cross-layer.
- Root frame: matrix-entry expansion for `coreGen d (canonFlatten d)`.
- Birth step: the selected divisor introduces exactly one `e₂` factor on the appropriate complementary rows.
- Suffix transport: intervening canonical steps preserve both the factor and coefficient independence.
- Threshold split: partial weights contain no `e₂`; extra weights are exactly `e₂ * remainder`, with the remainder independent of `e₂`.
- Closure lemmas for `Continuous` and `IgnoresCoords` under finite sums, products, and projections outside the center.

Continuity is genuine without division if the factor is exposed syntactically. `blockBlowupCoordQuot` is `1` at the pivot and the original coordinate elsewhere—there is no `/ e₂` [BlockDivision.lean:30](/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/aoyagi-engine/L4D/lean/DLNFibre/Core/Aoyagi/BlockDivision.lean:30). Avoid defining the coefficient as `F/e₂` or as a field-theoretic `b_i/b_j`; construct the residual tail product directly.

`IgnoresCoords` is the harder condition and is not automatic from literal divisibility. You must prove:

- partial coefficients do not read `e₂` or any partial coordinate;
- each `β_i` ignores the entire center;
- every extra coordinate lies outside the center.

Then the pivot coefficient

```lean
c e₂ u := ∑ i ∈ extra, β i u * u i
```

is continuous and ignores the center. A literal factor alone is insufficient: `e₂ * (e₂ + u_i)` is divisible by `e₂` but fails `IgnoresCoords`. Likewise, per-layer affine degree does not exclude the cross-layer term `e₂ * u_partial`, which has two center factors.

Finally, Aoyagi’s ideal equality after regular row/column operations is not by itself enough. The chart-frame lemma must give a pointwise identity for the actual `foldResid`, or transport through cofactors proved to ignore the center. Otherwise route (b) merely repackages another false generality.
CODEX_DONE exit=0
