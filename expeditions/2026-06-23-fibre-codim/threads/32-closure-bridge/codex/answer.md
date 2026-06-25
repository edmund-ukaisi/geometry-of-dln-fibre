**Verdict:** prove `hClosure` by the **dimension/codimension sandwich**, not by global closure equality.

**(A)** Yes. If
```lean
vanishingIdeal k (canonicalCoord d '' Σ^r)
  = vanishingIdeal k (canonicalCoord d '' Σ̄^r)
```
then `hClosure` is immediate by unfolding `varietyDim`; exact ideal equality is stronger than radical-insensitivity. If you only had equal radicals, use `ringKrullDim_quotient_eq_of_radical_eq`. `varietyDim` is literally quotient Krull dimension by the vanishing ideal. See [NullstellensatzCodim.lean](/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/NullstellensatzCodim.lean:139).

**(B)** The global vanishing-ideal equality is mathematically true for feasible `r`, but it is **not cheap from facts 1–8 alone**. G2 plus per-orbit closure proves:
```lean
canonicalCoord '' orbitRankLocus M = repClosure (orbitSet M)
```
per orbit; see [OrbitClosure.lean](/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/OrbitClosure.lean:993). But to cover all `corner < r` strata you still need the extra rank-raising/density theorem:

> every corner-`≤ r` orbit closure is contained in some corner-`r` orbit closure, equivalently every maximal component of `Σ̄^r` meets `Σ^r`.

That is the quiver orbit-closure-order density theorem, not a consequence of preimage density under `mult`, and not supplied just by H-sweep. Name it something like:
```lean
orbitRankLocus_subset_rankExact_component
-- or
productRankLocusLE_subset_repClosure_productRankLocus
```
The H-sweep route does not remove this: `Σ^r = H · fibre(E)` is landed, but the dimension/closure consequence is explicitly not proved and is identified as hard in [EndBaseChangeSweep.lean](/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/EndBaseChangeSweep.lean:15).

**(C)** The cheap escape is codimension. You do **not** need irreducibility of `Σ̄^r`. The repo has the reducible catenary bridge:
```lean
codimRepCanonical Z + varietyDim (canonicalCoord d '' Z) = Nat.card (RepCoord d)
```
for nonempty `Z`, no prime/irreducible hypothesis; see [RadicalCatenary.lean](/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/RadicalCatenary.lean:179).

Proof shape:

1. `Σ^r ⊆ Σ̄^r`, hence `codim Σ̄^r ≤ codim Σ^r` by `codimRepCanonical_mono` in [FibreCodim.lean](/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/FibreCodim.lean:53).

2. Pick a minimising Kostant partition `m₀ ∈ kostantPartitions d r`. Its realizer has exact product rank `r` by `rank_mult_realizerD`; see [ThetaComponentCount.lean](/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/ThetaComponentCount.lean:152).

3. `SigmaCodim` already proves that this realizer’s orbit closure attains `codim Σ̄^r = C`; see [SigmaCodim.lean](/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/SigmaCodim.lean:101).

4. The orbit of that realizer is contained in `Σ^r`, and its closure has codim `C`, so `codim Σ^r ≤ C = codim Σ̄^r`.

5. Thus codims are equal. Apply reducible catenary to both nonempty loci and cancel the same finite ambient card to get `varietyDim Σ^r = varietyDim Σ̄^r`.

This proves the `≥` side without proving `Σ̄^r = closure(Σ^r)`: exact rank contains a top-dimensional piece; lower-dimensional closed junk cannot change `varietyDim`.

**(D) Ranking**

1. **Dimension sandwich:** cheapest provable route. Roughly 6–10 small lemmas if you factor out the top-orbit witness and an `ENat` cancellation wrapper. Biggest risk: handling `codim`/`varietyDim` cancellation cleanly in `ℕ∞`, but the reducible catenary lemma makes this modest.

2. **Set-closure route:** stronger than needed. Provable only after the rank-raising density theorem above. Biggest risk/kill-condition: a component of `Σ̄^r` trapped inside `Σ̄^{r-1}`. If that existed, vanishing-ideal equality would be false. Paper says it does not for feasible `r`, but it is extra formalization.

3. **Orbit-image/H-sweep route:** most expensive. It needs associated-bundle/product-dimension or exact-rank chart trivialization/flatness. Do not use it for `hClosure`.

**(E)** For `d = (2,2,2)`, `r = 1`: `card = 8`, `C = 1`, so reducible catenary gives
```text
dim Σ̄^1 = 8 - 1 = 7
dim Σ^1 = 8 - 1 = 7
```
The route gives `7 = 7`. For `r = 0`, `Σ^0 = Σ̄^0` by rank `= 0 ↔ ≤ 0`, so it is trivial. For maximal feasible `r = min_i d_i`, `Σ̄^r` is the whole space and exact rank is dense/nonempty; the codim route gives dimension `card`. For infeasible `r`, do not state the theorem without a nonemptiness/feasibility hypothesis.