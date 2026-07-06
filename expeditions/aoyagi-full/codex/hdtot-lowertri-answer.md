**Verdict:** Route-C `lowerTri` is reachable, but **not wall-free**: `eIn ≠ eOut` is forced, so you must prove the determinant correction `|det eOut · det eIn⁻¹| = 1`; if both maps are only coordinate reindexing CLEs, that proof should be small, not a new mathematical obstruction.

Given vs inferred: the grading obstruction proves a single split cannot work. So `eIn = eOut` is not achievable without contradicting the banked obstruction. Route-C must use a **two-sided rectangular block presentation**.

**Clean Decomposition**
For `L = 2`, use:

- `M'`: the “free Schur frame” input/output block.
  - Input side: `V0 = {K, X, N, E}` slots.
  - Output side: layer-0 output block, the block already handled by `RouteMProjV0Gate`.

- `N'`: the remaining coordinates.
  - Input side: `{W, leaf}` slots.
  - Output side: remaining layer-1 / leaf-generated block, called `Agen1` in your numeric cert.

- `f : M' →ₗ M'`: the Schur-frame derivative
  `schurFrameDeriv readX readK readN`, with determinant absolute value `|det K|^(r+c)`.

- `g : N' →ₗ N'`: the leaf/remaining diagonal block, numerically certified and presumably banked as determinant `±1`, so `|det g| = 1`.

- `h : M' →ₗ N'`: the strictly-lower coupling block `J10`.

- top-right block: zero, because the layer-0 output is independent of `{W, leaf}` input slots: `J01 = 0`.

Thus:

```lean
eOut ∘ Dtot ∘ eIn.symm = lowerTri f g h
```

with genuinely different coordinate identifications:

- `eIn`: ambient input flat coordinates → `V0 ⊕ {W, leaf}`.
- `eOut`: ambient output flat coordinates → `layer0 ⊕ Agen1`.

A single split is ruled out by the proven input/output grading mismatch.

**Det Correction**
Inference from your description: if `eIn` and `eOut` are built only from `finSumFinEquiv`, `finCongr`, `chartIdxEquiv`, `paramsEquivFlat`, and similar coordinate permutations/reindexings, then `|det eIn| = |det eOut| = 1`. In that case the correction is a bookkeeping lemma, not a substantive wall.

But it is still a proof obligation. The dangerous point is `paramsEquivFlatCLE`: if it is a pure coordinate flattening/permutation, fine. If any side bundles coordinates using linear combinations, normalizations, triangular changes, or “read” maps with nontrivial scaling, then the correction is no longer automatic.

So: **build Route-C if you can expose `eIn`/`eOut` as permutation CLEs.** Surface a wall only if `eOut`, especially the `Agen1` projection/split, contains a non-permutation linear change.

**≤5-Step Close Order**
1. Define explicit `eIn` and `eOut` as linear equivalences from the ambient flat space to `M' × N'`.
2. Prove the block identity:
   `eOut ∘ Dtot ∘ eIn.symm = lowerTri f g h`.
3. Prove `det lowerTri = det f * det g`.
4. Use banked facts:
   `|det f| = |det K|^(r+c)` and `|det g| = 1`.
5. Prove correction:
   `|det eOut| = 1` and `|det eIn| = 1`, hence
   `|det Dtot| = |det lowerTri|`.

Single riskiest goal: **`|det eOut| = 1`**, because `eOut` is where a hidden non-permutation `Agen1` assembly could enter.

**Where A Green-But-Wrong Proof Hides**
The main trap is the determinant correction:

```lean
det (eOut ∘ Dtot ∘ eIn.symm)
  = det eOut * det Dtot * det eIn.symm
```

You cannot rewrite `det Dtot = det lowerTri` unless the absolute determinant of the side-change factor is `1`.

Secondary traps:

- proving only the Schur block determinant and silently assuming `g` has determinant `1`;
- using the one-sided `slotReadV0` gate as if it were a full ambient block equivalence;
- losing the `J10` reindex and accidentally proving block-diagonal instead of block-lower-triangular.

Decision: **build Route-C**, but make the determinant-correction lemma explicit and early. It should close cheaply if both `eIn` and `eOut` are pure coordinate permutations; otherwise that exact lemma is the real wall.