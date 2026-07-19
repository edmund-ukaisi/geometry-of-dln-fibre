## 1. COUNTEREXAMPLE VERDICT

**Yes.** For `t = .leaf l`, `lc.2 = id`, so LHS is `1`; setting a divisor coordinate with exponent at least `2` to zero makes RHS `0`.

The meaningful repair is a `PathLedgerCoherent t` hypothesis. Concretely, specialize to `t = buildTree M (conOracle M) conRoot` and prove that coherence. Pinning to `buildTree … s` for arbitrary `s` is insufficient: `s` may already contain divisors.

## 2. COHERENCE VERDICT

**Yes.** Chain rule plus determinant atoms only produces intermediate-point pivot factors; it contains no information about `stepUpdate`, divisor reindexing, or accumulated exponents.

The required invariant is a one-step relative Jacobian/ledger cocycle:

```lean
J_child w = |det Dβ_edge w| * J_parent (β_edge w)
```

including the persistent/new-divisor coordinate reindexing. It telescopes from `J_conRoot = 1`. This is stronger than map-fidelity clause (D).

## 3. PER-EDGE DET LEMMA

All three are **CONFIRMED** in this Mathlib pin and already used together in [RouteMConjBlock.lean](/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/aoyagi-engine/t11-fold/lean/DLNFibre/DLN/RLCT/Validate/RouteMConjBlock.lean:56).

1. Conjugation:

```lean
LinearMap.det_conj
```

It proves determinant invariance of `e ∘ f ∘ e.symm`. Use `e := CLE.symm.toLinearEquiv`. This is cleaner than determinant-inverse cancellation.

2. Block product:

```lean
LinearMap.det_prodMap
```

Use it after `.toLinearMap`; finite-dimensionality supplies its `Module.Free`/`Module.Finite` assumptions. There is no needed `ContinuousLinearMap.det_prodMap` wrapper.

3. Product derivative:

```lean
HasFDerivAt.prodMap (p := p) hf hg
```

It returns derivative `f'.prodMap g'` for `Prod.map f g`.

Likewise, composition uses `LinearMap.det_comp`; `ContinuousLinearMap.det` is an abbreviation over the underlying linear map.

## 4. RECOMMENDATION

**C.** Bank the per-edge atom, retire the false SPECIFY statement, and split the work into:

- a path-product theorem from chain rule;
- a separate built-root ledger-coherence theorem.

Before attempting the latter, repair the current virtual atlas: it inherits a fixed leaf `divCoord`, while different fan-out pivots use different `cNodeOf … pivot` coordinates, and the documented source gauge is absent from `geoChartMap`. Adding only `htree` would conceal rather than resolve that mismatch.