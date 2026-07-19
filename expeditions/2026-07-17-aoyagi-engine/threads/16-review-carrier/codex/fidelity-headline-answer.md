## 1. VACUITY VERDICT

Non-vacuous, but case 2 has a specification gap.

- **(a) Yes. (OBSERVED)** `DivBirthInv_conRoot` inhabits the root invariant, and `DivBirthInv_conOracle_stepChildren` transports it to every emitted child.

- **(b) Yes. (OBSERVED/derived directly from definitions)** For `L = 2`, `M = (2,2,4)`, `conRoot` emits a case-2 branch with residual dimensions `2 × 2`, hence `dCenterOfNode = 4 > 0` and `flatDim M = 12`. Moreover, following `case2 → case2 → rollover` reaches a genuine case-1 state at layer `1`, cleared `0`, target `1`, with center dimension `1 + 1·4 = 5`. Thus both case 1 and case 2 occur under maintained `DivBirthInv`.

- **(c) Yes, semantically. (OBSERVED)** In case 2,
  `centerSelCase none = resBlockOrFallback`, which is injective whether it chooses the real block or `Fin.castLE`. Thus vacuous `RealCNodeFacts` would also validate any bogus-but-injective case-2 selector. The theorem proves only that `cNodeOf`’s outer fallback is not used; it does not prove that `resBlockOrFallback`’s inner fallback is not used.

  This is not an actual reachable counterexample: the conOracle bounds imply block fit. But that implication is absent from the conclusion/proof, so advertised raw-coordinate fidelity is not certified.

## 2. SCOPE VERDICT

**(OBSERVED)** The theorem concerns only the root node of the subtree built from the supplied `s`. It is universally reusable at reachable descendant states, but does not itself quantify over every node of the original root tree.

The missing coverage lemma should have the shape:

```lean
∀ node ∈ ResolutionTree.nodes (buildTree M (conOracle M) s), ∀ hd,
  cNodeOf M node hd = realCNode M node hd
```

It requires well-founded induction over the construction, using:

- the headline at the current subtree root;
- `DivBirthInv_conOracle_stepChildren` for each child;
- the induction hypothesis on every child subtree;
- `DivBirthInv_conRoot` for the final root specialization.

Use `ResolutionTree.nodes`, not merely `stepEdges`. This is a separate coverage obligation, although the docstring’s “every built-tree branch node” wording overstates this theorem’s standalone scope.

## 3. “DivBirthInv-ONLY” VERDICT

Legitimate for this conditional theorem.

**(OBSERVED)** When `nodeOccMin = some target` but `chooseMin s target = none`, `conOracle` definitionally returns `oracleTerminal`; `buildTree_terminal` therefore produces a leaf, which cannot equal a branch. There is no conOracle path where chooser failure still emits a branch.

No assumption is smuggled in. However, this proves only:

> if a branch was emitted, its chooser succeeded.

It does not show that reachable occupied states never terminate prematurely. That global totality property still belongs to `OracleInv` or its chooser-totality consequence.

## 4. DISJOINTNESS ATTACK

No collision found; this part is sound.

- **Earlier birth layer:** `flatCoordOf_val_inj` forces equality of layer indices. Therefore `a < node.layer` makes collision impossible before row/column arithmetic is considered.

- **Current birth layer:** if equality forces `a = node.layer`, `hfresh f` gives `b < cleared`, whereas every block row is `cleared + r ≥ cleared`.

- **Correct divisor:** **(OBSERVED)** the same `f` returned by `chooseMin` is passed to `case1Decision`, and `toStepData` copies its `divBirthCoord`. Thus `hfresh f` is exactly the freshness fact for the merged divisor.

A merged divisor with `a = layer` and `b ≥ cleared` directly contradicts `DivBirthInv`.

## 5. NAME-HONESTY

The formal equation in the name is accurate, but the fidelity interpretation overclaims.

A more honest local name would be:

```text
cNodeOf_eq_guardedCNode_at_buildTree_root
```

or at least:

```text
cNodeOf_eq_realCNode_at_buildTree_root
```

To retain the stronger “intended coordinates” language, add:

1. case-2 equality of `resBlockOrFallback` with `resBlockCenterIndices`;
2. the all-internal-nodes lifting lemma above.

## 6. SHARPEST RESIDUAL DOUBT

Demand a kernel-checked case-2 reduction lemma proving the block-fit guard and hence:

```lean
resBlockOrFallback ... = resBlockCenterIndices ...
```

Without that, the headline certifies only outer-fallback elimination, not actual residual-block fidelity.