## VERDICT

CANNOT-DETERMINE — the rollover calculation is valid, but existence of a reachable parent satisfying the required all-left invariant is not established.

## STEP CHECK

1. **OK** — conditional on such a first edge existing; its reachability is unstated.
2. **OK** — for \(N \ge 2\), the arithmetic gives `hlast`.
3. **WRONG** — locally the rollover child satisfies the oracle and pins, but existence of the required reachable `p` is unstated.
4. **OK** — rollover implies `cleared ≥ widthMinUpto ≥ 1`, hence `edgeδ = false`.
5. **WRONG** — `FoldStepInvAt → LastLayerInv` is only conditional. No `FoldStepInvAt`, all-left invariant, or suitable `e,p` is shown to exist.
6. **OK** — conditional on step 5; the child is nonterminal and pure pullback preserves zero at the origin.
7. **OK** — all-zero residues make every proposed generator sum zero.
8. **WRONG** — this proves a conditional obstruction, not a counterexample satisfying all hypotheses jointly.

## FIX

`hparent` eliminates the proposed rollover-into-\(N-1\): together with `hlast`, parent and child both have layer \(N-1\). Rollover-out was already excluded by `hlast`.

It does **not** establish soundness from the supplied facts. It still admits all layer-preserving steps at \(N-1\), including merges and δ=0 clears; an all-left invariant there would reproduce the same zero-pullback issue, though its reachability is likewise unproved.

A cleaner guard is:

```lean
ed.nextState.layer = p.conState.layer
```

or “`ed` is not a rollover.” On real listed transitions under `hlast`, this is equivalent to `hparent`, not strictly weaker. No strictly weaker sound guard can be certified from the given definitions.