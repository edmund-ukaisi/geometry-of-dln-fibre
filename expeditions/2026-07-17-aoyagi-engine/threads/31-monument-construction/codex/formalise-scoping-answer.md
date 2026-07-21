## 1. SCOPING VERDICT

The combinatorial/geometric split is correct, but rebuilding the combinatorial layer is not the best increment in this checkout.

Fact, from source inspection: the retired engine already contains operational versions of the required results:

- `isFullMonomialization_buildTree_conRoot`
- `minAdm_le_terminalExponents`
- `tStar_realized`
- `o5_core_realized`

See [EngineConstruction.lean](/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/agent-a8b189ffcfdbcd4cb/lean/DLNFibre/DLN/RLCT/Engine/EngineConstruction.lean:2540) and [O5Realization.lean](/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/agent-a8b189ffcfdbcd4cb/lean/DLNFibre/DLN/RLCT/Engine/O5Realization.lean:869). I found no source `sorry` in those modules, but did not perform a fresh `#print axioms` audit.

Best session scope: salvage these results through a small adapter into the exact `bexp/jac/bindingAxes/qipMin` vocabulary of `exists_coreResolution`. Do not rebuild the recursion or revive its retired geometric `ChartBridge`.

A genuinely full-record restricted theorem is plausible for the scalar-chain subclass `∀ k, d k = 1`: undo `e` by a linear coordinate change, after which the sole generator is `∏ uₖ`; one invertible linear chart has `bexp = 1`, `jac = 0`, and `qipMin = 1`. This ranks below the adapter for advancing the general theorem, but above a duplicated combinatorial module as a full-record sanity theorem.

`N = 1` at arbitrary widths requires the full projective blow-up of the origin with `flatDim d` pivot charts. It is honest and useful, but its determinant and compact-sector cover are unlikely to fit safely into one session. Width ≤ 2 is still worse.

## 2. ENCODING

- Operational tree: biggest trap is dependent transport across changing `Fin numDiv`/`Fin numB`. The existing engine has already paid this cost.
- Direct closed forms: biggest trap is fabricating valid-looking divisors that no recursive branch produces.
- Profiles: biggest trap is false surjectivity. Not every admissible profile is realized, so indexing charts by all `Adm` profiles makes `hattain` tautological for the wrong reason.

Pick the operational tree as source of truth, with a closed-form, fixed-ambient-dimension view as the public adapter.

Be especially careful about indexing. Paper \(b_1\) should normally be Lean index `0`; paper \(b_0=1\) is only a recurrence convention and must not enter `monomialFam`. Thus the formula is effectively

```text
bexp i a = 1 iff threshold(a) ≤ i.val
```

not `threshold(a) < i.val`. Otherwise the Lean zeroth monomial is `1`, contradicting `hbind`; it also fails immediately when `M' = 1`.

## 3. FIDELITY TRAP

The risk is substantial: closed-form `bexp/jac` can satisfy `hchain`, squarefreeness, `hlb`, and even artificial attainment without describing any composed substitution.

The cheapest decisive check is a refinement theorem, not more numerical examples:

1. Prove the threshold and Jacobian-ledger formulas are preserved by each Case 1(1), Case 1(2), Case 2, and rollover transition.
2. Fold those lemmas along every root-to-leaf path.
3. Prove the attaining leaf is reachable by the operational steering relation.

This can be done over formal monomial exponent vectors; it does not require analytic maps or the cover. The four examples should remain regression tests only.

## 4. THE ENTANGLEMENT

No proper fragment of the existential target can be banked without actual `Chart`s. Lean cannot store “half a witness” without another assumption or `sorry`.

The best leaf-adjacent unit is an assembly interface:

```text
AtlasCombinatorics d
AtlasRealizes res data
```

where the first record contains fixed-axis `bexp`, `jac`, chain, squarefreeness, `hlb`, and `hattain`, and `AtlasRealizes` identifies those fields with the actual `res.charts`. Then prove, sorry-free:

```text
AtlasRealizes res data → target’s hlb ∧ hattain
```

and an assembly theorem turning geometric realizations plus the atlas cover into the exact existential target.

This belongs initially under `DLNFibre.DLN.Aoyagi`, not `Core`: it is presently DLN-specific and repository policy discourages speculative lifting.

## 5. BIGGEST RISK

The main risk is an orphaned second combinatorial model: green, elegant, and disconnected from the actual substitutions and charts. That risk is already concrete because the operational combinatorics exists. Reuse it and spend the session on the exact adapter/refinement seam. For the cover, build the explicit finite max-pivot-sector compact cover; cite rather than attempt a general Hironaka properness theorem.