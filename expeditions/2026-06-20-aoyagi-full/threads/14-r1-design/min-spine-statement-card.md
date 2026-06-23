# Statement card — `binding_recursion_of_min_step` (the R1 cover-route MIN spine)

- **Status:** PROVEN, sorry-free, clean-three (`#print axioms` = `[propext, Classical.choice, Quot.sound]`,
  no `sorryAx`). Branch `origin/fm3/routem-ga` @78df5d21. File
  `lean/DLNFibre/DLN/RLCT/Validate/BindingMinSpine.lean` (~95 LoC). Builds GREEN.
- The OUTER min-recursion of the binding R1, distinct from a5f5ceb1's per-node atom/cover (no collision).

## The theorem

```text
binding_recursion_of_min_step
    (redOf : (Fin (L+1)→ℕ) → (Fin (L+1)→ℕ))
    (mkOf nRegOf lamOf : (Fin (L+1)→ℕ) → ℚ)
    (rlctOf : (Fin (L+1)→ℕ) → ℝ≥0∞)
    (degenChild : (Fin (L+1)→ℕ) → Prop)
    (hstep_min : ∀ M, ¬ degenChild M →
        rlctOf M = min (ofReal (mkOf M / 2)) (ofReal (nRegOf M / 2) + rlctOf (redOf M)))
    (hbase     : ∀ M, degenChild M → rlctOf M = ofReal (mkOf M / 2))
    (harith_min : ∀ M, ¬ degenChild M →
        lamOf M = min (mkOf M / 2) (nRegOf M / 2 + lamOf (redOf M)))
    (harith_base : ∀ M, degenChild M → lamOf M = mkOf M / 2)
    (hdrop : ∀ M, ¬ degenChild M → ∑ i, redOf M i < ∑ i, M i)
    (hmk : ∀ M, 0 ≤ mkOf M) (hnReg : ∀ M, 0 ≤ nRegOf M) (hlam : ∀ M, 0 ≤ lamOf M)
    (M) : rlctOf M = ofReal (lamOf M)
```

## What it is / English gloss

The COVER route presents the per-node RLCT as a `⨅`-min over pivot branches — a **clean point-min at the
value level** (adjudicator-confirmed: no box-threading in the spine; the box-recursion is internal to
a5f5ceb1's GE producer). So the per-node fact is the SINGLE min `hstep_min`: the node is the smaller of
its own Morse value `mkOf M / 2` (the no-descent cell) and the descent `nRegOf M / 2 + rlctOf (redOf M)`
(into the reduced child). The spine closes this to `rlctOf M = ofReal (lamOf M)` (`= ½·minAdm`) by strong
induction on `∑ M`.

The min-collapse at the step branch (the load-bearing chain): recurse on the child →
`rlctOf (redOf M) = ofReal (lamOf (redOf M))`; then
- `ofReal (nRegOf M/2) + ofReal (lamOf (redOf M)) = ofReal (nRegOf M/2 + lamOf (redOf M))`
  (`ENNReal.ofReal_add`, needs `0 ≤ nRegOf M/2`, `0 ≤ lamOf (redOf M)` — from `hnReg`/`hlam`);
- `min (ofReal (mkOf M/2)) (ofReal (nRegOf M/2 + lamOf (redOf M)))
   = ofReal (min (mkOf M/2) (nRegOf M/2 + lamOf (redOf M)))`  (`ENNReal.ofReal_min`, unconditional);
- `= ofReal (lamOf M)`  (`harith_min`, with the ℚ→ℝ min cast `Rat.cast_min` via `push_cast`).

`degenChild` guards termination: the descent branch recurses only when `¬ degenChild` (the child
`redOf M` strictly decreasing `∑M` via `hdrop`); at a `degenChild` node the min has collapsed to the
Morse branch `mkOf M / 2` (`hbase`/`harith_base`). Identical termination shape to the proven additive
`binding_recursion_of_step` (`BindingRecursion.lean`); the MIN variant transfers cleanly.

## Update — `harith_min` PROVEN + spine base corrected (@c3df23ef)

The value-side `harith_min` is now a PROVEN on-branch lemma (`BindingMinArith.lean`, clean-three):
- **`lambdaCore_min_telescope`** (= `harith_min`): GIVEN the cover's minimal-codim min identity at the
  ℤ-`inf'` level `minAdmZ M = min (mk) (n + minAdmZ (redOf M))` (cert-104b V4, a5f5ceb1's combinatorial
  content), proves `lambdaCore M = min (mk/2) (n/2 + lambdaCore (redOf M))`. Pure ½-scaling, robust for
  ALL `L`, `redOf`-agnostic.
- **`lambdaCore_le_front_mul`** (F2, the `D₀` bound): `lambdaCore M ≤ M₀M₁/2` (`inf'_le` at
  `zero_mem_Adm` + `Mval_zeroT_eq`).
- **`lambdaCore_eq_minAdmZ_half`**: `lambdaCore = ½·(ℤ inf')`.

**Adjudication (pen-and-paper obstruction cert + decorrelated Codex, 673 nodes sympy):** the value-level
min is NOT a genuine selecting min — the descent branch `nReg/2 + lambdaCore(redOf M)` EQUALS
`lambdaCore M` unconditionally (additive F1), the `mk/2` leaf branch only DOMINATES (F2). The genuine
selecting min lives in the GEOMETRIC cover (raw smooth-block count, where `D₀` binds on wide-tail nodes
like `(2,2,4)`), not in `lambdaCore`. `harith_min` is true + honestly labelled; the `mk/2` branch is
value-level dead weight (caveat in `BindingMinArith.lean`).

**Spine base CORRECTED:** the obstruction found `harith_base : degenChild M → lamOf M = mkOf M/2` is
FALSE for the geometric `mkOf := M₀M₁` (counterexample `(1,2,1)`: `lambdaCore=1/2 ≠ 1=mkOf/2`). FIXED:
`hbase` generalized to `degenChild M → rlctOf M = ofReal (lamOf M)` (the `#70` Morse base asserts the
conclusion at the leaf — honest + maximally general; the producer supplies the base value), dropping the
false-able `harith_base`. The now-unused `hmk` (`0 ≤ mkOf`) removed (the `mkOf/2` branch is handled
unconditionally by `ofReal_min`). Spine still PROVEN, clean-three.

## Spine's REMAINING hypotheses (post this round)
- `hstep_min` — the geometric per-node min fact (a5f5ceb1's cover atom, #9). **The one genuinely-open
  input.**
- `hbase` — the `#70` Morse base (`degenChild M → rlctOf M = ofReal (lamOf M)`); the additive spine's
  `hbase` + arith supplies this (the value `= nReg/2` at the leaf-child level).
- `harith_min` — **PROVEN** (`lambdaCore_min_telescope`, given the V4 minAdm-min identity).
- `hdrop`/`hnReg`/`hlam` — termination + nonneg; fall out of `BindingArith`/`MinAdmMono` (the `bind_*`
  + `chainWidthSum_schurStateRed_lt` + `bind_hlam`), to be wired at instantiation.

## Related open item (noted, not mine)

`RouteMRecursion.lean:209` carries the named `routeStep` branch sorry (the general rank-pattern read /
per-cell admissible-`Mval` codims; realizability is the COVER's job #104). That is a5f5ceb1's GE-producer
territory, distinct from this outer spine — no collision. Flagged per the controller for possible fold-in.
