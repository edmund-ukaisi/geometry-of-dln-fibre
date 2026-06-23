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

## Honest scope / what is NOT here

- **Abstract / route-independent.** The per-node min fact `hstep_min`, the leaf base `hbase`, and the
  value-side min arithmetic `harith_min`/`harith_base` are HYPOTHESES — the producer (a5f5ceb1's cover
  atom) discharges them. This file is ONLY the recursion/min-collapse DESIGN; it does NOT prove the
  per-node min fact (the geometric cover content) nor the value arithmetic instantiation.
- The instantiation (`rlctOf := rlctAtOn (dlnLoss M 0) deepest`, `redOf := schurStateRed`,
  `mkOf`/`nRegOf`/`lamOf` := the concrete combinatorial functionals, `degenChild := isLeafNode ∘ …`) is
  the cross-branch wiring (#151-class), to be done once the cover atom + the value min-arithmetic land.
- The value-side min arithmetic `lamOf M = min (mkOf M/2) (nRegOf M/2 + lamOf (redOf M))` (the genuine
  point-min telescope of `lambdaCore`) is NOT yet a proven lemma on-branch — it is the combinatorial
  obligation the instantiation supplies (analogous to `BindingArith.bind_harith_step` for the additive
  spine, now in min form).

## Related open item (noted, not mine)

`RouteMRecursion.lean:209` carries the named `routeStep` branch sorry (the general rank-pattern read /
per-cell admissible-`Mval` codims; realizability is the COVER's job #104). That is a5f5ceb1's GE-producer
territory, distinct from this outer spine — no collision. Flagged per the controller for possible fold-in.
