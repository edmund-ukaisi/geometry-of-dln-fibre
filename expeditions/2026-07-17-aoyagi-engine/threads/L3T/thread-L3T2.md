# Thread L3T2 (succeeds seat-L3T at context limit)

Branch `expedition/aoyagi-engine-L3T2`, based on the post-redirect tip. Lanes: 0 port
LeafGeometryWire; 1 realBranch_terminal_edgeδ + terminal_edge_stepInv re-wire; 2 realBranch_cover
+ realBranch_descendView; 3 case2_preserves_stepInv; 4 GeneratorCleared consume-fit + Case1Wire dedupe.

## Status
- Lane 0 DONE — LeafGeometryWire.lean ported file-level, green, axiom-clean; integrated on canonical.
- Lane 2 DONE — realBranch_descendView (obtain-projection) + realBranch_cover (cleared=0 block
  equality); both `[propext, Classical.choice, Quot.sound]`.
- Lane 1 BLOCKED (STOP-ON-SUSPECT) — see kill-condition below; hpos fix queued to elder.
- Lane 3 IN PROGRESS.

## KILL-CONDITION (permanent record): realBranch_terminal_edgeδ MUST carry `hpos : ∀ k, 0 < d k`

`realBranch_terminal_edgeδ` as first extracted had NO `hpos`. It is then **FALSE**. Do not drop `hpos`.

Statement (broken form): `(hterm : N ≤ ed.nextState.layer) (hbranch : (p.extend ed).IsRealBranch e) ⊢
edgeδ d p = false`.

**Why the only proof route needs positivity.** The conclusion needs `p.conState.cleared ≠ 0`. A
terminal-reaching edge forces a ROLLOVER (case11/case12/case2 keep the layer — EngineConstruction
stepCase11/stepAppendAdvance; only stepRollover advances; and a non-terminal parent has `layer < N`).
The oracle rollover guard (conOracle) is `widthMinUpto d (layer+1) ≤ cleared`. To get `cleared ≥ 1`
you need `widthMinUpto d N ≥ 1`, i.e. `widthMinUpto_pos` — which REQUIRES `∀ i, 0 < d i`.
`widthMinUpto d n = (univ.filter (·≤n)).inf' _ d` (EngineDefs:154), so `d 0 = 0 ⟹ widthMinUpto d n = 0`
for every `n`. Positivity is not otherwise available: `e`'s existence does not force it (with `d 0 = 0`
the `d₁×0` matrix factor is a single point, so the homeomorphism still exists); there is no
`IsRealBranch → StateInvariant` reachability lemma; and `StateInvariant.live_width` is only an UPPER
bound on `cleared`.

**Concrete counterexample (`N ≥ 1`, `d 0 = 0`).** `widthMinUpto d ≡ 0`, so from `conRoot` (layer 0,
cleared 0) the rollover guard `0 ≤ 0` fires at every layer. `N−1` successive rollovers build a real
branch `p` at layer `N−1`, `cleared = 0` (each step: case = rollover, center `= ∅ = canonCenterOf
rollover`, pivot free since `canonPivotOf rollover = none`, shear `id` satisfies `ShearWithinCarveRaw`).
The rollover edge `ed` off `p` has `ed.nextState.layer = N ≥ N` (`hterm` ✓) and
`(p.extend ed).IsRealBranch e` ✓ — yet `edgeδ d p = decide (0 = 0) = true ≠ false`. Refuted.

**Fix (wiring-compatible):** add `hpos : ∀ k, 0 < d k`. The sole consumer `terminal_edge_stepInv`
already carries `hpos` (as do the case1/case2/lastLayer leaves), so it passes down — no downstream
statement change. This is an extraction oversight (every sibling redirect leaf has `hpos`; only this
one dropped it), the cheapest defect class.
