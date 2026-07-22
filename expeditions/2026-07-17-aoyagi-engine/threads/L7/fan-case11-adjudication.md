# L7 case-11 fan adjudication — does the cover need case-11 interior fan pivots?

Pen-and-paper `pnp-fan`, 2026-07-22. Sharp single-direction adjudication commissioned by the controller
(gates the fan half of the N_p bake; recoord half landed). Frame-in / hypothesis-out; decorrelated from
the elder (who rules in parallel). Exact algebra; the (2,2,2,2) instance is machine-checked in exact
`fractions.Fraction`. No Lean edits.

## THE QUESTION

The membership fan-pin `pivot ∈ canonCenterOf` (my L7 cover fix) contradicts the proven
pivot-preservation machinery: at a **case-11 (merge)** step the center is `{c₀} ∪ B` where `c₀ =
canonPivotOf(case11)` is the merged divisor's IMMUTABLE birth corner (at an EARLIER layer, `DivBirthInv`)
and `B` is a current-layer sub-block. A FREE interior fan pivot `p ∈ B` makes `blockBlowupMap({c₀}∪B, p)`
send `c₀ ↦ w_p · w_{c₀}` (a center coord `≠` the pivot is multiplied, not fixed), MOVING `c₀` and
breaking `stepMapRaw_fixes_parentLedgerCorner` (load-bearing for the (★) Jacobian-collapse chain).

Does the COVER genuinely need the case-11 interior pivots, or does the restricted fan suffice —
**free pivot at case-1(2)/case-2 (fresh-corner) steps + the CANONICAL pivot `c₀` ONLY at case-11 (merge)**?

## VERDICT: **covered-under-(b) — the case-11 interior fan is NOT needed; and (a) ≡ (b) at case-11.**

The case-11 merge child needs ONLY its canonical pivot `c₀`. Every point whose argmax at a case-1 node
lands on a current-layer center coordinate (a `B`-coord) is covered by the case-1(2) **sibling** child —
whose center is a fresh current-layer block that (i) contains `B` and (ii) has `c₀` as a **SPECTATOR**
(fixed), so the sibling's fan is ledger-corner-preserving and covers `B`. The case-11 canonical `c₀`-chart
covers exactly the complementary sector (`c₀` the argmax). The two children partition the node's cover.

Moreover the elder's candidate (a) — "constrain the fan to LEDGER-CORNER-PRESERVING pivots" — **coincides
with (b)**: at case-11 the ONLY pivot in the center that does not move an earlier ledger corner is `c₀`
itself (any `p ∈ B` multiplies `c₀ ∈ center\{p}` by `w_p`), and at case-1(2)/case-2 the center is a
fresh current-layer block containing NO earlier ledger corner, so all its pivots are ledger-preserving
(the free fan). So (a) and (b) are the same restriction, stated two ways. **This is exactly the partition
the engine's SORRY-FREE cover already proves** (`node_selfCover` + `fannedEdges_covers` +
`dCenterOfNode_edgeSum`: at a case-1 node the `dCenterOfNode = 1 + runLen·resCols` pivots are partitioned
across the edges — the case-11 edge owns 1 pivot = `c₀`, the case-1(2) edge owns `runLen·resCols` = the
block).

## THE MECHANISM (general, then the exact witness)

**General.** At a case-1 node (state `layer = S`, `cleared = J`, occupied levels nonempty):
- The oracle emits TWO children of the SAME node: case-1(1) (merge into divisor `f`) and case-1(2)
  (split off a fresh divisor). They are siblings (verified on the (2,2,2,2) tree: same path prefix).
- `c₀ = canonPivotOf(case11) = divBirthCoord(f)`; the merged divisor `f` was born at layer `< S`
  (`DivBirthInv`), so `c₀` is an EARLIER-layer flat coordinate.
- `canonCenterOf(case11) = {c₀} ∪ B`, `B = {layer S, col ∈ [J, J+runLen)}` (current-layer sub-block).
- `canonCenterOf(case12) = {layer S, col ∈ [J, widthMinUpto S)}` (the current-layer running-min block).
  Since `J + runLen = target = divTilde(f) ≤ widthMinUpto S − 1 < widthMinUpto S`, we get **`B ⊆
  canonCenterOf(case12)`**. And `c₀` (layer `< S`) `∉ canonCenterOf(case12)` (a current-layer set), so
  **`c₀` is a SPECTATOR of the case-1(2) blow-up → FIXED.**

The argmax routing at the node (the blow-up is outermost within a step, so the pivot is `argmax` over the
center of the ARRIVING point `x`):
- `argmax` over `{c₀}∪B` is `c₀` ⟹ route to case-11, pivot `c₀`. Its canonical `c₀`-chart reconstructs `x`
  (ratios `x_b/x_{c₀}` have modulus `≤ 1`); the case-12-only coords `∉ {c₀}∪B` are bounded spectators.
- `argmax` is a coord `b ∈ B` (so `|x_b| > |x_{c₀}|`) ⟹ route to the case-1(2) SIBLING, pivot `b`. Since
  `B ⊆ case12-center`, `b` is an available fan pivot there; `c₀` is a spectator (FIXED). Reconstructs `x`.

No point requires a case-11 interior pivot, and every routed pivot is ledger-corner-preserving (`c₀`
stays fixed on both branches). So the cover is complete under the restricted fan, and the pivot-
preservation machinery (`stepMapRaw_fixes_parentLedgerCorner`) holds because the case-11 pivot is always
`c₀` (the pivot is always fixed by `blockBlowupMap`).

## THE WORKED (2,2,2,2) INSTANCE (first case-11 on the real tree; exact)

`d = (2,2,2,2)`, `flatDim = 12`; flat coords `(layer, row, col)`, layers `0,1,2`, each `2×2`. The oracle
trace (faithful `_edgespec_traversal_334.py` state machine, 28 edges) reaches the FIRST case-1(1) at
**Lean layer `S = 1`, `J = 0`, path `['2','2','R']`** (two layer-0 case-2 births + a rollover). It merges
the divisor born at `(layer 0, cleared 1)`; its case-1(2) SIBLING is on the same path prefix `['2','2','R']`.

Exact structure (machine-checked):
- `c₀ = (0,1,1)` (birth corner, layer `0 < 1`); `runLen = 1`, `resCols = 2`, `bump = 2`.
- `canonCenterOf(case11) = {(0,1,1), (1,0,0), (1,1,0)}`, `|·| = 3`, Jacobian exponent `|·|−1 = 2 = bump`. ✓
- `B = {(1,0,0), (1,1,0)}`.
- `canonCenterOf(case12) [sibling] = {(1,0,0), (1,1,0), (1,0,1), (1,1,1)}` (all layer-1). `B ⊆` it (✓);
  `c₀ = (0,1,1) ∉` it → **`c₀` is a spectator of the sibling (FIXED)** (✓).
- Ledger-preserving pivots at case-11: only `c₀ = (0,1,1)` (any `B`-pivot multiplies `c₀` by `w_p`) (✓).

Witnesses (exact rational, all PASS):
- **A — `c₀`-argmax point** `x = (1/3)·e_{c₀} + (1/9)·e_{(1,0,0)}`: the case-11 CANONICAL chart (pivot
  `c₀`) reconstructs `x` exactly, ratios `≤ 1`. Covered by case-11, `c₀` = the pivot (fixed).
- **B — `B`-argmax point** `x = (1/3)·e_{(1,0,0)} + (1/9)·e_{c₀}`: case-11 canonical FAILS (ratio
  `|x_{(1,0,0)}/x_{c₀}| = 3 > 1`), so it routes to the case-1(2) SIBLING (pivot `(1,0,0)`), which
  reconstructs `x` exactly with `c₀` FIXED as a spectator, ratios `≤ 1`. **Covered without a case-11
  interior pivot.**
- **Harmful alternative (why the naive membership pin broke the render):** the case-11 INTERIOR pivot
  `(1,0,0)` gives `image_{c₀} = w_{(1,0,0)}·w_{c₀} ≠ w_{c₀}` — `c₀` is MOVED, breaking
  `stepMapRaw_fixes_parentLedgerCorner`. So the interior fan at case-11 is both UNNECESSARY (B covered by
  the sibling) and HARMFUL (moves the earlier ledger corner). Decisive.

## THE (a)-CHARACTERIZATION (what ledger-corner-preservation excludes, exactly)

Adopt the elder's (a): **the fan ranges over ledger-corner-preserving pivots** — `pivot ∈ canonCenterOf`
AND for every earlier ledger corner `c` in the center, `c = pivot` OR `c ∉ center` (i.e. the pivot choice
does not move any earlier ledger corner). Because `blockBlowupMap(center, p)` fixes exactly `p` and the
spectators, this is equivalent to: **`pivot ∈ canonCenterOf` and no earlier ledger corner lies in
`center \ {pivot}`.**

- **At case-1(1) (merge):** `center = {c₀} ∪ B` contains the earlier ledger corner `c₀`. The condition
  forces `pivot = c₀` (else `c₀ ∈ center\{pivot}`). ⟹ **single canonical pivot, no fan.** (Restriction
  bites here.)
- **At case-1(2) / case-2 (fresh corner):** `center` is a current-layer block containing NO earlier
  ledger corner. The condition is vacuous ⟹ **free fan over the whole center** (as in the base L7 cover
  design; the interior pivots there are governed by the N_p normalization, the landed recoord half — a
  SEPARATE mechanism from this case-11 blow-up question).

So (a) is the principled statement and (b) is its content: the fan is free except at merge steps, where
the earlier ledger corner in the center pins the pivot to `c₀`. The two are the same restriction.

## SCOPE / caveat (kept next to the claim)

- This adjudicates the **case-11 (merge)** blow-up conflict — `stepMapRaw_fixes_parentLedgerCorner`,
  `edgeShear(case11) = id` (no shear at case-11), so the mechanism is purely the block blow-up moving
  `c₀`. It is DISTINCT from (and does not re-open) the case-1(2)/case-2 interior-pivot NORMALIZATION that
  the landed N_p recoord half addresses (`canonNormalizationOf`) — there the issue is the shear/normalization
  fixing the pivot, not an earlier ledger corner. The (a)-restriction leaves the case-1(2)/case-2 fan free;
  the N_p normalization is what makes those interior pivots monomialise. Both are needed; they are
  orthogonal mechanisms at different case-classes.
- The completeness of the routing (that the case-11 canonical sector + the case-1(2) sibling sectors
  exhaust the node's cover) is exactly the engine's `dCenterOfNode_edgeSum` partition (`Σ_edges
  dCenterOfEdge = dCenterOfNode`), proven sorry-free. The monument's `canonCenterOf(case12)` is a
  (super)set of the engine's case-12 edge center, so it covers `B` a fortiori.

## Firmest / most likely to break / next

- **Firmest**: covered-under-(b); (a) ≡ (b) at case-11; the case-11 fan is a SINGLE canonical pivot `c₀`;
  the block-argmax points route to the case-1(2) sibling with `c₀` a fixed spectator; machine-checked on
  the first real (2,2,2,2) case-11 node.
- **Most likely to break it**: if a case-11 center could contain an earlier ledger corner that is NOT the
  merged `c₀` (a second earlier corner in `{c₀}∪B`). Checked: `B` is strictly current-layer, so the only
  earlier corner in the center is `c₀` — the pin is to a single pivot. (Guard: should the center model
  ever place a second earlier corner in `B`, re-open — but `B ⊆` current layer forbids it.)
- **Next**: implement the (a)-restriction in `IsRealBranch` — the fan pin becomes `pivot ∈ canonCenterOf
  ∧ (∀ earlier ledger corner c ∈ center, c = pivot)`, which the elder can state as `canonPivotOf`-forced
  at case-11 and free at case-1(2)/case-2. This is the fan half of the N_p bake.
