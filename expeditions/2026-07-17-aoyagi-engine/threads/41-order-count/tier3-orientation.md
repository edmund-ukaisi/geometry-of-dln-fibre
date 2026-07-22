# Tier-3 realization iso — orientation (seat-E, 2026-07-22)

The E-lane's most-audited statement: the realization `OrderIso` connecting the binding minimisers to
`BoxPart ℓ a` (Tier-1). Four named requirements (elder): tight lattice, global target, binding filter
as explicit DOMAIN hypotheses + the OrderIso BOTH-directions form. Consumes the banked DivChain
b-chain nesting. Kill-set: [1,1,2,1], [2,2,4,3] (the order-isomorphy / cover-jump test).

## Orientation finding 1 — Lambda's `Adm` is the LOOSE lattice, NOT the tight one (load-bearing)
`Foundations.Lambda.admBound M j = if j=0 then min (M 0) (M 1) else M j.succ` — the LOOSE cap. `Adm`
(built on `admBound`) is therefore the loose lattice, which admits the degenerate profiles that
OVER-count (my 6 naive-divergence instances, e.g. [3,3,1,1]). The **tight** (running-min) lattice —
`runMin M j = min over Iic j.succ of M` (EXISTS in Lambda:176, but `Adm` does NOT use it) — is what
P6.2's chain reading needs. So the Tier-3 iso's "tight lattice" pin requires a **NEW tight-lattice
profile set** (`admTight`, bounded by `runMin`), not the existing loose `Adm`. This is exactly why
the pin is load-bearing: a loose-lattice LHS breaks the OrderIso in the reverse direction (the
[1,1,2,1]/[2,2,4,3] cover-jump — the relocated trap).

## Orientation finding 2 — the 3a/3b design FORK (needs the elder's shape ruling)
The relocated pins (tight lattice, global target, binding filter) are PROFILE-LATTICE concepts, so
the OrderIso has two candidate shapes:
- **(3a) abstract profile-lattice iso** (recommended as THE OrderIso): `{T : admTight M ∧ Mval M T =
  minAdm M}` (componentwise order) `≃o BoxPart (ell d r) (residueA d r).toNat`. This is where the
  four pins + the trap live; it is tree-FREE (the (ℓ,a) come from the certified Def-3 selector). The
  encoding map (profile ↔ box partition) is the trap-laden piece — cover-jumping in the profile
  coords, clean in box coords; likely wants a decorrelated (pnp) certificate on the map before proof.
- **(3b) tree binding** (a SEPARATE further step, not the OrderIso): the built tree's leaf binding
  divisors (`FoldProduced`/`leafOf`/`divExp`, `t̃=0 ∧ divExp = minAdm`) = the abstract minimiser set.
  This is what "reads FoldProduced/leafOf/divExp"; it rides on `RecursionAdapter`'s existing
  tree↔minimiser bridges + the DivChain nesting (per-branch chain).
Recommendation: (3a) is the OrderIso the four pins describe (profile-lattice, trap, `≃o`); (3b) is
the tree-realization binding that composes with it. The controller's "reads FoldProduced/leafOf/
divExp" points at (3b) — so Tier-3 is likely BOTH, with (3a) the most-audited `OrderIso` core.

## Orientation finding 3 — the encoding map (the trap, the hard part)
The iso profile→box: a minimiser `T` ↦ its box partition. In box coords the rank = cell count =
`∑`; in profile coords the coord-sum jumps at covers (the trap). The map is the a-subset structure
(which of the ℓ increments take size M — Lemma 4's increment condition). `OrderIso` (not just mono
bijection) is REQUIRED — the reverse direction is what the cover-jump breaks; the [1,1,2,1]/[2,2,4,3]
kill-set tests exactly this. This map's construction + `strictMono` BOTH ways is the proof's crux and
the natural pnp-certificate ask (like the WALL leaf) before the Lean render.

## Available substrate
- `runMin` (Lambda:176) + `runMin_le`/`runMin_anti` (the tight bound, proved).
- `Mval` (Lambda:42), `minAdm` (Validate/RouteMLayerSplit), `ell`/`residueA` (ClosedForm) — the
  certified target + selector (pin (a)).
- `BoxPart`/`rankBP`/`chainHeight_boxPart` (Core.OrderChain) — the Tier-1 target of the iso.
- `RecursionAdapter` (`AtlasRealizesExponents`, `o5_core_realized`, `minAdm_le_terminalExponents`) —
  the existing tree↔exponent bridges for (3b).
- DivChain / b-chain nesting (thread-31 closed form `b_i = ∏ u`) — the per-branch chain mechanism.

## Plan (gate-order respected — the slip lesson)
orientation (this) → draft the (3a) OrderIso scaffold (sorried, four named pins) → SEND for the
elder's shape pass (3a-vs-3b + the tight-lattice-set + the pnp-certificate-for-the-map question)
→ prove after the pass (do NOT prove before, per the gate-order discipline). (3b) tree-binding +
the YoungDiagram citable bridge are downstream.
