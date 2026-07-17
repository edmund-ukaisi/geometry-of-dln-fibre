# Overlay — dead-route registry (cartographer, curated layer)

*Refuted / superseded / refuted-shape approaches, one line each + mechanism + witness pointer. Created
pass #1. A route here is DEAD as a destination; its trail is kept as a battery anchor / lesson.*

## Refuted routes (map nodes)

- **`naked-weight-route`** (map `refuted`). Integrate-early: form the naked Jacobian-weight residual
  obligation, bound it. FALSE on legal cuts, not merely hard — the target exponent is exactly tight at
  binding cells (zero slack), so a lossy factorization is false there. Killers:
  `battery/w-naked-weight-111.py` (M=(1,1,1): `∫|y|^{-1}` diverges) + `w-naked-weight-4444.py`
  (M=(4,4,4,4), t=2). Both KILLED (exit 1) as designed. This is the zero-slack lesson's anchor
  (compass fork 1). Forwarded → `engine-route`.

- **`decorated-descent-route`** (map `superseded`). The predecessor's conditional decorated route to
  `hbox` (`routeMBoxThresholdFinite_of_decoratedDescent`, conditional on `DecoratedDescent`). SOUND
  BUT DEAD as a destination: witnessing `DecoratedDescent` from the engine costs a tree→adm bridge
  that RE-IMPORTS the refuted decorated-peel object (architect fit report, tick 7). Fork 6 closed by
  the pre-agreed rule: TOMBSTONE (one live spine per fork, P6). Tombstone live at
  `RouteMSJDecoratedRec.lean:211`. Forwarded → `engine-route`.

## Refuted SHAPES (not map nodes — refuted statements/designs inside live nodes)

- **`region_glue` / `ChartsCover`-as-stated — REFUTED (vacuity), lane 2 tick 18.** The abstract
  `ChartsCover` (leaf `chartDom` constrained only as an abstract set `locus ⊆ U ⊆ ⋃ chartDom`) is
  satisfied by the UNIV atlas, so `region_glue`-as-stated is unprovable: a univ atlas + `hrat` are
  jointly satisfiable at a `c'` where the box integral DIVERGES. Witness: `g-chartscover-vacuity.py`
  (SURVIVES — (2,2,2) fake atlas chartDom=univ, divExp={4}, c'=8/5 ∈ [3/2,2) satisfies hyps,
  conclusion FALSE). Mechanism: the pure-monomial integrand omits the leaf's RESIDUAL factor. Fix
  (adopted, unlanded): per-leaf ChartBridge = chartMap + srcBox + resRank + LeafPullback +
  LeafJacobian + InjOn + image cover. `region-glue` node held at `adjudicated` (kill attached) until
  the ChartBridge signature lands. Cert: `threads/04-bridge/cert-bridge-design.md`.

- **Unary-`StepInvariant` carrier shape — REFUTED, council #2 (tick 23).** A per-NODE, edge-blind
  invariant provably CANNOT pin the paper's parent-referencing case-1(1) exponent-merge; the per-chart
  SUBSTITUTION is DATA no Prop supplies and no node field can hold; leaf-terminating charts lose their
  case label irrecoverably. (Correction the council caught: the raw NODE datatype is NOT inexpressive
  in the abstract — both seats struck that overstatement; the three binding facts above are what kill
  it.) Fix: edge-labelled carrier (`Edge {case, subst, child}`) + `State/StateInvariant` split,
  `StepInvariant → StepRel` relational. Root Lean STILL carries the refuted unary
  `StepInvariant` (`EngineObligations.lean:63`) — the edge shape is in flight (task #42), unlanded.
  Witness: `threads/01-skeleton/necessity-and-encodings.md §(i)` (probe `/tmp/NecessityProbe.lean`).

- **Candidate B (node carrier + relational side-table) — NOT ADOPTED, council #2.** An alternative to
  edge-labelling: keep the reviewer-validated node `ResolutionTree` and carry per-edge `case`+`φ` in a
  side relation `edgeCase/edgeSubst : List ℕ → …` with a heavy `EdgeCoherent` invariant. Rejected for
  the P6 two-structure-sync risk (a tree edit desyncs the table — a silent bug the type system won't
  catch, unlike A where the edge IS the datum). Witness: `necessity-and-encodings.md §(ii) Candidate B`.

- **The false Q5 fork framing — REFUTED on BOTH sides, council #2 (ticks 24–25).** The posed fork
  "flat-coord fderiv (a) vs RLCT-transport (b), because `Params M` has no normed instance and (b)
  drops fderiv" was VOID on both sides: (1) `ParamsFlatLinear` (0-sorry, 13 consumers) ALREADY banks
  the normed instances + CLE + fderiv — the probe ran without the import; (2) route (b)'s transport
  CONSUMES fderiv, it does not drop it. The real distinction was fresh-composer vs banked-reuse;
  route (b) adopted on corrected merits (reuse the banked local-homeomorph transport +
  ONE homogeneity scaling-bridge lemma). Lesson banked: instance probes without an import survey are
  not evidence. Witness: journal ticks 24–25; `necessity-and-encodings.md §Q5`.

- **`MinAdmMono` for threshold preservation — WRONG DIRECTION (formaliser trap), covdesign D2.** The
  compass had pinned `MinAdmMono`; it is the OPPOSITE direction. Correct pin: the minAdm-as-minimum
  property (`inf'_le` / `minAdm_le_Mval`). Recorded on `theorem4-localization`; kept here as a
  name-similarity trap warning.

- **`resolutionOf := (∃ t, IsFullMonomialization t).choose` — REFUTED (under-determination), review
  round 1 (tick 10, C2).** A naked `choose` under a single weak predicate lets a junk leaf (`numDiv =
  0`) satisfy it vacuously with empty `terminalExponents`, so the ledger/coverage obligations are not
  dischargeable. Fixed by the `CanonicalResolution` 5-conjunct bundle (junk-leaf provably rejected).
  This shape is retired; the bundle is live in `EngineObligations.lean`. Witness: rev-skeleton r1
  report (journal tick 10); the attainment conjunct `minAdm ∈ terminalExponents` is the load-bearing
  fix (`EngineDriver.lean:78` loss-proof example).
