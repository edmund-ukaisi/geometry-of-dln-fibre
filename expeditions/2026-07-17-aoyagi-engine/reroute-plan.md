# Re-route plan — the one-object resolution recursion (closing `exists_coreResolution:311` cite-free)

**Status: v1.0 FINAL (operator-side)** — grounded at trunk `db3474b4b` + lanes (gate2
`347531e3e`, 5d-cover `149e8623e`, gate-routeB `4c7bf682a`); every interface and atom signature
below verified verbatim against source in two independent sweeps + direct reads. Aoyagi citations use the repo's anchor-frozen
`theory/aoyagi-2023-reproduction/aoyagi-2023-worked.tex` line numbers and the preprint
(`paper-sources/…/aoyagi-2023-neural-networks-preprint.pdf`) page pins, per repo convention.

## 0. The verdict this plan implements

The gate-routeB wall (13:58, GateRouteB222) proved the *current two-object architecture* has no
cheap completion: sibling charts cannot be conjured by ambient symmetry (transport group ⊥ cover
set, exact witness), and a structural chart↔leaf bridge between the banked combinatorial tree and
post-hoc geometric charts is unbuilt and unstatable. This plan does not repair that architecture;
it replaces the *producer* while keeping every consumer and every banked theorem.

**The one-object principle.** Build a single recursion whose state carries BOTH the geometry
(the chart-so-far) and the ledger (the exponent bookkeeping), updated in lockstep by the same
case decisions that drive the banked combinatorial tree. Then:
- the cover is a per-stage property the recursion maintains (never a post-hoc patch);
- sibling charts are born pivot-generically from one constructor (never transported);
- the value conjuncts of `:311` become ledger-sharing facts (never a bridge).

This is Aoyagi's own construction order: her §resolution builds charts and exponents together,
one stage at a time (worked.tex:609–625 = preprint pp.15–22: the (S,J) step, Cases 1(1)/1(2)/2),
and her value recursion peels exactly one layer per (incidence + blow-up), leaving a *fresh
lower-depth core* (worked.tex:712–724) — the deeper layers are untouched at each stage, which is
precisely what makes per-stage constructions compose.

## 1. Interface audit — what the new object must satisfy (verified verbatim)

- **`exists_coreResolution` (LearningCoefficient.lean:292–311)** demands exactly:
  `∃ res : Resolution (coreGen d e) 0` with (hlb-shape) every binding-axis exponent
  `jac a + 1 ≥ qipMin d` and (hattain-shape) some binding-axis exponent `= qipMin d`.
  Hypotheses supply the linear origin-fixing flatten `e`. Nothing else. The summit chain
  downstream (`aoyagi_learning_coefficient_via_engine`, adapter, `qipMin_eq_minAdm`,
  `coreReduction`) is banked and unchanged.
- **`AtlasRealizesExponents` (RecursionAdapter.lean:55)** is BY ITS OWN DOCSTRING "a match of the
  ℕ-valued exponent value-supports ONLY — NOT a structural chart↔leaf correspondence." Clause (i):
  every chart binding exponent value ∈ `terminalExponents (buildTree d (conOracle d) conRoot)`.
  Clause (ii): every minAdm-attaining leaf divisor value is matched by some chart. **The bridge
  monument was never in the interface.**
- **`stepUpdate` (EngineDefs.lean:175) is pivot-independent**: transitions depend only on
  `(StepData, StepCase, ChartSubst)` — never on which pivot entry within a center is chosen
  (verified by inspection; transitions page-pinned to preprint p.16/p.17/pp.20–21).
  ⟹ all pivot-siblings at a node carry IDENTICAL ledger values.
- **`Chart`/`Resolution` (ProductResolution.lean:62–139)**: the fields to inhabit per chart are the
  map+geometry (g, dom/nbhd, injectivity off null exceptional, dom-wide `hjac` = monomial·unit),
  the monomial certificate (`bexp/k₀/hchain/hbind/hunit_mult/jac/unit`), and the two ideal
  inclusions (`hideal_fwd/hideal_bwd`); atlas-level `hcover`. Two field-classification facts
  (interface sweep, verbatim-verified): **`hideal_bwd` is value-critical, not lower-bound-only**
  (the per-chart value `two_mul_wrlctAt_eq_chartMin`:219 consumes the germ ideal BOTH ways and
  re-uses `hideal_bwd` for zero-set nullity) — so the per-stage maintenance MUST be two-sided,
  which the gate2 protos already are; and the strictly lower-bound-only fields are exactly
  `Resolution.{U,hU,hcover}` + `Chart.{dom,hdom_compact}`.
- **Per-chart value contract (Object C, MonomialRLCT.lean:650)**: chartMin =
  `inf' (bindingAxes (bexp k₀)) (fun a ↦ jac a + 1)`; demands `hchain` (k₀ chain-minimal),
  `hbind` (≥1 binding axis), `hunit_mult` (binding multiplicities = 1 — what makes the value the
  integer `jac+1`), `hjac` dom-wide. These are R4's emission checklist, per leaf.
- **Abstract-`e` note**: `exists_coreResolution` receives an ARBITRARY linear origin-fixing
  homeomorphic flatten `e` (only the summit keeps measure-preservation). Design: construct the
  resolution once at the concrete `canonFlatten` (its linearity/zero/measure-preservation are
  proven, LearningCoefficient.lean:222–230), then transport to abstract `e` by the banked
  `conjResolution` with `Φ = canonFlatten.symm ∘ e` (a linear homeomorphism; carries every field
  including `hcover` via the Haar-image lemma, no measure-preservation needed). One small
  bookkeeping lemma: package `Φ` as a `ContinuousLinearEquiv`.

## 2. The new core object

```
structure StageState (d) where
  S J        : ℕ                    -- Aoyagi's stage cursor (worked.tex:609)
  ledger     : StepData d           -- THE BANKED LEDGER, updated only via stepUpdate
  gPath      : composite chart map so far (blow-ups ∘ per-stage eliminations)
  binv       : the L-B invariant at this state:
               ⟨coreGen ∘ gPath⟩ = ⟨diag(b) · (E_J ⊕ D_J) · (deeper layers untouched)⟩
  cover_out  : the stage box data (compact dom, nbhd) for the tiling engine
```

**The step constructor (pivot-generic — the single load-bearing design rule).** For a state at
`(S,J)` with case decision `c` (from the SAME `conOracle` data driving `buildTree`) and center
`Z` (the equal-b run block, worked.tex:609–614), and FOR EACH pivot `p ∈ Z`:
1. blow-up chart at pivot `p` (banked `BlockBlowup` atoms — pivot-parameterized);
2. **elimination built inside this child from `p`'s own row/col** (Aoyagi Case 1(2),
   worked.tex:617–619: "first row normalised… regular transforms Q,P reduce D''") — the pivot is
   a unit in its own chart, so Q,P are unipotent, `det ≡ 1`. NO fixed shear frame exists.
   ⟹ the 128-invalid-leaves / fixed-shear-drift failure is structurally impossible;
3. ideal maintenance by the banked gate2 protos (`maintenance_step_two_sided` — two-sided,
   b-chain absorbing cross-terms; the chain hypothesis holds BY CONSTRUCTION since
   `b_{i+1} = u·b_i` is how the state accumulates b's — the "chain-along-path" lemma
   becomes definitional in this object);
4. ledger update `:= stepUpdate ledger c σ` — the proven transition, shared with `buildTree`.

Children = { step(p) : p ∈ Z }. All children share one ledger transition (pivot-independence),
differ only in geometry. Case 1(1) (exponent merge, worked.tex:615–617) and rollover update the
ledger/cursor without new geometry, exactly as in `buildTree`.

**Atom citations (verbatim-verified):** blow-up = `blockBlowupMap (S : Finset) (p : Fin D)`
(BlockBlowup.lean:31; Jacobian :123, injectivity :181, both keyed on `p ∈ S`); maintenance =
`maintenance_step_two_sided` (gate2 Corank2MaintenanceProto.lean:67 — **fully pivot-generic**,
`p : Fin n` arbitrary, coupling unconstrained, the b-chain entering only as continuity of the
quotients `rᵢ = b'ᵢ/b'_p`, which the state's construction order makes monomial hence continuous);
precompose = `regionRepresents_comp` (Corank2CompositeProto.lean:33, fully generic); terminal =
`terminal_bezout` (PrincipalInv.lean:318 — needs `IsOpen V`, `0 ∈ V`, unit nonvanishing at 0,
shrinks the region; plan the leaf regions accordingly); leaf assembly = `chart_of_collapse`
(LeafChartWire.lean:116 — consumes `GeoAtlasData` + both `RegionRepresents` + unit≡1 collapse).
The δ=1 substitution atom `stepInv_delta1_shear_child` exists (arbitrary center/pivot/shear) but
is Encoding-S-flavored and un-wired — FALLBACK ONLY; the gate2 ideal-level protos are the
sanctioned per-step mechanism.

**Recommended Lean shape for the recursion (from the banked idiom, proven 9×):** do NOT define a
new geometric tree datatype. R3 is a WF-induction over `ConState` in exactly the
`leaves_chart_clauses` pattern (DivBirthReach.lean:299: `induction s using (conRel_wf M).induction`,
`cases conOracle M s`, unfold `buildTree_terminal/step`, per-transition maintenance lemma, recurse
on `hdesc`) — threading a GEOMETRY-VALUED invariant: "from this state, given the chart-path
context, the subtree yields a finite chart family whose members carry StepInv/certificates, whose
ledger values are the subtree's leaf values, and whose images cover the current box up to the
tiling engine's inflation." The pivot fan lives inside the per-node step (each oracle child ×
each pivot p ∈ center); `conOracle : (s : ConState L) → ConDecision M s` is a function of the
combinatorial state ONLY (verified) — oracle purity holds, the lockstep pairing is sound. The
cover obligation per step is `covers_fanOfSteps`-shaped (GeneralGeoAtlas.lean:375): a ∀-radius
box-containment per shear, supplied by `blockShear_covers_scaled` (5d-cover
Corank2FanCover334.lean:35, inflation r + C·r², C ≤ shear block rank ≤ width).

## 3. The rung ladder

- **R0 — curation + map re-scope (1 tide).** Tombstone the two-object wiring (MonumentAtlas
  Encoding-S anchors + the chart↔leaf-bridge ambition + composite-then-fan chart family) into the
  dead-route registry with the GateRouteB222 witness as evidence; `:311`'s map node re-scoped to
  this plan; the four §8 guardrails + guardrail-0 (below) copied into the brief. Merge gate2 and
  the reusable 5d/5c atoms to the working trunk. Commit all floating decision docs.
- **R1 — `StageState` + the pivot-generic step constructor (2–4 tides).** The record, the
  constructor, per-step lemmas = instantiations of banked atoms (BlockBlowup, gate2 protos,
  stepUpdate). De-risk FIRST UNIT: one Case-1(2) step at the (2,2,2) core, all pivots, as
  regression — the constructor must produce every sibling with certificates, no transport.
- **R2 — the per-stage cover lemma (1–2 tides).** Children images cover the parent box up to
  null: the standard-charts-cover atom (banked, pivot-parameterized) + pivot-adapted shear
  box-containment (banked faithful-shear atom at corank-2; width-bounded C general — rendered).
  Threads `cover_out` through the constructor.
- **R3 — the fold (3–6 tides; the biggest).** WF recursion (the engine's `conRel_wf` pattern,
  proven 9×) over oracle-path × pivots. Threads: `binv` (maintenance per step), ledger coherence
  (definitional — shared `stepUpdate`), cover (LeafCoverTiling `Covers` fold, banked). Emits per
  leaf: terminal invariant → `PrincipalInv` (via banked `terminal_bezout`) → both ideal inclusions
  (banked L1 `principalInv_regionRepresents`).
- **R4 — leaf → `Chart` (1–2 tides).** `chart_of_collapse` (banked assembler; consumes geometry +
  the two ideal inclusions from R3), dom-wide `hjac` from the Jacobian telescope (banked
  `abs_jacDet_geoPath`; unit ≡ 1: unipotent eliminations, exact-monomial blow-ups — the rendered
  L6 argument, audited), monomial certificate fields from the state's accumulated b's (the chain
  is construction-ordered).
- **R5 — `Resolution` + the value conjuncts + transport + close `:311` (1–2 tides).** `hcover`
  from R2+R3. hlb-conjunct: every leaf ledger IS a `buildTree` leaf ledger (shared `stepUpdate`
  transitions — verified: the transition reads only `(StepData, case, σ.mergeIdx, σ.runLen)`,
  never the geometric pivot; `terminalExponents` reads only `divExp/numDiv/resRank`) ⟹ chart
  binding values ∈ terminalExponents ⟹ ≥ qipMin via banked `minAdm_le_terminalExponents` +
  `qipMin_eq_minAdm`. hattain-conjunct: `o5_core_realized` names a minAdm-attaining leaf; the
  geometric tree contains a branch with the same oracle path (same case/σ decisions), whose
  chart realizes the value. Then `conjResolution`-transport from `canonFlatten` to the abstract
  `e`, and hand `⟨res, hreal⟩` to the already-written `refine` in `:311` — the sorry closes with
  no change to the theorem.
- **R6 — summit + kill-cite + close (1 tide).** `#print axioms` on
  `aoyagi_learning_coefficient_via_engine` → clean-three; retire `AoyagiCited`; map close.

Total estimate: 10–16 tides (days at demonstrated cadence, not weeks), rung-gated, objects-only
close remains the STOP-fallback at every rung boundary.

## 4. Guardrails (inherited four + one new)

**Guardrail 0 (the lesson of this week): no geometry may be constructed outside the step
constructor.** No composite-then-fan, no post-hoc transport for siblings, no fixed frames. If a
chart is needed, it is a leaf of the recursion or it does not exist. (§8 guardrails 1–4 inherited
verbatim: running-coordinate D-block; no non-dividing row-mixes; ledger derived not assumed —
now definitional; both RegionRepresents directions.)

## 5. De-risks / kill-conditions to check BEFORE R1 (pen-and-paper + one-file probes)

1. **Gate2 proto pivot-generality: CONFIRMED GREEN** — `maintenance_step_two_sided` takes
   `p : Fin n` arbitrary; both inclusions; coupling unconstrained (verbatim, gate2
   Corank2MaintenanceProto.lean:67).
2. **Oracle purity: CONFIRMED GREEN** — `conOracle : (s : ConState L) → ConDecision M s` reads
   the combinatorial state only (EngineConstruction.lean:414 driver); the lockstep pairing and
   the `leaves_chart_clauses` induction idiom apply directly.
3. **Flatten handling**: RESOLVED by design — construct at `canonFlatten` (a literal reindex, so
   layer blocks ARE disjoint coordinates and "deeper layers untouched" is a coordinate fact),
   then `conjResolution`-transport to the abstract `e`. Residual check: the CLE packaging of
   `canonFlatten.symm ∘ e` (small).
4. **Non-monotone widths**: geometry must consume only block SIZES (running-min governed), never
   Case-2 raw-width head labels (the T-E defect lives there; ledger side already handled).
5. **The (2,2,2) regression**: the R1 first unit must reproduce GateRouteB222's M1a mechanism
   result from the constructor alone — siblings born, not transported — and the per-stage cover
   must close at that instance. STOP-on-wall as always.

## 6. What is explicitly abandoned (registry entries)

The chart↔leaf structural bridge (never in the interface); ambient-symmetry sibling transport
(GateRouteB222 witness); composite-then-fan chart families (gWrap escape-cone certificate);
the col-pinned cover (escape witness); the Encoding-S fold anchors (already ruled). The 334/222
modules remain as regression evidence; ConjResolution/transportChart remain as general tools
(they are correct — they were just the wrong *source* of siblings).

## 7. What survives and is consumed (the banked spine)

Ideal algebra: `maintenance_step_two_sided` + protos, `StepInv/PrincipalInv/terminal_bezout`,
`BlockDivision`, L1, IdealInvariance/Object A. Value: Object C (MonomialRLCT), Object D +
`minAdm_le_terminalExponents`, `o5_core_realized`, `qipMin_eq_minAdm`, `coreReduction`,
`#110` upper engine + `Corank2CiteFree334`. Geometry: BlockBlowup/OriginBlowup atoms,
LeafCoverTiling engine, GeneralGeoAtlas telescopes + shear-cover atoms, 5c faithful-shear atom,
`chart_of_collapse`. Combinatorics: the whole `buildTree`/`stepUpdate`/ledger layer — now the
shared spine of the one object rather than a separate book.
