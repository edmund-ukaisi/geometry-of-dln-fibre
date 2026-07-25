# R3 de-risk — the geometry-valued WF invariant (elaboration)

**Seat:** reroute-R3derisk (pen-and-paper + decorrelated Codex xhigh, converged independently). Persisted by
the controller (the seat is barred from writing report files). Codex prompt+answer: `/tmp/r3derisk-codex-{prompt,answer}.md`.

**VERDICT: NO STOP. The WF-fold MECHANISM composes and is de-risked with in-repo precedent.** The residual
risk is entirely CHART-CONTENT coupling at the leaf, not the threading.

## Headline — the "geometry-valued motive" fear is answered by in-repo precedent

`(conRel_wf M).induction` ALWAYS has a `Prop` motive (`ConState L → Prop`, never `→ Type`), and the exact
∀-context-quantified geometry-Prop shape R3 needs ALREADY BUILDS GREEN today:
- `GeoCoverSpec.flatCube_subset_leafPathImages` (DivBirthReach-sibling): a `conRel_wf` induction proving a
  **Set-valued cover `⊆`**, ∀-quantified over the chart-path context `acc : Params M → Params M` (the exact
  "gPath so far" type), threaded to children through the SAME `buildTree`.
- `leaves_chart_clauses` threads a hypothesis-carrying invariant; `GeoInvValWalk` threads a matrix-valued
  ledger identity.
So Set-valued, ∃-carrying, and hypothesis-threaded motives all demonstrably pass through the idiom. "Geometry-
valued" is loose: R3's invariant is a Prop that MENTIONS geometry (maps/Sets/RegionRepresents), all of FIXED
type. No new territory in the threading.

## 1. The invariant (DivBirthInv-style, ∀-context-quantified — matches the flatCube precedent)

Ambient `N := flatDim M`, FIXED (depends on M, never on the state `s`). Work in the FIXED full space
(`Params M` / `Fin N → ℝ`) — load-bearing (see 3c).

    R3Inv M s : Prop :=
      ∀ (gPath : (Fin N→ℝ)→(Fin N→ℝ)) (V : Set (Fin N→ℝ)) (R : ℝ),
        (Hcont)  Continuous gPath
        (Hopen)  IsOpen V ∧ 0 ∈ V ∧ closedBall 0 R ⊆ V
        (Hchain) accumulated b's form a divisibility chain b₁∣b₂∣…∣b_{numDiv s}
                 (⟹ every ratio bᵢ/b_p is a genuine monomial, ContinuousOn V)
        (Hbinv)  RegionRepresents (coreGen∘gPath) (targetGen s) V ∧
                 RegionRepresents (targetGen s) (coreGen∘gPath) V          -- TWO-SIDED
                 -- targetGen s = diag(b s)·(E_J ⊕ D_J)·(deeper-layer factor as spectator)
      →
        ∃ (fam : ∀ l ∈ leaves (buildTree M conOracle s), Chart-data),    -- INDEXED BY LEAVES
          (value) ∀ l k, (fam l).divExp k ∈ terminalExponents (buildTree M conOracle s)
          (cert)  ∀ l, TWO-SIDED RegionRepresents (coreGen∘(fam l).g) ⟨(fam l).b⟩ (fam l).V
                       ∧ dom-wide hjac = monomial·unit ∧ hunit_mult=1 on binding axes
          (cover) closedBall 0 R ⊆ ⋃ l, (fam l).g '' (fam l).dom          -- up to f^[depth] inflation

The four DivBirthInv-analogue conjuncts: **chart-path context** = (gPath, Hcont, Hopen); **binv** = Hbinv;
**cover box data** = (V, R); **ledger-lockstep** = NO separate ledger field — `targetGen s` + the value read
are functions of `s.toRootLedger` = buildTree's own ledger (§4).

## 2. Per-step obligation (all primitives banked & sorry-free in-worktree)

At `.step node children`, for each oracle child c and each pivot p ∈ center Z, produce σ_p and re-establish
R3Inv for c.child at (gPath∘σ_p, V_child, R_child):
- (i) `σ_p := blockBlowupMap Z p` (pivot-parameterized; Jacobian+injectivity keyed on p∈Z; continuous → feeds comp).
- (ii) precompose: `regionRepresents_comp Hbinv (cont σ_p)` ⟹ RegionRepresents (coreGen∘gPath∘σ_p)(targetGen s∘σ_p)(σ_p⁻¹'V).
- (iii) maintenance: `maintenance_step_two_sided` (Corank2MaintenanceProto:67) ⟹ TWO-SIDED (targetGen s∘σ_p)→(targetGen c.child), cofactor cᵢ·rᵢ (coupling cᵢ arbitrary; rᵢ continuous BY Hchain).
- (iv) chain: `(regionRepresents_comp X hg).mono hsub |>.trans crux` — **this exact idiom is banked at Corank2FaithfulComposite:223** (compose→restrict→trans), not speculative.
- (v) ledger: `c.child.toRootLedger = stepUpdate node c.ecase c.esubst` — the SAME transition buildTree uses; pivot-INDEPENDENT (EngineDefs:175) ⟹ all pivot-siblings share one ledger.
- (vi) terminal (leaf): `terminal_bezout` (PrincipalInv:318) BORNS PrincipalInv on a SHRUNK open V∋0 (unit nonvanishing); `principalInv_regionRepresents` (L1) → the two Chart ideal inclusions.

## 3. Does it compose?

- **(a) Cover inflation f=r+C·r² over depth — COMPOSES.** Per-step atom banked general-D
  (`blockShear_covers_of_norm_bound`/`n_of_norm_bound`, GeneralGeoAtlas §1; ‖φx‖≤C·r² ⟹ covers r-ball from
  (r+C·r²)-ball, dimension-free). Depth = iterated f^[depth], finite (μ lex-triple). A single global C*=max
  width dominates every node's local C (r+C_node·r² ≤ r+C*·r²). **THE GAP:** the cover machinery is SPLIT —
  `flatCube_subset_leafPathImages` folds the REAL branching buildTree but at fixed R=1 self-cover (no shear);
  `FanTree.Covers`/`covers_subset` carries the growing inflated radius but over a LINEAR step-list (no real
  branching). R3 needs BOTH: a radius-parameterized `conRel_wf` cover over buildTree with per-node sheared
  box-containment. **This is a GENUINE new fold = R2's real work** (plan §3's "cover … banked" refers to the
  `Covers` SHAPE; the marriage to buildTree is not free). Cheapest: a `∀ R acc, closedBall 0 R ⊆ leafImages`
  motive + a radius-monotonicity lemma, folded like flatCube but swapping node_selfCover → n_of_norm_bound,
  passing the IH at f(max R 1).
- **(b) "deeper layers untouched" makes binv COMPOSE — COMPOSES, conditional on two threaded conjuncts.**
  Shallower b's ride as the non-unit left factor `bp` inside maintenance; the step touches only the depth-k
  residual block; deeper layers are untouched spectators in Xᵢ. PROVIDED (1) Hchain (b_p∣bᵢ) is MAINTAINED
  as a threaded invariant — **NOT "definitional" (plan §2 line 90 is wrong here)**: it's structural-induction
  per birth (worked.tex:600-602), make it an explicit conjunct; and (2) σ_p is genuinely identity on deeper
  coords (the fixed-full-space embedding, 3c). Both directions chain in MIRROR order (2× bookkeeping, mechanical).
- **(c) Dependent-type obstruction — NONE (the headline de-risk; Codex agrees).** `.induction` motive is
  `→ Prop`. gPath/V/RegionRepresents/Chart all FIXED type (Params M state-independent). ∃-of-charts harmless
  (no Prop→Type elim while merely PROVING existence). **DESIGN CONSTRAINT (must hold): construct at
  canonFlatten in the fixed full Params M; "deeper layers untouched" is a COORDINATE fact, never a dimension
  drop.** A shrinking per-depth space would force transports/HEq through the fold — that (and only that) would
  reintroduce dependent-type pain, and a green-per-step build would mask it. Plan §5 de-risk 3 already commits
  to this — keep it a HARD invariant.

## 4. Lockstep-coherence — DEFINITIONAL

There is ONE recursion. The geometry is a Prop threaded through the SAME `buildTree M conOracle s`; NO parallel
geometric tree ⟹ NO chart↔leaf structural bridge (the thing the gate-routeB wall killed) is needed.
`terminalExponents` (ResolutionTree:289) reads only combinatorial leaf fields (numDiv/divExp/resRank), never
chartMap. hlb/hattain are ledger-sharing facts. **Caveat (Codex): index the family BY LEAVES** (as the §1
motive does) — a flattened bare list loses "which leaf made which chart" and each chart's divExp∈terminalExponents
would then need a per-chart leaf-ORIGIN certificate. Leaf-indexed ⟹ value-membership definitional again.

## Residual risks (ranked)

- **R1 [HIGHEST — seat + Codex independently]: TERMINAL-SHRINK ⋈ COVER at the leaf.** `terminal_bezout`
  SHRINKS V to a leaf-specific nonvanishing open nbhd; NO banked lemma says the inflated tiling domains still
  fit inside those shrunken regions. The ideal thread (wants small V) and the cover thread (wants V large
  enough to tile) must be conjoined ON THE SAME charts — the real coupling the plan's separate binv/cover_out
  framing (§2) glosses. **SETTLE BEFORE THE R3 DEEP BUILD:** prove one "admissible leaf region" lemma —
  shrunken nonvanishing nbhd ⊇ the tiling box at that leaf's inflated radius. Dedicated (2,2,2)-leaf probe (ties plan §5 item 5).
- **R2 [HIGH]:** the radius-parameterized real-tree cover fold (3a gap) — genuine new fold; R2's core deliverable, known-shaped but not banked.
- **R3 [MED]:** region-nesting `σ_p '' V_child ⊆ V_parent` per step (the `.mono hnest` arg) — package into the per-step "admissible path region" lemma (Hchain-continuity + 0-membership + both maintenance directions).
- **R4 [LOW]:** Hchain maintenance as an explicit conjunct (not definitional); mechanical structural induction per birth.
- **R5 [LOW]:** leaf-indexing of the family — free if the motive is leaf-indexed from the start.

## Close

FIRMEST: the WF-fold threading of an ∃-geometry Prop through `conRel_wf` is sound with direct in-repo precedent;
no dependent-type obstruction under the fixed-full-space design constraint; per-step binv maintenance chains via
the already-demonstrated `regionRepresents_comp+.mono+.trans+maintenance_step_two_sided` idiom.
MOST LIKELY TO BREAK IT: R1 — terminal-shrink vs cover incompatibility at the leaf (CONTENT, not threading).
NEXT: a one-file (2,2,2)-leaf probe proving the "admissible leaf region" lemma (shrunken nonvanishing nbhd ⊇
tiling box at inflated radius) — the TRUE gate to the R3 deep build, above the now-cleared fold mechanism.
