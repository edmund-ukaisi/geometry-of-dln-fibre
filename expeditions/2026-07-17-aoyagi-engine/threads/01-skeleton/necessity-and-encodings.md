# Council-window design notes — carrier shape (edge-vs-node) + Q5 route (t01, architect)

Prepared for the council of two (carrier-shape adjudication; givens fixed; Q5 = route fork). No
carrier changes made; these are notes the council gates against. Two deliverables: (i) the concrete
mixed-case Case-1 necessity witness; (ii) both candidate encodings, with ChartBridge placement and the
224-witness rebuild under each Q5 route.

---

## (i) Mixed-case Case-1 necessity witness — WITNESSED (probe-confirmed), fork NOT dissolved

**Concrete paper-faithful state** (Aoyagi pp.15–18; worked.tex §blow-up lines 499–510). Take a step
`(S,J)` whose `b`-run above `J` is a **partial** equal block `b_{J+1}=…=b_{J+J₁} ≠ b_{J+J₁+1}`,
`J₁ < M(S)−J`. Smallest genuine instance: `M(S)=2, J=0, J₁=1, M^{(S+1)}=2`, residual `D_0` a `2×2`
block. The step blows up `{d_{ij}=0 (0<i≤1, 0<j≤2), u=0}`. This ONE blow-up emits BOTH chart types of
its standard affine cover:

- a **Case 1(1)** chart — the `d`-block `= u·d'` (an EXISTING exceptional `u` divides); sets
  `t̃=J`, exponent-merge `M'_{s,k}=M_{s,k}+J₁(M^{(S+1)}−J)`; its substitution `φ_{1(1)}`.
- a **Case 1(2)** chart — first row normalised, `u = u_{S,J+1}·u'` (a NEW pivot `u_{S,J+1}`
  introduced); advances `J`; its substitution `φ_{1(2)}`.

So one blow-up ⇒ a mixed cover `{(case11, φ_{1(1)}), (case12, φ_{1(2)})}`. Each chart carries TWO
per-edge data: its **case tag** and its **substitution map**.

**Node-carrier test (probe `/tmp/NecessityProbe.lean`, reproducible):** in the current carrier
`ResolutionTree.branch (n : StepData M) (charts : List (ResolutionTree M))`, record the cover as
`branch n [chartA, chartB]`. Then:

- `LeafData` has **no `case` field** (`fun (l : LeafData M) => l.case` fails: `invalidField case`).
  So if a chart is TERMINAL (`leaf lA`), its 1(1)-vs-1(2) case is UNRECORDABLE.
- **No substitution field anywhere**: `LeafData.chartMap` absent (`invalidField chartMap`), and
  `StepData` has no substitution field. So NO edge — terminal or internal — can record its `φ_i`.
- For an INTERNAL chart (`branch nc …`), `nc.case` (the child root's "incoming-edge case") can hold
  the case, but it conflates the child's OWN step-type with its incoming edge, and STILL has no home
  for `φ_i`.

**Verdict.** The naive node carrier CANNOT faithfully record a mixed-case Case-1 cover (case of a
terminal chart + substitution of any chart). The fork is **not dissolved** — a restructure IS needed.
It is **not fully sealed to edge-labelling either**: the missing per-edge data (`case`, `φ`) could be
carried in a *side relation* keyed by parent+child-index (candidate B) rather than on the edge
(candidate A). So the genuine fork the council adjudicates is **A (edge-labelled) vs B (node +
relational invariant)** — both supply the per-edge `case`+`φ`, differing in where.

---

## (ii) The two candidate encodings

### Candidate A — edge-labelled children

```lean
structure Edge (M : Fin (L+1) → ℕ) where
  case  : StepCase
  subst : ChartSubst M          -- the per-edge chart CoV (type set by Q5, below)
  child : ResolutionTree M
inductive ResolutionTree (M) 
  | leaf   (l : LeafData M)
  | branch (n : StepData M) (edges : List (Edge M))
```

- `case`+`subst` live exactly where the paper puts them (per chart of one blow-up); mixed-case cover
  is native; the leaf's incoming case is on its edge (no `LeafData.case` needed). The full chart CoV
  to a leaf is the **composite of edge substitutions along its root→leaf path** (`chartMap` DERIVED,
  not a leaf field). Nested-`List` inductive with an `Edge` wrapper is a tested pattern (leaves/nodes
  read-offs port with the same `decreasing_by`).
- Termination (given: lex `μ=(L+1−S, layerCap−J, #{k|J<t̃})`) is unaffected — it descends on the
  child, `Edge` only wraps it.
- **ChartBridge placement:** `LeafData` keeps `resRank` + the disjoint-coord `‖z‖²` Morse data +
  order fields `a_i,b_i`; `LeafPullback`/`LeafJacobian` reference the path-composite substitution;
  the image cover is `⋃_leaf (pathSubst leaf) '' srcBox`.
- **224 rebuild:** `branch n224 [Edge case2 subst224 (leaf leaf224)]`.

### Candidate B — node carrier + relational invariant (carrier unchanged)

```lean
-- ResolutionTree unchanged: branch (n : StepData M) (List (ResolutionTree M))
structure Resolution (M) where
  tree      : ResolutionTree M
  edgeCase  : List ℕ → StepCase        -- keyed by child-index path
  edgeSubst : List ℕ → ChartSubst M
  coherent  : EdgeCoherent tree edgeCase edgeSubst   -- ties paths to the tree's actual structure
```

- Keeps the reviewer-validated `ResolutionTree` intact; the per-edge `case`+`φ` live in a side table.
- Cost: `EdgeCoherent` is a heavy relational invariant (every path must index a real edge; case must
  match dispatch); all reasoning about "this child's case/φ" goes through the relation (indirection);
  **two structures to keep in sync** — the P6 "one live gradient" concern (a tree edit that desyncs
  the table is a silent bug the type system won't catch, unlike A where the edge IS the datum).
- **ChartBridge placement:** `chartMap` derived from `edgeSubst` along the path; `LeafPullback`/
  `LeafJacobian` reference `edgeSubst`-composites; more boilerplate to thread `coherent`.
- **224 rebuild:** `tree = branch n224 [leaf leaf224]`; `edgeCase [0] = case2`, `edgeSubst [0] =
  subst224`, `coherent` discharged for the single path.

### Q5 route (couples to both A and B — `ChartSubst M`'s type)

**~~Hard given (my probe): `Params M` has no `NormedAddCommGroup`/`NormedSpace` (`inferInstance` fails
both) — so any fderiv over `Params M` is ill-typed.~~** — STRUCK, FALSE (see the CORRECTION below):
the probe ran without importing `Foundations/ParamsFlatLinear`, which banks the normed instances.
`Params M` IS normed / finite-dimensional; the fderiv route is unobstructed.

- **Route (a) — flat-coord fderiv.** `ChartSubst M := (Fin (flatDim M) → ℝ) → (Fin (flatDim M) → ℝ)`
  (normed ⟹ `HasFDerivWithinAt` works), the leaf map = `paramsEquivFlat.symm ∘ (path composite)`.
  `LeafJacobian` keeps cert §3's `HasFDerivWithinAt` + `|det Dφ|` monomial ledger. Cost: flat-coord
  bookkeeping (`paramsEquivFlat` round-trips) at every `LeafPullback`/`Jacobian`.
- **Route (b) — RLCT transport (Codex §8, both consults prefer).** `region_glue` = per-chart transport
  via the banked LOCAL-homeomorph transport (`rlctAtOn_boundedUnit_localHomeomorph` — a blow-up chart
  is proper, not globally injective, so NOT the global `weightedThreshold_transport`) + the ONE missing
  **homogeneity scaling bridge** `∫_{εK}F^{-c'} = ε^{N−2Lc'}∫_K F^{-c'}` + the banked radial/monomial
  reads. Narrows the P8 gap to the scaling bridge.

**CORRECTION (controller-verified, 2026-07-17):** an earlier draft of this note claimed `Params M` has
no normed instance (from an `inferInstance` probe run WITHOUT the import). That is FALSE —
`Foundations/ParamsFlatLinear` banks `instNormedAddCommGroupParams`/`instNormedSpaceParams`/
`FiniteDimensional` + `paramsEquivFlatCLE` + `hasFDerivAt_paramsEquivFlat` (norm topology rfl-equal to
the product topology, no diamond). So the fderiv route is unobstructed; a probe is not a survey. Q5 is
RULED **route (b)**; `LeafJacobian`'s statement is the transport-hypothesis form (`HasFDerivAt` of the
composite via `paramsEquivFlat`, `det = ∏ u^{divExp−1} × unit`), consumed by the local-homeomorph
transport + scaling bridge. The per-edge `localSub` is a plain coordinate map; the Jacobian rides the
existing monomial ledger — NO opaque derivative field is stored as data.

### Witness split (ruled, precision policy — option ii) — same under A and B

- `canonicalResolution224_arithmetic` : a **clean-three bank piece** proving the FOUR
  carrier-independent conjuncts (IsFullMonomialization + StepInvariant-on-nodes + branch-rooted +
  exponent-hooks) at `(2,2,4)`. Survives the restructure (its conjuncts don't touch the edge/chart
  data). AxCheck: this name gets the clean-three entry (replacing the old `canonicalResolution_224`).
- `canonicalResolution224` (full) : a `@[blueprint]` FORECAST — the arithmetic four ∧ the ChartBridge
  conjunct, the latter's `LeafPullback`/`LeafJacobian` **sorried pending the P8 lemma**. AxCheck: its
  own `expects-sorryAx` entry.
- Vacuity closes at TYPE strength under either A or B (the fake univ-atlas leaf has no chart data /
  fails `LeafPullback`); fold the Python note into `g-chartscover-vacuity` when implementing.

## g-chartscover-vacuity re-scope (2026-07-17, post-restructure)

The `g-chartscover-vacuity` counterexample (an all-`univ` atlas satisfying the OLD `ChartsCover ∧ hrat`
while the box diverges) is now closed IN-LEAN by the edge-labelled bundle — no Python edit needed:
`LeafPullback` ties each leaf's `chartMap` to the loss (`F ∘ chartMap = ∏ u² · residualCore`), so a
constant / `univ` / mislabelled chart cannot satisfy it (its pullback is not a monomial × residual);
and the `ChartBridge` coherence forces `chartMap = the fold of the edge substitutions`, so it is not a
free field. What now kills the fake atlas: a chart whose pullback is not `monomial × (unit OR Morse)`
fails `LeafPullback`; a `divExp` not matching the true resolution exponents fails
`exponent_ledger_bridge` (`minAdm ∈ terminalExponents`). Complementary Lean witness:
`stepRel_rejects_mismatched_case2` (a mislabelled Case-2 edge fails `StepRel`).
