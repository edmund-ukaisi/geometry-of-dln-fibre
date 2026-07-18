# Cert — COMBINED COVERAGE review: rung-1 fidelity + rung-2 statement + the (a)-vs-(b) adjudication

*Reviewer: independent audit (rev-cov), controller-spawned. Branch
`expedition/aoyagi-engine--revcov` (worktree `/home/ubuntu/workspace/rev-cov-wt`, off
`expedition/aoyagi-engine` @ `1a8ffeed3`). Aoyagi 2023 read as PAGE IMAGES pp.14-22
(`paper-sources/aoyagi-2023-consideration-of-learning-efficiency-of-dln/aoyagi-2023-neural-networks-preprint.pdf`),
never the extracted text. Rung-1 target on my branch; rung-2 fold `PivotCoverFold.lean` @
`754eccc05` (cov07), built here by checking that one file onto my FIX-A branch. Batteries re-run;
forced `#print axioms`; one decorrelated Codex consult on items 1+3
(`codex/revcov-rungs12-{prompt,answer}.md`, gpt-5.x xhigh, hypothesis withheld).*

**Verdicts (most severe first):**
- **Item 3 (a-vs-b): (a)-generalized CONFIRMED** — page + Codex + battery agree; a StepEmit design
  amendment is owed to the architect.
- **Item 2 (rung-2 statement): 3 of 4 SOUND; `node_pivotCover_of_atom` is an UNPROVABLE STUB**
  (`pivotComplete : True` forces nothing; false for `edges = []`). Flagged as a placeholder, so this
  is a scoping gap, not concealment — but it is the load-bearing hole and item 3 answers what fills it.
- **Item 1 (rung-1 fidelity): SURVIVED** — the atom faithfully renders Aoyagi's blow-up charts;
  clean-three verified; battery reproduces.

---

## Item 3 — THE (a)-vs-(b) ADJUDICATION — VERDICT: (a)-generalized

**The page reading (p.16 top, VERBATIM).** Case 1 constructs ONE blow-up along the submanifold
`{ d_ij = 0 (i=J+1..J+J₁, j=J+1..M^{(S+1)}),  u_{s,k} = 0 }`. That center is the vanishing of a
`J₁ × (M^{(S+1)}−J)` block of `d`-entries **plus** the single divisor coordinate `u_{s,k}`:

  **center codimension `d_center = J₁·(M^{(S+1)}−J) + 1`.**

A blow-up of a smooth codimension-`d_center` coordinate center is covered by `d_center` standard
affine pivot charts — one per center coordinate. The paper's **Case 1(1) and Case 1(2) are pivot
TYPES, not the two-element chart set**:
- **1(1)** (p.16) = the `u_{s,k}`-pivot chart: the whole block `= u_{s,k}·[d′]`, i.e. `u_{s,k}`
  factored out (ONE chart — there is one `u`).
- **1(2)** (pp.16-18) = a `d`-entry-pivot chart, written only at the CORNER `d_{J+1,J+1}=u_{S,J+1}`
  (corner → unit `1`), a **representative** of the `J₁·(M^{(S+1)}−J)` block-pivot charts. Aoyagi
  covers the rest by "by a blow-up process" + the total-comparability symmetry (`T ≤` or `≥`, p.15).

So the FULL per-node family is `d_center` charts; the paper writes 2 representatives.
Case 2 (p.19) is the same story with center = the whole residual block `D_J`, `d_center =
(M(S)−J)·(M^{(S+1)}−J)`, no `u` in the center.

**Why (b) fails (the decisive point, Codex-independent).** A resolution's recursion descends INSIDE
each emitted chart's image; a pivot direction OMITTED at a node cannot be recovered by deeper
branching or by the comparability invariant, because every descendant already lives inside a
parent-chart image. The total-comparability invariant is consumed for the **ratio / principalization**
side (which pivot is Def-4-minimal, the no-smaller-ratio content — `cert-2222 (c)`), **NOT** to
manufacture the geometric cover. Hence coverage requires the FULL per-node pivot family emitted as
edges — reading **(a)**.

**The design-doc defect this exposes.** `t2-buildtree-design.md §1` / `cert-paper-map §2.2` currently
model "one Case-1 blow-up emits a 1(1) + a 1(2) edge" (TWO edges). At `d_center ≥ 3` — e.g.
`J₁=1, M^{(S+1)}−J=2` — two edges (one `u`-pivot + one corner `d`-pivot) MISS the other block-pivot
charts. This is exactly `cert-atlas-probe` Verdict 1(b): the corner-only reading misses
`(c₁₁,c₁₂)=(0,ε)` (the `u`-chart forces both entries to 0; the `c₁₁`-pivot chart forces `c₁₂=0`).
The landed `corner_chart_not_cover` is the in-Lean witness of this gap.

**Battery cross-check (and a precision correction to the dispatch).** The dispatch called the atlas
counts "ground truth" for per-node full-family emission. They are **not** a discriminator: I re-ran
`nonmono-2232-sim.py` (validates (2,2,2)/(3,3,4)/(2,2,2,2), reproduces the (2,2,3,2) raw-width
defect, FIX-A cleans it) and confirmed it emits exactly **two** children per Case-1 node (1(1) mutate
+ 1(2) create) yet produces the CORRECT terminal `t̃=0` profile atlas. The profile atlas is a
**symmetric quotient** — the `d`-pivot charts collapse to one profile-child because their exponent /
head-inheritance is chart-independent — so the atlas counts are invariant under (a) vs (b) and cannot
witness the geometric fan-out. The (a)-vs-(b) discriminator is the **page reading** (center
codimension) + the geometric cover gap, both of which I have. So: batteries confirm the value/profile
closure; they are BLIND to fan-out.

**Codex decorrelation (hypothesis withheld) — full agreement.** Q1: `d_center = 1+J₁(M^{(S+1)}−J)`,
that many charts, 1(1)/1(2) are representatives. Q2: corner-only has the `(0,ε)` gap. Q4: "the full
pivot family is required; descendants remain inside their parent-chart images, so later branching and
label comparability cannot recover a direction already omitted." BOTTOM LINE: **(a)**. Codex flagged
(correctly, preserved as inference) that the "by a blow-up process" compression is *inferred* intent;
the chart count and the cover gap are algebraic-geometry FACT.

**→ Item 3 VERDICT: (a)-generalized.** The recursion descends into the full per-node pivot family
(one edge per center coordinate; `d_center` charts). The `StepEmit` amendment for the architect: the
loose `hlive : 0 < edges.length ∨ True` must be replaced by a **`pivotComplete`** clause forcing the
edges to realize the full pivot family of the center (the `u`-pivot + every block-`d`-entry pivot),
so `node_pivotCover_of_atom`'s `hnode` discharges from the rung-1 atom. Emitting only 2 representatives
is unsound for coverage at `d_center ≥ 3`. (For the ledger/`StepRel` the multiplicity is invisible —
all `d`-pivot edges satisfy the same 1(2) ledger relation — so the amendment is coverage-only, no
`StepRel` change.)

---

## Item 2 — RUNG-2 STATEMENT REVIEW (`PivotCoverFold.lean` @ 754eccc05)

Built the file onto my FIX-A branch: **elaborates clean, exactly 4 sorries** (lines 60/76/91/103 =
the 4 targets); no other declaration affected. cov07 predates FIX-A but did NOT modify `EngineDefs`
after the merge-base (`7ee530331`), so FIX-A survives any merge of the coverage branch — **no
revert risk** (integration-safety note). The fold is FIX-A-agnostic (uses only
`ChartBridge`/`leaves`/`leafPaths`/`localSub`).

Traced each statement against the actual `ResolutionTree` defs:

- **`leafPathImages_branch` — SOUND.** True and provable via the prepend lemma
  `leafPaths (g∘h) c = (leafPaths h c).map (l,φ)↦(l, g∘φ)` (mutual induction on the tree; `map`
  distributes over `++`) + image/union distribution `(g∘φ)''S = g''(φ''S)`. The `edgesLeafPaths`
  recursion composes `acc ∘ s.localSub`, so the root edge's substitution is applied outermost
  (leaf-coords → root-coords) — the fold shape is correct.
- **`ownCovers_branch` — SOUND.** The inductive step follows from `leafPathImages_branch` +
  monotonicity: `childRegion e ⊆ leafPathImages e.child` (from `hchild`) ⟹
  `⋃ localSub '' childRegion ⊆ ⋃ localSub '' leafPathImages child = leafPathImages branch`; combine
  with `hnode`. Carrying `hnode` as an EXPLICIT hypothesis (not silently derived) is the right call.
- **`chartBridge_imageCover_of_ownCovers` — SOUND, and correctly wired to the consumer.** True
  because `(leafPaths id t).map Prod.fst = leaves t` (induction; `acc` never touches the leaf
  component) and `hcoh` rewrites each `p.2 → p.1.chartMap`, turning `leafPathImages t` into
  `⋃ l ∈ leaves t, l.chartMap '' l.srcBox`. Conclusion + `hcoh` shape are a VERBATIM match to
  `ChartBridge`'s image-cover clause + coherence clause (`EngineDefs.lean:76-78, 86`). Honest
  separation: the geometric cover (composites) is the fold's; coherence (stored `chartMap` =
  composite) is buildTree/`ChartLeaf`'s.
- **`node_pivotCover_of_atom` — UNPROVABLE STUB (the load-bearing gap).** Hypothesis
  `pivotComplete : True` forces nothing; with `edges` and `V` free the conclusion is FALSE (take
  `edges = []` ⟹ RHS `= ∅` ⟹ `V ⊆ ∅`, but `V` arbitrary). The `sorry` cannot be discharged as
  written. This is the classic abstract-field trap (a hypothesis so loose it forces neither what the
  atom needs nor what buildTree supplies). It IS explicitly labelled a placeholder held for this
  review, so it is a scoping gap, not concealment. **Repair (= item 3's amendment):** replace
  `pivotComplete : True` with the concrete contract — `edges` = the `d_center` pivot-chart edges,
  `childRegion e` = per-pivot max-modulus sub-cube, `V` = the center cube, `localSub` = the
  flat-embedded `pivotChart` — whereupon `hnode` discharges directly from
  `iUnion_pivotChart_image_eq_cubeBox`. The depth-1 fit (single node, leaf children) then reduces to
  the atom verbatim, confirming the fold's base case.

**Fold shape verdict: RIGHT.** `leafPathImages` recursion + `OwnCovers` induction + the headline are
sound and the headline produces exactly `ChartBridge`'s image-cover clause. The one hole is the atom
bridge's stub hypothesis — and it is precisely the interface item 3 resolves. One scoping note (not a
defect): the tree induction needs a coherent **region assignment** (what each subtree covers, and that
the node's pivot images of child regions cover the parent region); it is currently abstracted into the
free `childRegion` + the `pivotComplete` stub and must be made concrete in the grind.

---

## Item 1 — RUNG-1 FIDELITY (`PivotCover.lean`, landed) — VERDICT: SURVIVED

**Forced `#print axioms` (my own, scratch module importing the landed file):** all three theorems
`cubeBox_subset_iUnion_pivotChart_image`, `iUnion_pivotChart_image_eq_cubeBox`,
`corner_chart_not_cover` depend on **`[propext, Classical.choice, Quot.sound]`** — clean-three, no
`sorryAx`, no custom axiom, no `native_decide`. Module imports only `Foundations.S1Cover` (circularity
guard clear: no `rlct=c*`, no `cited_aoyagi_dln`).

**Battery re-run** `c-pivot-chart-cover.py` → exit 0: COVER (exhaustive rational grid `d=1..4`), BOUND,
GAP (reproduces the `(0,ε)` corner miss), JAC (`|det D(pivotChart i)| = |u_i|^{d−1}`, symbolic).

**Fidelity to the pages.** The atom is the SINGLE-blow-up normal-slice model, and it is faithful:
- `pivotChart i u k = u_i` (k=i) `= u_i·u_k` (k≠i) is exactly Aoyagi's affine chart "pivot free,
  others = pivot × ratio": Case 1(1) has old block `= u_{s,k}·d′`, i.e. new = pivot × ratio — a
  verbatim match.
- **Max-modulus normalization is a faithful covering refinement**, not a distortion: chart `i` is the
  standard affine chart restricted to `{|x_k| ≤ |x_i| ∀k}`; every cube point has a max-modulus
  coordinate, so the bounded charts still cover exactly (`= cubeBox`), and the `|ratio| ≤ 1` bound
  serves `ChartBridge`'s bounded-`srcBox` requirement for free.
- **Jacobian faithful to Aoyagi's exponent increment.** The atom's `u_i^{d−1}` with `d = d_center`
  equals Aoyagi's Case-1(1) exponent bump `J₁·(M^{(S+1)}−J) = d_center − 1` for the new divisor. The
  cov07 docstring's "single exceptional divisor at `divExp = d`, leaf `divExp` is the fold" reading is
  consistent (`divExp − 1 = d − 1`).
- The atom blows up `ℝ^d` at the ORIGIN; Aoyagi blows up a codim-`d_center` coordinate SUBMANIFOLD.
  These coincide in the normal coordinates (untouched center directions are spectators) — the atom is
  the correct local model, and the ambient embedding (spectators passing through) is rung-2's
  `node_pivotCover_of_atom`, correctly deferred.

**Codex (item 1, Q3) agrees:** faithful/standard rendering; union of images `= [-R,R]^d`; a fixed
chart covers only `{|x_k| ≤ |x_i|}`; Jacobian `= u_i^{d−1}`.

**→ Item 1 VERDICT: SURVIVED.** The bounded max-modulus pivot atom is a faithful, clean-three
rendering of Aoyagi's per-blow-up chart cover, and `corner_chart_not_cover` correctly witnesses that
the full family is load-bearing.

---

## Actions owed
- **Architect:** amend `StepEmit` — replace `hlive : 0 < edges.length ∨ True` with a `pivotComplete`
  clause forcing the full per-node pivot family (`d_center` edges: the `u`-pivot + every block-`d`
  pivot). Two-representative emission is unsound for coverage at `d_center ≥ 3`.
- **Coverage seat (rung-2 grind):** fill `node_pivotCover_of_atom`'s `pivotComplete : True` with the
  concrete center/edges/childRegion/localSub contract; the other 3 fold statements are sound to grind
  as written.
- **Precision note (for the map/design docs):** `cert-paper-map §2.2` and `t2-buildtree-design §1`
  say "one Case-1 blow-up emits a 1(1) + a 1(2) edge (two charts)". Correct that 1(1)/1(2) are pivot
  TYPES; the full family is `d_center` charts (the 1(2) representative stands for
  `J₁·(M^{(S+1)}−J)` block-pivot charts). The coverage-thread `page-pin-centers.md` (cov07) already
  states this correctly.
