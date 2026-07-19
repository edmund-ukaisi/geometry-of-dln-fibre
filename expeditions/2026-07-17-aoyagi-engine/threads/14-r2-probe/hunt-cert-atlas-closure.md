# Hunt-cert — R2 atlas-closure probe: does the constructed atlas IMAGE-COVER the zero-locus?

*Seat: `pen-and-paper` (pnp-o5), R2 gate DECORRELATED probe (adversarial — try to BREAK the cover).
Chosen decorrelated from the atlas design (I worked the ledger/strand side; did NOT consult
coverage-t07 or pnp-atlas). Atlas read from DURABLE artifacts only: `threads/10-coverage/`
(`cert-cov-rungs12.md`, `page-pin-centers.md`), `threads/08-atlas-probe/cert-single-psi.md`, the Lean
STATEMENTS (not proofs) of `Engine/PivotCover.lean`, `PivotCoverFold.lean`, `ShearReconcile.lean`,
`ChartBridgeWiring.lean`, `EngineConstruction.lean` (ConDecision/buildTree), + Aoyagi pp.15–21.
Exact rational grid + exact sympy; NO Monte-Carlo. Circularity guard: every leg is pure geometry/
algebra — consumes NO statement downstream of `rlct=c*` / `cited_aoyagi_dln`. Decorrelated Codex leg
(`codex/atlas-closure-{prompt,answer}.md`, hypothesis withheld). Batteries: `battery/leg{1,2,3,4}*.py`
(all exit-0).*

## Headline verdict

**The image-cover is MATHEMATICALLY SOUND — no geometric undershoot in the intended atlas** (the full
per-node `d_center` pivot family, ψ-composed, folded). Legs 1–4 find no missed point or direction; the
Lean node-cover theorems (`node_pivotCover_of_atom`, `node_pivotCover_of_atom_sheared`) are proved.

**BUT the single load-bearing precondition — the constructed tree must EMIT the full `d_center` pivot
family per blow-up node (`hbij`) — is NOT discharged by the current `buildTree`.** `ConDecision.step`
(`EngineConstruction.lean:391`) carries only LEDGER content (`hnode`/`hlayer`/`hstep`); it has **no
pivot-completeness clause**, so the concrete oracle emits the profile-quotient edges (2 representatives
per Case-1 node), not the `d_center` geometric family. At the bottleneck instance `(3,3,4,2,3)`,
**173/363 nodes have `d_center ≥ 3`** — where a 2-representative emission has the `corner_chart_not_cover`
gap. This is a decorrelated confirmation + quantification of the review's flagged gap
(`cert-cov-rungs12` item 2/3: the `StepEmit` `pivotComplete` amendment owed to the architect). It is a
WIRING precondition, not a break of the cover math — so it does NOT reopen the coverage theorem, but it
is where an undershoot WOULD occur if the amendment does not land.

## Atlas structure under test (from the durable artifacts)

Per-node local map `= ψ ∘ β`: `β` the max-modulus monomial pivot blow-up of a codim-`d_center`
coordinate center (`PivotCover.pivotChart`; Case-1 `d_center = J₁(M^{S+1}−J)+1`, Case-2
`(M(S)−J)(M^{S+1}−J)`, `page-pin-centers.md`), `ψ` the per-node unit-triangular unipotent Schur/shear
gauge (`cert-single-psi.md`, `det Dψ = 1`). Leaf chart `= ` root→leaf fold of these (`PivotCoverFold`).
The cover chain is a sequence of PROVED implications:
`chartBridge_of_pieces` ← `himg` ← `chartBridge_imageCover_of_ownCovers` ← `ownCovers_branch` (fold) ←
`node_pivotCover_of_atom[_sheared]` (per-node) ← rung-1 `iUnion_pivotChart_image_eq_cubeBox`. The
antecedent that is NOT established: the tree's edges realize the full pivot family per node (`hbij`).

## Kill-set (elder-gate7 adequacy — both mechanisms + corner)

`(2,2,2)` baseline · `(2,2,1,1)` + `(3,3,4,2,3)` interior-bottleneck width-drop (mechanism i) ·
`(2,2,3,3,2)` L≥4 non-monotone depth (mechanism ii) · `(3,3,2,2)` bottleneck · the
`corner_chart_not_cover` config (mechanism iii, boundary). Arising `d_center` values across the
kill-set: `{1,2,3,4,5,6,9,12}` (up to 12 at the bottleneck).

## Leg 1 — per-node max-modulus TILING at the ARISING d_center `[PASS]`

*Kill: full family misses a cube point (breaks rung-1) OR a proper subset silently covers (family not
tight).* Exact rational grid (`fractions`), `d = 1..6` full grid + the arising values.
- FULL family image = cubeBox^{d} exactly at every tested `d`: **0 misses**. (Every cube point has a
  max-modulus coordinate whose pivot reaches it.)
- Every `(d−1)`-subset MISSES its omitted pivot's axis direction `e_omit` (the omitted pivot uniquely
  covers it): **tight at every `d ≥ 2`**. So emitting fewer than `d_center` charts undershoots.
→ **N = 6 dims / 0 full-family misses / (d−1)-subset undershoot confirmed at all d≥2.**

## Leg 2 — Schur gauge ψ COVER-PRESERVATION (chartMap = ψ∘β) `[PASS]`

*Kill: det ≠ 1 (degeneracy) OR ψ⁻¹ not polynomial / unbounded (cover gap).* Exact sympy, residual
block sizes `{2×2, 2×3, 3×3, 3×4, 4×4}`.
- `det Dψ = 1` on BOTH the residual-Schur block and the C-row-mix block (unit-triangular, unipotent) —
  ψ is measure-preserving, no Jacobian vanishing (unlike β). *[transcription note: the C-map is the
  unit-triangular `Q⁻¹`; the corner index must be excluded from the row-mix sum or it double-counts —
  caught and fixed in-leg.]*
- ψ is a polynomial BIJECTION: `ψ⁻¹∘ψ = id` symbolically (the Schur up-date `d_ij ↦ d_ij + d_i1 d_1j`
  is the exact inverse).
- BOUNDED distortion on the unit box: `|ψ|,|ψ⁻¹|` entries `≤ box + box² = 2` (finite, explicit) — no
  unbounded push, so the scaling bridge globalises small→unit box.
→ ψ is a bounded-unit diffeo with full inverse; `ownCover_transport` (`ShearReconcile.lean`, PROVED)
carries the pivot cover through ψ. **N = 5 block sizes / det=1, bijection, bounded — 0 cover-breaks.**

*Refinement (Codex-sharpened, two-way):* `⋃(ψ∘f_i)(D_i) = ψ(⋃ f_i(D_i))` — ψ creates NO internal gap,
but it covers `ψ(target)`, NOT the UNCHANGED target box. Codex's witness: `ψ(x,y,z)=(x,y,z−xy)` sends
`p=(¾,¾,¾)` to `ψ⁻¹(p)=(¾,¾,21/16) ∉ [−1,1]³` — so at `R=1` the raw cube is NOT covered; one needs
`R ≥ 2` (my Leg-2c bound `box+box² = 2`) or the target stated in ψ-coords. This is EXACTLY the Lean
theorem's shape: `node_pivotCover_of_atom_sheared`'s hypothesis is `hV : V ⊆ ψ '' (center-slab)` (the
ψ-image, not the raw slab), discharged for the zero-locus by the banked SCALING BRIDGE (small-box→unit-
box, clean-three). So this is a SECOND satisfiable precondition (after `hbij`), correctly stated in the
Lean theorem and handled by the scaling bridge — not a break, but named.

## Leg 3 — the FOLD + the interior-bottleneck stranding `[PASS]`

*Kill: a node whose full family fails to tile (fold gap); a stranded stratum whose points no leaf
reaches (geometric undershoot).*
- (3a) **tree-fold tiling**: replayed the built tree; at EVERY node the arising-`d_center` pivot family
  tiles its center cube (full covers + corner-only undershoots). Arising `d_center = {1,2,3,4,5,6,9,12}`,
  all tile. The tilings compose (`ownCovers_branch`, PROVED) → leaves TILE the box → every zero-locus
  point is in some leaf region. **0 fold gaps.**
- (3b) **amendment load-bearing count** (nodes with `d_center ≥ 3`, where 2-representative emission has
  the corner gap): `(2,2,2)` 3/6 · `(2,2,1,1)` 1/6 · `(3,3,4,2,3)` **173/363** · `(2,2,3,3,2)` 22/44 ·
  `(3,3,2,2)` 19/39. The full-family emission is required at a MAJORITY of deep-instance nodes — not a
  corner case.
- (3c) **stranding is NOT an image-cover gap**: at every bottleneck the stranded stratum's HEAD is
  carried by a `t̃>0` leaf divisor (e.g. `(2,2,2,0)` stranded at `(3,3,4,2,3)` → `(2,2,2,2)` at `t̃=2`),
  so a leaf region contains those points. The tiling argument (3a) reaches every point regardless of
  `t̃`. The stranding affects only the `t̃=0` MONOMIALIZATION read (a `residualCore` squeeze obligation,
  fork 12(b)(ii)) — a finiteness burden correctly placed on T3, NOT a missing chart. **0 stranded-
  stratum geometric misses.**

## Leg 4 — corner / boundary class `[PASS]`

*Kill: a boundary `d_center` where the family is empty but V nonempty; the corner config uncovered.*
- (4a) the `corner_chart_not_cover` config `(0,…,0,ε)` generalized to `d = 2..6`: the corner (pivot-0)
  chart does NOT cover it, the correct (last) pivot DOES, and the FULL family covers it — so the atlas's
  pivot family genuinely handles what the corner chart misses. **0 uncovered.**
- (4b) `d_center = 1` degenerate: the single chart covers `[−R,R]` (no gap).
- (4c) no blow-up node emits `d_center = 0`: replayed the kill-set trees — every Case-1/Case-2 node has
  `d_center ≥ 1` (`0 violations`); no empty center against a nonempty V.

## The load-bearing finding (surfaced; not a math undershoot)

The cover chain is proved MODULO `hbij` (full family per node). The current `buildTree`
(`EngineConstruction.lean`) constructs the LEDGER/profile-quotient tree: `ConDecision.step`'s `hstep`
forces only the `stepUpdate` ledger relations (+ eligibility + rollover guard) — **there is no
pivot-completeness / `hbij` clause**. The framework ALLOWS `d_center` children under one ledger relation
(the `d`-pivot edges share the 1(2)/Case-2 ledger — `cert-cov-rungs12`), but the concrete oracle
(transcribing the profile simulator) emits only the 2 representatives. So:
- **Route (i) — explicit full family** (the review's (a)-generalized): the oracle + `ConDecision.step`
  must be amended to emit the `d_center` pivot-chart edges per node and CARRY `hbij` (the `pivotComplete`
  amendment owed to the architect). This is the sound route; it is NOT yet wired.
- **Route (ii) — cover via `CompChainInv` over the profile tree**: REFUTED (`cert-cov-rungs12` +
  Leg 1): descendants live inside their parent-chart images, so no later branching or label invariant
  recovers an omitted pivot direction. A profile-quotient tree with 2 charts per Case-1 node UNDERSHOOTS
  at every `d_center ≥ 3` node (the corner gap). So route (ii) does not close the cover.
Therefore: the cover holds iff the full family is emitted (route i). This is the one precondition; it is
massively load-bearing (Leg 3b) and not yet discharged.

## Kill-conditions status

- **Geometric undershoot of the intended (full-family) atlas:** NOT found (Legs 1–4). The full-family
  cover is sound; ψ preserves it; the fold tiles; stranding is a finiteness obligation, not a chart gap.
- **Undershoot of the AS-BUILT tree (profile quotient, 2 reps/node):** WOULD occur at `d_center ≥ 3`
  (corner gap) — this is the wiring precondition, not a math break. Flagged, quantified (173/363 at the
  bottleneck), consistent with the review.
- Kill-set exercised both mechanisms (interior bottleneck + L≥4 depth) + the corner class; all legs
  pass on all of them.

## Codex decorrelation (hypothesis withheld) — FULL CONVERGENCE + one sharpening

`[OBS]` Codex (xhigh, given only the atlas definitions + the "2 representatives per Case-1 node" fact,
NOT my conclusion) independently:
- **Q1 [PROVED]:** full family covers `[−R,R]^d` exactly (`C_i = {|x_k|≤|x_i| ∀k}`, union = cube); a
  proper subfamily misses `ε·e_j` for any omitted pivot `j` — "the two representative charts fail
  whenever `d_center > 2`, i.e. Case-1 `J₁(M^{S+1}−J) > 1`." (= my Leg 1 + Leg 3b.)
- **Q2 [PROVED]:** ψ creates no internal gap (`⋃(ψ∘f_i) = ψ(⋃ f_i)`) but covering the UNCHANGED target
  needs compatibility — the `ψ(x,y,z)=(x,y,z−xy)`, `ψ⁻¹(¾,¾,¾)=(¾,¾,21/16)∉cube` witness (folded into
  Leg 2 above). "det Dψ = 1 alone does not preserve the cube." (= my Leg 2, sharpened.)
- **Q3 [PROVED]:** fold preserves the cover node-by-node; "folding cannot repair a failed local cover —
  descendants remain inside their parent-chart images." (= my Leg 3a + the review.)
- **Q4 [PROVED]:** "stranding alone does not uncover points — a `t̃>0` leaf is still a leaf chart …
  a gap arises only if `t̃>0` leaves are discarded, or if representative-chart omission already
  destroyed geometric coverage." (= my Leg 3c, verbatim mechanism.)
- **Q5 bottom line:** the load-bearing precondition = "at every internal node the emitted GEOMETRIC
  children — not merely their profile classes — must cover the node's neighbourhood; two representatives
  do not suffice when `d_center > 2` … profile equivalence does not identify these actual image points;
  the failure occurs immediately in the parent-to-children step and persists, unless the missing charts
  are restored via explicit symmetry-translated copies." (= my finding: route i required, route ii dead.)
Two independent derivations agreeing to the component; Codex adds the ψ target-compatibility sharpening.

## Close

- **Firmest:** the full per-node `d_center` pivot family (ψ-composed, folded) IMAGE-COVERS the
  zero-locus with no undershoot — per-node max-modulus tiling (exact, arising `d_center` 1..12), gauge
  cover-preservation (det 1, bounded diffeo), fold tiling, and stranding-is-a-finiteness-obligation, all
  verified; the Lean node-cover theorems are proved. Kill-set covered both mechanisms + the corner.
- **Most likely to break it:** the constructed `buildTree` NOT emitting the full family — `ConDecision.step`
  has no `pivotComplete` clause, so as-built it undershoots at `d_center ≥ 3` (majority of deep nodes).
  The `StepEmit` amendment (route i) is the load-bearing wiring and is NOT yet landed.
- **Next:** land the `pivotComplete` amendment (oracle emits the `d_center` pivot edges per node +
  `ConDecision.step` carries `hbij`), so `node_pivotCover_of_atom[_sheared]`'s `hbij` discharges over the
  constructed tree. The other node-cover hypotheses (`hloc` gauge-shape, `hdom`, `hV`) are satisfiable
  (Legs 2/3/4). Route (ii) is dead — do not attempt to cover via `CompChainInv` over the profile tree.
