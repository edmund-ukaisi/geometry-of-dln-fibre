# Counter-sign — the corrected `ChartBridge` type (coverage seat)

*Seat: `coverage-t08` (COVERAGE counter-sign), succeeding `coverage-t07` (VM-restart; its Lean lane
banked + merged). Reviews `threads/11-construction/decision-package-chartbridge-type.md` (architect-t05).
Grounded in the LIVE lane at HEAD `6b2e406a5`: every `file:line` below read directly. Acceptance test
(the commission): can coverage PROVE its remaining content against the proposed type? Decorrelated Codex
leg on the highest-risk item (`codex/single-psi-cover-factoring-{prompt,answer}.md`, hypothesis withheld).
No Lean re-typed (ratification precedes it).*

Sources read in full: the decision package; `EngineDefs.lean:36-86` (`ChartBridge`, `LeafPullback`,
`LeafJacobian`); `ChartBridgeWiring.lean` (`chartBridge_of_pieces` + the `*With` fold-forms);
`PivotCover.lean`, `PivotCoverFold.lean`, `PivotInjOn.lean`, `ShearReconcile.lean`, `PivotLeafClauses.lean`,
`FlatCubeLeaf.lean` (the banked cover lane); `ResolutionTree.lean` (`LeafData`, `leaves`, `leafPaths`,
`terminalExponents`); `RegionGlueAssembly.lean` + `RegionGluePerLeaf.lean` (the two glue lemmas);
`cert-single-psi.md`, `page-pin-centers.md`, `cert-cov-rungs12.md`, `hunt-cert-atlas-closure.md` (R2);
journal ticks 111-114 (the gauge-fact arc).

---

## Verdict: COUNTER-SIGN

The flat virtual-leaf atlas `∃ atlas : List (LeafData M), (A)∧(B)∧(C)∧(D)` is the right type. Coverage's
remaining content is provable against it; nothing found is a **type** defect. Two qualifications, neither a
rejection: (item 2) the cover clause is produced by the banked fold over an auxiliary geometric tree
(`atlas = leaves t_geo`), and its single-per-node-gauge assumption is likely INSUFFICIENT for Case-1 nodes —
a decorrelated Codex leg (hypothesis withheld) refutes the "u-pivot = ledger-only extra" escape the team's
tick-113/162 resolution relied on, so coverage should plan for the per-edge or source-reparameterization
route (a fold-machinery fix, NOT a type change); (item 4) clause (D) should be D1's fidelity content but must
reference the geometric fan-out, not the quotient `t`. The named grind (item 5) is substance the type
correctly LOCATES per-piece, not owed to the type.

Why the corrected type is not merely a repair: under the frozen type the three fed Props are **unprovable**,
not just awkward. `LeafPullback`/`LeafJacobian` read ONE `divCoord`/`divExp` per leaf (`EngineDefs.lean:47,64`);
one ledger leaf stands for a `d_center`-member pivot family, and different pivots blow up different flat
coordinates, so no single `chartMap`/`divCoord` per ledger leaf can satisfy the monomial-pullback identity
for the whole family. Per-piece `divCoord` dissolves this: each atlas piece is one geometric chart with its
own coordinate data. The corrected type is a **precondition** for provability, confirming the package's §0.

---

## Item 1 — the 3 fed Props per atlas piece (a.e.-InjOn / LeafPullback / LeafJacobian)

**Does per-piece `divCoord` dissolve the piecewise failure? YES.** Each atlas piece carries its own
`divCoord`/`divExp`/`chartMap`/`srcBox`, so a single geometric chart (one pivot-choice fold) is one piece,
and the three Props reduce to the standard single-`ψ∘β` obligations — exactly the shape
`leaf_chart_image_lintegral_lt_top` consumes (`RegionGluePerLeaf.lean:119`, reads only per-leaf fields).

Banked vs owed, per Prop (all against `pivotChart` = Aoyagi's `β`, `|det Dβ| = |u_i|^{d-1}`):

- **a.e.-InjOn** (`∃ N, volume N = 0 ∧ InjOn c.chartMap (c.srcBox \ N)`): the ATOM is banked —
  `pivotChart_ae_injOn` (`PivotInjOn.lean:47`) gives injectivity off the null exceptional hyperplane
  `{u_i = 0}`. The transport to `c.chartMap = ψ ∘ β` (fold across nodes, `q`-conjugation, spectator
  product, post-compose the homeomorphism `ψ`) is OWED grind — standard (InjOn is preserved by injective
  post-composition and homeomorphism conjugation; null sets stay null under diffeos), gated only on the
  concrete `β`/`ψ`. Provable against the type; not yet in Lean.
- **LeafPullback c** (`frobSq(prod M (chartMap w)) = (∏ (flat w (divCoord k))²)·core`, squeezed): NOT in the
  pivot lane — it is the analytic monomialization identity (o5's spine, the `Mval`/`residualCore` content),
  not coverage's cover geometry. Named as a per-piece dependency of clause (B); the type locates it correctly
  (per-piece `divCoord` is exactly what the monomial factor needs).
- **LeafJacobian c** (`chartMap = ψ∘β`, `|det Dβ| = ∏|flat w (divCoord k)|^{divExp k - 1}`, `ψ` bounded
  diffeo): the geometry is banked (`β` = `pivotChart`; `ψ` = the Schur gauge, `cert-single-psi`, det 1,
  bounded). **The Jacobian-det is NOT proven in Lean** — `PivotCover.lean` proves the cover
  (`iUnion_pivotChart_image_eq_cubeBox`) and the corner ¬-theorem, but there is no `HasFDerivAt (pivotChart i)`
  / `(D…).det = …` theorem; the det lives only in the docstring + battery `c-pivot-chart-cover.py` (JAC leg).
  So `LeafJacobian c`'s `Dβ` obligation is owed Lean work: the per-blow-up det atom, then the path fold
  `|det| = ∏ monomial`. Named precisely (item 5b).

**Item 1 verdict: COUNTER-SIGN.** Per-piece `divCoord` dissolves the failure exactly as claimed; the Props
become standard single-chart obligations. a.e.-InjOn atom banked; det-atom, pullback, and the transport are
named grind — correctly per-piece under the type.

---

## Item 2 — the image-cover clause over the flat atlas

**Does the banked fold produce clause (A) `U ⊆ ⋃ c ∈ atlas, c.chartMap '' c.srcBox`? YES, via
`atlas = leaves t_geo`.** The chain `chartBridge_imageCover_of_ownCovers` ← `ownCovers_branch` ←
`node_pivotCover_of_atom_sheared` ← `iUnion_pivotChart_image_eq_cubeBox` produces
`U ⊆ ⋃ l ∈ leaves t', l.chartMap '' l.srcBox` for the tree `t'` it folds over
(`PivotCoverFold.lean:224`). The one design point the package glosses:

- `node_pivotCover_of_atom_sheared`'s `hbij` demands the tree's edges at a node realize the FULL `d_center`
  pivot family. The SPINE tree `t` (argument of `ChartBridge M t`) is the symmetric quotient (2 reps/Case-1
  node, `cert-cov-rungs12` — `hbij` FAILS on it). So the fold cannot run on `t`.
- Resolution: coverage builds an **auxiliary geometric fan-out tree `t_geo`** (each node emits its full
  `d_center` pivot family as edges, so `hbij` holds by construction), folds over `t_geo`, and sets
  `atlas := ResolutionTree.leaves t_geo`. Then `chartBridge_imageCover_of_ownCovers t_geo` produces
  `⋃ l ∈ leaves t_geo, l.chartMap '' l.srcBox = ⋃ c ∈ atlas, c.chartMap '' c.srcBox` — clause (A) VERBATIM.
  `t_geo` is a proof-internal device (not in `StepRel`/`Edge`/the spine), so it respects the sub-gap-3 pin
  ("fan-out lives in the atlas List, not the spine"): the atlas List IS `leaves t_geo`, the tree is scaffolding.

So the package's "a geometric-fan-out traversal EMITS a flat list" must be read as **"the leaf-list of the
geometric fan-out tree"** — that is the object the proven headline emits. A raw List NOT arising as
`leaves t_geo` would forfeit the banked tree-fold and force a from-scratch List-level cover induction. Flag:
keep the atlas realized as `leaves t_geo`.

**The single-per-node-gauge assumption — the load-bearing risk.** `node_pivotCover_of_atom_sheared` bakes in
ONE `ψ` per node shared by all edges (`hloc : ∀ e ∈ edges, localSub e w = ψ (q.symm (pivotChart (pivotOf e) …))`,
`ShearReconcile.lean:47`). Journal tick 113 records the architect's page-determination (pp.17-18) that
per-node single-`ψ` is faithful ("the `d_center` family is its symmetric orbit; in the post-pivot frame the
clearing is the SAME structural unipotent shear"), so the lemma "applies AS-IS", with a **standing gate**:
the construction mechanically checks the single-`ψ` factorization, and a contradiction STOP-AND-SURFACEs to
coverage's per-edge (ii) branch (a generalized bridge). This is already a team watch-point — tick-162's
addendum names it and its **expected resolution (i)**: case-1(1) merges are LEDGER-only edges (`localSub = id`,
no geometric content), so the COVER family is the `d`-pivot family sharing the node's single gauge, and the
`ψ=id` merge edges are extras under the `⋃`. My adversarial sharpening of WHERE resolution (i) could fail:
`cert-single-psi.md:47` puts the Case-1 `1(1)` `u`-pivot at `ψ = id`, the `d`-entry pivots at `ψ = Schur`,
while `page-pin-centers.md` counts the `u` coordinate INTO the center (`d_center = J₁(M^{S+1}−J) + 1`), so the
`u`-max-modulus sector needs SOME cover chart. Resolution (i) is clean **iff** that sector needs no separate
node-level cover chart (the `u`-degeneration is carried by the descent, and the ledger-only `localSub=id`
edge suffices) — the u-pivot is then genuinely absent from the geometric cover family, which is homogeneous
(all `ψ=Schur`) and single-`ψ` holds. It FAILS **iff** the `u`-max sector needs a geometric `u`-pivot cover
chart at the node with a gauge distinct from the `d`-pivots' — then the node is mixed-`ψ`, and the atom's
single tiled cube (ALL center charts together, max-modulus) cannot be split into `ψ`-homogeneous sub-families
without breaking the tiling, so the per-edge (ii) branch is the owed unit (item 5a). This is exactly the
question the carrier-map's "per-node edge classification (cover-family vs ledger-only)" item (tick 162) is
meant to settle by inspection.

**Decorrelated Codex leg (`codex/single-psi-cover-factoring-{prompt,answer}.md`, xhigh, hypothesis withheld)
— it indicates resolution (i) FAILS in the natural model.** Given only the Case-1 geometry (not my
hypothesis, not the team's position), Codex independently concludes: (1) in the natural fixed-coordinate
target-postcomposition model `chartMap_p = ψ ∘ β_p` with pure `β_p`, **no single `p`-independent `ψ` exists**
— the `u`-pivot chart has `ψ_u = id` (no regular pivot to Schur-eliminate, `D = uD'`) while `d`-entry pivots
have the nontrivial Schur update; (2) **the `u`-chart CANNOT be dismissed as a ledger-only extra** — it is the
unique standard chart covering the `u`-axis `{D = 0, u ≠ 0}`, where every `d`-pivot (pivot `d_{rc} = 0` there)
collapses all center coordinates to zero; (3) even the `d`-entry gauges are pivot-dependent (pivot `(1,1)`
updates `x_{22}`, pivot `(1,2)` updates `x_{21}` — distinct ambient maps; "same syntax after renaming" is
conjugacy `ψ_p = σ_p^{-1} ψ_0 σ_p`, not equality); (4) independently shearing covering sectors CREATES GAPS —
concrete det-1 witness `C_1 = {|y|≤|x|}`, `C_2 = {|x|≤|y|}`, `ψ_1 = id`, `ψ_2(x,y) = (x+y², y)`: the point
`(-t+t²/2, t)` (`0<t<1`) lies in neither `C_1` nor `ψ_2(C_2)`, so `⋃_p ψ_p(S_p) ≠ ψ(⋃_p S_p)` for any common
`ψ`. **Verdict: the single-per-node-gauge lemma is not sufficient for a Case-1 node; a per-edge-gauge cover —
OR a source-reparameterization theorem — is required.** Codex's source-reparam route is the cleaner
alternative and may reuse MORE banked machinery: absorb the cleaning into the SOURCE domain,
`β̃_p = β_p ∘ α_p^{-1}`, so `β̃_p(α_p(D_p)) = β_p(D_p)` — the chart IMAGE is unchanged, so the PURE
`node_pivotCover_of_atom` (no `ψ`) applies with reparametrized domains, and no per-edge-`ψ` cover statement is
needed. This is a decorrelated CHALLENGE to tick-113/162's resolution (i), to adjudicate at the elder gate.

**Item 2 verdict: COUNTER-SIGN with sharpening.** Clause (A) is produced by the banked fold VERBATIM over
`atlas = leaves t_geo`. The single-`ψ` node lemma is NOT a type concern (the flat atlas carries per-piece
`chartMap`, so any `ψ`-structure is fine at the type level) — but the decorrelated leg indicates the current
`node_pivotCover_of_atom_sheared` is likely INSUFFICIENT for Case-1 nodes, and coverage should plan for the
per-edge cover or (preferably) Codex's source-reparameterization route rather than count on resolution (i).
This escalates item 5a from "risk if the gate fails" to "leg indicates the gate fails; plan the fix."

---

## Item 3 — `chartBridge_of_pieces` re-typing

**The re-typed skeleton is provable from the same pieces, and SIMPLER.** Under the corrected type the wiring
lemma becomes a bundling: given `atlas`, the image-cover (A), the per-piece Props (B), clause (C), clause
(D), return `⟨atlas, hA, hB, hC, hD⟩`. No `χ`, no coherence rewrite — each piece's `chartMap` IS the real
chart, so plain `LeafPullback c` / `LeafJacobian c` are the fed Props (no placeholder to route around).

Verified against the code:

- **`χ` drops.** The `χ` parameter (`ChartBridgeWiring.lean:59`) existed only because the frozen type's
  `l.chartMap` was a LEDGER-leaf placeholder field, and the anti-vacuity pin forbade stating Props against a
  placeholder. Virtual-leaf pieces carry the real chart, so the placeholder problem is gone and `χ` is
  unneeded. Confirmed the package's §3 forecast.
- **`LeafPullbackWith`/`LeafJacobianWith` + `leafPullback_eq_with`/`leafJacobian_eq_with` are deletable.**
  Grep confirms they are consumed ONLY inside `ChartBridgeWiring.lean` — no external consumer. Deleting them
  breaks nothing (item 5 has no entry for this).
- **No downstream breakage.** `chartBridge_of_pieces` currently has NO consumers (grep: only its own def).
  Re-typing it is free of ripple; the discharge target `chartBridge_buildTree` keeps its one `sorry`
  (re-elaborates against the new def).

The substance relocates correctly: the new `chartBridge_of_pieces` is trivial; the work is in items 1
(the Props per piece) and 2 (the cover). That is the right factoring — a wiring lemma should be a bundling.

**Item 3 verdict: COUNTER-SIGN.** The re-typed skeleton is provable and strictly simpler than the current
one; `χ` and the `*With` lemmas drop cleanly (verified no external consumers).

---

## Item 4 — clause (D): D1 vs D2 (elder-gate8 amendment folded in)

**The elder-gate8 pin SUPERSEDES my initial "D1-flat" recommendation, and it is the correct tightening.**
The elder ratified D1 as the direction and pinned its CONTENT (encoding deferred to coverage): D1 must
(i) quantify over `t`'s ACTUAL geometric paths — a `geometricLeafPaths` analog of the existing `leafPaths`,
referencing `t`'s edge/node structure — and (ii) define the fold as the REAL `β∘ψ` composition from the
banked atoms (`pivotChart` + `ShearReconcile`), never an opaque `Params M → Params M`. Honesty test
(two-sided, since (D) has NO `region_glue` consumer): **provable over the constructed atlas AND false on a
fake/generic atlas.** A D1 whose path/fold are opaque placeholders is D2 wearing D1's name — reject.

I withdraw my "D1-flat" phrasing: it was UNDER-TIED. My per-piece existential ("a pivot-choice sequence
whose induced ledger equals some `leaf ∈ leaves t`") anchored the fold to `leaves t`'s ledger but let the
PATH float free of `t`'s tree structure — the elder's `geometricLeafPaths t` correctly ties the fan-out to
`t`'s real edges/nodes, closing exactly the "D2 wearing D1's name" hole the honesty test guards.

**Confirmation the pinned D1 is provable by the banked machinery + carrier surface, and passes the honesty
test:**

- **(i) `geometricLeafPaths t` is buildable from `t`'s structure.** The per-node fan-out count is computable
  from `t`: `d_center` (Case 1) `= J₁·(M^{S+1}−J) + 1 = runLen·resCols + 1` reads the node's `resCols`
  (`StepData`) and its `1(2)` edge's `runLen` (`ChartSubst`); Case 2 `= (M(S)−J)(M^{S+1}−J)` reads node
  fields. So a `geometricLeafPaths` recursion (analog of `leafPaths`, `PivotCoverFold.lean:216`) fans out
  `d_center` pivot choices per node and recurses into the shared profile child (the fan-out charts collapse
  to one profile-child — chart-independent exponents, `cert-cov-rungs12:66`). This recursion is OWED (not yet
  banked) but is the direct analog of the existing `leafPaths`/`edgesLeafPaths` mutual recursion.
- **(ii) the fold is the REAL `β∘ψ`, non-opaque.** `β = q.symm ∘ pivotChart(pivot) ∘ q` (`PivotCover`,
  `β` = the banked atom); `ψ` = the Schur gauge (`ShearReconcile`, det 1, `.refl` on `ψ=id` edges);
  `localSub = ψ ∘ β` (carrier spec, tick 163). Non-opaque MODULO one owed carrier piece: the coordinate
  split `q : Params M ≃ₜ (Fin d → ℝ) × E` must be CONCRETELY constructed (the flat-coordinate embedding of
  the center via `divCoord`/`resCoord`), not left the existential it is in `node_pivotCover_of_atom`. Name
  that: D1's non-opacity bar requires a concrete `q`, which is the sub-gap-1 carrier work.
- **fails-on-fake.** A generic atlas whose `chartMap` is an arbitrary `Params M → Params M` cannot satisfy
  `chartMap = geometricLeafPaths-fold of banked β∘ψ atoms` — the fold equation pins `chartMap` to a specific
  composition, so a placeholder chart is refuted. The honesty test is met by the shape of the clause.

Anti-vacuity: the elder's two-sided test is the right instrument precisely because (D) has no `region_glue`
consumer (`RegionGlueAssembly.lean:106` discards it) — (A)+(B) forbid an arbitrary cover, and the
fails-on-fake half of (D) forbids an arbitrary FOLD-STRUCTURE, which is the fidelity (D) is there to insure.
**Counter-signed as pinned.** The encoding I will carry: `geometricLeafPaths t` (a new `leafPaths` analog) +
`chartMap = fold of banked β∘ψ` coherence; the one dependency to name is the concrete `q` (sub-gap-1 carrier).

Caveat linking to item 2: D1's "REAL `β∘ψ` fold" is the SAME object my item-2 single-`ψ` finding concerns,
but the two are separable — (D) is a definitional COHERENCE (`chartMap` = its geometric fold), which holds
regardless of gauge structure; the single-`ψ` insufficiency bites only in PROVING the cover (clause A), not
in stating (D). So the item-2 finding does not weaken the pinned D1.

---

## Item 5 — what coverage CANNOT (yet) prove from banked machinery + carrier surface

Named precisely. None is a type defect; each is substance the type correctly locates per-piece.

- **5a. A per-edge-`ψ` (or source-reparam) node cover lemma** — the highest-risk item, and the decorrelated
  Codex leg (item 2) indicates the current single-`ψ` `node_pivotCover_of_atom_sheared` is INSUFFICIENT for
  Case-1 nodes (the `u`-pivot has `ψ=id` and uniquely covers the `u`-axis; independent shears create gaps).
  Two fixes, neither banked: (ii-a) per-edge cover `⋃_e (ψ_e ∘ β_e)(D_e)` with per-edge open `V_e`
  (`ψ_e^{-1}(V_e) ⊆ β_e(D_e)`); (ii-b, preferred) source-reparameterization `β̃_e = β_e ∘ α_e^{-1}` keeping
  chart images fixed so the PURE `node_pivotCover_of_atom` applies. Adjudicate against tick-113's
  page-frame determination at the elder gate; if it stands, one route is owed grind for the coverage tide.
- **5b. The `pivotChart` Jacobian-det in Lean** — `|det D(pivotChart i)| = |u_i|^{d-1}` is docstring +
  battery only, not a Lean theorem. `LeafJacobian c`'s `Dβ` obligation (per-blow-up det, then path fold to
  `∏ monomial`) is owed.
- **5c. `LeafPullback c`** — the monomialization pullback identity (`frobSq∘chartMap = ∏u²·core`, squeezed).
  o5's analytic spine, not coverage's cover geometry; named as a per-piece dependency of clause (B).
- **5d. The a.e.-InjOn transport** — atom banked (`pivotChart_ae_injOn`); the fold/`q`-conjugation/spectator/
  `ψ`-post-composition transport to `c.chartMap` is owed (standard, gated on concrete `β`/`ψ`).
- **5e. The clause-(C) exponent bridge** — `∀ c ∈ atlas, ∀ k, c.divExp k ∈ terminalExponents t`. Provable
  because a geometric chart's exponents equal its ledger-quotient leaf's (the `d`-pivot charts collapse to
  one profile-child precisely because the exponent bump `J₁(M^{S+1}−J)` is chart-independent,
  `cert-cov-rungs12:66`), so `c.divExp k = (its `leaf ∈ leaves t`).divExp ∈ terminalExponents t`. The Lean
  bridge (geometric-fold `divExp` = quotient-leaf `divExp`) is a modest owed step.

---

## Consumer-side confirmation (not my lane, verified in passing)

The package's load-bearing §1 claim — the two proven glue lemmas are atlas-index-AGNOSTIC — holds:
`lintegral_leaves_cover_lt_top` (`RegionGlueAssembly.lean:51`) is `∀ (ls : List (LeafData M))`, a plain List
induction; `leaf_chart_image_lintegral_lt_top` (`RegionGluePerLeaf.lean:119`) is `∀ (l : LeafData M)`,
reading only per-leaf fields. Pointing either at `atlas` instead of `leaves t` needs zero adaptation.
`region_glue_of_chartBridge` (`RegionGlueAssembly.lean:84`) re-elaborates by destructuring `atlas` + routing
`hrat` through clause (C) instead of the `flatMap`-over-leaves membership — the `~12` LoC the package
forecasts. Confirms "no new sorry, no new axiom" on the consumer side.

---

## Elder-gate8 checks against my 3-Prop work

Two checks the elder asked me to run against items 1/5; both PASS.

- **Clause (C) is load-bearing — confirmed, and orthogonal to the 3 Props.** In the frozen type,
  `region_glue` routed `hrat` to the per-leaf thresholds via a `flatMap`-over-`leaves t` membership
  (`RegionGlueAssembly.lean:120-123`). The atlas is decoupled from `leaves t`, so that automatic routing is
  gone; clause (C) `∀ c ∈ atlas, (∀ k, c.divExp k ∈ terminalExponents t) ∧ (0 < c.resRank → c.resRank ∈
  terminalExponents t)` replaces it, feeding EXACTLY the two hypotheses of `leaf_chart_image_lintegral_lt_top`
  — `hdivExp : ∀ k, c' < c.divExp k / 2` and `hres : 0 < c.resRank → c' < c.resRank / 2`
  (`RegionGluePerLeaf.lean:127-128`). My 3-Prop work (item 1) is over each piece's `chartMap`/geometry and is
  orthogonal to (C)'s exponent routing; the two do not interact.
- **The type reads NOTHING off ledger leaves' `chartMap` — confirmed; my Props are all atlas-side.**
  `terminalExponents t` reads only `l.divExp` and `l.resRank` (`ResolutionTree.lean:284-286`), never
  `l.chartMap`; the exponent side is pure ledger. My item-1 Props are all over `c ∈ atlas` (the charts),
  never `leaves t`'s `chartMap`. So the split — ledger carries exponents, atlas carries charts — holds
  cleanly in my analysis (item 5e's exponent bridge is the one place they meet, and it reads only exponents).

## Decision asks — coverage position

1. **ADOPT the flat virtual-leaf atlas** (§2 of the package). Counter-signed.
2. **Provability of (B)+(C)+(D):** confirmed provable against the type, with the atlas realized as
   `leaves t_geo` and the item-5 grind named. **Elder/controller flag (decorrelated):** my Codex leg
   indicates tick-113/162's single-`ψ` resolution (i) FAILS in the natural model (the `u`-pivot obstruction);
   the fix is coverage's per-edge (5a) or source-reparam route, not a type change — but it should be
   adjudicated against the architect's page-frame determination before the coverage tide plans on single-`ψ`.
3. **Clause (D) — pinned by elder-gate8 (counter-signed as pinned):** `geometricLeafPaths t` (a new
   `leafPaths` analog referencing `t`'s edge/node structure) + `chartMap = fold of banked β∘ψ` coherence,
   two-sided honesty (provable-over-real, false-on-fake). Dependency named: a CONCRETE coordinate split `q`
   (sub-gap-1 carrier). Also ratify the item-2 realization `atlas = leaves t_geo` (proof-internal geometric
   tree, spine untouched).
4. **Verification gate on execution:** the elder-gate8 full batch (full `lake build` + AxCheck all watched
   roots + the (2,2,4) witness re-elaboration), not the single re-elaboration — noted, not re-litigated.

Nothing here blocks ratification of the TYPE. The type is sound, more faithful than the frozen type, and
coverage's content is provable against it. The single-`ψ` finding (5a) is a fold-machinery matter, not a type
matter: the decorrelated leg indicates `node_pivotCover_of_atom_sheared` is insufficient for Case-1 nodes, so
coverage plans for the per-edge or source-reparam route — carry this to the elder/controller alongside the
ratification, don't fold it into the type decision.
