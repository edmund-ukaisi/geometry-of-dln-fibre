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

## Item 4 — clause (D): D1 vs D2

**Recommendation: D1's fidelity content, realized in a FLAT shape, with the fan-out amendment.**

D1 (each atlas chart is a genuine root→leaf geometric fold of per-node `β∘ψ` atoms) is the faithful clause:
it says the atlas is THE resolution's atlas, not an arbitrary finite good cover. It is **free** for coverage:
`chartBridge_imageCover_of_ownCovers` already requires the coherence `∀ p ∈ leafPaths id t_geo, p.1.chartMap
= p.2` (`PivotCoverFold.lean:225`) to run the item-2 cover — that coherence IS D1's content over `t_geo`. So
D1 costs coverage nothing beyond item 2. D2 (a chart is "some composition of banked atoms" + shares a
`leaves t` member's ledger) is strictly weaker fidelity for equal-or-greater stating cost, and buys nothing
region_glue needs (region_glue DISCARDS (D) — `RegionGlueAssembly.lean:106` `-`). So D1 dominates.

**The amendment (owned by coverage — the geometry):** D1 as written references "a root→leaf geometric path
in `t`", but the geometric fan-out is NOT in the quotient `t` (it lacks the `d_center` edges). D1 must
reference the geometric fan-out. Two realizations:

- **D1-literal:** `∃ t_geo, (t_geo quotients to t) ∧ atlas = leaves t_geo ∧ (∀ p ∈ leafPaths id t_geo, p.1.chartMap = p.2)`
  — sharpest fidelity, but exposes the proof-internal `t_geo` in the type.
- **D1-flat (recommended):** keep the atlas a flat List; state (D) as a per-piece existential — each `c`'s
  `chartMap` is a finite composition of `q`-conjugated `pivotChart` atoms and bounded unipotent gauges along
  a pivot-choice sequence whose induced ledger equals some `leaf ∈ leaves t`. Keeps `t_geo` internal to the
  coverage proof; carries D1's fold-fidelity without a second tree in the type.

Anti-vacuity: agreed with the package that it rests on (A)+(B) (a cover of the zero-locus by finite-integral
monomial-Jacobian charts is already forced); (D) is fidelity insurance the elder will want, and D1-content
is the faithful choice. **Recommend D1-flat.** The one point for the elder to pin: whether the fidelity
clause may reference `t_geo` (D1-literal, sharper) or must stay flat (D1-flat). I recommend flat.

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

## Decision asks — coverage position

1. **ADOPT the flat virtual-leaf atlas** (§2 of the package). Counter-signed.
2. **Provability of (B)+(C)+(D):** confirmed provable against the type, with the atlas realized as
   `leaves t_geo` and the item-5 grind named. **Elder/controller flag (decorrelated):** my Codex leg
   indicates tick-113/162's single-`ψ` resolution (i) FAILS in the natural model (the `u`-pivot obstruction);
   the fix is coverage's per-edge (5a) or source-reparam route, not a type change — but it should be
   adjudicated against the architect's page-frame determination before the coverage tide plans on single-`ψ`.
3. **Elder gate — pin clause (D):** recommend D1-flat (D1's fold-fidelity, no `t_geo` in the type). Also
   ratify that the atlas is realized as `leaves t_geo` (proof-internal geometric tree, spine untouched).
4. **Verification gate on execution:** unchanged from the package (`region_glue_of_chartBridge` green +
   clean-three; `chartBridge_buildTree` keeps its one sorry; AxCheck watch lines stable).

Nothing here blocks ratification of the TYPE. The type is sound, more faithful than the frozen type, and
coverage's content is provable against it. The single-`ψ` finding (5a) is a fold-machinery matter, not a type
matter: the decorrelated leg indicates `node_pivotCover_of_atom_sheared` is insufficient for Case-1 nodes, so
coverage plans for the per-edge or source-reparam route — carry this to the elder/controller alongside the
ratification, don't fold it into the type decision.
