# Coupled corank≥2 faithful `hcover` — go/no-go + Lean-ready build template

**Seat:** pen-and-paper (WITNESS). **Date:** 2026-07-25. **Question:** does the coupled corank≥2
FAITHFUL MULTI-TERM `hcover` (L7, the measure-zero cover — `Resolution.hcover`,
`ProductResolution.lean:139`) close as detail-at-scale, or is there a hidden monument/obstruction?
**Method:** decorrelated exact-algebra (sympy 1.14, no floats) + one decorrelated Codex consult
(xhigh, verdict withheld). **Artefacts:** `/tmp/probe_hcover_obl1.py`, `/tmp/probe_hcover_obl2.py`,
`/tmp/probe_hcover_template.py`, `/tmp/probe_hcover_anypivot.py`; Codex `threads/hcover-obl/codex/`.

---

## VERDICT: **DETAIL-AT-SCALE** (GO), conditional on one provenance check

The coupled corank≥2 faithful `hcover` is **detail-at-scale** — a formaliser can build the general-`d`
`leafPath_compactCover` as a clean lemma library on top of the ALREADY-PROVEN abstract engine
(`LeafCoverTiling`). There is **no monument** in the cover. The coupling at corank≥2 changes only
*which* coordinates the per-node shear corrects — never the per-node polynomial DEGREE (fixed at 2)
and never the block-blow-up argmax routing that does the actual covering.

**The single residual risk (both I and Codex flag the SAME one):** the *fan-completeness of the actual
`buildTree` atlas* — does the recursion emit a chart for EVERY pivot `p ∈ S` at each node (the full
fan), or a pruned/col-pinned subset? This is a `buildTree`/`conOracle` **provenance** question, not a
cover-math question: I verified every off-canonical pivot yields a genuine valid Schur-clearing chart,
so the full fan *exists*; the only open point is whether the Lean tree *enumerates* it (or completes
it via the loss's row/col-permutation symmetry — the `#86(B)` column-orbit transport). A col-pinned
recursion without that transport fails by the exhibited `ε·e₂` escape.

Codex (decorrelated, verdict withheld): independently **detail-at-scale**, same single break-point
("confusing the synthetic full fan with the actual leaf atlas").

---

## The objects (verify, don't assume)

- `hcover` field (`Resolution`, `ProductResolution.lean:139`): `volume (U \ ⋃ c, (charts c).g '' (charts c).dom) = 0`.
  In the assembly (`MonumentAssembly.lean:73–85`) it is discharged by the STRONGER **empty escape**
  `ball 0 ρ ⊆ ⋃ c, gmap c '' dom c` (L7 `leafPath_compactCover`, `MonumentAtlas.lean:1850`, sorried),
  then `Set.diff_eq_empty.2 ▸ measure_empty`. So `hcover` = a genuine FULL cover, not merely a.e.
- The atlas chart `gmap c = pathMap ((steps c).map GeoStep.σ) = foldG (pathOf c)` — a composition,
  **blow-up OUTERMOST at each node**: `stepMap = blockBlowupMap center pivot ∘ edgeShear`
  (`MonumentAtlas.lean:332`, `edgeShear = blockShear shearφ` for case12/case2).
- The banked engine `LeafCoverTiling` (`covers_subset`, `closedBall_subset_iUnion_blockBlowup_image_radius`,
  `ball_subset_iUnion_blockBlowup_comp`, `exists_ball_subset_leafImages`) is **generic in the inflation
  `f : ℝ → ℝ` and in the per-node shear `σ`** — its `FanTree.node S hS σ child` already fans over ALL
  `p ∈ S` (`leafImages_node = ⋃ p ∈ S, (blockBlowupMap S p ∘ σ p) '' …`). It is NOT "for single-term
  shears" — that is only the instance `covers_coTree` (`Corank2GeoAtlas`), which feeds it `coShear`.

### The render's "single-term vs faithful multi-term" seam, resolved precisely

`Corank2GeoAtlas.coShear = blockShear coPhi` corrects the 4 `C₂₂` slots by the **Schur update only**
(`Δ = C₂₂ − c₂₁⊗c₁₂`, ONE product per slot). The FAITHFUL per-node shear additionally carries the
**Lemma-2 recoord** `C₂' = Q₂⁻¹ C₂` (the pivot-row combine), giving up to `C = block-size` products per
corrected slot. The seam is: does the box-containment survive the extra products?

**It does, and the reason is exact:** the recoord is `Q₂⁻¹ = I − N` with `N` the single pivot-row block,
so `N² = 0` and the recoord is DEGREE 1; each product (recoord entry × downstream entry, or Schur
`c₂₁·c₁₂`) is DEGREE 2. Multi-term = *more degree-2 products*, never a higher degree. See OBL-1.

---

## OBL-1 — per-edge box-containment for the FAITHFUL shear (`/tmp/probe_hcover_obl1.py`)

**CLAIM (exact-verified, corank 2, 3, (2,4), 4):** the faithful per-node coordinate change
`σ = blockShear φ`, where `φ` realises `Q₁-clear(col) ∘ Schur ∘ Q₂-recoord(row)`, satisfies:

| property | corank-2 | corank-3 | (2,4) | corank-4 |
|---|---|---|---|---|
| valid unipotent shear (`φ=0` on kept, reads only kept, write-set ⟂ read-set) | ✓ | ✓ | ✓ | ✓ |
| polynomial DEGREE of `φ` | **2** | **2** | **2** | **2** |
| exact inverse `v ↦ v − φ(v)` (two-sided) | ✓ | ✓ | ✓ | ✓ |
| max #products in a corrected slot `= C` | 2 | 3 | 4 | 4 |
| shear coefficients (`/tmp/…anypivot.py`) | all ±1 | all ±1 | all ±1 | all ±1 |

**Consequence (the box lemma):** on `|v|_∞ ≤ r`, `|φ(v)|_∞ ≤ C·r²` (C degree-2 products, unit coeffs),
so `|v − φ(v)|_∞ ≤ r + C·r²`. Hence, for `f(r) = r + C·r²`,
`closedBall 0 r ⊆ σ '' closedBall 0 (f r)` — the exact `Covers`-node clause. Boundary-tight
(`/tmp/…template.py`: `y − ab − cd` attains `r + 2r²` at `y=r, ab=cd=−r²`).
**Codex refinement (adopted):** "degree 2" alone is insufficient — one needs homogeneous quadraticity
PLUS a coefficient bound; here `∑|a| = C` (unit coeffs), and for ONE global `f` take
`C∗ = max C over all nodes/pivots ≤ D` (ambient dim). Finite.

**REUSE vs NEW:**
- REUSE verbatim: the entire `LeafCoverTiling` engine (`Covers`, `covers_subset`, the argmax atom,
  `ball_subset_iUnion_blockBlowup_comp`, `exists_ball_subset_leafImages`). Generic in `f` and `σ`.
- NEW (detail-at-scale, ~1 lemma): `faithfulShear_covers` — the box-containment for the FULL faithful
  `blockShear φ`, REPLACING `Corank2GeoAtlas.coShear_covers`. **Same proof shape** (`coShear_covers`,
  `Corank2GeoAtlas.lean:154–192`): `pi_norm_le_iff_of_nonneg`, per-corrected-coord `by_cases`,
  `abs_le` + `linarith`/`nlinarith`, closing via `blockShearInv_rightInverse`. Only change: more
  `by_cases` branches (one per corrected slot) and `f = r ↦ r + C·r²` (C ≥ 2). No new math.

---

## OBL-2 — fan-completeness / no omitted direction (`/tmp/probe_hcover_obl2.py`, `…anypivot.py`)

**CLAIM (exact-verified):**
1. The full-fan argmax lift covers EVERY coordinate direction (26/26 on the 3-coord model): for
   `x ∈ closedBall 0 R`, pick `p = argmax_{q∈S}|x_q|`, set `w_p = x_p`, `w_q = x_q/x_p` (|·|≤1),
   spectators pass; then `blockBlowupMap S p w = x`. This is an EXACT (empty-escape) cover, **corank
   independent** — a bijective shear cannot introduce an omitted direction. (This is exactly the
   banked `closedBall_subset_iUnion_blockBlowup_image_radius`, PROVEN.)
2. A fan PRUNED to a pivot subset MISSES a direction: forcing pivot `0` with `x_0 = 0` sends every
   center coord to `0`, so `(0,0,ε)` is unreachable — the `ε·e₂` escape (Codex's col-0 escape). The
   FULL fan picks pivot `2` and covers it.
3. **Every off-canonical pivot yields a VALID chart** (`…anypivot.py`): `Q₁·A·Q₂ = diag(1,Δ)` holds
   for ALL 9 pivots of a 3×3 block (Gaussian elimination on any unit pivot). So the full-fan charts all
   EXIST as genuine Schur-clearing resolution charts.

**Consequence:** fan-completeness is NOT "do off-canonical charts exist" (they do) — it is "does the
Lean atlas ENUMERATE them." Two sound routes, both detail-at-scale:
- (a) `buildTree`/`conOracle` branches on all pivots at each node (`FoldProduced` fan-completeness,
  `MonumentAtlas.lean:152`-region — the `hstep_block`/surjectivity provenance);
- (b) the loss `K = ‖∏C‖²_F` is invariant under row-perms(`C¹`) × col-perms(`Cᴸ`), so the full fan is
  the SYMMETRY ORBIT of the col-pinned ledger charts — the `#86(B)` column-orbit transport. The
  symmetry is genuine (permuting columns of `Cᴸ` permutes the terms of `Σ_ij`, leaving `K` fixed).

**REUSE vs NEW:**
- REUSE: the argmax atom is the covering mechanism, PROVEN, corank-independent.
- NEW (controller-owned provenance, NOT a frontier): the `buildTree`-realizes-full-fan discharge (a) OR
  the `#86(B)` σ-transport (b). ← **THIS is the one residual to verify (see risk).**

---

## Measure-zero exceptional (`/tmp/probe_hcover_template.py` §C)

`excep(gmap c) = ⋃_{steps} {u_pivot = 0}` (blow-up non-injective locus); the shear is GLOBALLY
injective (`|det| = 1`, `injective_blockShear`) so contributes nothing. Each `{coord = 0}` is a
coordinate hyperplane (volume 0); a finite union is volume 0. In the `Chart` record this is
`hexcep_null`, matching `Corank2GeoAtlas.coG_injOn` (InjOn off `{u_p = 0}`). Note (Codex): the cover
itself is EMPTY-escape (exact); the null set enters only through a.e.-INJECTIVITY (`hexcep_null`), a
DISTINCT field from `hcover`. REUSE `injOn_comp_diff` (`PathAtoms.lean:266`) + `centerCoordAligned_of_injective`.

---

## The Lean-ready template (corank-2 → general-`d`)

The general-`d` `leafPath_compactCover` reduces to instantiating the engine on `buildTree`:

1. **`faithfulShear_covers`** (NEW, ~1 lemma; template = `coShear_covers`): for the general edge shear
   `blockShear shearφ` (`edgeShear`, case12/case2), `closedBall 0 r ⊆ blockShear shearφ '' closedBall 0 (r + C·r²)`.
   Hypotheses it consumes (all already carried on `TreeEdge`): `shearφ` reads only kept coords + writes
   a disjoint set (the `keep`/`hkeep`/`hread` witnesses of `blockShearInv_rightInverse`), and the
   per-slot product count `≤ C`. Proof: `coShear_covers` verbatim with C-many `by_cases`.
2. **`atlas → FanTree` bridge** (NEW, structural bookkeeping): build `FanTree` from `buildTree` with
   node `= blockBlowupMap ed.center ed.pivot ∘ edgeShear ed`, leaf boxes `= dom c = closedBall 0 (f^[depth] 1)`;
   prove `thisTree.leafImages = ⋃ c, gmap c '' dom c` (unfold `leafImages` = `foldG`/`pathMap`;
   `foldG_eq_pathMap` already banked, `MonumentAtlas.lean:391`).
3. **`Covers f thisTree 1`** (NEW): structural induction discharged per-node by `faithfulShear_covers`
   (clause 1) + child IH at inflated radius (clause 2) + leaf box `≥ f^[depth] 1` (clause 3). Exactly
   the `covers_coTree` shape (`Corank2GeoAtlas.lean:282`), one global `f = r ↦ r + C∗·r²`.
4. **`covers_subset thisTree` + `Metric.ball_subset_closedBall`** (REUSE): gives `ball 0 ρ ⊆ leafImages`;
   compose with the bridge (2) for `leafPath_compactCover`.
5. **fan-completeness** (route (a) or (b) above) supplies that the `FanTree` node's `child p` is
   populated for every `p ∈ S` — the `FoldProduced` surjectivity/`hstep_block` provenance.

Concrete corank-2 acceptance witness to bank FIRST (mirror `covers_coTree`, C: 1→2): the depth-2,
`|S|=2` tree with the FAITHFUL shear (Schur + recoord) at both levels closes `Covers (r ↦ r + 2r²) · 1`;
leaf box `closedBall 0 21 = f^[2] 1` (verified `/tmp/…template.py` §B: `f(1)=3`, `f(3)=21`). This is
`covers_coTree` with `coShear → faithfulShear` and `closedBall 0 6 → closedBall 0 21`.

---

## Close

- **Firmest result:** the coupled faithful `hcover` is detail-at-scale. OBL-1 (box-containment) holds
  for the faithful multi-term shear at every corank/width — degree fixed at 2, unit coeffs, box
  `r + C·r²`; the banked engine is generic in `f`/`σ` and REUSES verbatim; the only new box lemma is
  `faithfulShear_covers` (= `coShear_covers` with more branches). OBL-2 (fan-completeness) is an exact
  argmax cover, corank-independent, and every off-canonical chart is a valid Schur-clearing chart.
- **Most likely to break it:** the actual `buildTree` atlas being pruned/col-pinned WITHOUT the
  `#86(B)` column-orbit transport (or without full-pivot enumeration) — then `ε·e₂` escapes. This is a
  `buildTree` provenance check, not a cover-math gap. NOT a monument.
- **Next check that settles the open part (Codex's, adopted):** at the first depth-2 `3×3` residual
  state, enumerate EVERY off-canonical pivot and verify symbolically that its faithful shear + state
  update + next center preserve the recursive residual identity AND appear as a `buildTree` child —
  this tests full-fan REALIZATION in the actual tree (not merely the one-step map).

---

# ADDENDUM (2026-07-25): buildTree-provenance check — route a-vs-b + the K-cover-transport

**Seat:** pen-and-paper, re-invoked for the ONE hcover residual (the general-`d` cover provenance).
**Artefacts:** `threads/hcover-obl/probe_K_cover_transport.py`, `…/probe_layered_transport.py`,
`…/probe_anypivot.py`; Codex `threads/hcover-obl/codex/Kcover-{prompt,answer}.md`.

## (a) Reconcile #119/#120 — what is NEW

#119 (`pnp-l7coupled`) + #120 (its Codex) settled: the MATH EXISTENCE (full-fan argmax cover is exact,
corank-independent — my OBL-2 re-confirms) AND flagged the col-pin escape is GENUINE ("BOUNDED for the
stated full-fan atlas; the currently col-pinned atlas has a genuine escape unless the promised outer
gauge charts are actually added"). They did NOT verify that the #86(B) transport carries the COVER (only
named it as the fix). **NEW here:** (b) which route the actual `buildTree` takes, and (c) whether the
transport carries the cover (not just the ideal), incl. the general-`d` layered refinement.

## (b) Route a-vs-b — SETTLED: route (b). Route (a) is REFUTED.

Read `EngineConstruction.lean` `conOracle`/`case2Decision`/`case1Decision`/`rolloverDecision`: the oracle
emits **one canonical geometric child per combinatorial step** — `case2Decision` → 1 child (the full-block
append), `case1Decision` → 2 children (the merge/split *types* of the SAME divisor blow-up), `rolloverDecision`
→ 1. **There is NO fan over the |S| geometric pivots.** `IsRealBranch` (`MonumentAtlas.lean:1068-9`) pins the
case12/case2 pivot column to `cleared`. So `buildTree` is canonical-pivot / col-pinned (route a refuted);
the full fan MUST come from the `#86(B)` symmetry transport (route b). gate2's read confirmed.

## (c) THE KEY — does the K-symmetry transport carry the COVER (not just the ideal)?

**Transport carries the cover — VERIFIED, no obstruction on this point.** The loss `K = ‖∏C‖²_F` symmetry
group `G` = ⟨row-perms(C¹), col-perms(Cᴸ), INTERNAL permutations `C^(s) ↦ G_{s-1}C^(s)G_s⁻¹` (`G_s` a perm
matrix)⟩. Exact (sympy):
- (c1) `K` invariant under all of `G` (all 36 row×col perms at 3×3; internal perms at L=2);
- (c2) every generator is a COORDINATE PERMUTATION of `w`-space (the flattened C-entries) ⟹ an ℓ²/ℓ∞
  ISOMETRY, so it maps `closedBall 0 ρ` onto itself — this is why it carries a set-CONTAINMENT, not merely
  the generator set;
- (c3) a col-perm of `A` induces a CLEAN col-perm of the depth-2 residual `Δ = C₂₂ − C₂₁·C₁₂` (transport
  acts cleanly at depth; likewise row); the internal perm reaches INTERMEDIATE-layer pivots (`probe_layered`);
- transported chart `σ∘g_canon`: image `= σ(im g_canon)` exactly; `|det D(σ∘g)| = |det Dg|` (σ perm, det ±1);
  a.e.-injective; `dom` compact; `⟨F∘σ∘g⟩ = ⟨F∘g⟩` — a GENUINE resolution `Chart`. **Value preserved:**
  orbit charts are isometric images ⟹ IDENTICAL `chartMin` ⟹ the `min`-over-charts value is unchanged
  (resolves the col-pinned-value vs full-fan-cover tension: full-fan cover, same value).
- Codex (decorrelated, verdict withheld) INDEPENDENTLY: transporting the cover is exact and legitimate
  ("ideal invariance alone would establish monomialization algebra, not any containment of target points").

**The orbit-covers-the-ball claim needs a full-history STABILIZER INDUCTION (Codex's sharpening, adopted).**
`⋃_σ σ(C_can) ⊇ ball` requires `∀ w ∈ ball, ∃ σ ∈ G, σ·w ∈ C_can`, and `C_can` constrains the argmax pivot
to be canonical at EVERY node — not just the root. Per-position transitivity gives the ROOT pivot only. The
certificate is: after canonicalizing the first `k` pivots, their STABILIZER (i) acts equivariantly on the
next residual/center, and (ii) acts as the full symmetric group on the next block (canonicalizes pivot `k+1`
without disturbing the prior `k`). **Base + first step VERIFIED exact:** at the depth-2 3×3 residual, the
stabilizer of pivot-1 (S₂×S₂ fixing its row/col) acts as the FULL fan of the deep 2×2 `Δ` (`probe_K_cover`);
the layered internal-perm equivariance is verified at L=2 (`probe_layered`). The general-depth induction is
the required cover certificate — detail-at-scale (a clean stabilizer/equivariance induction), NOT a monument.
- Tie handling: for the LITERAL empty-escape closedBall containment, ties (multiple argmax) use WEAK (≤)
  argmax — already in the banked atom `closedBall_subset_iUnion_blockBlowup_image_radius` (`Finset.exists_max_image`).

## VERDICT (provenance): **CONDITIONAL GO** — no obstruction; one named certificate

Route (b) is real; the K-symmetry transport CARRIES THE COVER (verified exact + Codex-agreed), and preserves
the value. The general-`d` cover provenance is **detail-at-scale, GO**, conditional on ONE named proof
obligation: the full-history stabilizer induction (base + first step verified). **No OBSTRUCTION flag** — the
transport does preserve the cover; the residual is a well-shaped induction, not a monument.

### Cover-transport template (the Lean lemmas the formaliser builds — general-`d` gate, NOT the corank-2 atom)
1. `lossSymm_isometry` — `G` generators are coord-perm isometries of `w`-space fixing `closedBall 0 ρ`
   (permutation matrices; `|det| = 1`).
2. `transport_chart` — for `σ` a `G`-generator, `σ∘(c.g)` inhabits `Chart` with the SAME `jac`/`bexp`/`dom`
   (`chartMin` invariant): `hjac` via `|det Dσ|=1`, `hideal` via `⟨F∘σ⟩=⟨F⟩` (perm of generators), `hg_inj`
   via σ injective, `dom ↦ σ '' dom` compact.
3. `orbitAtlas` — extend the canonical `buildTree` atlas to its `G`-orbit; `numCharts` scales by `|G|`
   (finite), value unchanged (min over identical `chartMin`s).
4. `orbit_covers` — the STABILIZER INDUCTION: `ball 0 ρ ⊆ ⋃_{σ∈G} σ(C_can) = ⋃ orbitAtlas charts`, by
   induction on node depth (stabilizer equivariance + stabilizer-transitivity per block; base = depth-2 3×3).
5. compose with the OBL-1/engine cover of `C_can` (the canonical cone) → the full `leafPath_compactCover`.

### Most likely to break it (Codex's + mine, concurring)
Replacing node-dependent permutations by one global σ: each pivot individually canonicalizable, but the
GLOBAL σ must canonicalize the WHOLE pivot history simultaneously. The stabilizer induction is exactly the
certificate that closes this; its per-node step is what a settling formalisation must discharge. Its base
case is verified here; a deeper (depth-3, e.g. (3,3,3,2,2)) instance check would further de-risk before the
general-`d` build commits.

---

# ADDENDUM 2 (2026-07-25): DEPTH-3 rollover check — the inductive step (+ a Codex precision fix)

**Seat:** pen-and-paper, re-invoked for the final de-risk: the stabilizer-induction STEP at a
layer-rollover where internal gauge perms COMPOUND (the spot the depth-2 base can't reach).
**Instance:** (3,3,3,2,2), `A = C⁴C³C²C¹`, internal indices d₁=3, d₂=3, d₃=2.
**Artefacts:** `threads/hcover-obl/probe_depth3_rollover.py`, `…/probe_hyp2_correction.py`;
Codex `…/codex/rollover-{prompt,answer}.md`.

## Result: inductive step is **GO** at the rollover — with hyp (ii) CORRECTED (Codex catch)

**Hyp (i) — equivariance-as-coord-perm at the rollover: HOLDS.** Exact (sympy) at (3,3,3,2,2):
- each internal gauge perm `G_s` (`C^(s) ↦ G_{s-1}C^(s)G_s⁻¹`, `G_s` a perm) is a coordinate permutation
  of `w`-space (isometry) AND a symmetry of `K` (verified s=1,2,3);
- the COMPOUNDING `G₁` (permutes `C²` columns, index d₁) and `G₂` (permutes `C²` rows, index d₂)
  **commute**, and their composite is a SINGLE coordinate permutation (isometry) + a symmetry of `K`.
  So compounding across the rollover CANNOT produce a non-isometry. (Codex: composition of coord-perms is
  a coord-perm regardless — commutativity isn't even required.)
- **Named lemma still owed (Codex, adopted):** beyond "compounding is a coord-perm", full equivariance
  needs the standard *residual-chart equivariance* — the stabilizer PRESERVES the residual block and the
  chart↔residual identification INTERTWINES its action. Standard for coordinate blow-ups when the earlier
  pivots are fixed; a named lemma the cover certificate must carry (not assumed here).

**Hyp (ii) — CORRECTED (Codex precision catch; my earlier statement was too strong and FALSE).**
The stabilizer of the fixed pivots does NOT act as "the full symmetric group on the block's entries"
(that was overstated: on a 2×3 residual the available group is `S₂×S₃`, order 12, NOT `S₆`, order 720).
What the induction actually NEEDS — and what HOLDS — is weaker: the stabilizer `S_{d_{s-1}-1} × S_{d_s}`
(row-perms × col-perms, the cleared position removed) is **transitive on the pivot POSITIONS `(row,col)`**
of the residual block, so it canonicalizes the ONE next pivot. Verified exact at every block shape
(2×3, 2×2, 3×3, 1×3, 2×1): position-transitivity `True`. The two index-constraints (d_{s-1} as the next
pivot's row, d_s as its col) are INDEPENDENT (distinct indices), so no rollover interference.

**Correction noted honestly:** ADDENDUM-1's hyp (ii) ("full symmetric group on the next block") was
too strong. The correct, sufficient, and true hypothesis is **position-transitivity of `S_row × S_col`**.
The verdict is unchanged (GO) because the induction only ever needs to place the ONE next pivot, for which
position-transitivity is exactly right. Codex's own conclusion: "If hypothesis (ii) is weakened to the
transitivity actually needed for choosing one pivot, and residual-chart equivariance is proved, then the
rollover step is GO."

## Net (final provenance de-risk)

The general-`d` cover's stabilizer induction is **GO at the rollover / compounding step**, no obstruction.
Two precise, standard, non-monument obligations for the `orbit_covers` certificate (updating template
lemma 4 in ADDENDUM-1):
- `orbit_covers` inducts on node depth with, at each node: (i) *residual-chart equivariance* (stabilizer
  preserves the residual block + intertwines the chart id — standard coordinate-blow-up lemma), and
  (ii) *position-transitivity* of `S_row × S_col` on the residual's `(row,col)` pivot positions (NOT full
  symmetric group). Both verified at the base (depth-2 3×3) AND the first rollover (depth-3 (3,3,3,2,2)).
- Everything else in the 5-lemma template (ADDENDUM-1) stands.

**No OBSTRUCTION flag** — equivariance does not fail at the rollover; the compounding is harmless. The
only change is the corrected (weaker, true) hyp (ii). General-`d` cover provenance = **CONDITIONAL GO**,
fully de-risked at the rollover; the certificate's exact hypotheses are now pinned.
