# Decision package — the corrected `ChartBridge` type

*Seat: `architect-t05` (construction), drafted SOLO from the banked record (VM-restart #2 replaced the
two-seat negotiation: coverage-t07 dead, its joint-note half lost — tick 177). Grounded in the LIVE
tree at HEAD `0bfbeafc3`: every `file:line` below read directly, not recalled. This package is
decision-ready for the controller to carry to a fresh coverage counter-sign (acceptance = its 3-Prop
provability against the corrected type) and then the pre-staged elder gate (type change = skeleton
revision). DO NOT re-type Lean before ratification.*

Sources consumed: `EngineDefs.lean:75-86` (frozen `ChartBridge`), `ChartBridgeWiring.lean:59-84`
(`chartBridge_of_pieces`), `RegionGlueAssembly.lean:51-127` (`region_glue_of_chartBridge` +
`lintegral_leaves_cover_lt_top`), `RegionGluePerLeaf.lean:119` (`leaf_chart_image_lintegral_lt_top`),
`ResolutionTree.lean:128-168,284` (`LeafData`, `terminalExponents`), `CanonicalWitness224.lean:135`
(the witness), `AxCheck.lean:1277-1303` (watch lines); the R2 hunt-cert
(`threads/14-r2-probe/hunt-cert-atlas-closure.md`), `cert-single-psi`, journal tick 163, the
sub-gap-3 pin (tick 169 / RULINGS-t04 §1).

---

## 0. The finding, restated and verified against the code

The frozen `ChartBridge M t` (`EngineDefs.lean:75`) has image-cover clause

    U ⊆ ⋃ l ∈ ResolutionTree.leaves t, l.chartMap '' l.srcBox            (EngineDefs.lean:78)

— **one chart per LEDGER leaf.** The ledger tree is the symmetric QUOTIENT of the geometric fan-out
tree: one ledger leaf stands for its full per-node `d_center` pivot family (fork 13(o5); the profile
simulator is blind to geometric fan-out by design). The R2 decorrelated probe QUANTIFIED the gap:

- the FULL per-node `d_center` pivot family (ψ-composed, folded) image-covers the zero-locus with NO
  undershoot (Legs 1–4, arising `d_center` 1..12, both known mechanisms + corners);
- a single chart per ledger leaf structurally UNDERSHOOTS at every `d_center ≥ 3` node — a MAJORITY of
  deep nodes (173/363 at (3,3,4,2,3), 22/44, 19/39; `hunt-cert-atlas-closure.md` Leg 3b);
- route (ii) — recover the cover from ledger invariants over the profile tree — is REFUTED two-way,
  registered dead.

`chartBridge_of_pieces` (`ChartBridgeWiring.lean:64`) does NOT repair this: its `himg` antecedent is
the SAME single-chart-per-leaf union `U ⊆ ⋃ l ∈ leaves t, χ l '' l.srcBox`. A piecewise chartMap
gluing the family into one map per ledger leaf fails the per-leaf Props: `LeafPullback`/`LeafJacobian`
read the leaf record's ONE `divCoord`/`divExp` (`EngineDefs.lean:43-66`), but different pivots blow up
different coordinates ⇒ different `divCoord`. So the fix must carry a FAMILY of chart records, each
with its own geometry.

This is the 5th obligation-statement instance and the first at TYPE level (an already-merged hole type
with a PROVEN consumer). It is a statement-soundness fix, not a math undershoot — the cover math is
sound (R2), only the shape is wrong.

---

## 1. What the PROVEN consumers actually consume (the design constraint)

`region_glue_of_chartBridge` (`RegionGlueAssembly.lean:84`) is the proven consumer. Its ACTUAL use of
`ChartBridge` (read verbatim at `:106-127`):

    obtain ⟨⟨U, hUopen, hUlocus, hUcover⟩, hleaf, -⟩ := hbridge     -- coherence DISCARDED (the `-`)

then it needs exactly three things:

1. **`hUcover : U ⊆ ⋃ (cover family) chartMap '' srcBox`** — an open nbhd of the zero-locus inside the
   cover-family image union.
2. **per-piece finiteness** via `leaf_chart_image_lintegral_lt_top` (`RegionGluePerLeaf.lean:119`) —
   which is stated over an ARBITRARY `LeafData l`, reading ONLY per-leaf fields (`l.srcBox`,
   `l.divCoord`, `l.resCoord`, `l.chartMap`, `l.divExp`, `l.resRank`, `LeafPullback l`,
   `LeafJacobian l`) + the threshold `∀ k, c' < l.divExp k / 2` and `0 < l.resRank → c' < l.resRank/2`.
3. **finiteness of the union** via `lintegral_leaves_cover_lt_top` (`RegionGlueAssembly.lean:51`) —
   stated over an ARBITRARY `List (LeafData M)`, a plain `List` induction on `lintegral_union_le`.

The threshold hypotheses in (2) are routed from `hrat : ∀ e ∈ terminalExponents t, c' < e/2` by
proving `l.divExp k ∈ terminalExponents t` (a `flatMap` membership, `:120-123`).

**KEY: the two load-bearing PROVEN glue lemmas are atlas-index-AGNOSTIC.** They consume a finite
`List (LeafData M)` of pieces, each with finite integral, whose union covers. They do NOT read
`leaves t` — `region_glue` passes `leaves t` as the list ONLY because that is where the charts
currently live. Point either lemma at any `List (LeafData M)` and it applies unchanged. Verified by
reading the signatures (`:51`, `:119`).

---

## 2. (i) The corrected type — RECOMMENDATION: the flat virtual-leaf atlas

Carry an explicit atlas of geometric chart pieces, each a full `LeafData` (a "virtual leaf"),
decoupled from `leaves t`:

    def ChartBridge (M) (t : ResolutionTree M) : Prop :=
      ∃ atlas : List (LeafData M),
        -- (A) image cover over the ATLAS pieces (each carries its OWN chartMap/srcBox/divCoord)
        (∃ U, IsOpen U ∧
            {A | A ∈ paramsBoxM M 1 ∧ frobSq (prod M A) = 0} ⊆ U ∧
            U ⊆ ⋃ c ∈ atlas, c.chartMap '' c.srcBox) ∧
        -- (B) the SAME 8 per-leaf props, now per atlas piece
        (∀ c ∈ atlas,
            MeasurableSet c.srcBox ∧
            (∃ R, 0 < R ∧ c.srcBox ⊆ paramsEquivFlat M ⁻¹' cubeBox (flatDim M) R) ∧
            Function.Injective c.divCoord ∧ Function.Injective c.resCoord ∧
            Disjoint (range c.divCoord) (range c.resCoord) ∧
            (∃ N, volume N = 0 ∧ InjOn c.chartMap (c.srcBox \ N)) ∧
            LeafPullback c ∧ LeafJacobian c) ∧
        -- (C) exponent agreement: each piece's exponents are terminal exponents of t (routes hrat)
        (∀ c ∈ atlas, (∀ k, c.divExp k ∈ terminalExponents t) ∧
                      (0 < c.resRank → c.resRank ∈ terminalExponents t)) ∧
        -- (D) fidelity coherence (NOT consumed by region_glue): each piece is a genuine
        --     geometric-path fold of t's fan-out (see §5); shape owned by coverage
        (fidelityCoherence M t atlas)

**Why `List (LeafData M)`, flat and decoupled from `leaves t`:**

- `lintegral_leaves_cover_lt_top` applies to `atlas` with ZERO adaptation (it is already `∀ List
  (LeafData M)`); `region_glue` closes (A) with `lintegral_mono_set (hεU.trans hUcover)` then
  `lintegral_leaves_cover_lt_top c' atlas Hleaf` — the exact current shape with `atlas` for `leaves t`.
- `leaf_chart_image_lintegral_lt_top` applies to each piece with ZERO adaptation (already `∀
  LeafData`).
- Each piece has its OWN `divCoord`/`divExp`/`chartMap`/`srcBox` — different pivots get different
  `divCoord`, dissolving the piecewise-gluing failure the frozen type would force.
- (C) replaces the `flatMap`-over-leaves membership; it hands `region_glue` the per-piece threshold
  directly (`c' < c.divExp k / 2` from `c.divExp k ∈ terminalExponents t`).

This IS the geometric-path-indexed atlas, represented FLAT so the proven `List`-induction glue is
reused verbatim.

**Equivalent alternative (grouped-by-leaf), noted not recommended.** `atlas : LeafData M → List
(LeafData M)` (per ledger leaf → its geometric family), image-cover a DOUBLE union `⋃ l ∈ leaves t, ⋃
c ∈ family l, …`. Same mathematics; `region_glue` reuses the proven glue by flattening
`(leaves t).flatMap family` inside its proof. It buys a per-ledger-leaf coherence grouping at the cost
of a `flatMap` step + double iteration in `region_glue` and in coverage's proof. Recommend the flat
form: it matches coverage's natural construction (a geometric-fan-out traversal EMITS a flat list),
and keeps `region_glue`'s re-elaboration to the destructure only.

**Rejected alternative (fold-form over tuples).** Keep `leaves t` indexing + `(chartMap, srcBox,
divCoord, resCoord)` tuples with `LeafPullbackWith`/`LeafJacobianWith`-style fold-form Props. REJECTED:
it forces re-stating BOTH proven glue lemmas (`leaf_chart_image_lintegral_lt_top` and
`lintegral_leaves_cover_lt_top`) in the tuple fold-form — the exact re-elaboration the flat-`LeafData`
form avoids by making each piece a real `LeafData`.

---

## 3. (ii) Full re-elaboration cost map

| Site | `file:decl` | Change | ~LoC |
|---|---|---|---|
| `ChartBridge` def | `EngineDefs.lean:75` | REWRITE: 3 clauses → 4 over `atlas` (A–D above) | ~20 |
| `chartBridge_of_pieces` | `ChartBridgeWiring.lean:59` | REWRITE: build the new `ChartBridge` from atlas pieces. The `χ` fold-form parametrization likely DROPS — atlas pieces carry real charts, so plain `LeafPullback c`/`LeafJacobian c` suffice (no placeholder to route around) | ~40 |
| `LeafPullbackWith`/`LeafJacobianWith` + `leafPullback_eq_with`/`leafJacobian_eq_with` | `ChartBridgeWiring.lean:28,36,47,51` | LIKELY DELETE (the `χ`-parametrization existed only to avoid the placeholder `l.chartMap`; unneeded once pieces carry real charts) | −25 |
| `region_glue_of_chartBridge` | `RegionGlueAssembly.lean:84` | destructure `atlas` (+ clause C) instead of `leaves t`; route `hrat` through (C); the `Hleaf`/final assembly reuse `leaf_chart_image_lintegral_lt_top` + `lintegral_leaves_cover_lt_top` untouched | ~12 |
| `lintegral_leaves_cover_lt_top` | `RegionGlueAssembly.lean:51` | **UNCHANGED** | 0 |
| `leaf_chart_image_lintegral_lt_top` | `RegionGluePerLeaf.lean:119` | **UNCHANGED** | 0 |
| `RegionGlueGlobalize` (scaling bridge), `exists_small_paramsBox_subset_open`, `prod_zero_glue` | — | **UNCHANGED** (atlas-agnostic) | 0 |
| `chartBridge_buildTree` hole | `EngineObligations.lean:52` | `sorry` re-elaborates vs new def; STATEMENT text `ChartBridge M (buildTree …)` unchanged | ~0 |
| `o5_realization` / `o5_core` / `minAdm_le_terminalExponents` / assembly | `EngineObligations` / `EngineConstruction` | **UNCHANGED** (never touch `ChartBridge`) | 0 |
| `CanonicalResolution` | `EngineDefs.lean:226` | **UNCHANGED** (`ChartBridge M t` is an opaque conjunct) | 0 |
| `canonicalResolution224` witness | `CanonicalWitness224.lean:135` | ALREADY `by sorry` (off-cone); the `sorry` re-elaborates vs new def | ~0 |
| `AxCheck` watch lines | `AxCheck.lean:1277-1303` | **UNCHANGED** — every watched name (`region_glue_of_chartBridge`, `region_glue`, `chartBridge_buildTree`, `canonicalResolution224`, `monomialization_terminates`) is stable | 0 |

**Net:** the change concentrates in `ChartBridge` def + `chartBridge_of_pieces` + the destructure of
`region_glue_of_chartBridge`. The two proven glue lemmas, `RegionGlueGlobalize`, the whole
chart-independent spine, and all AxCheck names are untouched. The single verification gate:
`region_glue_of_chartBridge` must re-elaborate GREEN and stay clean-three (`#print axioms`
`AxCheck.lean:1285`).

**No new sorry, no new axiom.** The hole count is unchanged (the discharge target `chartBridge_buildTree`
keeps its sorry; the (2,2,4) witness keeps its off-cone sorry). The change makes the hole TRUE-as-stated
(the frozen type is unfillable per §0), which is the point.

---

## 4. (iii) pp.15–21 fidelity — the paper's atlas IS the geometric-family atlas

- Each blow-up node carries a `d_center` pivot family of max-modulus charts covering its coordinate
  center: Case-1 `d_center = J₁(M^{S+1}−J)+1` (pp.15–18), Case-2 `d_center = (M(S)−J)(M^{S+1}−J)`
  (p.20) (`page-pin-centers.md`, `PivotCover.pivotChart`). Each pivot chart is Aoyagi's monomialized-
  integrand blow-up `β`; the per-node gauge `ψ` (det 1) is the Schur/shear reconciliation
  (`cert-single-psi`).
- The atlas that covers the zero-locus is the union over ALL geometric charts = ALL
  (ledger-leaf × root→leaf pivot-choice path). The `LeafData.chartMap` in the frozen type is the
  symmetric-quotient PROJECTION, blind to the fan-out (fork 13(o5)). So the FAITHFUL atlas is the flat
  list of geometric charts — exactly the corrected type. The R2 probe verified this atlas image-covers
  with no undershoot and that the single-chart-per-ledger-leaf undershoots (route ii dead). The p.22
  t̃=0 read-off is a per-chart property, preserved unchanged (each piece's `divExp`/`divProfile`
  enumerate that chart's t̃=0 divisors).

Conclusion: the corrected type is MORE faithful to pp.15–21 than the frozen type, not merely a
technical repair. The frozen type asserted a false collapse (one chart per inductive statement); the
paper's construction fans out.

---

## 5. (iv) The 4-part per-edge carrier surface + per-NODE family data

**Per-edge surface (mine; `ChartSubst` already IS it — `ResolutionTree.lean:65`):** `localSub`,
`runLen`, `mergeIdx`, `jacDivCount`, `jacPow`. The 4-part spec (journal tick 163):
1. pivot flat-coordinate index + exponent;
2. `β = q.symm ∘ pivotChart(pivot) ∘ q` (coverage's atom; `|det Dβ| = ∏|u|^{divExp−1}`);
3. `ψ : Params M ≃ₜ Params M`, `|det Dψ| = 1` (Schur gauge; `.refl` on ledger-only case-1(1) merge
   edges) — proof-carrying;
4. `localSub_e = ψ_e ∘ β_e`; `leaf.chartMap = fold of localSubs`.

**Per-NODE family data (sub-gap-3 pin — attaches to NODES as data, NEVER tree edges):** the `d_center`
pivot family is per-NODE ChartBridge-layer data. In the corrected type it is REALIZED as the `atlas`:
each atlas piece = one root→leaf geometric path = one choice of pivot at each node along the path,
times the ledger leaf. The ledger tree stays the symmetric quotient (spine untouched: the geometric
fan-out lives ENTIRELY in the atlas `List`, not in `Edge`s / `StepRel`). The `d_center` counts the
decisions already compute internally (`J₁(M^{S+1}−J)+1` / `(M(S)−J)(M^{S+1}−J)`) let coverage
enumerate the family.

**Ownership (fork B):**
- Construction (me): the ledger tree + the per-edge SLOTS (real `ChartSubst.localSub`/`jacPow`) +
  sub-gap-1 (injective `divCoord`/`resCoord` + `numDiv ≤ flatDim`, battery-verified true — see
  `battery/numdiv-le-flatdim.py`, and the report below).
- Coverage: the `atlas` construction (the `d_center` family enumeration, `β`/`ψ`, the geometric-path
  fold producing the flat `List (LeafData M)`) + the 3 Props (B) over it + clause (C) + the fidelity
  coherence (D).

**The one open sub-decision inside the recommendation — clause (D)'s shape.** `region_glue` DISCARDS
coherence, so (D) is a FIDELITY clause (the atlas is THE resolution's charts, not an arbitrary cover),
not a `region_glue` prerequisite. Candidates for coverage + elder to pin at counter-sign:
- (D1) a geometric-`leafPaths` analog: `∀ c ∈ atlas, ∃ (a root→leaf geometric path in t), c.chartMap
  = fold of the path's per-node (β∘ψ) charts` — the direct fan-out generalization of the frozen
  `leafPaths id` coherence.
- (D2) looser: each `c` shares some `leaves t` member's ledger content (already implied by clause C via
  `terminalExponents`) + `c.chartMap` is a composition of banked `pivotChart`/gauge atoms.
Anti-vacuity does NOT rest on (D): clauses (A)+(B) already forbid an arbitrary atlas (it cannot cover
the zero-locus with finite-integral charts unless it is a genuine resolution atlas). (D) is fidelity
insurance the elder gate will want; I recommend (D1) and defer its exact Lean shape to coverage (it
owns the geometry).

---

## 6. Decision asks (for counter-sign + elder gate)

1. **ADOPT the flat virtual-leaf atlas** `∃ atlas : List (LeafData M), (A)∧(B)∧(C)∧(D)` (§2), over the
   grouped and fold-form alternatives (both weighed, §2).
2. **Coverage counter-sign:** confirm its 3 Props (B) + clause (C) + coherence (D) are provable over
   the constructed atlas (the `d_center` fan-out fold). Acceptance = provability.
3. **Elder gate:** ratify the type change (skeleton revision) + pin clause (D)'s shape (D1 vs D2).
4. **Verification gate on execution:** `region_glue_of_chartBridge` re-elaborates GREEN + `#print
   axioms` stays clean-three; `chartBridge_buildTree` keeps exactly its one sorry; full `lake build
   DLNFibre` green; AxCheck watch lines unchanged.

No spine risk, no new hole, no `Edge`/`StepRel` change (the fan-out is atlas data, per the sub-gap-3
pin). The change is confined to the chart lane and makes the merged hole type TRUE-as-stated.
