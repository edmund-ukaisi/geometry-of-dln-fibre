# Execution plan — the coupled-B build (Aoyagi Cases-1/2, ideal-level)

**Frame.** The render (`theory/aoyagi-2023-reproduction/ideal-route-full-render.md`, Phase 1–3 complete)
established the close-out is bounded-and-buildable: reproduce Aoyagi's Cases-1/2 `(S,J)` recursion,
ideal-level, → `⟨∏C⟩=⟨diag(b)⟩` normal crossing → the value `rlct = ½·cCodim`. All cruxes resolved
general (L-A block-elim; L-B maintenance via the `b`-chain; cases exhaustive/terminating; totality-
over-claim dropped; Theorem 4 landed+wired; `Mval=cCodim` landed). The remaining content is the LEAN
reproduction — combinatorial proof-engineering, not open math.

**Three-level ownership (operator, 2026-07-24).**

---

## LEVEL 1 — process / execution (CONTROLLER owns, fully)

**The build sequence (dependency order; each a census-drop milestone):**
1. **Foundation atoms** — the clean block-elimination ideal-identity (L-A / `N1` core), general corank,
   over the local ring; avoid the retired chart `Engine/`. + the `b`-chain divisibility maintenance lemma.
2. **The `(S,J)` recursion skeleton** — `buildTree`-driven (combinatorial tree LANDED); the invariant
   `⟨∏C⟩=⟨diag(b)·(E_J⊕D_J)·∏_{s>S}C⟩` as the carried datum (drop the false totality — partial order +
   `b`-chain).
3. **Cases 1 / 1(1) / 1(2) / 2** — the per-step blow-up + block-elim (`N1`), maintenance ideal equality.
4. **The exponent ledger** — `M_{s,k}` accumulation = `Mval` (Object C/D bridge, LANDED); the read-off.
5. **`N2` (path-fold)** — folds `N1` along the tree to the per-chart `PrincipalInv` (the CURRENT L5
   output type — interface-invisible re-point of L1→hideal→Chart).
6. **Value re-point** — `2·rlct = cCodim` via the resolution; Theorem 4 (landed) + Object B CoV +
   Object D. Wire `via_engine` off the geometric `exists_coreResolution` onto the new construction.
7. **Retire the geometric fold** — banners "superseded by N1/N2" (NOT "false"); quarantine
   FoldStepInvAt/WALL/KILL/#95/#98/couplingClear/CanonicalPivots/CapDescent.
8. **Green + `#print axioms`** on `aoyagi_learning_coefficient_via_engine` = `[propext, Classical.choice,
   Quot.sound]` (no DLN cite). Delete `cited_aoyagi_lower_ax`.

**Integration discipline (controller):** single-writer on the aggregator + the summit module; gate every
builder "done" on a re-derived green + `#print axioms` (not the builder's word); census-DROP not commit
count; branch guard on every commit; one PR at close behind operator merge-gate.

---

## LEVEL 2 — math (CONTROLLER owns render + understanding; DECORRELATED helpers, advisory)

I own `ideal-route-full-render.md` and the math understanding. Three decorrelated seats (they inform +
validate; they do NOT own the math):
- **Review-only pen-and-paper (`rev-render`):** decorrelated audit of the render — L-A, the L-B
  maintenance (`b`-chain absorption), KC-2 (cases exhaustive/terminating; totality droppable), Theorem 4
  use, the value chain. REVIEW-ONLY: finds gaps/over-claims/soundness issues; does NOT render or propose
  new math. Fires its own Codex. This is the calibrated-sensor on my owned render BEFORE we build on it.
- **Code-frontiers scout (`scout-code`):** maps the current code terrain the build stands on — the
  `Chart`/`Resolution` framework, Objects A/B/C/D, `buildTree`, the RLCT foundation
  (`localAdmissibleExponents`/`rlctAt`/`wrlctAt`), the block-elim candidates (`SchurRankZero`,
  `FibreNormalForm`), `Mval=cCodim`, and the retired geometric fold (what to reuse vs retire). Output:
  a reuse/retire map.
- **Long-range code-projection scout (`scout-proj`):** projects the build to Lean structure — how the
  `(S,J)` recursion + Cases 1/2 + `N1`/`N2` map to modules; the dependency graph; the integration path
  (N2→L5-consumer re-point, aggregator wire, retire sequence); the module skeleton + statement-delta
  targets. Output: the code-level build blueprint (feeds the Level-3 briefs).

---

## LEVEL 3 — Lean (OUTSOURCED to builders via VERY DETAILED briefs)

The only outsourced level. Builders (`lean-formaliser`) get a self-contained brief per unit:
- **target statement** (from the render, at the render's generality) + **what it supersedes**;
- **the math argument** (from the render — the builder transcribes, does not re-derive);
- **module placement + dependencies** (from `scout-proj`);
- **Lean idioms/gotchas** (from `lean/CLAUDE.md` — the dependent-dim `mul_three_reassoc`, the ℤ-matrix
  `decide`+cast, the opaque-width `have`+`exact`, `decide +kernel` not `native_decide`);
- **the gate** (green via `scripts/lb`; `#print axioms`; `scripts/sorries`/cordon) + the **tripwire**
  (statement-fidelity: if the render's statement can't close as-stated, STOP and report — do NOT weaken).
Builders build; controller re-derives the gate + integrates. Builders spawn ON the operator's build-go.

---

## PREP PHASE (before the build-go — THIS phase)
- [ ] Execution plan (this doc).
- [ ] Operational center: spawn + charge `rev-render`, `scout-code`, `scout-proj`.
- [ ] House-cleaning: branch triage (delete dead seat branches); task board; fossil-quarantine plan
      (RouteM/Engine off-cone; the literal-name Skeleton root is operator-gated — surface, don't act);
      render-doc cleanup pass (fold the trail into a clean front-to-back statement, superseded-marked).
- [ ] Charter/compass/heartbeat-memo update to the new mode (elder authors charter/compass; controller
      commits; controller owns the heartbeat memo).
- [ ] Checkpoint operator: prep complete, build ready to fire → await the explicit build-go.

---

## SHARPENED BLUEPRINT (scout-code + scout-proj, controller-cross-checked 2026-07-24)

**The seam is razor-thin:** `via_engine`'s only `sorryAx` is the bare `sorry` at `LearningCoefficient:311`
(`∃ res : Resolution (coreGen d e) 0, AtlasRealizesExponents d res`). Replace it → clean-three, delete
`cited_aoyagi_lower_ax`.

**Module plan (Core never imports DLN):**
- NEW Core: `SchurClearing.lean` (N1 atom = L-A: `⟨A⟩=⟨diag(A₁,Δ)⟩` any corank, RegionRepresents both ways
  + the b-chain cross-term absorption, Phase-3a) — built FRESH (no reusable atom), reusing `SchurRankZero`
  + Object A + `BlockBlowup`/`BlockDivision` + `PrincipalInv` vocab. `ChainRecursion.lean` (abstract
  `RepInv` + one-step + path-fold to terminal `PrincipalInv`).
- NEW DLN: `ChainFold.lean` (N1 edge-wrapper `chartStep_idealIdentity` dispatching case11/12/2/rollover
  onto the Core atom; N2 `leafChart_idealIdentity` = the path-fold). `ViaEngineSummit.lean` (relocated
  summit — resolves the import cycle below).

**The interface-invisible joint (load-bearing, scout-proj §0/§3):** N2 must emit EXACTLY the type of
`leaf_stepInv_of_path`'s 3rd conjunct — the per-chart `PrincipalInv (coreGen d e) (gmap c) (monoOf bexp)
q r (region c)`. Then L1 (`principalInv_regionRepresents`, LANDED, UNTOUCHED) → the two RegionRepresents →
L6 → Chart → Resolution → value, all invisible below L1. The driver `exists_atlasRealizesExponents`
changes only its one L5 line (swap `leaf_stepInv_of_path` for `leaf_atlas_of_path` [carrier only] +
`leafChart_idealIdentity` [N2]).

**THE IMPORT CYCLE + re-point (scout-proj §4):** `exists_coreResolution`+`via_engine` are UPSTREAM of the
driver, which imports `LearningCoefficient` — so `:311` can't be discharged in place. FIX: relocate
`exists_coreResolution` + `via_engine` into `ViaEngineSummit.lean` DOWNSTREAM of the driver (body =
`exists_coreResolution_via_monument`'s, sorry-free once the leaves land); delete the sorried upstream
copies. `via_engine` body unchanged, only its module moves.

**THE ACTUAL BUILD SCOPE (bigger than N1/N2 — scout-proj RISK B, the correction to my render):** a
sorry-free `via_engine` needs BOTH halves: (i) the IDEAL identity = N1/N2 (new, the coupled-B crux,
render-resolved general); AND (ii) the GEOMETRIC/COMBINATORIAL carrier = `leaf_atlas_of_path` (split from
`leaf_stepInv_of_path`, carrier only) + L6 (`leafPath_chartGeometry`, Jacobian fold) + L7
(`leafPath_compactCover`, cover — the engine is on the KEPT `-L7cover` branch, needs wiring) + L8
(`leafPath_realizesExponents`, Object-D-bridged). L6/L7/L8 are `@[blueprint]`-sorried TODAY and on the
critical path — bounded (geometric/combinatorial, no new analytic monument) but REAL work N1/N2 does not
touch. Build scope = N1 + N2 + the carrier-split + L6 + L7 + L8 + the re-point + retire.

**RISK A (cast tax — #1 hotspot):** recurs at EVERY `(S,J)` step. MITIGATION (load-bearing): N1 STRICTLY
ideal-level — carry `foldRep` as a `Fin nR → germ` family, NEVER form `diag(b)·(E⊕D)·P` as `Matrix.mul`;
casts only via `finCongr` at the index/equiv level. The prototype's ~5-cycle bound holds ONLY if
ideal-level. GO/NO-GO de-risk (scout-proj): a 1-step corank-≥2 N1 ideal-level prototype (e.g. `(3,3,4)`
S=2 case-1(1) merge) to remeasure the tax + confirm the b-chain absorption discharges with finCongr-only
casts. **This prototype is a candidate first build unit (on the operator's go).**

**Retire (on-branch fold, all OFF the summit cone — scout-code):** `MonumentAtlas` (13-16 sorries incl.
the WALL), `MonumentAssembly`, `GeometricAtlasD12`, the Wire cluster (`CanonShear`/`LastLayerWire`/
`MergeBoostSplit`/`Case*Wire`/`CaseStepAssembly`/`MultiAffine*`/`PivotPreservation`/`L5FoldSpec`/
`LeafChartWire`/`LeafGeometryWire`). `CapDescent`/`SourceClearedResid`/`LeafCoverTiling`/`couplingClear`/
`CanonicalPivots` are ALREADY ABSENT from this branch. Fossils (RouteM*/Skeleton/retired Engine/*):
quarantine per the fossil plan — RouteM is AxCheck-imported for the aoyagi-full roots (separate
deliverable), Skeleton is operator-gated (#94); do NOT bulk-delete.

**Retained value stack (do not touch):** Objects A/B/C/D, `Chart`/`Resolution`, L1, `terminal_bezout`,
`coreReduction`/`lossDLN_zero_homogeneous`/`exists_flatten`, the adapter + `AtlasRealizesExponents`,
`buildTree`. All landed sorry-free.
