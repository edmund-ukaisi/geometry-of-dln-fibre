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
