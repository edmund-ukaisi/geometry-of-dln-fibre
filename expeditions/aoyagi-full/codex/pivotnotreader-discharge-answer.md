   Updating ssh://git@github.com/AI-Safety-Institute/aisi-inspect-tools (HEAD)
    Updated ssh://git@github.com/AI-Safety-Institute/aisi-inspect-tools (fa7351f6ef4773f536ee4975c3251325eb9c44df)
Reading prompt from stdin...
OpenAI Codex v0.142.4
--------
workdir: /home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/agent-a9bb11c22680d93d4
model: gpt-5.5
provider: openai-aisi
approval: untrusted
sandbox: read-only
reasoning effort: high
reasoning summaries: none
session id: 019f151a-46fe-7c42-9235-7257f6ae4f61
--------
user
# Design review: discharging PivotNotReader cleanly (Lean 4 + Mathlib, DLNFibre harness)

## Context
A (2,2,2) interior-determinant headline `interiorDet_headline_222` is COMPLETE + axiom-clean except it rests on one open hypothesis:

    PivotNotReader : structPivot M222 hN_M222 ∉ readerSet

where:
- `structPivot M hN : Fin (routeMAmbient M) := ⟨0, hN⟩`  — a GLOBALLY-SHARED def (RouteMFlatStructV.lean), the LITERAL flat-slot 0. It is the radial coordinate of the achiever chart `phiFlatLiveR1` (its rate is `(x structPivot)^2 · U`), and is consumed pervasively downstream: the RLCT measure-transfer contract `RouteMInteriorContract` integrates over `{x | x (structPivot) = 0}` (the radial axis), and many rate/diff lemmas read `x (structPivot)`.
- `readerSet : Finset (Fin (routeMAmbient M222))` = `{readerSlotK, readerSlotX, readerSlotN, readerSlotW0, readerSlotW1}`, the 5 reader slots, each defined as `(chartIdxEquiv M222 …).symm ⟨tag⟩` where `chartIdxEquiv` is a NONCOMPUTATIONAL bijection (built via `Fintype.equivFin`). It does NOT kernel-reduce: `decide` gets stuck.
- `PivotNotReader` is used to build a `Fin 8 ≃ Fin 8` reindex equiv (`slotEquiv`/`colEquivT`) from the 8 slots `[a,b,n,w0,w1,p,lf0,lf1]` being PAIRWISE DISTINCT. The pivot `p = structPivot` must be ≠ each of the 5 readers. That equiv computes `|det DB| = |aRead|²` (the engine). `PivotNotReader` is the ONLY thing that ties slot-0 to "not a reader".

## Verified facts (I checked the actual code)
1. NO proof does `rfl`/`decide` on `structPivot = ⟨0,_⟩` to extract the literal 0. It's used purely as an abstract `Fin N` element everywhere. So changing its VALUE is type-safe (no literal-0 dependence).
2. The headline wiring `interiorDet_headline_of_BData` / `radialComp_abs_det` uses ONLY `hp_mem : structPivot ∈ active` + `hcard : active.card = minAdm` — NOT slot-0-ness, NOT PivotNotReader.
3. The leaf slots `lf0, lf1` are ALREADY chosen from `univ \ forbiddenSlots` where `forbiddenSlots = insert structPivot {5 readers}` (card ≤ 6, complement ≥ 2), so `lf_i ∉ readerSet` and `lf_i ≠ structPivot` hold BY MEMBERSHIP — no opaque comparison. This is the existing discharge PATTERN.
4. A pen-and-paper verdict says `PivotNotReader` for `structPivot = ⟨0,_⟩` is FRAGILE/possibly FALSE (slot-0 has no constructed relation to the chartIdxEquiv readers; "prove it semantically" = route (i) is a dead end). Verdict = route (ii): "re-point the pivot to a chosen non-reader slot."

## The tension I want adjudicated
`structPivot` is GLOBALLY shared (RouteMFlatStructV, consumed by the chart `phiFlatLiveR1`, the rate lemmas, AND the RLCT measure-transfer `RouteMInteriorContract` which integrates over `{x (structPivot) = 0}`). "Re-point structPivot to a non-reader slot" is NOT obviously local — it touches the whole downstream cone, and worse, the general `structPivot M hN` has NO `readerSet M` to choose its complement from (readerSet is M222-specific). So "choose pivot from `univ \ readerSet`" doesn't directly generalize ∀M the way `structPivot := ⟨0,_⟩` does.

## QUESTION
What is the CLEANEST discharge of `PivotNotReader`, given the above? Rank these and flag traps:

(A) Change `structPivot M hN := ⟨0,hN⟩` globally to a `Classical.choice` of `univ \ (reader-image)` — but reader-image needs `chartIdxEquiv M` ∀M, and structPivot is in a low-level shared file that may not import the chart machinery. Is this a layering violation / import cycle risk?

(B) Keep `structPivot := ⟨0,_⟩` global, but make the (2,2,2) BData use a DIFFERENT pivot `pRad := Classical.choice (univ \ readerSet)` LOCAL to RouteMBData222, and prove the headline for THAT pivot — then bridge `phiFlatLiveR1 … (radial read at structPivot)` to the pРad-radial chart. Does this require re-deriving the rate `routeMCore_phiFlatLiveR1` for a non-structPivot radial? (The rate is `(x structPivot)^2·U` — hard-wired.)

(C) Prove `PivotNotReader` is TRUE after all via a CARDINALITY/counting argument: `readerSet.card + minAdm M ≤ flatDim M` is TIGHT at M222 (5 + 3 = 8). Does tightness HELP prove `structPivot ∉ readerSet`? (I suspect NOT — a counting bound says the complement is nonempty, but doesn't pin slot-0 into it. Confirm this is a dead end, or show the counting argument that DOES force `⟨0,_⟩ ∉ readerSet`.)

(D) Some other route — e.g. make `phiFlatLiveR1` PARAMETRIC in the radial slot `p₀` (currently hard-wired to `structPivot`), so the chart, rate, and headline all take `p₀` as an argument, and instantiate `p₀ := a chosen non-reader slot`. Most faithful but most invasive — is it the right ∀M move?

Give me: the ranked recommendation, the import-layering check for (A), whether (C) is truly a dead end, and which route GENERALIZES to ∀M cleanly. Be concrete about Lean mechanics.

codex
I’ll check the local Lean layout before giving the recommendation, especially where `structPivot`, reader slots, and the BData/headline contracts live. That should make the import and generalization advice concrete instead of speculative.
exec
/bin/bash -lc "sed -n '1,220p' CLAUDE.md" in /home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/agent-a9bb11c22680d93d4
 succeeded in 0ms:
# geometry-of-dln-fibre

AI-assisted math-research + Lean-formalisation harness for **digesting and formalising** the paper
*"Geometry of the fibers of the multiplication map of deep linear neural networks"* (Simon Pepin
Lehalleur & Richárd Rimányi, 2024; `paper-sources/lehalleur-rimanyi-2024-geometry-of-dln-fibre/`).
Orientation is in [`README.md`](README.md); this file is the disposition and the working discipline.
The process harness (disposition + policies + roles + skills + the markdown→Lean pipeline) is ported
from the `ai-research-assistant` harness and is **domain-agnostic** — see [`TEMPLATE.md`](TEMPLATE.md)
to instantiate it for another paper.

## Disposition

The work here is research. Not coding, not ticking off a support ticket, not shipping a product. 
The stance: 
- careful, conscientious, objective as a scientist.
- meticulous in calculation as Euler, bold as Grothendieck. 
- methodical as Sherlock Holmes. Observe before theorising. Distinguish data from interpretation. 
- update like a Bayesian; do not collapse to the mode. 


- **Resist the move-fast-and-ship-it instinct.** Stackable, solid progress is the goal; the trap is
  *visible* progress raced ahead of it — a clean doc or confident headline that travels far while leaving
  holes behind. When you reach for a confident headline, that is the moment to look for the confound. Each
  layer should be solid and hole-free before the next stands on it.
- **Fill the layer — completion is your strength.** *The sea rises inexorably, but not in spikes*
  ([`docs/policies/bedrock.md`](docs/policies/bedrock.md)): within a boundary already staked, close the holes
  — the generality a statement promised, the cases it already claims, fidelity to the definition and the
  underlying spirit it invokes — rather than defer them. Such hardening is high-value, and it is where your
  **comparative advantage** lies: your bottleneck is scoping, taste, and direction, not the patient completion
  of well-scoped work — so do not treat that completion capacity, which is *abundant*, as if it were *scarce*.
  **Just do it!** Don't file it as a "chore" (an *unprobed* difficulty claim, not a defer). Surface to move the
  *boundary* — but an **earned** taste-judgment that a gap is the *right* extension is itself direction:
  **Just Do It** if within reach, else **roadmap** it; only a *bare, unargued* extension waits for the operator.
- **Name results for what they are.** A result's name and statement denote exactly what is proven — no more;
  reaching for an impressive name (or "done") is the visible-progress instinct in disguise. Separate Proved /
  Assumed / Cited / Deferred. See [`docs/policies/precision.md`](docs/policies/precision.md). (Here the
  recurring trap: a `rlct_…`-named result that in fact proves only a *codimension* — the `rlct = ½·codim`
  reading needs the cited Aoyagi equality.)
- **Build to bedrock.** A sorry-free build defeats *technical* slop; it never defeats *conceptual* slop —
  "technically correct but subtly wrong, not The Way." **Bedrock is the rock the rising sea rises over**: build
  the theory so the next result can stand on it without re-opening it. Where short feedback loops fail, **beauty
  is the instrument** — a vacuous, mis-scoped, or overclaiming result is *ugly*, and the ugliness is
  information. The **controller holds this taste and judges against it**; a green build is necessary, never
  sufficient. See [`docs/policies/bedrock.md`](docs/policies/bedrock.md).
- **Caveats live next to claims, not in footnotes.** An assumed hypothesis or a cited interface goes in the
  same paragraph as any claim that depends on it.
- **Write to figure out the truth, not to persuade.** Concise and fact-based.
- **Elementary, precisely.** Build explanations up from precise but simple well-chunked objects, established locally in the
  document. "Elementary" does not mean imprecise or dumbed-down or toy analogies: every step stays
  mathematically precise. Introduce the objects you use before you use them; prefer a chain of small exact
  statements over one dense one. Resist over-naming things to do chunking. Reach for an analogy only when it is exact and load-bearing. See
  [`docs/policies/writing-style.md`](docs/policies/writing-style.md).

## Writing and communication discipline (object-level focus)
In writing or in communication, focus on object-level. Resist meta-level pull. 
Remove authorial self-reassurance: `honestly`, `fundamentally`, `this is the whole point`, `this is loadbearing`, `of course`, `simply`, `just`, and selling phrasing.
The full list and the review function that enforces it are in [`docs/policies/review.md`](docs/policies/review.md).

## How research runs here

- **Expeditions** ([`docs/policies/expedition.md`](docs/policies/expedition.md)) are the unit: a central
  question, a controller delegating to thread teammates (explore / formalisation / infra), reviewers, and a
  synthesis at close. Run on the Agent Teams substrate (`CLAUDE_CODE_EXPERIMENTAL_AGENT_TEAMS=1`); launch with
  cwd = this repo root.
- **Pipeline: markdown → Lean.** Theory develops in markdown (`theory/`, expedition notes). A stable claim is
  formalised in Lean (`lean/`, library `DLNFibre`). The reader-facing digest/expositions live in
  `docs/expositions/`.
  - *Scholium* is a **viewer** (renders these markdown docs with KaTeX + callouts), not an editor; write to its
    conventions in [`docs/policies/scholium-writing-format.md`](docs/policies/scholium-writing-format.md). The
    recurring trap: display math `$$…$$` needs a **blank line before and after**, fences on their own lines
    (indented inside `!!!`/`???` callouts) — packed against text it falls through to markdown and the `_`
    subscripts render as emphasis. A second trap: **fenced code does not render inside a callout** — use an
    indented code block (8-space indent) there; top-level fenced code is fine.
- **Claims** carry kill-conditions; new claims are stress-tested, established/cited results verified against
  source ([`docs/policies/claims.md`](docs/policies/claims.md)).
- **Codex** is the independent second model for strategy and review
  ([`docs/policies/codex-consultation.md`](docs/policies/codex-consultation.md)).

## Team structure

Roles are documented under [`.agent-team/roles/`](.agent-team/roles/):
- `controller` — this lead session: meta-planning, delegation, integration.
- `scout` — explore / reconnaissance threads: map the terrain (Mathlib, the paper, possibility spaces), compute / derive / claims.
- `pen-and-paper` — a specialised `scout`: design-space math adjudicating a truth-value (`witness` / `obstruction` seats), exact algebra, decorrelated Codex; hands a certificate to the formaliser. No Lean.
- `formaliser` — formalisation (tide) threads.
- `reviewer` — controller-spawned independent audit (soundness / fidelity).
- `hardener` — independent principles / taste reviewer (precision, bedrock).

If dispatched into a role, read its role file and agent definition first.

## Branch discipline

- **One remote: `origin = git@github.com:edmund-ukaisi/geometry-of-dln-fibre.git`.** All work lives here.
- **`dev` is the integration branch.** Feature and expedition branches branch off `dev` and PR back into
  `dev`. `master` is the **release** branch — promoted from `dev` deliberately by the operator, never pushed
  to directly.
- Use a **feature branch** for any non-trivial unit of work; you can push here; don't commit to `dev` or `master` directly. One
  expedition runs on one branch (`expedition/<slug>`); PR at close behind signal-and-wait.
- **Pushing feature/expedition branches to `origin` is pre-authorized** (operator standing instruction,
  2026-06-12) — push freely to bank and share work. **Opening/merging PRs and the `dev → master` promotion
  remain operator-gated** (signal-and-wait); the operator performs those. Always confirm the push target is
  `origin`, never a non-`origin` remote.

## Memory

Persistent context lives **in-repo**: this file, the policies in `docs/policies/`, the expedition docs
(`synthesis.md` / statement cards / `thread.md`), `ROADMAP.md`, and `lean/CLAUDE.md`. Save conventions and
decisions there.

**Do NOT write to global Claude memory (`~/.claude/**/memory/`).** It pollutes other workspaces and is
invisible to collaborators reading the repo. This binds the controller **and every teammate** — the harness
may prompt you to save a memory there; do not. If a teammate writes one, the controller deletes it and
re-homes the content in-repo. (Agent-Teams *runtime* state under `~/.claude/teams/` and `~/.claude/tasks/` is
fine — that's the substrate, not persistent context.)

## The destination, plainly

We want, in honest Lean, the paper's results about the **fibres of matrix multiplication** for deep linear
networks:

- the space $\operatorname{Rep}_{\underline d}$ of composable matrix tuples, the multiplication map
  $\operatorname{mult}$, the zero-product / rank-$r$ loci, and the fibres $\operatorname{mult}^{-1}(B)$;
- via the **type-A quiver** translation (orbits ↔ Kostant partitions ↔ rank patterns, Gabriel, orbit-closure
  order, the `Ext` codimension): the codimension $C$ and the number $\theta$ of top-dimensional components,
  in the paper's three forms (Poincaré series, a quadratic integer program, an explicit formula), and the
  surprising **permutation invariance** of $(C,\theta)$;
- the payoff: the real log-canonical threshold of the square-Frobenius loss is $C/2$ — DLNs are "mildly
  singular". The geometric codimension is the new content; the Aoyagi `rlct = ½·codim` **equality** is
  **Cited** (Watanabe's universal `rlct ≤ ½·codim` + Aoyagi's exact DLN computation — the formal
  `RlctInterface.cited_aoyagi_dln` is the equality, which the payoff needs).

The reusable **engine** (everything before "the payoff") is network-free and lives in `DLNFibre.Core`; the
DLN/RLCT **application** lives in `DLNFibre.DLN`. See [`ROADMAP.md`](ROADMAP.md) for the formalisation ladder.

## Pointers

- [`README.md`](README.md) — orientation, how to launch an expedition, Lean build.
- [`ROADMAP.md`](ROADMAP.md) — the result-map + the Core/DLN formalisation-target ladder.
- [`docs/policies/`](docs/policies/) — expedition, claims, review, precision, bedrock, codex-consultation, statement-cards, writing-style (+ the reader-facing exposition trio).
- [`docs/expositions/`](docs/expositions/) — the curated reader-facing digest (starts with `paper-digest/high-level-overview.md`).
- [`.claude/skills/`](.claude/skills/) — lean-formalisation, local-codex-consult.
- [`lean/CLAUDE.md`](lean/CLAUDE.md) — Lean build + Mathlib conventions; the Core/DLN split.
- [`theory/`](theory/) — markdown theory workspace.
- [`TEMPLATE.md`](TEMPLATE.md) — how to instantiate this harness for a new paper.

exec
/bin/bash -lc 'pwd && rg -n "def structPivot|structPivot|readerSet|PivotNotReader|phiFlatLiveR1|RouteMInteriorContract|interiorDet_headline" -S .' in /home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/agent-a9bb11c22680d93d4
exec
/bin/bash -lc "rg --files . | sed -n '1,240p'" in /home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/agent-a9bb11c22680d93d4
 succeeded in 0ms:
./TEMPLATE.md
./README.md
./paper-sources/aoyagi-relu/aoyagi-2025-relu-with-softmax.pdf
./paper-sources/aoyagi-relu/aoyagi-2025-relu.pdf
./paper-sources/aoyagi-2023-consideration-of-learning-efficiency-of-dln/entropy-15-03714.pdf
./paper-sources/aoyagi-2023-consideration-of-learning-efficiency-of-dln/aoyagi-2023-neural-networks-preprint.pdf
./paper-sources/lehalleur-rimanyi-2024-geometry-of-dln-fibre/2411.19920.pdf
./paper-sources/lehalleur-rimanyi-2024-geometry-of-dln-fibre/source/main.bib
./paper-sources/lehalleur-rimanyi-2024-geometry-of-dln-fibre/source/main.bbl
./paper-sources/lehalleur-rimanyi-2024-geometry-of-dln-fibre/source/main.tex
./threads/31-L6.4-orbit-closure/statement-card.md
./lean/lean-toolchain
./lean/DLNFibre.lean
./lean/lake-manifest.json
./lean/lakefile.toml
./threads/31-L6.4-orbit-closure/codex/piece2-dimcast-prompt.md
./threads/31-L6.4-orbit-closure/codex/crux-body-answer.md
./threads/31-L6.4-orbit-closure/codex/crux-body-prompt.md
./threads/31-L6.4-orbit-closure/codex/piece2-arch-answer.md
./threads/31-L6.4-orbit-closure/codex/piece2-dimcast-answer.md
./threads/31-L6.4-orbit-closure/codex/piece2-arch-prompt.md
./AGENTS.md
./CLAUDE.md
./theory/setup.md
./expeditions/2026-06-22-explicit-ctheta/threads.md
./lean/CLAUDE.md
./theory/README.md
./expeditions/2026-06-22-explicit-ctheta/synthesis.md
./theory/aoyagi-2023-reproduction/verify-repro-s4s5.md
./theory/aoyagi-2023-reproduction/verify-r1-shortcut.md
./theory/aoyagi-2023-reproduction/verify-r1-diagb-4422.md
./theory/aoyagi-2023-reproduction/verify-r1-135-cover-design.md
./theory/aoyagi-2023-reproduction/verify-r1-route-adjudication.md
./theory/aoyagi-2023-reproduction/aoyagi-2023-extracted-text.txt
./theory/aoyagi-2023-reproduction/verify-l2-gauge-architecture.md
./theory/aoyagi-2023-reproduction/verify-r1-diagb-334.md
./theory/aoyagi-2023-reproduction/verify-def3-underspec.md
./theory/aoyagi-2023-reproduction/aoyagi-2023-worked.tex
./theory/aoyagi-2023-reproduction/verify-r1-light-recursion.md
./theory/aoyagi-2023-reproduction/verify-arith-groundtruth.md
./ROADMAP.md
./lean/DLNFibre/Core/DeterminantalChart.lean
./lean/DLNFibre/Core/ChartGaugeTower.lean
./lean/DLNFibre/Core/ChartPhiFibCoord.lean
./lean/DLNFibre/Core/CTheta.lean
./lean/DLNFibre/Core/AffineDomainDimension.lean
./lean/DLNFibre/Core/CThetaQIPConverse.lean
./lean/DLNFibre/Core/EndpointNormalization.lean
./lean/DLNFibre/Core/ChartPhiSubstitution.lean
./lean/DLNFibre/Core/ChartEvalGaugeCommute.lean
./lean/DLNFibre/Core/OrbitCodim.lean
./threads/b-mvpoly-zeroset/codex/architecture-prompt.md
./threads/b-mvpoly-zeroset/codex/architecture-answer.md
./expeditions/aoyagi-full/codex/pivotnotreader-discharge-prompt.md
./lean/DLNFibre/Core/Matrix/RankNormalForm.lean
./expeditions/2026-06-22-explicit-ctheta/threads/01-arbitrary-ctheta/statement-card.md
./expeditions/2026-06-18-c-theta/threads.md
./expeditions/aoyagi-full/codex/pivotnotreader-discharge-answer.md
./docs/policies/review.md
./docs/policies/writing-style-graduate-math-textbook.md
./docs/policies/README.md
./docs/policies/bedrock.md
./lean/DLNFibre/Core/Matrix/RankNormalFormTriangular.lean
./lean/DLNFibre/Core/ChartLocalizedCoordinates.lean
./docs/policies/expedition.md
./docs/policies/statement-cards.md
./docs/policies/writing-style.md
./docs/policies/claims.md
./docs/policies/draft-policy-semantic-auditing.md
./docs/policies/codex-consultation.md
./docs/policies/writing-style-agent-exposition.md
./docs/policies/precision.md
./docs/policies/lean-build-workflow.md
./docs/policies/scholium-writing-format.md
./docs/expositions/core-machinery/03-gabriels-theorem-interval-modules-and-the-barcode.md
./docs/expositions/core-machinery/05-the-classification-orbits-and-kostant-partitions.md
./docs/expositions/core-machinery/permutation-invariance-of-C-and-theta.md
./docs/expositions/core-machinery/the-type-a-quiver-classification.data.yaml
./docs/expositions/core-machinery/04-rank-patterns-and-kostant-partitions.md
./expeditions/2026-06-18-c-theta/synthesis.md
./docs/expositions/core-machinery/01-tuples-and-the-multiplication-map.md
./lean/DLNFibre/Core/QSeriesShift.lean
./lean/DLNFibre/Core/QSeriesOrth.lean
./lean/DLNFibre/Core/ChartEvalRealize.lean
./lean/DLNFibre/Core/CCodimZeroStrict.lean
./lean/DLNFibre/Core/DeepChartRing.lean
./lean/DLNFibre/Core/FibreCodim.lean
./lean/DLNFibre/Core/ChartSigmaGaugeBridge.lean
./lean/DLNFibre/Core/ChartSweepWiring.lean
./lean/DLNFibre/Core/ClosureBridge.lean
./lean/DLNFibre/Core/BaseChange.lean
./lean/DLNFibre/Core/EndBaseChangeSweep.lean
./docs/expositions/core-machinery/README.md
./docs/expositions/core-machinery/01-tuples-and-the-multiplication-map.data.yaml
./docs/expositions/core-machinery/04-rank-patterns-and-kostant-partitions.data.yaml
./docs/expositions/core-machinery/the-type-a-quiver-classification.md
./docs/expositions/core-machinery/02-quiver-representations-and-the-base-change-group.md
./docs/expositions/core-machinery/02-quiver-representations-and-the-base-change-group.data.yaml
./lean/DLNFibre/Core/SmoothPointRegular.lean
./lean/DLNFibre/Core/FibreDimFibrationProbe.lean
./docs/expositions/paper-digest/high-level-overview.md
./lean/DLNFibre/Core/OrbitImageDim.lean
./lean/DLNFibre/Core/FibreCodimFinal.lean
./expeditions/2026-06-22-explicit-ctheta/threads/01-arbitrary-ctheta/codex/fidelity-answer.md
./docs/expositions/paper-digest/high-level-overview.data.yaml
./lean/DLNFibre/Core/AffineNoetherRank.lean
./expeditions/2026-06-22-explicit-ctheta/threads/01-arbitrary-ctheta/codex/fidelity-prompt.md
./lean/DLNFibre/Core/IntegralDimension.lean
./lean/DLNFibre/Core/AffineLocalizationNoDrop.lean
./lean/DLNFibre/Core/BoxMoveGeneral.lean
./lean/DLNFibre/Core/ChartSigmaAwayZero.lean
./lean/DLNFibre/Core/Barcode.lean
./lean/DLNFibre/Core/SigmaComponents.lean
./lean/DLNFibre/Core/CThetaQIP.lean
./lean/DLNFibre/Core/GenericTuple.lean
./lean/DLNFibre/Core/CThetaArbitrary.lean
./lean/DLNFibre/Core/MatrixKaehler.lean
./lean/DLNFibre/Core/DeterminantalStratumDim.lean
./lean/DLNFibre/Core/FibreDimFibration.lean
./lean/DLNFibre/Core/FlatTrivialProductProbe.lean
./lean/DLNFibre/Core/ChartRetraction.lean
./lean/DLNFibre/Core/OrbitLinearCodim.lean
./lean/DLNFibre/Core/SchurChartIff.lean
./lean/DLNFibre/Core/ChartGaugeNormalize.lean
./lean/DLNFibre/Core/GraphIdealHeight.lean
./lean/DLNFibre/Core/ChartEvalGauge.lean
./lean/DLNFibre/Core/SchurSideNoDrop.lean
./lean/DLNFibre/Core/ChartLocalizedAlgEquiv.lean
./lean/DLNFibre/Core/FibreReducedTrivialization.lean
./lean/DLNFibre/Core/ChartSigmaEvalGauge.lean
./lean/DLNFibre/Core/VarietyDimPolyExtension.lean
./lean/DLNFibre/Core/PolynomialCurveLimit.lean
./lean/DLNFibre/Core/ChartSchurConnect.lean
./lean/DLNFibre/Core/CCodimZeroMono.lean
./lean/DLNFibre/Core/SigmaStratification.lean
./lean/DLNFibre/Core/CThetaThetaBridge.lean
./lean/DLNFibre/Core/FibreJacobian.lean
./lean/DLNFibre/Core/QSeriesFivegon.lean
./lean/DLNFibre/Core/BoxMoveDegeneration.lean
./lean/DLNFibre/Core/Basic.lean
./lean/DLNFibre/Core/ChartSection.lean
./lean/DLNFibre/Core/LocalizationKrullDim.lean
./lean/DLNFibre/Core/BoxMoveGeneration.lean
./lean/DLNFibre/Core/CThetaValue.lean
./lean/DLNFibre/Core/MvPolynomialKerAeval.lean
./lean/DLNFibre/Core/JacobianTrdeg.lean
./lean/DLNFibre/Core/DeterminantalChartRing.lean
./lean/DLNFibre/Core/ChartPointEval.lean
./lean/DLNFibre/Core/RadicalCatenary.lean
./lean/DLNFibre/Core/Submult.lean
./lean/DLNFibre/Core/ChartRoundTripH1.lean
./lean/DLNFibre/Core/ChartEvalLemma.lean
./lean/DLNFibre/Core/CThetaExplicit.lean
./lean/DLNFibre/Core/OrbitDifferential.lean
./lean/DLNFibre/Core/VarietyDimRadical.lean
./lean/DLNFibre/Core/ThetaComponentCount.lean
./lean/DLNFibre/Core/RouteCAssembly.lean
./lean/DLNFibre/Core/ChartFlatnessProbe.lean
./lean/DLNFibre/Core/NoetherMonicPositioning.lean
./lean/DLNFibre/Core/OrbitTangentCotangent.lean
./lean/DLNFibre/Core/MultDifferential.lean
./lean/DLNFibre/Core/CThetaPermInvariance.lean
./lean/DLNFibre/Core/OrbitSmooth.lean
./lean/DLNFibre/Core/QSeries.lean
./lean/DLNFibre/Core/SigmaCodim.lean
./lean/DLNFibre/Core/ChartPhiLoc.lean
./lean/DLNFibre/Core/RankNormalFormDim.lean
./lean/DLNFibre/Core/OrbitDifferentialRank.lean
./lean/DLNFibre/Core/CascadeRealizable.lean
./lean/DLNFibre/Core/CThetaGeometric.lean
./lean/DLNFibre/Core/FibreCodimMinPrimes.lean
./lean/DLNFibre/Core/MultComorphism.lean
./lean/DLNFibre/Core/PrincipalOpenComorphism.lean
./lean/DLNFibre/Core/DeformationExt.lean
./lean/DLNFibre/Core/PolynomialDimension.lean
./lean/DLNFibre/Core/GenericFreeness.lean
./lean/DLNFibre/Core/SmoothLocalRelativeDimension.lean
./lean/DLNFibre/Core/FibreNormalForm.lean
./lean/DLNFibre/Core/OrbitKostant.lean
./lean/DLNFibre/Core/ChartPsiSubstitution.lean
./lean/DLNFibre/Core/OrbitClosure.lean
./lean/DLNFibre/Core/VoigtDischarge.lean
./expeditions/2026-06-20-aoyagi-full/discuss-at-close.md
./expeditions/2026-06-20-aoyagi-full/threads.md
./expeditions/2026-06-20-aoyagi-full/synthesis.md
./lean/DLNFibre/Core/ChartPsiDsigUnit.lean
./lean/DLNFibre/Core/Gabriel.lean
./lean/DLNFibre/Core/OrbitVariety.lean
./lean/DLNFibre/Core/CascadeAchiever.lean
./lean/DLNFibre/Core/ChartSigmaEvalRealize.lean
./lean/DLNFibre/Core/DeterminantalBasePresentation.lean
./lean/DLNFibre/Core/QSeriesThm55.lean
./lean/DLNFibre/Core/CascadeRank.lean
./lean/DLNFibre/Core/NullstellensatzCodim.lean
./lean/DLNFibre/Core/QSeriesExtraction.lean
./lean/DLNFibre/Core/VarietyDimBaseChange.lean
./lean/DLNFibre/Core/RankLocusClosed.lean
./lean/DLNFibre/Core/DeterminantalBaseElimination.lean
./lean/DLNFibre/Core/ChartLocalizedPolyDim.lean
./expeditions/2026-06-22-explicit-ctheta/threads/01-arbitrary-ctheta/thread.md
./lean/DLNFibre/Core/RankPattern.lean
./lean/DLNFibre/Core/ChartPsiDescent.lean
./lean/DLNFibre/Core/CotangentJacobian.lean
./lean/DLNFibre/Core/OrbitPullbackDim.lean
./lean/DLNFibre/Core/CCodimCornerMono.lean
./lean/DLNFibre/Core/QSeriesPeel.lean
./lean/DLNFibre/Core/Orbit.lean
./expeditions/2026-06-22-explicit-ctheta/loop-prompt.md
./lean/DLNFibre/Core/SchurGauge.lean
./lean/DLNFibre/Core/ChartPsiReconstruct.lean
./lean/DLNFibre/Core/QSeriesDurfee.lean
./lean/DLNFibre/Core/SourceNoDrop.lean
./lean/DLNFibre/Core/ChartRoundTrip.lean
./lean/DLNFibre/Core/ChartSigmaEval.lean
./lean/DLNFibre/Core/ChartBijection.lean
./lean/DLNFibre/Core/CThetaDropM.lean
./lean/DLNFibre/Core/FlatQuasiFiniteHeight.lean
./lean/DLNFibre/Core/FibreHeightDirect.lean
./lean/DLNFibre/Core/IntervalModule.lean
./lean/DLNFibre/Core/CThetaGeometricPerm.lean
./lean/DLNFibre/Core/ChartPhiDescent.lean
./expeditions/2026-06-18-c-theta/threads/09-ctheta-theta-bridge/statement-card.md
./expeditions/2026-06-18-c-theta/threads/08-ctheta-value/statement-card.md
./expeditions/2026-06-18-c-theta/threads/06-drop-to-m/statement-card.md
./lean/DLNFibre/Core/MeasureTheory/PolynomialZeroSet.lean
./lean/DLNFibre/Core/Setup.lean
./lean/DLNFibre/Core/SchurFibreVanishing.lean
./lean/DLNFibre/DLN/RlctPayoffGeneral.lean
./lean/DLNFibre/DLN/RlctPayoff.lean
./expeditions/2026-06-22-explicit-ctheta/brief.md
./lean/DLNFibre/DLN/BundleShiftDischarge.lean
./lean/DLNFibre/DLN/Basic.lean
./expeditions/2026-06-22-explicit-ctheta/lessons.md
./expeditions/2026-06-22-explicit-ctheta/priorities.md
./expeditions/2026-06-20-rlct-payoff/threads.md
./expeditions/2026-06-20-rlct-payoff/synthesis.md
./lean/DLNFibre/DLN/Aoyagi/ClosedForm.lean
./expeditions/2026-06-18-c-theta/threads/08-ctheta-value/codex/assembly-prompt.md
./expeditions/2026-06-18-c-theta/threads/08-ctheta-value/codex/bijection-equality-answer.md
./expeditions/2026-06-18-c-theta/threads/08-ctheta-value/codex/theta-prompt.md

 succeeded in 301ms:
./expeditions/2026-06-20-aoyagi-full/lessons.md:976:|x p|^{minAdm−1}` from it — and couldn't (the decoder has `Rfin=0`, `structPivot=coord-0`, `u` scaling all
./expeditions/2026-06-20-aoyagi-full/threads/36-genM-jacobian-det/codex/bcd-answer.md:17:Current Lean caveat: the implementation does **not yet encode this fixed residual slot correctly**. `readE` reads ordinary `E` variables, `structPivot` is hardcoded as flat coordinate `0`, `chartIdxEquiv` is opaque via `Fintype.equivFin`, and `genBlkFlatStruct` currently has `Rfin := fun _ => 0`. See [RouteMGenFlatStruct.lean](</home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/agent-a008af4c8473e3063/lean/DLNFibre/DLN/RLCT/Validate/RouteMGenFlatStruct.lean:104>) and [RouteMFlatStructV.lean](</home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/agent-a008af4c8473e3063/lean/DLNFibre/DLN/RLCT/Validate/RouteMFlatStructV.lean:88>). As written, the full determinant target is not derivable; the decoder needs `pRad/fixedSlot` and nonzero leaf `Rfin` first.
./expeditions/2026-06-20-aoyagi-full/threads/36-genM-jacobian-det/scripts/jac_full_222.py:6:# u = x p = the pivot coordinate = structPivot = flat coord 0.
./expeditions/2026-06-20-aoyagi-full/threads/36-genM-jacobian-det/scripts/jac_full_222.py:11:# The decoder uses structPivot=<0,hN>. Whatever role flat-0 maps to, u=that coord. Let me test BOTH and
./expeditions/2026-06-20-aoyagi-full/threads/36-genM-jacobian-det/codex/decoder-fix-prompt.md:26:The pivot is defined as flat coordinate 0 (structPivot := <0>). The radial scalar u = x_0 enters ONLY linearly
./expeditions/2026-06-20-aoyagi-full/threads/36-genM-jacobian-det/thread.md:423:   transition `C_L = u • Rfin L = 0`. And `structPivot := ⟨0, hN⟩` (`RouteMFlatStructV.lean:89`) is just
./expeditions/2026-06-20-aoyagi-full/threads/36-genM-jacobian-det/thread.md:459:+ `structPivot` so the radial blow-up is encoded (fixed-`1` residual slot + nonzero `Rfin`), keeping the
./expeditions/2026-06-20-aoyagi-full/threads/36-genM-jacobian-det/thread.md:729:`∀ᵐ x : Fin (routeMAmbient M) → ℝ, 0 < VvalGen (x (structPivot M hN)) M (tach M)
./expeditions/2026-06-20-aoyagi-full/threads/80-genM-nodechart/frame-qm-statement-card.md:5:> `|det Q_M| = 1`. The clean factorization `phiFlatLiveR1 = Q_M ∘ T_M` is then DEFINITIONAL (no refuted
./expeditions/2026-06-20-aoyagi-full/threads/80-genM-nodechart/frame-qm-statement-card.md:28:>   via `interiorDet_headline_of_blockTri`. Then `|det Dφ| = |det Q_M|·|det DT_M| = 1·headline`.
./expeditions/2026-06-20-aoyagi-full/threads/80-genM-nodechart/route-i-l2/bridge_fixedE.py:2:print("Does phiFlatLiveR1 M222 (FIXED-E genBlkFlatLiveR1) factor as B ∘ pivotBlowupOn (faithful)?")
./expeditions/2026-06-20-aoyagi-full/threads/80-genM-nodechart/route-i-l2/bridge_fixedE.py:20:print("not just the gauge-slot. → phi222 ≠ phiFlatLiveR1 M222 even up to relabeling. BRIDGE = they are")
./expeditions/2026-06-20-aoyagi-full/threads/80-genM-nodechart/route-i-l2/bridge_fixedE.py:21:print("DIFFERENT charts; the (2,2,2) pack/T template is for B_det222, NOT phiFlatLiveR1 M222.")
./expeditions/2026-06-20-aoyagi-full/threads/80-genM-nodechart/role-grade-locality-det-statement-card.md:63:>   REAL chart `phiFlatLiveR1` is NOT reached by route-α's de-risked locality alone. Two pieces remain,
./expeditions/2026-06-20-aoyagi-full/threads/80-genM-nodechart/role-grade-locality-det-statement-card.md:74:>      `fderiv phiFlatLiveR1`'s diagonal blocks to the engine values (`schurFrame_abs_det`,
./expeditions/2026-06-20-aoyagi-full/threads/80-genM-nodechart/role-grade-locality-det-statement-card.md:81:>   grading (radial grade `0` + one grade per boundary), keep `interiorDet_headline_of_blockTri` as-is,
./expeditions/2026-06-20-aoyagi-full/threads/80-genM-nodechart/codex/affine-radial-resolution-prompt.md:41:   radial stay a pure pivotBlowupOn (the structPivot coord) regardless?
./expeditions/2026-06-20-aoyagi-full/threads/80-genM-nodechart/route-i-l2/bridge_final.py:2:print("BRIDGE (corrected, against actual genBlkFlatStruct): phiFlatLiveR1 M222 factors as B ∘ pb?")
./expeditions/2026-06-20-aoyagi-full/threads/80-genM-nodechart/route-i-l2/bridge_final.py:8:# For the BRIDGE we need: does phiFlatLiveR1 M222 = B ∘ pb for a faithful u-free B? Test with genBlkFlatLiveR1's
./expeditions/2026-06-20-aoyagi-full/threads/80-genM-nodechart/route-i-l2/bridge_final.py:34:print("So phiFlatLiveR1 M222 has the SAME u-structure as the (2,2,2) template (T222: u0 the radial coord).")
./expeditions/2026-06-20-aoyagi-full/threads/80-genM-nodechart/route-i-l2/bridge_definitive.py:2:print("="*72); print("DEFINITIVE: does phiFlatLiveR1 M222 (genBlkFlatLiveR1) factor as B ∘ pivotBlowupOn,")
./expeditions/2026-06-20-aoyagi-full/threads/80-genM-nodechart/route-i-l2/bridge_definitive.py:7:# radial u = x_structPivot. The pivot slot p: structPivot — a coordinate. Call it 'u'.
./expeditions/2026-06-20-aoyagi-full/threads/80-genM-nodechart/route-i-l2/bridge_definitive.py:22:print("det Dφ (phiFlatLiveR1 M222) =", detphi)
./expeditions/2026-06-20-aoyagi-full/threads/80-genM-nodechart/chain-assemble-diff-statement-card.md:1:# Statement card — b-FrameM-2 COMPLETE: DifferentiableAt phiFlatLiveR1, `genm-detcomp`
./expeditions/2026-06-20-aoyagi-full/threads/80-genM-nodechart/chain-assemble-diff-statement-card.md:3:> **Claim (b-FrameM-2 done).** The R1 active-center chart `phiFlatLiveR1` is `DifferentiableAt` over
./expeditions/2026-06-20-aoyagi-full/threads/80-genM-nodechart/chain-assemble-diff-statement-card.md:8:> - **Lean:** `DLNFibre.DLN.RLCT.phiFlatLiveR1_differentiableAt`
./expeditions/2026-06-20-aoyagi-full/threads/80-genM-nodechart/chain-assemble-diff-statement-card.md:13:>   `DifferentiableAt ℝ (phiFlatLiveR1 M t ha hN p hp1 hp2 rfin) u`. Threads the banked atoms
./expeditions/2026-06-20-aoyagi-full/threads/80-genM-nodechart/chain-assemble-diff-statement-card.md:15:>   `Agen` → `phiFlatLiveR1_differentiableAt_of_Agen` (the top reduction).
./expeditions/2026-06-20-aoyagi-full/threads/80-genM-nodechart/chain-assemble-diff-statement-card.md:27:>   `phiFlatLiveR1_differentiableAt` (the `DFrame_M = fderiv` existence) +
./expeditions/2026-06-20-aoyagi-full/threads/80-genM-nodechart/chain-assemble-diff-statement-card.md:30:>   `interiorDet_headline_of_blockTri` (b-3) ⟹ the headline, modulo b-FrameM-1 (`Frame_M`/`Q_M` +
./expeditions/2026-06-20-aoyagi-full/threads/80-genM-nodechart/codex/G-faithfulness-prompt.md:4:Deep-linear-network achiever chart `φ = phiFlatLiveR1 : (Fin N → ℝ) → (Fin N → ℝ)`, N = flatDim M, opaque
./expeditions/2026-06-20-aoyagi-full/threads/80-genM-nodechart/codex/G-faithfulness-prompt.md:6:(|det K_s|^{r_s+c_s}·∏_i|q_{s,i}|^{2(t_s−1−i)})`, where `u_p = u(structPivot)`.
./expeditions/2026-06-20-aoyagi-full/threads/80-genM-nodechart/codex/G-faithfulness-prompt.md:59:   pivotBlowupOn(active, structPivot)`. My finding says the pivot column of `Dφ` carries the r_i — is that
./expeditions/2026-06-20-aoyagi-full/threads/80-genM-nodechart/route-i-l2/bridge_check.py:2:print("="*72); print("BRIDGE: phi222 (B_det222, free-E pivot) vs phiFlatLiveR1 M222 (genBlkFlatLiveR1, fixed-E)"); print("="*72)
./expeditions/2026-06-20-aoyagi-full/threads/80-genM-nodechart/route-i-l2/bridge_check.py:18:print("→ differ ONLY at (1,1): free has u·x6, fixed has u·1. So phiFlatLiveR1 = phi222 |_{x6 := 1} ... NO:")
./expeditions/2026-06-20-aoyagi-full/threads/80-genM-nodechart/route-i-l2/bridge_check.py:24:print("VERDICT: phi222 and phiFlatLiveR1 M222 are NOT literally equal — DIFFERENT decoders")
./expeditions/2026-06-20-aoyagi-full/threads/80-genM-nodechart/route-i-l2/fixb_corrected_contract_verify.py:2:# Fix B corrected contract: phiFlatLiveR1 = B ∘ pivotBlowupOn(active, p), B = de-radialized chart (radial 1),
./expeditions/2026-06-20-aoyagi-full/threads/80-genM-nodechart/statement-card-bdata222.md:13:  Agen (x (structPivot M222 hN_M222)) M222 tach222 (Glr rfin x) (hleStruct …) 0
./expeditions/2026-06-20-aoyagi-full/threads/80-genM-nodechart/statement-card-bdata222.md:15:         aRead x * bRead x, aRead x * bRead x * nRead x + x (structPivot M222 hN_M222)]
./expeditions/2026-06-20-aoyagi-full/threads/80-genM-nodechart/statement-card-bdata222.md:17:  Agen (x (structPivot M222 hN_M222)) M222 tach222 (Glr rfin x) (hleStruct …) 1
./expeditions/2026-06-20-aoyagi-full/threads/80-genM-nodechart/statement-card-bdata222.md:18:    = !![x (structPivot …) * rfin x ⟨0⟩ ⟨0⟩ - nRead x * w0Read x,
./expeditions/2026-06-20-aoyagi-full/threads/80-genM-nodechart/statement-card-bdata222.md:19:         x (structPivot …) * rfin x ⟨0⟩ ⟨1⟩ - nRead x * w1Read x;  w0Read x, w1Read x]
./expeditions/2026-06-20-aoyagi-full/threads/80-genM-nodechart/statement-card-bdata222.md:22:(`Glr rfin x`), reindexed, ARE the Codex-claimed explicit Schur-frame matrices. The `+ x structPivot`
./expeditions/2026-06-20-aoyagi-full/threads/80-genM-nodechart/statement-card-bdata222.md:30:  phiFlatLiveR1 M222 tach222 structAdm_tach222 hN_M222 1 hp1_222 hp2_222 rfin222
./expeditions/2026-06-20-aoyagi-full/threads/80-genM-nodechart/statement-card-bdata222.md:31:    = Bchart ∘ pivotBlowupOn active222 (structPivot M222 hN_M222)
./expeditions/2026-06-20-aoyagi-full/threads/80-genM-nodechart/statement-card-bdata222.md:34:`Bparams` reading the pivot as the ORDINARY coord `y structPivot` (the `+u`), readers a/b/n/w0/w1 from
./expeditions/2026-06-20-aoyagi-full/threads/80-genM-nodechart/statement-card-bdata222.md:35:`y`, leaf `y lf0 / y lf1`; `rfin222 x = !![x lf0, x lf1]`; `active222 = {structPivot, lf0, lf1}`
./expeditions/2026-06-20-aoyagi-full/threads/80-genM-nodechart/statement-card-bdata222.md:37:reader slots (R2: `free_card_ge_two`), so `lf ≠ structPivot`, `lf ∉ readerSet` hold by membership — the
./expeditions/2026-06-20-aoyagi-full/threads/80-genM-nodechart/statement-card-bdata222.md:49:(~120-150 LoC). The headline `interiorDet_headline_of_BData` then gives `|det Dφ| = |u_p|²·|aRead u|²`.
./expeditions/2026-06-20-aoyagi-full/threads/80-genM-nodechart/route-i-bridge-resolved.md:1:# Bridge RESOLVED — `phiFlatLiveR1 M222` vs the (2,2,2) `phi222`/`T222` template (the pre-delegation pin)
./expeditions/2026-06-20-aoyagi-full/threads/80-genM-nodechart/route-i-bridge-resolved.md:4:the banked (2,2,2) `phi222`/`pack222`/`T222` (on `B_det222`) is literally `phiFlatLiveR1 M222` (on
./expeditions/2026-06-20-aoyagi-full/threads/80-genM-nodechart/route-i-bridge-resolved.md:11:`phiFlatLiveR1 M222` (decoder `genBlkFlatLiveR1`, FIXED-pivot + live-leaf) and `phi222` (decoder
./expeditions/2026-06-20-aoyagi-full/threads/80-genM-nodechart/route-i-bridge-resolved.md:15:formaliser to prove `phiFlatLiveR1 = phi222` (false).
./expeditions/2026-06-20-aoyagi-full/threads/80-genM-nodechart/route-i-bridge-resolved.md:34:- **Target: `phiFlatLiveR1`'s ACTUAL fixed-pivot/live-leaf blocks** (`genBlkFlatLiveR1`), using `T222` ONLY
./expeditions/2026-06-20-aoyagi-full/threads/80-genM-nodechart/route-i-bridge-resolved.md:39:- **Active set (fixed-pivot decoder):** `{structPivot} ∪ {leaf free coords} ∪ {E-free coords excl. the fixed
./expeditions/2026-06-20-aoyagi-full/threads/80-genM-nodechart/route-i-bridge-resolved.md:42:- **Wiring (all banked, decoder-agnostic):** `interiorDet_headline_of_BData` (radial via `radialComp_abs_det`),
./expeditions/2026-06-20-aoyagi-full/threads/80-genM-nodechart/item3-2bi-minus1-spec.md:8:`NodeAchieverChart` needs: `leafH : Fin N → ℕ`, `leafH_pivot : leafH (structPivot) = minAdm − 1`, and
./expeditions/2026-06-20-aoyagi-full/threads/80-genM-nodechart/item3-2bi-minus1-spec.md:9:`cov`'s `|det Dφ(u)| = ∏_j |u_j|^{leafH j}`. The chart is `phiFlatLiveR1 ∘ (kLDU lens)` (R1 active-center
./expeditions/2026-06-20-aoyagi-full/threads/80-genM-nodechart/item3-2bi-minus1-spec.md:22:composeFold fs = phiFlatLiveR1∘kLDU over opaque widths — the genuine bottleneck, the per-boundary split-CLE).
./expeditions/2026-06-20-aoyagi-full/threads/80-genM-nodechart/item3-2bi-minus1-spec.md:47:- 2b-i-B: the item-3 map equality `composeFold fs = phiFlatLiveR1 ∘ kLDU` over opaque widths (the per-boundary
./expeditions/2026-06-20-aoyagi-full/threads/80-genM-nodechart/decoder-diff-statement-card.md:29:>   `diffAt_chainA`. Then `phiFlatLiveR1_differentiableAt_of_Agen` ⟹ `DFrame_M` exists ⟹
./expeditions/2026-06-20-aoyagi-full/threads/80-genM-nodechart/frame-locality-statement-card.md:25:>   - **b-FrameM-2 (the long pole):** `HasFDerivAt phiFlatLiveR1 D u` over OPAQUE `Fin (Wext M k)` widths.
./expeditions/2026-06-20-aoyagi-full/threads/80-genM-nodechart/frame-locality-statement-card.md:35:>   phiFlatLiveR1`, `g := bLayer`, `hloc :=` lifted `Agen_genBlkFlatStruct_reads_le`).
./expeditions/2026-06-20-aoyagi-full/threads/80-genM-nodechart/item3-frameM-buildspec.md:14:  phiFlatLiveR1 ∘ kLDU = paramsEquivFlat ∘ chartParamsGen(decoder) = Q_M ∘ Frame_M ∘ (kLDU absorbed in decoder),
./expeditions/2026-06-20-aoyagi-full/threads/80-genM-nodechart/codex/assembly-arch-answer.md:5:1. Work with `J := LinearMap.toMatrix' (fderiv ℝ phiFlatLiveR1 u).toLinearMap`.
./expeditions/2026-06-20-aoyagi-full/threads/80-genM-nodechart/codex/assembly-arch-answer.md:13:This avoids both the recursive `StairProd` target and a global `composeFold fs = phiFlatLiveR1` map equality.
./expeditions/2026-06-20-aoyagi-full/threads/80-genM-nodechart/codex/assembly-arch-answer.md:50:Then build the hard content behind the hypotheses: `phiFlatLiveR1_jacobian_scaledColumns` and `boundary_diagBlock_abs_det_engine`. No code changes made; I only inspected the local v4.29/mathlib and repo APIs.
./expeditions/2026-06-20-aoyagi-full/threads/80-genM-nodechart/chain-diff-statement-card.md:5:> `phiFlatLiveR1_differentiableAt_of_Agen` (`Agen s = chainA(N_s, W_s, Cgen(s+1))`).
./expeditions/2026-06-20-aoyagi-full/threads/80-genM-nodechart/chain-diff-statement-card.md:32:>   `Agen` differentiable: `phiFlatLiveR1_differentiableAt_of_Agen` ⟹ `DFrame_M` exists ⟹
./expeditions/2026-06-20-aoyagi-full/threads/80-genM-nodechart/codex/detbridge-review-answer.md:5:SOUND. The left side of `hconj` is syntactically the actual Lean object `(fderiv ℝ (phiFlatLiveR1 …) u).toLinearMap`, so proving `hconj` requires equating the staircase conjugate with the real chart’s Fréchet derivative at `u`. The conclusion’s left side is the same `fderiv … u` object, so the theorem itself provides no place to swap in a surrogate map. A bad caller could only misuse the theorem by proving a false-looking `hconj`, but Lean would require an actual proof of that exact equality.
./expeditions/2026-06-20-aoyagi-full/threads/80-genM-nodechart/staircase-headline-statement-card.md:4:interior-det headline, tied to the REAL chart `phiFlatLiveR1`. Branch `genm-detbridge` (off
./expeditions/2026-06-20-aoyagi-full/threads/80-genM-nodechart/staircase-headline-statement-card.md:54:> `interiorDet_headline_of_blockTri`, SOUND hypotheses (staircase conjugacy + engine block-dets).
./expeditions/2026-06-20-aoyagi-full/threads/80-genM-nodechart/staircase-headline-statement-card.md:56:> - **Lean:** `DLNFibre.DLN.RLCT.interiorDet_headline_of_stairConj`
./expeditions/2026-06-20-aoyagi-full/threads/80-genM-nodechart/staircase-headline-statement-card.md:65:## Brick 5 — the headline on the REAL chart `phiFlatLiveR1` (`RouteMInteriorDetReal`)
./expeditions/2026-06-20-aoyagi-full/threads/80-genM-nodechart/staircase-headline-statement-card.md:67:> **Claim.** Brick 4 tied to the ACTUAL flat chart `fderiv ℝ (phiFlatLiveR1 …) u` — not a surrogate.
./expeditions/2026-06-20-aoyagi-full/threads/80-genM-nodechart/staircase-headline-statement-card.md:69:> - **Lean:** `DLNFibre.DLN.RLCT.interiorDet_phiFlatLiveR1_of_stairConj`
./expeditions/2026-06-20-aoyagi-full/threads/80-genM-nodechart/staircase-headline-statement-card.md:71:> - **Gloss.** `hconj : (fderiv ℝ (phiFlatLiveR1 …) u).toLinearMap = e.symm ∘ stairMap V (L+1) f c ∘ e`
./expeditions/2026-06-20-aoyagi-full/threads/80-genM-nodechart/staircase-headline-statement-card.md:73:>   `fderiv` (whose EXISTENCE is the banked `phiFlatLiveR1_differentiableAt`), so the hypothesis cannot be
./expeditions/2026-06-20-aoyagi-full/threads/80-genM-nodechart/staircase-headline-statement-card.md:79:The unconditional `interiorDet_headline` (general M) reduces to ONE goal: the **staircase conjugacy of the
./expeditions/2026-06-20-aoyagi-full/threads/80-genM-nodechart/staircase-headline-statement-card.md:87:  `(fderiv ℝ (phiFlatLiveR1 M t ha hN p hp1 hp2 rfin) u).toLinearMap
./expeditions/2026-06-20-aoyagi-full/threads/80-genM-nodechart/staircase-headline-statement-card.md:92:`schurFrame_abs_det × lduCoreDeriv_abs_det`). Feeding these to `interiorDet_phiFlatLiveR1_of_stairConj`
./expeditions/2026-06-20-aoyagi-full/threads/80-genM-nodechart/staircase-headline-statement-card.md:98:  bilinear `−dN_s·W_s` shear of `Cgen`. The DIFFERENTIABILITY is banked (`phiFlatLiveR1_differentiableAt`,
./expeditions/2026-06-20-aoyagi-full/threads/80-genM-nodechart/codex/bridge-prompt.md:1:# Bridge fact: phiFlatLiveR1 M222 (fixed-pivot genBlkFlatLiveR1) vs the (2,2,2) phi222 template
./expeditions/2026-06-20-aoyagi-full/threads/80-genM-nodechart/codex/bridge-prompt.md:4:The BData interface / headline targets `phiFlatLiveR1 M t ha hN p hp1 hp2 rfin` (the R1 live-leaf decoder
./expeditions/2026-06-20-aoyagi-full/threads/80-genM-nodechart/codex/bridge-prompt.md:22:1. `phiFlatLiveR1 M222` and `phi222` are NOT literally equal (different decoders: fixed-E+live-leaf vs
./expeditions/2026-06-20-aoyagi-full/threads/80-genM-nodechart/codex/bridge-prompt.md:24:   `phiFlatLiveR1`, NOT a literal bridge equality.
./expeditions/2026-06-20-aoyagi-full/threads/80-genM-nodechart/codex/bridge-prompt.md:25:2. BUT `phiFlatLiveR1 M222` independently has the faithful structure: det = u^{minAdm−1}·engine (verified
./expeditions/2026-06-20-aoyagi-full/threads/80-genM-nodechart/codex/bridge-prompt.md:32:   `phiFlatLiveR1 = phi222` (false).
./expeditions/2026-06-20-aoyagi-full/threads/80-genM-nodechart/codex/bridge-prompt.md:35:A. Is finding (2) correct — det Dφ(phiFlatLiveR1 M222) = u^{minAdm−1}·engine with B a u-free local iso, so
./expeditions/2026-06-20-aoyagi-full/threads/80-genM-nodechart/codex/bridge-prompt.md:40:   for genBlkFlatLiveR1's ACTUAL blocks, generalizing T222 structurally, target phiFlatLiveR1 — NOT a
./expeditions/2026-06-20-aoyagi-full/threads/80-genM-nodechart/codex/bridge-prompt.md:43:C. Sanity: the active set for the FIXED-pivot decoder = {structPivot} ∪ {leaf free coords} (NOT the E-slot,
./expeditions/2026-06-20-aoyagi-full/threads/80-genM-nodechart/interior-det-headline-statement-card.md:10:> - **Lean:** `DLNFibre.DLN.RLCT.interiorDet_headline_of_blockTri`
./expeditions/2026-06-20-aoyagi-full/threads/80-genM-nodechart/interior-det-headline-statement-card.md:23:>   - `blockTri_headline_regroup` + `interiorDet_headline_of_blockTri`: the **regrouping** of the
./expeditions/2026-06-20-aoyagi-full/threads/80-genM-nodechart/codex/G-faithfulness-answer.md:33:from a factor-fold equality `composeFold fs = φ`, using [RouteMChartFactorFold.lean](/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/agent-a9bb11c22680d93d4/lean/DLNFibre/DLN/RLCT/Validate/RouteMChartFactorFold.lean:31), `radialFactor_abs_det`, `schurChartFactor_abs_det`, `lduChartFactor_abs_det`, etc.; or the already-shaped staircase theorem [interiorDet_phiFlatLiveR1_of_stairConj](/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/agent-a9bb11c22680d93d4/lean/DLNFibre/DLN/RLCT/Validate/RouteMInteriorDetReal.lean:35), whose layer `0` is the radial arrow and layers `s+1` are the boundary engine blocks.
./expeditions/2026-06-20-aoyagi-full/threads/80-genM-nodechart/coarse-route-grading-obstruction.md:10:prove `D(T_M).BlockTriangular g`, feed `interiorDet_headline_of_blockTri`. `Matrix.BlockTriangular`
./expeditions/2026-06-20-aoyagi-full/threads/80-genM-nodechart/coarse-route-grading-obstruction.md:79:det reads. The `interiorDet_headline_of_blockTri` conditional headline is still the correct TARGET shape
./expeditions/2026-06-20-aoyagi-full/threads/80-genM-nodechart/staircase-twosided-wrapper-statement-card.md:38:  - `interiorDet_headline_of_twoStairConj` — the SAME interior-det headline output formula
./expeditions/2026-06-20-aoyagi-full/threads/80-genM-nodechart/staircase-twosided-wrapper-statement-card.md:50:Feed `interiorDet_phiFlatLiveR1_of_stairConj` (single-`e`, banked) OR the new
./expeditions/2026-06-20-aoyagi-full/threads/80-genM-nodechart/staircase-twosided-wrapper-statement-card.md:51:`interiorDet_headline_of_twoStairConj` (two-sided) by constructing, over opaque `Text`/`Wext` widths:
./expeditions/2026-06-20-aoyagi-full/threads/80-genM-nodechart/staircase-twosided-wrapper-statement-card.md:64:5. **`hconj`** (the load-bearing identity): `(fderiv ℝ phiFlatLiveR1 u).toLinearMap = e.symm ∘ stairMap ∘ e`
./expeditions/2026-06-20-aoyagi-full/threads/80-genM-nodechart/staircase-twosided-wrapper-statement-card.md:65:   (single-`e`) or `eOut ∘ D ∘ eIn.symm = stairMap` (two-sided). Via `phiFlatLiveR1_differentiableAt_of_Agen`
./expeditions/2026-06-20-aoyagi-full/threads/80-genM-nodechart/staircase-twosided-wrapper-statement-card.md:168:- **`V 0 = ℝ^minAdm`** (NOT `ℝ`). `active = {structPivot} ∪ {ALL free entries of the u-scaled Rmat_k
./expeditions/2026-06-20-aoyagi-full/threads/80-genM-nodechart/staircase-twosided-wrapper-statement-card.md:170:  structPivot)`, `|det f 0| = |u|^{minAdm−1}` via `radial_abs_det_minAdm` + `active.card = minAdm` (the
./expeditions/2026-06-20-aoyagi-full/threads/80-genM-nodechart/staircase-twosided-wrapper-statement-card.md:205:- `radialRcols` (`= active.erase structPivot`) + `radialRcols_card` (`= minAdm−1`) — the COUNT obligation
./expeditions/2026-06-20-aoyagi-full/threads/80-genM-nodechart/staircase-twosided-wrapper-statement-card.md:209:- **(P) `phiFlatLiveR1_jacobian_scaledColumns`**: `toMatrix' (fderiv phiFlatLiveR1 u) = of fun i j =>
./expeditions/2026-06-20-aoyagi-full/threads/80-genM-nodechart/staircase-twosided-wrapper-statement-card.md:211:  Jacobian matrix of the MODIFIED chart `φ̃` = `phiFlatLiveR1` with `u•Rmat`/`u•Rfin` replaced by
./expeditions/2026-06-20-aoyagi-full/threads/80-genM-nodechart/staircase-twosided-wrapper-statement-card.md:256:- **(1) the MAP identity** `phi_eq_B_comp_pivotBlowupOn : ∀ y, phiFlatLiveR1 … y = B (pivotBlowupOn active
./expeditions/2026-06-20-aoyagi-full/threads/80-genM-nodechart/staircase-twosided-wrapper-statement-card.md:257:  structPivot y)` — shallow extensional packaging (`ext`/`chartIdxEquiv` cases + per-block rewrites via the
./expeditions/2026-06-20-aoyagi-full/threads/80-genM-nodechart/staircase-twosided-wrapper-statement-card.md:260:  fed via `interiorDet_phiFlatLiveR1_of_stairConj`-analogue (or directly stated on `fderiv phiFlatLiveR1`).
./expeditions/2026-06-20-aoyagi-full/threads/80-genM-nodechart/staircase-twosided-wrapper-statement-card.md:298:  `interiorDet_headline_of_twoStairConj` (the headline wrapper for the rectangular layout).
./expeditions/2026-06-20-aoyagi-full/threads/80-genM-nodechart/staircase-twosided-wrapper-statement-card.md:299:- Prior: `stairMap_abs_det_conj` (single-`e`), `interiorDet_phiFlatLiveR1_of_stairConj` (the real-chart
./expeditions/2026-06-20-aoyagi-full/threads/80-genM-nodechart/staircase-twosided-wrapper-statement-card.md:301:  `chainA_apply_castAdd/natAdd`, `phiFlatLiveR1_differentiableAt(_of_Agen)`, `diffAt_Agen`,
./expeditions/2026-06-20-aoyagi-full/threads/80-genM-nodechart/codex/hdet-fork-prompt.md:62:   (`interiorDet_phiFlatLiveR1_of_stairConj`, `interiorDet_headline_of_blockTri`) take the factorization as
./expeditions/2026-06-20-aoyagi-full/threads/80-genM-nodechart/item3-2bi-B-F1-subspec.md:1:# 2b-i-B F1 SUB-SPEC — the prefix-threading map equality `composeFold fs = phiFlatLiveR1 ∘ kLDU`
./expeditions/2026-06-20-aoyagi-full/threads/80-genM-nodechart/item3-2bi-B-F1-subspec.md:40:- 2b-i-B-4: assemble `composeFold fs = phiFlatLiveR1 ∘ kLDU` by funext + the prefix-invariance (2) threading
./expeditions/2026-06-20-aoyagi-full/threads/80-genM-nodechart/chart-diff-statement-card.md:3:> **Claim (b-FrameM-2 assembly step 1).** `DifferentiableAt phiFlatLiveR1 x₀` reduces to the per-layer
./expeditions/2026-06-20-aoyagi-full/threads/80-genM-nodechart/chart-diff-statement-card.md:7:> - **Lean:** `DLNFibre.DLN.RLCT.phiFlatLiveR1_differentiableAt_of_Agen` (+ `diffAt_reindex_finCongr`)
./expeditions/2026-06-20-aoyagi-full/threads/80-genM-nodechart/chart-diff-statement-card.md:10:>   `DifferentiableAt ℝ` at `x₀`, then `phiFlatLiveR1 M t ha hN p hp1 hp2 rfin` is `DifferentiableAt ℝ`
./expeditions/2026-06-20-aoyagi-full/threads/80-genM-nodechart/chart-diff-statement-card.md:13:>   - **A** (linear CLE comp): `phiFlatLiveR1 = paramsEquivFlat ∘ chartParamsGen` (`rfl`), and
./expeditions/2026-06-20-aoyagi-full/threads/80-genM-nodechart/chart-diff-statement-card.md:27:>   `phiFlatLiveR1_differentiableAt_of_Agen` ⟹ `DFrame_M` exists ⟹
./expeditions/2026-06-20-aoyagi-full/threads/80-genM-nodechart/frame-diff-statement-card.md:3:> **Claim (b-FrameM-2 foundation).** The chart `phiFlatLiveR1` is differentiable over OPAQUE width
./expeditions/2026-06-20-aoyagi-full/threads/80-genM-nodechart/frame-diff-statement-card.md:30:>   (Params-valued, per-layer via `differentiableAt_pi`) → `phiFlatLiveR1 = paramsEquivFlat ∘ chartParamsGen`
./expeditions/2026-06-20-aoyagi-full/threads/80-genM-nodechart/frame-diff-statement-card.md:32:>   budget over the dependent widths). Output: `DifferentiableAt phiFlatLiveR1 u`, which + the b-FrameM-3
./expeditions/2026-06-20-aoyagi-full/threads/80-genM-nodechart/codex/assembly-arch-prompt.md:5:`|det (fderiv ℝ phiFlatLiveR1 u)| = |u_p|^{minAdm M − 1} · ∏_{s:Fin L} ( |det K_s|^{r_s+c_s} · ∏_i |q_{s,i}|^{2(t_s−1−i)} )`.
./expeditions/2026-06-20-aoyagi-full/threads/80-genM-nodechart/codex/assembly-arch-prompt.md:8:- `interiorDet_headline_of_twoStairConj` (route B target): given `D : E →ₗ E`, equivs `eIn eOut : E ≃ₗ
./expeditions/2026-06-20-aoyagi-full/threads/80-genM-nodechart/codex/assembly-arch-prompt.md:19:- `radialActive_exists` (`∃ active, structPivot ∈ active ∧ active.card = minAdm`).
./expeditions/2026-06-20-aoyagi-full/threads/80-genM-nodechart/codex/assembly-arch-prompt.md:45:composition `phiFlatLiveR1 = composeFold [radial, shear, frames]` (needs map value-equality — Codex
./expeditions/2026-06-20-aoyagi-full/threads/80-genM-nodechart/item3-2bi-B-mapeq-spec.md:1:# 2b-i-B — the item-3 map equality `composeFold fs = phiFlatLiveR1 ∘ kLDU` (SPEC, cast-avoiding, for the gate)
./expeditions/2026-06-20-aoyagi-full/threads/80-genM-nodechart/item3-2bi-B-mapeq-spec.md:8:`∃ fs : List (ChartFactor N), composeFold fs = phiFlatLiveR1 M (tach M) ha hN p hp1 hp2 (kLDU-reparam)`,
./expeditions/2026-06-20-aoyagi-full/threads/80-genM-nodechart/item3-2bi-B-mapeq-spec.md:10:monomial det. `phiFlatLiveR1 ∘ kLDU = phiGen (x p₀) (genBlkFlatLiveR1 … (kLDU x) x)` = `paramsEquivFlat ∘
./expeditions/2026-06-20-aoyagi-full/threads/80-genM-nodechart/item3-2bi-B-mapeq-spec.md:45:  must be the SAME phi as the rate's (NodeAchieverChart ties one phi). So F2 needs phiFlatLiveR1 = composeFold
./expeditions/2026-06-20-aoyagi-full/threads/80-genM-nodechart/item3-2bi-B-mapeq-spec.md:63:COMPLETE + sorry-free: rate (phiFlatLDU/phiFlatLive/phiFlatLiveR1), witness (2e), budget_identity,
./expeditions/2026-06-20-aoyagi-full/threads/80-genM-nodechart/codex/bridge-answer.md:25:phiFlatLiveR1 M222 = B ∘ π
./expeditions/2026-06-20-aoyagi-full/threads/80-genM-nodechart/codex/bridge-answer.md:59:For B: yes, the delegation target should be **`genBlkFlatLiveR1`’s actual fixed-pivot/live-leaf blocks**, using `T222` only as a structural template. Do not ask the formalizer to prove `phiFlatLiveR1 = phi222`; that equality is false at the decoder level. The right proof shape is Schur-frame isolate pivot, shear off the `N W` leaf terms, then apply radial `pivotBlowupOn` to the live active coordinates.
./expeditions/2026-06-20-aoyagi-full/threads/80-genM-nodechart/codex/bridge-answer.md:64:{structPivot} ∪ {leaf free coords} ∪ {E-free coords excluding fixed E(0,0), if any}
./expeditions/2026-06-20-aoyagi-full/threads/80-genM-nodechart/codex/detbridge-review-prompt.md:8:Here are the two load-bearing Lean theorems (verbatim signatures). Real chart = `phiFlatLiveR1`,
./expeditions/2026-06-20-aoyagi-full/threads/80-genM-nodechart/codex/detbridge-review-prompt.md:22:  theorem interiorDet_phiFlatLiveR1_of_stairConj
./expeditions/2026-06-20-aoyagi-full/threads/80-genM-nodechart/codex/detbridge-review-prompt.md:25:    (hconj : (fderiv ℝ (phiFlatLiveR1 M t ha hN p hp1 hp2 rfin) u).toLinearMap
./expeditions/2026-06-20-aoyagi-full/threads/80-genM-nodechart/codex/detbridge-review-prompt.md:30:    |LinearMap.det (fderiv ℝ (phiFlatLiveR1 M t ha hN p hp1 hp2 rfin) u).toLinearMap|
./expeditions/2026-06-20-aoyagi-full/threads/80-genM-nodechart/codex/detbridge-review-prompt.md:32:  proof: it just feeds hconj/hR/hB to the abstract headline interiorDet_headline_of_stairConj.
./expeditions/2026-06-20-aoyagi-full/threads/80-genM-nodechart/codex/detbridge-review-prompt.md:46:    is `(fderiv ℝ (phiFlatLiveR1 …) u).toLinearMap` — the REAL chart's Fréchet derivative at u.
./expeditions/2026-06-20-aoyagi-full/threads/80-genM-nodechart/codex/detbridge-review-prompt.md:49:    Specifically: does the LHS of hconj pin the actual `fderiv ℝ (phiFlatLiveR1 …) u`, so that a
./expeditions/2026-06-20-aoyagi-full/threads/80-genM-nodechart/live-locality-statement-card.md:22:>   (`toMatrix_blockTriangular_of_locality`'s hypothesis) needs `phiFlatLiveR1`'s flat OUTPUT coord `i`'s
./expeditions/2026-06-20-aoyagi-full/threads/80-genM-nodechart/live-locality-statement-card.md:23:>   invariance under input coord `j` for `bLayer i < bLayer j`. `phiFlatLiveR1 v i = paramsEquivFlat
./expeditions/2026-06-20-aoyagi-full/threads/80-genM-nodechart/live-locality-statement-card.md:27:>   `phiFlatLiveR1_differentiableAt`) `hbt` via `toMatrix_blockTriangular_of_locality`.
./expeditions/2026-06-20-aoyagi-full/threads/80-genM-nodechart/bdata222-residual.md:12:   - `Agen1 = [[u·lf0 − n·w0, u·lf1 − n·w1],[w0,w1]]` (`u = x structPivot`, readers a/b/n/w0/w1, leaf
./expeditions/2026-06-20-aoyagi-full/threads/80-genM-nodechart/bdata222-residual.md:18:   (`Classical.choose` from the complement → `lf ≠ structPivot`, `lf ∉ readerSet` for free),
./expeditions/2026-06-20-aoyagi-full/threads/80-genM-nodechart/bdata222-residual.md:19:   `active222 = {structPivot, lf0, lf1}` with `active222_card : = minAdm M222`, `structPivot_mem_active222`,
./expeditions/2026-06-20-aoyagi-full/threads/80-genM-nodechart/bdata222-residual.md:23:   `phiFlatLiveR1 M222 tach222 structAdm_tach222 hN_M222 1 hp1_222 hp2_222 rfin222
./expeditions/2026-06-20-aoyagi-full/threads/80-genM-nodechart/bdata222-residual.md:24:      = Bchart ∘ pivotBlowupOn active222 (structPivot M222 hN_M222)`.
./expeditions/2026-06-20-aoyagi-full/threads/80-genM-nodechart/bdata222-residual.md:27:   `y structPivot` (NOT `phiGen 1 (genBlkFlatLiveR1)`, the superseded wrong B).
./expeditions/2026-06-20-aoyagi-full/threads/80-genM-nodechart/bdata222-residual.md:34:- **`DB`** — `Bchart`'s fderiv as a CLM at `pivotBlowupOn active222 structPivot u`. `Bchart =
./expeditions/2026-06-20-aoyagi-full/threads/80-genM-nodechart/bdata222-residual.md:54:  hp_mem := structPivot_mem_active222
./expeditions/2026-06-20-aoyagi-full/threads/80-genM-nodechart/bdata222-residual.md:57:  DB := <DB at (pbo active222 structPivot u)>
./expeditions/2026-06-20-aoyagi-full/threads/80-genM-nodechart/bdata222-residual.md:63:theorem interiorDet_headline_222 (u) :
./expeditions/2026-06-20-aoyagi-full/threads/80-genM-nodechart/bdata222-residual.md:64:    |LinearMap.det (fderiv ℝ (phiFlatLiveR1 M222 tach222 structAdm_tach222 hN_M222 1 hp1_222 hp2_222
./expeditions/2026-06-20-aoyagi-full/threads/80-genM-nodechart/bdata222-residual.md:66:      = |u (structPivot M222 hN_M222)| ^ (minAdm M222 - 1) * ∏ s, (bData222 u).engine s :=
./expeditions/2026-06-20-aoyagi-full/threads/80-genM-nodechart/bdata222-residual.md:67:  interiorDet_headline_of_BData M222 tach222 structAdm_tach222 hN_M222 1 hp1_222 hp2_222 rfin222 u
./expeditions/2026-06-20-aoyagi-full/threads/80-genM-nodechart/codex/engine-id-prompt.md:6:`phiFlatLiveR1 : (Fin N → ℝ) → (Fin N → ℝ)`. The fderiv reduces (banked) per layer `s : Fin L` to the
./expeditions/2026-06-20-aoyagi-full/threads/80-genM-nodechart/codex/engine-id-prompt.md:41:Express `(fderiv phiFlatLiveR1 u).toLinearMap = eOut.symm ∘ stairMap V (L+1) f c ∘ eIn` (two-sided form,
./expeditions/2026-06-20-aoyagi-full/threads/80-genM-nodechart/codex/engine-id-prompt.md:43:the banked `interiorDet_headline_of_twoStairConj` to get the unconditional headline.
./expeditions/2026-06-20-aoyagi-full/threads/80-genM-nodechart/codex/detfderiv-route-answer.md:1:**Short verdict:** the direct locality route should be treated as blocked for the real `phiFlatLiveR1`. The staircase is not merely a heavier proof of the same square block-triangular fact; it is the way to express the rectangular/input-output partition mismatch.
./expeditions/2026-06-20-aoyagi-full/threads/80-genM-nodechart/codex/detfderiv-route-answer.md:38:where `boundaryEngineDeriv` is built from `schurFrameDeriv`, `lduCoreDeriv`, and the det-1 shear/identity pieces. Then assemble these componentwise derivative identities into the `hconj` required by `interiorDet_phiFlatLiveR1_of_stairConj`.
./expeditions/2026-06-20-aoyagi-full/threads/80-genM-nodechart/codex/detfderiv-route-prompt.md:1:# Strategic fork: closing the interior-det headline on `phiFlatLiveR1` (Lean 4 / Mathlib v4.29)
./expeditions/2026-06-20-aoyagi-full/threads/80-genM-nodechart/codex/detfderiv-route-prompt.md:6:achiever chart `phiFlatLiveR1 : (Fin N → ℝ) → (Fin N → ℝ)` (N = `routeMAmbient M`, opaque in the width
./expeditions/2026-06-20-aoyagi-full/threads/80-genM-nodechart/codex/detfderiv-route-prompt.md:9:  `|det (fderiv ℝ phiFlatLiveR1 u)| = |u_p|^{minAdm−1} · ∏_{s:Fin L} ( |det K_s|^{r_s+c_s} · ∏_i |q_{s,i}|^{2(t_s−1−i)} )`.
./expeditions/2026-06-20-aoyagi-full/threads/80-genM-nodechart/codex/detfderiv-route-prompt.md:17:1. `phiFlatLiveR1_differentiableAt` — the chart is differentiable; `diffAt_Agen` per layer.
./expeditions/2026-06-20-aoyagi-full/threads/80-genM-nodechart/codex/detfderiv-route-prompt.md:29:   headline wrapper `interiorDet_headline_of_stairConj` that splits radial layer 0 from boundary layers.
./expeditions/2026-06-20-aoyagi-full/threads/80-genM-nodechart/codex/detfderiv-route-prompt.md:31:   - `interiorDet_headline_of_blockTri`: takes `hbt : DFrame.BlockTriangular g` + per-grade
./expeditions/2026-06-20-aoyagi-full/threads/80-genM-nodechart/codex/detfderiv-route-prompt.md:33:   - `interiorDet_phiFlatLiveR1_of_stairConj`: takes the staircase conjugacy `D.toLinearMap = e.symm ∘
./expeditions/2026-06-20-aoyagi-full/threads/80-genM-nodechart/codex/detfderiv-route-prompt.md:43:`(fderiv phiFlatLiveR1 u).toLinearMap = e.symm ∘ stairMap V (L+1) f c ∘ e`. This is over opaque
./expeditions/2026-06-20-aoyagi-full/threads/80-genM-nodechart/codex/detfderiv-route-prompt.md:47:(a) lift the banked `Agen`-level value-locality to coordinate-level locality of `phiFlatLiveR1`
./expeditions/2026-06-20-aoyagi-full/threads/80-genM-nodechart/codex/detfderiv-route-prompt.md:48:    (`phiFlatLiveR1 v i = phiFlatLiveR1 u i` whenever `v` agrees with `u` off a higher-bLayer coord `j`),
./expeditions/2026-06-20-aoyagi-full/threads/80-genM-nodechart/codex/affine-radial-resolution-answer.md:19:Your conflation diagnosis is right. In the chart matrix, `C 2 = x0 · !![1, x7]`; the literal `1` becomes the pivot coordinate contribution `x0`, not an additive chart-output constant. See [RouteM222Det.lean](/tmp/genm-subbox-review/lean/DLNFibre/DLN/RLCT/Validate/RouteM222Det.lean:180). The R1 live decoder similarly has a fixed `pivotEIndicator`, but `phiFlatLiveR1` reads the radial scalar from `structPivot`; that is a decoder-level fixed indicator, not an affine radial layer. See [RouteMFlatLive.lean](/tmp/RouteMFlatLive.lean:47) and [RouteMFlatLive.lean](/tmp/RouteMFlatLive.lean:263).
./expeditions/2026-06-20-aoyagi-full/threads/80-genM-nodechart/codex/affine-radial-resolution-answer.md:24:- The radial factor itself can remain `pivotBlowupOn active structPivot`; the generic wrapper already proves `|det| = |u_p|^(active.card-1)`. See [RouteMRadialFactor.lean](/tmp/genm-subbox-review/lean/DLNFibre/DLN/RLCT/Validate/RouteMRadialFactor.lean:33).
./expeditions/2026-06-20-aoyagi-full/threads/80-genM-nodechart/codex/L2-explicit-finset-answer.md:21:  {structPivot} ∪
./expeditions/2026-06-20-aoyagi-full/threads/80-genM-nodechart/codex/L2-explicit-finset-answer.md:32:  i = structPivot ∨
./expeditions/2026-06-20-aoyagi-full/threads/80-genM-nodechart/codex/L2-explicit-finset-answer.md:44:- You need a proof that `structPivot` is not an E-role slot and not a leaf slot. Usually this follows because it is a K/core slot at `k0`.
./expeditions/2026-06-20-aoyagi-full/threads/80-genM-nodechart/codex/L2-explicit-finset-answer.md:74:For `p = structPivot ∈ active`, with `u = x_p`,
./expeditions/2026-06-20-aoyagi-full/threads/80-genM-nodechart/codex/engine-id-answer.md:62:A `det_comp` bypass is only viable if you build a genuine global factorization by full-space endomorphisms, e.g. a `composeFold` of conjugated factors. But proving that fold equals the real chart is essentially the same cast problem as building `eIn/eOut`, and usually worse because it requires value equality of the whole nonlinear map. Since `interiorDet_headline_of_twoStairConj` is banked, feed it.

codex
The search confirms the pivot dependency is spread through the validate layer, not isolated in the 222 determinant file. I’m narrowing to the exact signatures now: the low-level pivot file, the chart definition, the BData interface, and the 222 determinant module.
exec
/bin/bash -lc "sed -n '1,220p' lean/CLAUDE.md" in /home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/agent-a9bb11c22680d93d4
 succeeded in 0ms:
# Lean conventions (DLNFibre)

## Build
- **Multi-worktree / multi-session: build via `scripts/lb`, NOT bare `lake build`.** `lb` symlinks this
  worktree's `.lake/packages` to the shared rev-keyed mathlib store (mmap-shared, no per-worktree clone)
  and throttles total Lean workers across all sessions via a global semaphore. Full rationale + box
  sizing: [`../docs/policies/lean-build-workflow.md`](../docs/policies/lean-build-workflow.md). **Do NOT
  `lake exe cache get` in a worktree** — it re-clones ~7 GB and defeats the sharing; the shared store is
  built once by `scripts/lake-store-setup <mathlib-rev>` (detached; exceeds the 10-min cap).
- Fresh shells: `source ~/.elan/env` before any `lake` command.
- Build from this `lean/` directory: `scripts/lb DLNFibre.<Module>`, or `scripts/lb` for the whole
  library. (Bare `lake build`/`lake env lean` still work for one-off elaboration, but bypass the shared
  store + the global concurrency cap — fine for a single `#eval`, not for parallel builds.)
- Toolchain: Lean `v4.29.0` (`lean-toolchain`), Mathlib `v4.29.0` (`lakefile.toml`). Matches the `ai-research-assistant` harness one level up, so its v4.29 Mathlib idioms transfer.

## Library shape — engine vs application
- **`DLNFibre.Core.*`** is the network-free **engine** (quiver orbits, Kostant partitions / rank patterns, `Ext` codimension, `(C, θ)`). It **must never import `DLNFibre.DLN`**. The dependency arrows point `DLN → Core → Mathlib`.
- **`DLNFibre.DLN.*`** is the **application** (multiplication-map fibres, the square-Frobenius loss, the RLCT payoff); it depends on `Core`.
- State each result at the specificity its claim needs; lift a piece into shared `Core` API on its **second** use, not in anticipation of one. Good API (characterizations over predicates, weakest hypotheses, name = content) is the `bedrock`/`precision` discipline, not a folder layout.

## Aggregator
- `DLNFibre.lean` is single-writer. Add new module imports at the end; do not reorder existing imports.
- New modules live at `DLNFibre/<Core|DLN>/<Topic>/<File>.lean`; one substantive theorem family per file.

## Sorry gate
- Zero `sorry` / `axiom` / `native_decide` / `#exit` in committed files. Audit with `scripts/sorries` from `lean/` before every commit.
- A `sorry` with a correct statement is a building block; a `sorry` with a wrong statement misleads. Fix wrong statements first.
- **`lake build` / `scripts/lb` exit-0 can MASK a `sorryAx` via a stale olean cache.** If an edit does not
  invalidate a `.olean` (a downstream-only change, an edit Lean's incremental compiler deems irrelevant), a
  prior `sorry` / type-error can persist in the cached olean and the build still reports success. **Confirm
  any "sorry-free" / axiom-footprint claim with `#print axioms` (which FORCES elaboration), never the build's
  exit status alone** — or force-recompile (delete the `.olean` / `touch` the source). The aggregator's
  `AxCheck.lean` does this for the load-bearing results on every build; add new load-bearing results there, or
  run a force-rebuilt `#print axioms` scratch (delete its olean first). (Caught a persisted diagonal-`sorry` +
  an unreported type-error in `RouteMSchurFrameDet`, 2026-06-26.)
- **`scripts/lb <Module>` builds a module's import-closure only — it does NOT catch NAME CLASHES with sibling
  modules the full aggregator imports.** A module that re-defines a constant another module already owns (e.g.
  two `(2,2,2)` anchor files both defining `t222`/`M222` in the same namespace) builds green in isolation but
  fails `lake build DLNFibre` with `environment already contains '…'`. **Before reporting a module as
  integration-ready, green-gate the FULL `lake build DLNFibre`** (or at least `rg` your new top-level names
  against the siblings you'll sit beside). Reuse shared anchor constants by `import`ing the module that owns
  them, don't re-declare. (Caught `RouteM222Det` re-defining `RouteM222StructAdm`'s `t222`, 2026-06-27.)

## Bedrock (the bar above the sorry gate)
A green, sorry-free build is the **floor**: it defeats *technical* slop, never *conceptual* slop —
"technically correct but subtly wrong, not The Way." Build each result as **bedrock**: something the next
theorem stands on without re-opening it. Where there's nothing to check against, **beauty is the guide** — a
vacuous, mis-scoped, or overclaiming theorem is *ugly*. In practice that recurrently means (not exhaustively):
name = content; non-vacuous, with the witness *shown* in-file; the weakest hypotheses that suffice, in usable
form; characterized (an `iff`) over asserted; every *cited*/*assumed* step named (never an `…rlct…`-style
theorem that secretly claims an unproved analytic interface — here the `rlct = ½·codim` reading rests on a
cited bound). The controller judges against this taste and holds precedence — full statement:
[`../docs/policies/bedrock.md`](../docs/policies/bedrock.md).

## Style
- `↦` not `=>` for lambda arrows.
- `decide +kernel`, not `native_decide`. Avoid `@[implemented_by]`, `@[extern]`, `unsafePerformIO`.
- One-line docstrings.
- Name a lemma for what it proves: a kernel/ideal *membership* fact is `…_mem_ker`, not `…_gen` (which reads as an ideal-generation claim).
- Confirm a Mathlib lemma exists before building a proof around it: `scripts/lean-search "..."`, or `rg` over `.lake/packages/mathlib/Mathlib/`.
- Pre-stage uncertain API with `example` blocks that pin lemma names/types; keep them as durable contracts.

## Mathlib gotchas (v4.29 pin)
Toolchain-generic notes that transfer at this pin. Accumulate new, DLN-specific ones here as they are found
(the ReLU programme's proof-specific notes were intentionally not ported — they were about a different theory).

- **`Basis` is `Module.Basis` at the v4.29 pin.** Bare `Basis` is unknown even with full Mathlib imports;
  ascribe `Module.Basis (Fin _) ℝ _` (e.g. from `Pi.basisFun`). Dot-notation (`b.tensorProduct b'`) is
  unaffected. Likely to recur in any `Matrix.rank` / column-span work.
- **`decide +kernel`, never `native_decide`.** Kernel `decide` is axiom-clean; `native_decide` trusts the
  compiler and breaks `#print axioms` hygiene. Kernel-reduction cost is **heartbeat-invisible** (a
  `maxHeartbeats` bump does not speed it), so a heartbeat timeout on a `decide` is not the symptom to chase.
- **Matrix-product identities over `ℤ` by `decide`, then cast.** An `ℝ` matrix-product identity is a
  `Matrix.ext` blow-up (per-entry `simp`, times out at scale). Write the matrices over `ℤ`
  (`DecidableEq` ⟹ `Matrix.mul` decides by kernel reduction, `by decide`), define the `ℝ` ones via
  `· .map (Int.castRingHom ℝ)`, and transfer products with `← Matrix.map_mul` (cast is a ring hom). No `ℝ`
  `Matrix.ext` at all.
- **`Fin`-vector `![…]` + `fin_cases` friction.** `fin_cases i` leaves the index as `⟨k, ⋯⟩` (a `Fin.mk`),
  so `Matrix.cons_val_one`/`_two`/… do not fire on the outer selection. Normalize first with
  `rw [show (⟨k, by omega⟩ : Fin n) = (k : Fin n) from rfl]`, then the `cons_val_*` simp set fires; or prove
  the components as separate `have`s and assemble with `funext i; fin_cases i`.
- **Matrix-apply `simp` fires in ISOLATION but "no progress" IN-CONTEXT when the index is typed at a
  DEPENDENT, non-syntactic-`succ` width** (e.g. `i : Fin (Wext M k)` / `Fin (Text M t k)`, defeq but not
  syntactic `Fin 2`/`Fin 1`). After `ext`/`fin_cases` the indices are `Fin.mk`s at the opaque width, so
  `Matrix.smul_apply`/`mul_apply`/`cons_val_*` don't fire, AND `Fin.zero_eta`/`Fin.mk_one` can't normalize
  (the width isn't a syntactic `n+1`), so `change`/`show` to a literal `Fin n` is unavailable. **Working
  pattern: prove each entry as a `have` at EXPLICIT `⟨_, by decide⟩` (or `by omega`) indices where the
  matrix-apply lemmas DO fire, then `exact` it into the `fin_cases` goal — `Fin` proof-irrelevance unifies
  the two index forms.** This is the recurring opaque-width cast quirk; it cost two tides on the (2,2,2)
  `chartParamsGen_eq_chartParams222` det bridge before the `have`+`exact` form landed it (2026-06-27,
  Codex-corroborated). Transfers to any entrywise identity over `chainA`/`GenBlk` dependent widths (the
  ∀M `φ_det_eq` lift).
- **`FactoredChain`/`Chain` projection mismatch (`c.Wwid` vs `c.toChain.Wwid`) breaks `HMul` instance
  synthesis** in products mixing the two structures' width fields — the dependent matrix-mul instance can't
  unify the two defeq-but-syntactically-distinct width projections. Resolve by **literal `Wext`/`Text`
  `let`-ascription** at the product (pin the widths to the concrete `Wext M k` / `Text M t k` form, cf.
  `Hmat_pivot`), or a generic `mul_three_reassoc'` whose abstract index types unify up to defeq. Side note:
  `omega` over `Text`/`Wext` arithmetic needs `k+1+1` normalized to `k+2` first. (Found in the ∀M interior
  witness build, 2026-06-27; recurs in any achiever-chart product mixing chain layers.)
- **`φ` (U+03C6) as a binder name can hit a lexer reject** (`unexpected token 'φ'; expected identifier`)
  when an editing tool inserts a confusable/variant codepoint. If a `∃ φ …` / `obtain ⟨φ, …⟩` line fails
  to parse despite looking right, rename the binder to ASCII (`phi`) or `ψ`; capital `Φ` (U+03A6) has not
  shown the problem. Cost two build cycles on `NoetherMonicPositioning.lean`.
- **No off-the-shelf rank-normal-form / "equal rank ⟹ equivalent matrices" in v4.29.** Built at the
  linear-map level in `Core.FibreNormalForm` (`exists_conj`, `exists_baseChange_of_rank_eq`): for a
  rank-`r` `f : (Fin n → k) →ₗ (Fin m → k)`, restrict to `fU : U ≃ range f` (`U` a `ker`-complement,
  via `Submodule.quotientEquivOfIsCompl _.symm ≪≫ LinearMap.quotKerEquivRange`); two maps with equal
  ker+range finrank are conjugate (`prodEquivOfIsCompl` kernel/range decompositions glued by
  `LinearEquiv.ofFinrankEq`), transferred to matrices by `LinearMap.toMatrix'_comp` +
  `LinearMap.toMatrix'_toLin'`. Useful `rfl`s: `Matrix.rank A = finrank (range (toLin' A))` and
  `toLin' A = A.mulVecLin`. The `IsCompl` finrank lemma is `Submodule.finrank_add_eq_of_isCompl`.
- **`RingEquiv.height_comap` is the clean `Ideal.height` transport** (`(I.comap e).height = I.height`,
  any ideal, no `IsPrime`). For codim-invariance of a locus under a *linear* coordinate change, the
  set-level route `vanishingIdeal (shifted) = comap (algEquiv) (vanishingIdeal)` + `height_comap` is
  cleaner than re-deriving an `Ideal.map` identity. Used in `Core.FibreNormalForm.codimRep_baseChange_image`
  — this closes the linear-coordinate-invariance gap `Core.OrbitCodim`'s docstring flagged, for the
  base-change family of isos.
- **The end-factor (`GL_{d_N}×GL_{d_0}`) action is just `Core.BaseChange.baseChange` with inner units
  `= 1`.** No new action needed: mult-equivariance `mult (P•A) = P_N·(mult A)·(P_0)⁻¹` is
  `mult_eq_submult` + the LANDED `submult_smul` at the full interval `(0, last)`. Caveat: the
  same-rank ⟹ same-fibre-codim headline genuinely needs `N ≥ 1` (`hN : (0 : Fin (N+1)) ≠ Fin.last N`)
  — for `N = 0` `mult` is the constant `1`, the end vertices coincide, the action only conjugates, and
  the claim is false.

## θ-count discharge findings (`Core.CCodimCornerMono`, thread 06)
- **The θ-count headline reduces to ONE combinatorial inequality**: the dimension-monotonicity of
  `cCodim · 0` (`cCodim e 0 ≤ cCodim e' 0` for `e ≤ e'`, + a strict all-vertex version). Both gating
  bricks (`hLowerBound`, `hRecover`) discharge from it via the LANDED rank-shift `cCodim d t = cCodim
  (d−t) 0` + the Gabriel→Kostant bridge `gabrielPartition` (a tuple's `kostantArrayOfRank (rankFn ·)`
  recast into the `CTheta` `Fin × Fin → ℕ` encoding via `finArrayOfSupp`).
- **The right construction for the dimension-monotonicity is the SHORTEST-interval split** (at an
  over-covered vertex `k`, split the shortest `[i,j] ∋ k` into `[i,k−1]+[k+1,j]`): verified to never
  increase `codimForm` (199/199), whereas splitting a non-shortest interval CAN increase it. The
  merge-up route (raise the corner per-partition) is DEAD — corner-`s` partitions often admit no
  corner-raise with non-increasing `codimForm` (71/252).
- **Strict SINGLE-vertex dimension-mono is FALSE** (e.g. `cCodim [1,1,0] 0 = cCodim [1,2,0] 0 = 0`);
  only the strict ALL-vertex version holds (`d−r < d−s` everywhere when `r > s`). Strict corner-
  monotonicity (needed for `hRecover`'s "corner = r") rides on the all-vertex strict version.
- **`codimForm` is the type-A `Ext`-pairing form**: reindexed, `= ∑_{A=[a,b],B=[c,e]: a<c≤b+1, b<e}
  m̄(A) m̄(B)`. The split delta is `∑_B coeff(B) m̄(B)` with the positive-coeff `B` being the shorter
  intervals covering `k` (absent when `I` is shortest). `codimForm` is also corner-blind
  (`codimForm_update_corner`, LANDED) — it never reads `m_{0N}`.

## `cCodim·0` weak monotonicity LANDED (`Core.CCodimZeroMono`, thread 07)
- **`cCodim_zero_mono` is PROVED sorry-free** (`e ≤ e' ⟹ cCodim e 0 ≤ cCodim e' 0`), discharging the
  weak gating hypothesis `hMono`. The θ-count headline is now `numTop_eq_ncard_topComponents_of_strict`
  — UNCONDITIONAL except for the strict `hMonoStrict`. Axiom-clean `[propext, Classical.choice,
  Quot.sound]`. `hLowerBound` is fully unconditional.
- **Reusable infrastructure** (all in `CCodimZeroMono`, built on `CThetaQIPConverse`'s `codimBil`):
  `codimBil_extendℤ_boxℤ_right`/`_left` (univ-sum collapse of `codimBil` vs a single box, via the
  clamped `rrInd`/`llInd` indicators), `codimBil_boxℤ_boxℤ` (the box-pairing value), `codimForm_add`
  (reused), `codimForm_congr_onbox` (codimForm reads only on-box values).
- **Four atomic shortest-split moves**, each with delta / sign / `_le` / `_cover` / `_mem`: interior
  `redMove` (`c = b+2` gap kills the self-term), `leftShrink` (omit left endpoint; handles `a=0` and
  singleton-via-empty-piece), `rightShrink` (omit right endpoint; handles `d'=N`), `removeMove`
  (singleton removal; coefficient ALWAYS `≤ 0`). Boundary lesson: there is NO `Fin` `b` with `b+1 = 0`,
  so `k=0` left-endpoint and `k=N` right-endpoint genuinely need the dedicated shrink moves (the
  interior `redMove`'s empty-piece guard `a≤b` can't be made false when `a=0`). `reduceStep` dispatches
  by `k`'s position; `exists_le_codimForm` is the recursion (strong induction on `∑ e'`).
## `cCodim·0` strict monotonicity LANDED → θ UNCONDITIONAL (`Core.CCodimZeroStrict`, thread 08)
- **`cCodim_zero_strict` is PROVED sorry-free** (`(∀ v, e v < e' v) → cCodim e 0 < cCodim e' 0`),
  discharging `hMonoStrict`. **`numTop_eq_ncard_topComponents` is now UNCONDITIONAL** (`θ =
  #top-dimensional irreducible components of Σ̄^r`, no open hypothesis); axiom-clean `[propext,
  Classical.choice, Quot.sound]`.
- **Route B (the landed route), reusing the four atomic moves + their `_le` sign lemmas:**
  - **Double sum** `codimForm_extendℤ_eq_sum_pairs`: `codimForm (extendℤ m) = ∑_{A,B} m(A) m(B) ·
    [pairBox A B]` (built from `codimBil_sum_right` + `codimBil_const_mul_right` + the existing
    right-rectangle collapse; `rrInd (B.1)(B.2) A ↔ pairBox A B` on the box). Gives `∃ active pair ⟺
    codimForm ≥ 1` (`codimForm_extendℤ_pos_of_exists_pair` / `exists_pair_of_codimForm_pos`).
  - **Lemma Y** `codimForm_extendℤ_pos_of_fullCover`: full coverage ⟹ `codimForm ≥ 1`, via the
    extremal longest-`[0,b]` argument (`b<N` from corner-`0`; maximality forces `c≥1` so `[0,b]→[c,d]`
    pairs).
  - **Lemma X** `reduceStep_strict`: select the active pair minimising `min(ilen A, ilen B)`; split the
    shorter member at the partner-adjacent vertex. **ClaimA** (`claimA_left`/`claimA_right`) — that
    member is shortest *active* covering that vertex — is the one non-mechanical step (the `y<d` vs
    `d≤y` / `a<x` vs `x≤a` interval-arithmetic case split; minimality MUST be over the shorter member,
    Codex-confirmed). The partner sits at split-coefficient EXACTLY `−1` (`splitCoeff_partner_le` &c.,
    `omega` on indicators), and `sum_coeff_le_neg_one` upgrades the `_le` ("≤0") to `_lt` ("≤ −1").
    8-way dispatch (left/right member × interior/leftShrink/rightShrink/removeMove); each move has TWO
    partner orientations (the partner can sit left or right of the split source).
  - **Wiring** (`cCodim_zero_strict`): a minimiser `m'` of `cCodim e' 0` is full-coverage (Lemma Y ⟹
    `codimForm ≥ 1`); `reduceStep_strict` drops it `≥ 1` to a partition of `e'` decremented at `k`,
    which still dominates `e` (`e ≤ e''` since `e < e'` everywhere), so LANDED `exists_le_codimForm`
    gives `cCodim e 0 ≤ cCodim e' 0 − 1`. (No `+1`-step vector needed — the minimiser-of-`e'` route is
    cleaner and uses only the two given nonemptiness hypotheses.)
  - RULED OUT (don't re-explore): Route A (simple `Φ` with `codimForm ≥ Φ ≥ cCodim+1`) — the gap is
    often exactly 1, no simple `Φ` carries it; every deterministic LOCAL step-selection rule fails —
    the strict step's location is config-dependent (the "involved-in-a-pair + extremal-by-length"
    refinement is load-bearing).
- **Dependent-dimension matrix reassociation / cast handling — the kernel that cracked the `prodAux`
  front-peel (deferred twice).** For products over `Fin (M k)`-style dependent dimensions:
  (i) `rw [Matrix.mul_assoc]` / `simp` / `conv` will NOT match `(a*b)*c = a*(b*c)` through the dependent
  `HMul` instance (higher-order matching fails). Close it with a **fully-applied term** instead:
  `set X := …; set Y := …; exact Matrix.mul_assoc a X Y` (or state a generic
  `mul_three_reassoc {p q r s : Type*} [Fintype …] (a b c) : a*b*c = a*(b*c) := Matrix.mul_assoc a b c`
  once and reuse — cf. `RouteMFrontPeel.mul_three_reassoc`, generalising `DeepestTelescoping.mul_four_reassoc`).
  (ii) Do cast bookkeeping at the **equiv level, never entrywise** (`ext` into a cast-wrapped `∑ if…` is the
  trap that stalled two tides): `finCongr_refl` collapses `finCongr (rfl-true width eq)` to `Equiv.refl`,
  then `Matrix.reindex_refl_refl` (via `erw` — plain `rw`/`simp` won't match the dependent `Matrix.reindex`)
  collapses `reindex refl refl` to identity; `RouteMAchieverBridge.reindex_finCongr_mul` distributes a
  width-reindex over a product. (iii) Peel layer-products by **prefix-length induction reusing
  `prodAux_succ`**, not entrywise. This kernel transfers to any `prod`/`prodAux` reassociation (e.g. the
  L2/D1 `endpoint_telescoping`).

exec
/bin/bash -lc "sed -n '1,160p' lean/DLNFibre/DLN/RLCT/Validate/RouteMBInterface.lean" in /home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/agent-a9bb11c22680d93d4
 succeeded in 0ms:
import DLNFibre.DLN.RLCT.Validate.RouteMRadialComp
import DLNFibre.DLN.RLCT.Validate.RouteMBFactorsDet
import DLNFibre.DLN.RLCT.Validate.RouteMFlatLive

/-!
# `RouteMBInterface` — the frozen B-interface: the boundary factor `B` + its map-identity contract

The FROZEN interface between the BFactors construction (the formaliser's (a)+(b): the per-bdy CLEs
`ρ`/`E` + the `BFactors` list) and the headline wiring (the controller's (c): the map identity + the
final `det_comp`). Route #1 (`φ = B ∘ pivotBlowupOn(active,p)`, 2nd-eye-cleared): the chart factors
through the radial arrow, and the boundary factor `B = composeFold BFactors` is a `ChartFactor`-fold
of the per-boundary Schur/chain/LDU factors, each conjugated by a `chartIdxEquiv`-derived CLE
(`RouteMRoleCLE.flatBlockSplitCLE` + the engine-reshape `RouteMEngineReshape`).

This module FREEZES that interface as a `structure BData` bundling:
- `B` — the boundary factor map (the formaliser's `composeFold BFactors`);
- `DB` — its fderiv (`(foldDerivList BFactors u).prod`, FREE via `composeFold_hasFDerivAt`);
- `hasDB` — `HasFDerivAt B DB` (obligation (2));
- `hmap` — the MAP identity `φ = B ∘ pivotBlowupOn active structPivot` (obligation (1), discharged
  per-block via `schurFrameProd_block_*` + `pivotBlowupOn_apply`);
- `hdet` — `|det DB| = ∏ engine` (obligation (3), banked `foldDerivList_abs_det_perBoundary`).

Given a `BData`, the headline follows by `radialComp_abs_det` (the banked wiring) —
`interiorDet_headline_of_BData` below; the formaliser builds the `BData` instance. The interface
decouples the two: each side builds against `BData`'s fields without waiting on the other.

* `BData` — the frozen interface structure.
* `interiorDet_headline_of_BData` — the unconditional interior-det headline from a `BData` (WIRING:
  `radialComp_abs_det` + the bundled obligations). The LAST step once a `BData` is constructed.

Axiom-clean `[propext, Classical.choice, Quot.sound]` (the banked wiring; no analysis beyond it).
-/

open scoped BigOperators

noncomputable section

namespace DLNFibre.DLN.RLCT

variable {L : ℕ}

/-- **The frozen B-interface.** Bundles the boundary factor `B` (= `composeFold BFactors`), its
fderiv `DB`, obligation (2) `HasFDerivAt B DB`, obligation (1) map identity `φ = B ∘ pivotBlowupOn`,
and obligation (3) boundary det `|det DB| = ∏ engine` — at the achiever radial active set
(`p ∈ active`, `active.card = minAdm`). The formaliser constructs an instance (the (a)+(b) work);
headline is read off it by `interiorDet_headline_of_BData`. `engine s` is the per-boundary value
`|det K_s|^{r_s+c_s}·∏_i|q_{s,i}|^{2(t_s−1−i)}`. -/
structure BData (M t : Fin (L + 1) → ℕ) (ha : StructAdm M t) (hN : 0 < routeMAmbient M) (p : ℕ)
    (hp1 : Text M t (p + 1) ≤ Text M t p) (hp2 : Text M t (p + 1) ≤ Wext M p)
    (rfin : (Fin (routeMAmbient M) → ℝ) → Matrix (Fin (Text M t L)) (Fin (Wext M L)) ℝ)
    (u : Fin (routeMAmbient M) → ℝ) where
  /-- The radial active set (the pivot + the `u`-scaled `R`/`Rfin` free coords). -/
  active : Finset (Fin (routeMAmbient M))
  /-- The pivot is in the active set. -/
  hp_mem : structPivot M hN ∈ active
  /-- The active set has cardinality `minAdm` (the banked count). -/
  hcard : active.card = minAdm M
  /-- The boundary factor map `B = composeFold BFactors`. -/
  B : (Fin (routeMAmbient M) → ℝ) → (Fin (routeMAmbient M) → ℝ)
  /-- `B`'s fderiv at the blown-up point (`(foldDerivList BFactors _).prod`). -/
  DB : (Fin (routeMAmbient M) → ℝ) →L[ℝ] (Fin (routeMAmbient M) → ℝ)
  /-- Obligation (2): `B` has fderiv `DB` at the blown-up point. -/
  hasDB : HasFDerivAt B DB (pivotBlowupOn active (structPivot M hN) u)
  /-- Obligation (1): the MAP identity `φ = B ∘ pivotBlowupOn active structPivot`. -/
  hmap : phiFlatLiveR1 M t ha hN p hp1 hp2 rfin
    = B ∘ pivotBlowupOn active (structPivot M hN)
  /-- The per-boundary engine values `|det K_s|^{r_s+c_s}·∏_i|q_{s,i}|^{2(t_s−1−i)}`. -/
  engine : Fin L → ℝ
  /-- Obligation (3): the boundary factor's det is the engine product. -/
  hdet : |LinearMap.det DB.toLinearMap| = ∏ s : Fin L, engine s

/-- **The unconditional interior-det headline from a `BData`** (the WIRING, obligation (c)). Given
frozen `BData` (the formaliser's instance), the chart's Jacobian abs-det factorizes as
`|u_p|^{minAdm−1} · ∏_s engine s`. Reads off `radialComp_abs_det` (the banked route-#1 wiring) + the
bundled obligations (2)/(1)/(3). The LAST step of the interior-det leg. -/
theorem interiorDet_headline_of_BData (M t : Fin (L + 1) → ℕ) (ha : StructAdm M t)
    (hN : 0 < routeMAmbient M) (p : ℕ)
    (hp1 : Text M t (p + 1) ≤ Text M t p) (hp2 : Text M t (p + 1) ≤ Wext M p)
    (rfin : (Fin (routeMAmbient M) → ℝ) → Matrix (Fin (Text M t L)) (Fin (Wext M L)) ℝ)
    (u : Fin (routeMAmbient M) → ℝ) (d : BData M t ha hN p hp1 hp2 rfin u) :
    |LinearMap.det (fderiv ℝ (phiFlatLiveR1 M t ha hN p hp1 hp2 rfin) u).toLinearMap|
      = |u (structPivot M hN)| ^ (minAdm M - 1) * ∏ s : Fin L, d.engine s := by
  rw [radialComp_abs_det M hN d.active d.hp_mem d.hcard d.B
      (phiFlatLiveR1 M t ha hN p hp1 hp2 rfin) u d.DB d.hmap d.hasDB, d.hdet]

end DLNFibre.DLN.RLCT

end

exec
/bin/bash -lc "sed -n '1,220p' lean/DLNFibre/DLN/RLCT/Validate/RouteMFlatStructV.lean" in /home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/agent-a9bb11c22680d93d4
 succeeded in 0ms:
import DLNFibre.DLN.RLCT.Validate.RouteMGenFlatStruct

/-!
# `RouteMFlatStructV` — the VECTOR-parametrized structured achiever chart + its rate (∀M)

`RouteMGenFlatStruct` banks the structured decoder `genBlkFlatStruct M t ha x` (reading free
Schur/lift coords from a flat vector `x` via disjoint `chartIdxEquiv` role slots) but exposes the rate
only for the CONSTANT-radius diagonal `phiFlatStruct M t ha u = phiGen u M t (genBlkFlatStruct M t ha
(fun _ => u)) …` — a one-parameter family, not a full chart map.

This module lifts the rate to a genuine **full chart map** `phiFlatStructV M t ha : (Fin N → ℝ) →
(Fin N → ℝ)`, reading the radial pivot as the scalar coordinate `x p` (`p = ⟨0,_⟩`) and the block data
from the SAME vector `x`. The decoder-agnostic engine `routeMCore_phiGen` consumes only the block data
+ `hC0`, and the identity-boundary `C 0 = 1` reads only the x-INDEPENDENT constants `Bmat 0 = reindex 1`,
`Rmat 0 = 0`, so it holds for arbitrary `x` (and arbitrary scalar `v`, since `v • Rmat 0 = 0`). Hence
the rate transfers ∀M to the vector chart with NO bridge:

  `routeMCore M (phiFlatStructV M t ha x) = (x p)² · VvalGen (x p) M t (genBlkFlatStruct M t ha x) hle`.

This is the `NodeAchieverChart.leaf_integrand` rate factor `routeMCore (phi u) = (u p)² · Ufun(u)` for
arbitrary `M` (`Ufun := VvalGen (x p) …`). The determinant `cov` field is the genuinely hard piece (the
factored telescope) and is handled separately.

Axiom-clean `[propext, Classical.choice, Quot.sound]` (pure matrix algebra / finite equivalences).
-/

namespace DLNFibre.DLN.RLCT

open Matrix

variable {L : ℕ}

/-! ## The identity-boundary `C 0 = 1` for a GENERAL decoder argument + scalar

`C0_eq_one` (`RouteMGenFlatStruct`) proves `C 0 = 1` for `genBlkFlatStruct M t ha (fun _ => u)`; its
proof reads only `.Bmat 0 = reindex 1` and `.Rmat 0 = 0` (both x-independent), plus `v • Rmat 0 = 0`.
The same proof works verbatim for an arbitrary decoder argument `x` and an arbitrary scalar `v`. -/

/-- **The identity boundary `C 0 = 1`** (general decoder argument `x`, general scalar `v`): the proof of
`C0_eq_one` reads only the x-independent boundary constants `Bmat 0 = reindex 1`, `Rmat 0 = 0`, so it
holds for any `x` and any `v` (since `v • Rmat 0 = 0`). -/
theorem C0_eq_one_gen (M t : Fin (L + 1) → ℕ) (ha : StructAdm M t)
    (v : ℝ) (x : Fin (routeMAmbient M) → ℝ) :
    (chainOfMt v M t (genBlkFlatStruct M t ha x) (hleStruct M t ha)).toChain.C 0
      = (1 : Matrix (Fin (Text M t 0)) (Fin (Text M t 0)) ℝ) := by
  rw [chainOfMt_C_zero v M t _ (hleStruct M t ha) ha.hL,
    show (genBlkFlatStruct M t ha x).Rmat 0 = 0 from rfl, smul_zero, add_zero]
  have h1W : Text M t 1 = Wext M 0 := Wext0_eq_Text1 M t ha
  have hBmat : (genBlkFlatStruct M t ha x).Bmat 0
      = Matrix.reindex (Equiv.refl _) (finCongr (Text0_eq_Text1_struct M t ha.h0))
          (1 : Matrix (Fin (Text M t 0)) (Fin (Text M t 0)) ℝ) := rfl
  rw [hBmat]
  ext i j
  rw [Matrix.mul_apply, Finset.sum_eq_single (Fin.cast (Text0_eq_Text1_struct M t ha.h0) i)]
  · rw [Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.refl_symm, Equiv.refl_apply,
      finCongr_symm, finCongr_apply, Fin.cast_cast, Fin.cast_eq_self, Matrix.one_apply_eq, one_mul]
    have hjcol : (j : Fin (Wext M 0)) = Fin.cast (genWidthEq M t (hleStruct M t ha) 0 ha.hL)
        (Fin.castAdd (Wext M 0 - Text M t (0 + 1)) (Fin.cast h1W.symm j)) := by
      apply Fin.ext; simp
    rw [hjcol, chainQ_apply_castAdd, Matrix.one_apply, Matrix.one_apply]
    by_cases h : (i : ℕ) = (j : ℕ)
    · rw [if_pos (by apply Fin.ext; simpa using h), if_pos (by apply Fin.ext; simpa using h)]
    · rw [if_neg (by intro hc; exact h (by simpa using congrArg Fin.val hc)),
        if_neg (by intro hc; exact h (by simpa using congrArg Fin.val hc))]
  · intro b _ hb
    rw [Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.refl_symm, Equiv.refl_apply,
      finCongr_symm, finCongr_apply]
    rw [show (1 : Matrix (Fin (Text M t 0)) (Fin (Text M t 0)) ℝ) i
          (Fin.cast (Text0_eq_Text1_struct M t ha.h0).symm b) = 0 from by
      rw [Matrix.one_apply, if_neg]; intro hc; apply hb; rw [hc]; apply Fin.ext; simp]
    rw [zero_mul]
  · intro hi; exact absurd (Finset.mem_univ _) hi

/-- **`hC0` for the structured decoder at a general `x` + scalar `v`**: `C 0 · suffix 0 = suffix 0`
(`C 0 = 1`). -/
theorem hC0_struct_gen (M t : Fin (L + 1) → ℕ) (ha : StructAdm M t)
    (v : ℝ) (x : Fin (routeMAmbient M) → ℝ) :
    (chainOfMt v M t (genBlkFlatStruct M t ha x) (hleStruct M t ha)).toChain.C 0
        * (chainOfMt v M t (genBlkFlatStruct M t ha x)
            (hleStruct M t ha)).toChain.suffix 0 (Nat.zero_le L)
      = (chainOfMt v M t (genBlkFlatStruct M t ha x)
          (hleStruct M t ha)).toChain.suffix 0 (Nat.zero_le L) := by
  rw [C0_eq_one_gen M t ha v x]
  exact Matrix.one_mul _

/-! ## The vector-parametrized structured chart + its rate -/

/-- The binding radial pivot axis `p = ⟨0,_⟩` of the structured chart (the radial scalar coordinate). -/
def structPivot (M : Fin (L + 1) → ℕ) (hN : 0 < routeMAmbient M) : Fin (routeMAmbient M) := ⟨0, hN⟩

/-- **The vector-parametrized structured achiever chart** `phiFlatStructV M t ha hN x := paramsEquivFlat
∘ chartParamsGen (x p) ∘ genBlkFlatStruct x` — a genuine full chart map `(Fin N → ℝ) → (Fin N → ℝ)`,
with the radial scalar read as the pivot coordinate `x p` and the block data from the same `x`. -/
noncomputable def phiFlatStructV (M t : Fin (L + 1) → ℕ) (ha : StructAdm M t)
    (hN : 0 < routeMAmbient M) (x : Fin (routeMAmbient M) → ℝ) : Fin (routeMAmbient M) → ℝ :=
  phiGen (x (structPivot M hN)) M t (genBlkFlatStruct M t ha x) (hleStruct M t ha)

/-- The rate-quotient unit factor `UvalStructV x := VvalGen (x p) M t (genBlkFlatStruct M t ha x) hle`
— the radial quotient `routeMCore (phiFlatStructV x) / (x p)²` of the rate `routeMCore = (x p)² · U`.
A telescoped squared norm `‖reindex (Hmat 0)‖²`. NB it is NOT in general `(x p)`-free: `VvalGen` reads
the radial scalar `x p` (through `Hmat 0`'s dependence on the chain's `C`-layers, which carry `(x p) •
Rmat`). The `(4,4,2,2)` pure-radial-blow-up instance `Uval4422` IS pivot-free, but the general
structured chart does not inherit that; the `leaf_integrand`/`Ubound` interface only needs `U ≤ B` on
the box + `U > 0` a.e., neither requiring pivot-freeness. -/
noncomputable def UvalStructV (M t : Fin (L + 1) → ℕ) (ha : StructAdm M t)
    (hN : 0 < routeMAmbient M) (x : Fin (routeMAmbient M) → ℝ) : ℝ :=
  VvalGen (x (structPivot M hN)) M t (genBlkFlatStruct M t ha x) (hleStruct M t ha)

/-- **The rate transfers to the vector chart ∀M (NO bridge)**: `routeMCore M (phiFlatStructV x) =
(x p)² · UvalStructV x`, directly from the decoder-agnostic `routeMCore_phiGen` + the general-`x`
identity-boundary `hC0_struct_gen`. This is the `NodeAchieverChart.leaf_integrand` rate factor for
arbitrary `M`. -/
theorem routeMCore_phiFlatStructV (M t : Fin (L + 1) → ℕ) (ha : StructAdm M t)
    (hN : 0 < routeMAmbient M) (x : Fin (routeMAmbient M) → ℝ) :
    routeMCore M (phiFlatStructV M t ha hN x)
      = (x (structPivot M hN)) ^ 2 * UvalStructV M t ha hN x :=
  routeMCore_phiGen (x (structPivot M hN)) M t (genBlkFlatStruct M t ha x) (hleStruct M t ha)
    (hC0_struct_gen M t ha (x (structPivot M hN)) x)

end DLNFibre.DLN.RLCT

exec
/bin/bash -lc 'rg --files lean/DLNFibre/DLN/RLCT/Validate' in /home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/agent-a9bb11c22680d93d4
 succeeded in 0ms:
lean/DLNFibre/DLN/RLCT/Validate/RouteMChainBlock.lean
lean/DLNFibre/DLN/RLCT/Validate/RouteM3333.lean
lean/DLNFibre/DLN/RLCT/Validate/RouteMAchieverVvalPoly.lean
lean/DLNFibre/DLN/RLCT/Validate/RouteM4422Hfin.lean
lean/DLNFibre/DLN/RLCT/Validate/RouteMFrameQM.lean
lean/DLNFibre/DLN/RLCT/Validate/RouteMFlatStructV.lean
lean/DLNFibre/DLN/RLCT/Validate/DeepestSplitSmooth.lean
lean/DLNFibre/DLN/RLCT/Validate/RouteM4422.lean
lean/DLNFibre/DLN/RLCT/Validate/RouteM4422Bridge.lean
lean/DLNFibre/DLN/RLCT/Validate/RouteMBridge.lean
lean/DLNFibre/DLN/RLCT/Validate/RouteMFrontBottleneck.lean
lean/DLNFibre/DLN/RLCT/Validate/RouteMAgenFDerivValue.lean
lean/DLNFibre/DLN/RLCT/Validate/RouteMInteriorContract.lean
lean/DLNFibre/DLN/RLCT/Validate/RouteM222StructAdm.lean
lean/DLNFibre/DLN/RLCT/Validate/Case222Algebra.lean
lean/DLNFibre/DLN/RLCT/Validate/RouteMAchieverPath.lean
lean/DLNFibre/DLN/RLCT/Validate/RouteMStairTwoSided.lean
lean/DLNFibre/DLN/RLCT/Validate/DeepestMinRlct.lean
lean/DLNFibre/DLN/RLCT/Validate/RouteMLocalityDet.lean
lean/DLNFibre/DLN/RLCT/Validate/Case222NodeDescent.lean
lean/DLNFibre/DLN/RLCT/Validate/RouteMSchurDepth2.lean
lean/DLNFibre/DLN/RLCT/Validate/RouteMGenFlatChart.lean
lean/DLNFibre/DLN/RLCT/Validate/NodeHomogeneity.lean
lean/DLNFibre/DLN/RLCT/Validate/RouteMRoleCLE.lean
lean/DLNFibre/DLN/RLCT/Validate/RouteMLayerGrade.lean
lean/DLNFibre/DLN/RLCT/Validate/RouteMChainAssembleDiff.lean
lean/DLNFibre/DLN/RLCT/Validate/DeepestRegSliceFderiv.lean
lean/DLNFibre/DLN/RLCT/Validate/RouteMState.lean
lean/DLNFibre/DLN/RLCT/Validate/RouteMSchurFrameDet.lean
lean/DLNFibre/DLN/RLCT/Validate/CascadeAchiever.lean
lean/DLNFibre/DLN/RLCT/Validate/DeepestBlockDecomp.lean
lean/DLNFibre/DLN/RLCT/Validate/RouteMConjBlock.lean
lean/DLNFibre/DLN/RLCT/Validate/RouteMChartIdx.lean
lean/DLNFibre/DLN/RLCT/Validate/RouteMAchieverStructAdm.lean
lean/DLNFibre/DLN/RLCT/Validate/RouteMBoundaryCleanU.lean
lean/DLNFibre/DLN/RLCT/Validate/Case111Bridge.lean
lean/DLNFibre/DLN/RLCT/Validate/DeepestCoreNonvanishing.lean
lean/DLNFibre/DLN/RLCT/Validate/RouteMChartIdxEquiv.lean
lean/DLNFibre/DLN/RLCT/Validate/RouteMStaircaseShear.lean
lean/DLNFibre/DLN/RLCT/Validate/DeepestGaugeChart.lean
lean/DLNFibre/DLN/RLCT/Validate/Case334RouteStep.lean
lean/DLNFibre/DLN/RLCT/Validate/RouteMAchieverForce.lean
lean/DLNFibre/DLN/RLCT/Validate/LossHomogeneity.lean
lean/DLNFibre/DLN/RLCT/Validate/RouteMLayerCover.lean
lean/DLNFibre/DLN/RLCT/Validate/RouteMLiveLocality.lean
lean/DLNFibre/DLN/RLCT/Validate/RouteMChartSlots.lean
lean/DLNFibre/DLN/RLCT/Validate/Case323RouteStep.lean
lean/DLNFibre/DLN/RLCT/Validate/RouteMRoleGrade.lean
lean/DLNFibre/DLN/RLCT/Validate/RouteMGeneralAssembly.lean
lean/DLNFibre/DLN/RLCT/Validate/DeepestPivotFrame.lean
lean/DLNFibre/DLN/RLCT/Validate/RouteMDecoderDiff.lean
lean/DLNFibre/DLN/RLCT/Validate/RouteMNodeDescentBuild.lean
lean/DLNFibre/DLN/RLCT/Validate/RouteMAchieverBridge.lean
lean/DLNFibre/DLN/RLCT/Validate/RouteMBData.lean
lean/DLNFibre/DLN/RLCT/Validate/RouteMFrameDiff.lean
lean/DLNFibre/DLN/RLCT/Validate/RouteMSmearedContract.lean
lean/DLNFibre/DLN/RLCT/Validate/RRR.lean
lean/DLNFibre/DLN/RLCT/Validate/Case222Cover.lean
lean/DLNFibre/DLN/RLCT/Validate/RouteMRadialComp.lean
lean/DLNFibre/DLN/RLCT/Validate/BindingRecursion.lean
lean/DLNFibre/DLN/RLCT/Validate/RouteMFrameLocality.lean
lean/DLNFibre/DLN/RLCT/Validate/DeepestFrame.lean
lean/DLNFibre/DLN/RLCT/Validate/RouteM334Ratiofin.lean
lean/DLNFibre/DLN/RLCT/Validate/Case222RouteStep.lean
lean/DLNFibre/DLN/RLCT/Validate/DeepestEFullSregComparability.lean
lean/DLNFibre/DLN/RLCT/Validate/Case222Rlct.lean
lean/DLNFibre/DLN/RLCT/Validate/RouteM121Smeared.lean
lean/DLNFibre/DLN/RLCT/Validate/RouteMChartFactorFold.lean
lean/DLNFibre/DLN/RLCT/Validate/DeepestSchurComparability.lean
lean/DLNFibre/DLN/RLCT/Validate/RouteMDeepBottleneck.lean
lean/DLNFibre/DLN/RLCT/Validate/RouteMBoundaryCleanRate.lean
lean/DLNFibre/DLN/RLCT/Validate/RouteMPhiFlatDet.lean
lean/DLNFibre/DLN/RLCT/Validate/RouteMFlatLDU.lean
lean/DLNFibre/DLN/RLCT/Validate/RouteMRecursion.lean
lean/DLNFibre/DLN/RLCT/Validate/Case222Value.lean
lean/DLNFibre/DLN/RLCT/Validate/Case222Lemma2.lean
lean/DLNFibre/DLN/RLCT/Validate/DeepestSplitConcrete.lean
lean/DLNFibre/DLN/RLCT/Validate/RouteMEngineReshape.lean
lean/DLNFibre/DLN/RLCT/Validate/RouteMLayerCoverGE.lean
lean/DLNFibre/DLN/RLCT/Validate/RouteMSchurAlg.lean
lean/DLNFibre/DLN/RLCT/Validate/RouteMAchieverTelescope.lean
lean/DLNFibre/DLN/RLCT/Validate/Case222Block.lean
lean/DLNFibre/DLN/RLCT/Validate/RouteMGradingObstruction.lean
lean/DLNFibre/DLN/RLCT/Validate/BindingArith.lean
lean/DLNFibre/DLN/RLCT/Validate/ResolutionAtlas.lean
lean/DLNFibre/DLN/RLCT/Validate/SchurNodeAssembly.lean
lean/DLNFibre/DLN/RLCT/Validate/RouteMAchieverWitnessInterior.lean
lean/DLNFibre/DLN/RLCT/Validate/RouteMSchur.lean
lean/DLNFibre/DLN/RLCT/Validate/RouteMFactorMaps.lean
lean/DLNFibre/DLN/RLCT/Validate/RouteMAchieverRateFields.lean
lean/DLNFibre/DLN/RLCT/Validate/RouteM231Smeared.lean
lean/DLNFibre/DLN/RLCT/Validate/RadialResidualPower.lean
lean/DLNFibre/DLN/RLCT/Validate/GeneralR1Recursion.lean
lean/DLNFibre/DLN/RLCT/Validate/RouteMAchieverGeneralDet.lean
lean/DLNFibre/DLN/RLCT/Validate/RouteMBoundaryCleanMinAdm.lean
lean/DLNFibre/DLN/RLCT/Validate/RouteMStairHeadline.lean
lean/DLNFibre/DLN/RLCT/Validate/Case212.lean
lean/DLNFibre/DLN/RLCT/Validate/DeepestGaugeConstruction.lean
lean/DLNFibre/DLN/RLCT/Validate/RouteMGenChartId3333.lean
lean/DLNFibre/DLN/RLCT/Validate/RouteMChainRate.lean
lean/DLNFibre/DLN/RLCT/Validate/RouteMLeaf.lean
lean/DLNFibre/DLN/RLCT/Validate/DeepestGaugeDiffeo.lean
lean/DLNFibre/DLN/RLCT/Validate/RouteMLinearFactor.lean
lean/DLNFibre/DLN/RLCT/Validate/RouteMBData222.lean
lean/DLNFibre/DLN/RLCT/Validate/RouteMSmearedGenRate.lean
lean/DLNFibre/DLN/RLCT/Validate/RouteMCoverLemmas.lean
lean/DLNFibre/DLN/RLCT/Validate/RouteMGenChartId.lean
lean/DLNFibre/DLN/RLCT/Validate/RouteM3333Atom.lean
lean/DLNFibre/DLN/RLCT/Validate/RouteMScaffold.lean
lean/DLNFibre/DLN/RLCT/Validate/NodeAchieverChart.lean
lean/DLNFibre/DLN/RLCT/Validate/RouteMSchurShear.lean
lean/DLNFibre/DLN/RLCT/Validate/DeepestSchurShift.lean
lean/DLNFibre/DLN/RLCT/Validate/DeepestRegBlockInvertible.lean
lean/DLNFibre/DLN/RLCT/Validate/FrontPivotWLOG.lean
lean/DLNFibre/DLN/RLCT/Validate/RouteMChainVar.lean
lean/DLNFibre/DLN/RLCT/Validate/RouteMChainFDerivValue.lean
lean/DLNFibre/DLN/RLCT/Validate/Case222CoverGE.lean
lean/DLNFibre/DLN/RLCT/Validate/RouteMNodeDescent.lean
lean/DLNFibre/DLN/RLCT/Validate/RouteMFactorFDeriv.lean
lean/DLNFibre/DLN/RLCT/Validate/DeepestRegAbsorbIFT.lean
lean/DLNFibre/DLN/RLCT/Validate/DeepestFramedProductPivot.lean
lean/DLNFibre/DLN/RLCT/Validate/RouteMLayerCoverGEL2.lean
lean/DLNFibre/DLN/RLCT/Validate/RouteMGenChain.lean
lean/DLNFibre/DLN/RLCT/Validate/RouteMCLEConj.lean
lean/DLNFibre/DLN/RLCT/Validate/RouteMSchurCorank3.lean
lean/DLNFibre/DLN/RLCT/Validate/RouteM222Det.lean
lean/DLNFibre/DLN/RLCT/Validate/RouteMBoundaryClass.lean
lean/DLNFibre/DLN/RLCT/Validate/RouteMStairTwoSidedHeadline.lean
lean/DLNFibre/DLN/RLCT/Validate/RouteMStaircaseDet.lean
lean/DLNFibre/DLN/RLCT/Validate/DeepestRegSliceFderivPivot.lean
lean/DLNFibre/DLN/RLCT/Validate/DeepestTelescoping.lean
lean/DLNFibre/DLN/RLCT/Validate/Case222CoverGETail.lean
lean/DLNFibre/DLN/RLCT/Validate/RouteMBudget.lean
lean/DLNFibre/DLN/RLCT/Validate/Case222Resolution.lean
lean/DLNFibre/DLN/RLCT/Validate/RouteMChartDiff.lean
lean/DLNFibre/DLN/RLCT/Validate/MinAdmMono.lean
lean/DLNFibre/DLN/RLCT/Validate/RouteM3333Det.lean
lean/DLNFibre/DLN/RLCT/Validate/BindingSpine.lean
lean/DLNFibre/DLN/RLCT/Validate/RouteMBoundaryCleanChartFull.lean
lean/DLNFibre/DLN/RLCT/Validate/DeepestDiffeoBridge.lean
lean/DLNFibre/DLN/RLCT/Validate/DeepestFramedProduct.lean
lean/DLNFibre/DLN/RLCT/Validate/DeepestGermCharge.lean
lean/DLNFibre/DLN/RLCT/Validate/MatMulFibre.lean
lean/DLNFibre/DLN/RLCT/Validate/DeepestBaseL1.lean
lean/DLNFibre/DLN/RLCT/Validate/RouteMInteriorDetHeadline.lean
lean/DLNFibre/DLN/RLCT/Validate/MvalMultSum.lean
lean/DLNFibre/DLN/RLCT/Validate/Case222RouteMValidation.lean
lean/DLNFibre/DLN/RLCT/Validate/RouteMGenChainBridge.lean
lean/DLNFibre/DLN/RLCT/Validate/RouteMChainDiff.lean
lean/DLNFibre/DLN/RLCT/Validate/RouteMFlatLive.lean
lean/DLNFibre/DLN/RLCT/Validate/RouteMBridgeCLE.lean
lean/DLNFibre/DLN/RLCT/Validate/RouteMBoundaryCleanChart.lean
lean/DLNFibre/DLN/RLCT/Validate/RouteMGenFlatStruct.lean
lean/DLNFibre/DLN/RLCT/Validate/RouteMBranch.lean
lean/DLNFibre/DLN/RLCT/Validate/RouteMChartIdxCard.lean
lean/DLNFibre/DLN/RLCT/Validate/RouteMSlotId.lean
lean/DLNFibre/DLN/RLCT/Validate/RouteM132Smeared.lean
lean/DLNFibre/DLN/RLCT/Validate/DeepestNormalFormWiring.lean
lean/DLNFibre/DLN/RLCT/Validate/RouteMValue.lean
lean/DLNFibre/DLN/RLCT/Validate/RouteMExtraction.lean
lean/DLNFibre/DLN/RLCT/Validate/DeepestSchurSmooth.lean
lean/DLNFibre/DLN/RLCT/Validate/RouteMBranchRead.lean
lean/DLNFibre/DLN/RLCT/Validate/RouteMKLens.lean
lean/DLNFibre/DLN/RLCT/Validate/RouteMNReg.lean
lean/DLNFibre/DLN/RLCT/Validate/RouteMClassify.lean
lean/DLNFibre/DLN/RLCT/Validate/Case222RouteMCover.lean
lean/DLNFibre/DLN/RLCT/Validate/RouteMFactoredChain.lean
lean/DLNFibre/DLN/RLCT/Validate/RouteMStairFold.lean
lean/DLNFibre/DLN/RLCT/Validate/DeepestSplitReindex.lean
lean/DLNFibre/DLN/RLCT/Validate/DeepestCompositionE1.lean
lean/DLNFibre/DLN/RLCT/Validate/RouteMPhiTargetDet.lean
lean/DLNFibre/DLN/RLCT/Validate/RouteMLayerSplit.lean
lean/DLNFibre/DLN/RLCT/Validate/RouteMChainRateValid.lean
lean/DLNFibre/DLN/RLCT/Validate/RouteMAchieverDispatch.lean
lean/DLNFibre/DLN/RLCT/Validate/RouteMInteriorDet.lean
lean/DLNFibre/DLN/RLCT/Validate/DeepestFrameRaw.lean
lean/DLNFibre/DLN/RLCT/Validate/RouteMCardBridge.lean
lean/DLNFibre/DLN/RLCT/Validate/RouteMRadialFactor.lean
lean/DLNFibre/DLN/RLCT/Validate/RouteM334Hfin.lean
lean/DLNFibre/DLN/RLCT/Validate/RouteMBInterface.lean
lean/DLNFibre/DLN/RLCT/Validate/SchurState.lean
lean/DLNFibre/DLN/RLCT/Validate/Case111.lean
lean/DLNFibre/DLN/RLCT/Validate/RouteMGenLeafIntegrand.lean
lean/DLNFibre/DLN/RLCT/Validate/RouteMSuffixBridge.lean
lean/DLNFibre/DLN/RLCT/Validate/RouteMLayerValue.lean
lean/DLNFibre/DLN/RLCT/Validate/DeepestGaugeBlocks.lean
lean/DLNFibre/DLN/RLCT/Validate/FrontPivotProducer.lean
lean/DLNFibre/DLN/RLCT/Validate/RouteMColumnFactor.lean
lean/DLNFibre/DLN/RLCT/Validate/RouteM221.lean
lean/DLNFibre/DLN/RLCT/Validate/DeepestPsiLens.lean
lean/DLNFibre/DLN/RLCT/Validate/RouteMO1Bridge.lean
lean/DLNFibre/DLN/RLCT/Validate/RouteMChainFactor.lean
lean/DLNFibre/DLN/RLCT/Validate/RouteMShearDet.lean
lean/DLNFibre/DLN/RLCT/Validate/RouteMSchurValue.lean
lean/DLNFibre/DLN/RLCT/Validate/RouteMBFactorsDet.lean
lean/DLNFibre/DLN/RLCT/Validate/RouteMChainBlockValid.lean
lean/DLNFibre/DLN/RLCT/Validate/RouteMFrontPeel.lean
lean/DLNFibre/DLN/RLCT/Validate/RouteMInteriorDetReal.lean

exec
/bin/bash -lc "sed -n '1,240p' lean/DLNFibre/DLN/RLCT/Validate/RouteMFlatLive.lean" in /home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/agent-a9bb11c22680d93d4
 succeeded in 0ms:
import DLNFibre.DLN.RLCT.Validate.RouteMKLens
import DLNFibre.DLN.RLCT.Validate.RouteMAchieverWitnessInterior

/-!
# `RouteMFlatLive` — the LIVE-leaf structured achiever decoder + its decoder-agnostic rate (∀M)

The DET-route decoder for the interior branch. The radial-separability certificate + the verified
`(3,3,3,3)` monomial det `|u0|^5·|u1|^4·|u4|^2·|u9|^3` are for the LIVE-leaf `B_det` family (`Rfin ≠ 0`,
the leaf block FREE); the dead-leaf `genBlkFlatStruct` (`Rfin := 0`) gives the WRONG radial exponent
`q = #interior-E-blocks ≠ minAdm − 1` (Codex-confirmed: at `(3,3,3,3)`, `q = 3` but `minAdm − 1 = 5`). So
the interior chart's determinant genuinely needs the live leaf. See `threads/80-genM-nodechart/`
`item3-2b-deadleaf-gap.md` (the decision-A refinement) + `codex/liveleaf-budget-{prompt,answer}.md`.

**This module banks the NO-REGRET part** (independent of the budget cardinality `#angular = minAdm − 1`,
which the parallel `genm-budget` pen-and-paper adjudicates): the live-leaf decoder + the decoder-agnostic
rate. `genBlkFlatLive M t ha rfin x` is the structured decoder with the leaf residual `Rfin L := rfin`
made LIVE (a free leaf block, read from `x` — the SPECIFIC slot-rerouting reader is the deferred budget
piece). The identity boundary is UNCHANGED from `genBlkFlatStruct` (`Bmat 0 = reindex 1`, `Rmat 0 = 0`),
so the decoder-agnostic rate engine (`routeMCore_phiGen` + `hC0_struct_gen`) fires verbatim:

  `routeMCore (phiFlatLive M t ha hN rfin x) = (x p)² · UvalLive …`.

Sub-tides 1+2a (`phiFlatLDU`/`kLDU`, `RouteMFlatLDU`/`RouteMKLens`) are decoder-agnostic; here they are
re-instantiated on the live decoder. The budget identity (`#angular = minAdm − 1` + square-chart for the
rerouted layout) is DEFERRED — it is the determinant-side cardinality, not the rate.

Axiom-clean `[propext, Classical.choice, Quot.sound]` (matrix algebra; the rate engine, no analysis).
-/

open Matrix
open scoped BigOperators

namespace DLNFibre.DLN.RLCT

variable {L : ℕ}

/-! ## The R1 active-center decoder: fixed-1 pivot at `p*` + freed-slot live `Rfin`

The DET-route decoder (R1, controller-confirmed): the structured decoder with the active-center pivot
boundary `p` (the witness's deepest drop `p*`, `InteriorDrop`) carrying a FIXED `1`-pivot
`E_{p}(0,0) = 1` (the gauge-fixed radial direction, a literal — not a free `readE`), and the freed
pivot-slot's budget rerouted to a live leaf `Rfin`. The slot-guard verdict (verified vs `B_det3333`):
this relocates WHICH slot is the fixed-1 (the pivot E-slot → fixed; its coordinate reroutes to `Rfin`),
keeping `N = flatDim` (the `chartDim_eq_flatDim` "+1 radial −1 fixed residual" accounting) — NO new
Fin-N bijection. The identity boundary is unchanged, so the rate holds decoder-agnostically. -/

/-- **The fixed pivot E-indicator** at boundary `s` — `e_{(0,0)}`: `1` at the first residual row/col,
`0` elsewhere (the gauge-fixed radial direction the `u·Rmat` blow-up targets). -/
def pivotEIndicator (M t : Fin (L + 1) → ℕ) (s : ℕ) :
    Matrix (Fin (Text M t s - Text M t (s + 1))) (Fin (Wext M s - Text M t (s + 1))) ℝ :=
  Matrix.of fun i j => if i.val = 0 ∧ j.val = 0 then 1 else 0

/-! ## The live-leaf structured decoder (structured decoder + a free leaf `Rfin`) -/

/-- **The LIVE-leaf structured decoder** `genBlkFlatLive M t ha rfin x` — the dead-leaf
`genBlkFlatStruct M t ha x` with the leaf residual `Rfin L` made LIVE: `Rfin k := if k = L then rfin
else 0`. The interior blocks (`Bmat`/`Nblk`/`Wblk`/`Rmat`) and the identity boundary are UNCHANGED, so
`Bmat 0 = reindex 1`, `Rmat 0 = 0` (the rate's identity-boundary precondition) hold verbatim. The leaf
block `rfin` is the free leaf coordinate matrix; the SPECIFIC reader (which `x`-slots feed `rfin` + the
interior-pivot fixing) is the deferred budget piece. -/
noncomputable def genBlkFlatLive (M t : Fin (L + 1) → ℕ) (ha : StructAdm M t)
    (rfin : Matrix (Fin (Text M t L)) (Fin (Wext M L)) ℝ)
    (x : Fin (routeMAmbient M) → ℝ) : GenBlk M t where
  Bmat := (genBlkFlatStruct M t ha x).Bmat
  Nblk := (genBlkFlatStruct M t ha x).Nblk
  Wblk := (genBlkFlatStruct M t ha x).Wblk
  Rmat := (genBlkFlatStruct M t ha x).Rmat
  Rfin := fun k => if h : k = L then h ▸ rfin else 0

/-- The live decoder's identity boundary matches the dead one: `Bmat 0 = reindex 1`, `Rmat 0 = 0`
(both `rfl` — they are the structured decoder's, unchanged). -/
theorem genBlkFlatLive_Bmat0 (M t : Fin (L + 1) → ℕ) (ha : StructAdm M t)
    (rfin : Matrix (Fin (Text M t L)) (Fin (Wext M L)) ℝ) (x : Fin (routeMAmbient M) → ℝ) :
    (genBlkFlatLive M t ha rfin x).Bmat 0 = (genBlkFlatStruct M t ha x).Bmat 0 := rfl

theorem genBlkFlatLive_Rmat0 (M t : Fin (L + 1) → ℕ) (ha : StructAdm M t)
    (rfin : Matrix (Fin (Text M t L)) (Fin (Wext M L)) ℝ) (x : Fin (routeMAmbient M) → ℝ) :
    (genBlkFlatLive M t ha rfin x).Rmat 0 = (genBlkFlatStruct M t ha x).Rmat 0 := rfl

/-! ## The identity-boundary `hC0` for the live decoder (verbatim from the structured proof) -/

/-- **The identity boundary `C 0 = 1`** for the live decoder — the `C0_eq_one_gen` proof reads ONLY
`Bmat 0`/`Rmat 0` (both unchanged from the structured decoder), so it holds verbatim. -/
theorem C0_eq_one_live (M t : Fin (L + 1) → ℕ) (ha : StructAdm M t)
    (rfin : Matrix (Fin (Text M t L)) (Fin (Wext M L)) ℝ)
    (v : ℝ) (x : Fin (routeMAmbient M) → ℝ) :
    (chainOfMt v M t (genBlkFlatLive M t ha rfin x) (hleStruct M t ha)).toChain.C 0
      = (1 : Matrix (Fin (Text M t 0)) (Fin (Text M t 0)) ℝ) := by
  rw [chainOfMt_C_zero v M t _ (hleStruct M t ha) ha.hL,
    show (genBlkFlatLive M t ha rfin x).Rmat 0 = 0 from rfl, smul_zero, add_zero]
  have hBmat : (genBlkFlatLive M t ha rfin x).Bmat 0
      = Matrix.reindex (Equiv.refl _) (finCongr (Text0_eq_Text1_struct M t ha.h0))
          (1 : Matrix (Fin (Text M t 0)) (Fin (Text M t 0)) ℝ) := rfl
  have h1W : Text M t 1 = Wext M 0 := Wext0_eq_Text1 M t ha
  rw [hBmat]
  ext i j
  rw [Matrix.mul_apply, Finset.sum_eq_single (Fin.cast (Text0_eq_Text1_struct M t ha.h0) i)]
  · rw [Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.refl_symm, Equiv.refl_apply,
      finCongr_symm, finCongr_apply, Fin.cast_cast, Fin.cast_eq_self, Matrix.one_apply_eq, one_mul]
    have hjcol : (j : Fin (Wext M 0)) = Fin.cast (genWidthEq M t (hleStruct M t ha) 0 ha.hL)
        (Fin.castAdd (Wext M 0 - Text M t (0 + 1)) (Fin.cast h1W.symm j)) := by
      apply Fin.ext; simp
    rw [hjcol, chainQ_apply_castAdd, Matrix.one_apply, Matrix.one_apply]
    by_cases h : (i : ℕ) = (j : ℕ)
    · rw [if_pos (by apply Fin.ext; simpa using h), if_pos (by apply Fin.ext; simpa using h)]
    · rw [if_neg (by intro hc; exact h (by simpa using congrArg Fin.val hc)),
        if_neg (by intro hc; exact h (by simpa using congrArg Fin.val hc))]
  · intro b _ hb
    rw [Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.refl_symm, Equiv.refl_apply,
      finCongr_symm, finCongr_apply]
    rw [show (1 : Matrix (Fin (Text M t 0)) (Fin (Text M t 0)) ℝ) i
          (Fin.cast (Text0_eq_Text1_struct M t ha.h0).symm b) = 0 from by
      rw [Matrix.one_apply, if_neg]; intro hc; apply hb; rw [hc]; apply Fin.ext; simp]
    rw [zero_mul]
  · intro hi; exact absurd (Finset.mem_univ _) hi

/-- **`hC0` for the live decoder** (`C 0 · suffix 0 = suffix 0` from `C 0 = 1`). -/
theorem hC0_live (M t : Fin (L + 1) → ℕ) (ha : StructAdm M t)
    (rfin : Matrix (Fin (Text M t L)) (Fin (Wext M L)) ℝ)
    (v : ℝ) (x : Fin (routeMAmbient M) → ℝ) :
    (chainOfMt v M t (genBlkFlatLive M t ha rfin x) (hleStruct M t ha)).toChain.C 0
        * (chainOfMt v M t (genBlkFlatLive M t ha rfin x)
            (hleStruct M t ha)).toChain.suffix 0 (Nat.zero_le L)
      = (chainOfMt v M t (genBlkFlatLive M t ha rfin x)
          (hleStruct M t ha)).toChain.suffix 0 (Nat.zero_le L) := by
  rw [C0_eq_one_live M t ha rfin v x]; exact Matrix.one_mul _

/-! ## The live-leaf chart + its decoder-agnostic rate -/

/-- **The LIVE-leaf structured achiever chart** `phiFlatLive M t ha hN rfin x := phiGen (x p) M t
(genBlkFlatLive M t ha (rfin x) x) hle`, where the leaf block `rfin x` may itself read from `x` (the
free leaf coordinates). The radial scalar is read from the ORIGINAL `x` at the pivot `p`. -/
noncomputable def phiFlatLive (M t : Fin (L + 1) → ℕ) (ha : StructAdm M t)
    (hN : 0 < routeMAmbient M)
    (rfin : (Fin (routeMAmbient M) → ℝ) → Matrix (Fin (Text M t L)) (Fin (Wext M L)) ℝ)
    (x : Fin (routeMAmbient M) → ℝ) : Fin (routeMAmbient M) → ℝ :=
  phiGen (x (structPivot M hN)) M t (genBlkFlatLive M t ha (rfin x) x) (hleStruct M t ha)

/-- **The LIVE-leaf unit factor** `UvalLive … := VvalGen (x p) M t (genBlkFlatLive …) hle`. -/
noncomputable def UvalLive (M t : Fin (L + 1) → ℕ) (ha : StructAdm M t)
    (hN : 0 < routeMAmbient M)
    (rfin : (Fin (routeMAmbient M) → ℝ) → Matrix (Fin (Text M t L)) (Fin (Wext M L)) ℝ)
    (x : Fin (routeMAmbient M) → ℝ) : ℝ :=
  VvalGen (x (structPivot M hN)) M t (genBlkFlatLive M t ha (rfin x) x) (hleStruct M t ha)

/-- **The rate transfers to the LIVE-leaf chart ∀M (NO bridge)**: `routeMCore M (phiFlatLive rfin x) =
(x p)² · UvalLive rfin x`. Decoder-agnostic: `routeMCore_phiGen` + the live identity-boundary `hC0_live`
(which holds verbatim — the identity boundary is unchanged from the structured decoder). -/
theorem routeMCore_phiFlatLive (M t : Fin (L + 1) → ℕ) (ha : StructAdm M t)
    (hN : 0 < routeMAmbient M)
    (rfin : (Fin (routeMAmbient M) → ℝ) → Matrix (Fin (Text M t L)) (Fin (Wext M L)) ℝ)
    (x : Fin (routeMAmbient M) → ℝ) :
    routeMCore M (phiFlatLive M t ha hN rfin x)
      = (x (structPivot M hN)) ^ 2 * UvalLive M t ha hN rfin x :=
  routeMCore_phiGen (x (structPivot M hN)) M t (genBlkFlatLive M t ha (rfin x) x)
    (hleStruct M t ha)
    (hC0_live M t ha (rfin x) (x (structPivot M hN)) x)

/-- **`0 ≤ UvalLive`** — sum of squares (banked `VvalGen_nonneg`). -/
theorem UvalLive_nonneg (M t : Fin (L + 1) → ℕ) (ha : StructAdm M t) (hN : 0 < routeMAmbient M)
    (rfin : (Fin (routeMAmbient M) → ℝ) → Matrix (Fin (Text M t L)) (Fin (Wext M L)) ℝ)
    (x : Fin (routeMAmbient M) → ℝ) :
    0 ≤ UvalLive M t ha hN rfin x :=
  VvalGen_nonneg _ M t _ _

/-- **Non-vacuity of the live rate**: with `rfin = fun _ => 0`, `routeMCore_phiFlatLive` gives the
`(x p)²·UvalLive` rate on the leaf-killed decoder (the rate is genuinely transferred to the live chart,
not vacuous; the `rfin = 0` leaf is the dead-leaf reduction). -/
example (M t : Fin (L + 1) → ℕ) (ha : StructAdm M t) (hN : 0 < routeMAmbient M)
    (x : Fin (routeMAmbient M) → ℝ) :
    routeMCore M (phiFlatLive M t ha hN (fun _ => 0) x)
      = (x (structPivot M hN)) ^ 2 * UvalLive M t ha hN (fun _ => 0) x :=
  routeMCore_phiFlatLive M t ha hN (fun _ => 0) x

/-! ## The R1 active-center decoder `genBlkFlatLiveR1` -/

/-- **The R1 active-center decoder** `genBlkFlatLiveR1 M t ha p hp rfin x` — the live decoder
`genBlkFlatLive` with the `Rmat` at the active-center pivot boundary `p` OVERRIDDEN to the fixed
`1`-pivot `rmatPad (pivotEIndicator)` (the gauge-fixed radial direction), via `Function.update` on the
`ℕ`-indexed `Rmat` family (no dependent-Fin cast — `p : ℕ`, the updated value is at the exact
`Matrix (Fin (Text p)) (Fin (Wext p)) ℝ` type). The pivot needs the row/col drops `Text(p+1) ≤ Text p`,
`Text(p+1) ≤ Wext p` (`hp` — from `InteriorDrop`'s `p*`). All other blocks (incl the identity boundary
`Rmat 0`, untouched since `p ≥ 1`) and the live leaf `rfin` are as in `genBlkFlatLive`. -/
noncomputable def genBlkFlatLiveR1 (M t : Fin (L + 1) → ℕ) (ha : StructAdm M t) (p : ℕ)
    (hp1 : Text M t (p + 1) ≤ Text M t p) (hp2 : Text M t (p + 1) ≤ Wext M p)
    (rfin : Matrix (Fin (Text M t L)) (Fin (Wext M L)) ℝ)
    (x : Fin (routeMAmbient M) → ℝ) : GenBlk M t where
  Bmat := (genBlkFlatLive M t ha rfin x).Bmat
  Nblk := (genBlkFlatLive M t ha rfin x).Nblk
  Wblk := (genBlkFlatLive M t ha rfin x).Wblk
  Rmat := Function.update (genBlkFlatLive M t ha rfin x).Rmat p
    (rmatPad M t p hp1 hp2 (pivotEIndicator M t p))
  Rfin := (genBlkFlatLive M t ha rfin x).Rfin

/-- The R1 decoder's `Rmat` at the pivot `p` IS the fixed `1`-pivot pad (`Function.update` hit). -/
theorem genBlkFlatLiveR1_Rmat_pivot (M t : Fin (L + 1) → ℕ) (ha : StructAdm M t) (p : ℕ)
    (hp1 : Text M t (p + 1) ≤ Text M t p) (hp2 : Text M t (p + 1) ≤ Wext M p)
    (rfin : Matrix (Fin (Text M t L)) (Fin (Wext M L)) ℝ) (x : Fin (routeMAmbient M) → ℝ) :
    (genBlkFlatLiveR1 M t ha p hp1 hp2 rfin x).Rmat p
      = rmatPad M t p hp1 hp2 (pivotEIndicator M t p) :=
  Function.update_self ..

/-- The R1 decoder's identity boundary `Rmat 0 = 0` (untouched: `Function.update` at `p ≥ 1` misses `0`).
Needs `p ≠ 0` (the pivot is interior, `1 ≤ p`). -/
theorem genBlkFlatLiveR1_Rmat0 (M t : Fin (L + 1) → ℕ) (ha : StructAdm M t) (p : ℕ) (hp0 : p ≠ 0)
    (hp1 : Text M t (p + 1) ≤ Text M t p) (hp2 : Text M t (p + 1) ≤ Wext M p)
    (rfin : Matrix (Fin (Text M t L)) (Fin (Wext M L)) ℝ) (x : Fin (routeMAmbient M) → ℝ) :
    (genBlkFlatLiveR1 M t ha p hp1 hp2 rfin x).Rmat 0
      = (0 : Matrix (Fin (Text M t 0)) (Fin (Wext M 0)) ℝ) := by
  show Function.update (genBlkFlatLive M t ha rfin x).Rmat p _ 0 = _
  rw [Function.update_of_ne (Ne.symm hp0)]
  rfl

/-- **The identity boundary `C 0 = 1`** for the R1 decoder — reads only `Bmat 0`/`Rmat 0`, both unchanged
(`Bmat 0` is the live decoder's; `Rmat 0 = 0` since `p ≥ 1` misses the update). Proof verbatim from
`C0_eq_one_live` (the `Bmat 0` is identical; `Rmat 0 = 0` via `genBlkFlatLiveR1_Rmat0`). -/
theorem C0_eq_one_liveR1 (M t : Fin (L + 1) → ℕ) (ha : StructAdm M t) (p : ℕ) (hp0 : p ≠ 0)
    (hp1 : Text M t (p + 1) ≤ Text M t p) (hp2 : Text M t (p + 1) ≤ Wext M p)
    (rfin : Matrix (Fin (Text M t L)) (Fin (Wext M L)) ℝ)
    (v : ℝ) (x : Fin (routeMAmbient M) → ℝ) :
    (chainOfMt v M t (genBlkFlatLiveR1 M t ha p hp1 hp2 rfin x) (hleStruct M t ha)).toChain.C 0
      = (1 : Matrix (Fin (Text M t 0)) (Fin (Text M t 0)) ℝ) := by
  rw [chainOfMt_C_zero v M t _ (hleStruct M t ha) ha.hL,
    genBlkFlatLiveR1_Rmat0 M t ha p hp0 hp1 hp2 rfin x, smul_zero, add_zero]
  have hBmat : (genBlkFlatLiveR1 M t ha p hp1 hp2 rfin x).Bmat 0
      = Matrix.reindex (Equiv.refl _) (finCongr (Text0_eq_Text1_struct M t ha.h0))
          (1 : Matrix (Fin (Text M t 0)) (Fin (Text M t 0)) ℝ) := rfl
  have h1W : Text M t 1 = Wext M 0 := Wext0_eq_Text1 M t ha
  rw [hBmat]
  ext i j
  rw [Matrix.mul_apply, Finset.sum_eq_single (Fin.cast (Text0_eq_Text1_struct M t ha.h0) i)]
  · rw [Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.refl_symm, Equiv.refl_apply,
      finCongr_symm, finCongr_apply, Fin.cast_cast, Fin.cast_eq_self, Matrix.one_apply_eq, one_mul]
    have hjcol : (j : Fin (Wext M 0)) = Fin.cast (genWidthEq M t (hleStruct M t ha) 0 ha.hL)
        (Fin.castAdd (Wext M 0 - Text M t (0 + 1)) (Fin.cast h1W.symm j)) := by
      apply Fin.ext; simp
    rw [hjcol, chainQ_apply_castAdd, Matrix.one_apply, Matrix.one_apply]
    by_cases h : (i : ℕ) = (j : ℕ)
    · rw [if_pos (by apply Fin.ext; simpa using h), if_pos (by apply Fin.ext; simpa using h)]
    · rw [if_neg (by intro hc; exact h (by simpa using congrArg Fin.val hc)),

exec
/bin/bash -lc "sed -n '1,280p' lean/DLNFibre/DLN/RLCT/Validate/RouteMBData222.lean" in /home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/agent-a9bb11c22680d93d4
 succeeded in 0ms:
import DLNFibre.DLN.RLCT.Validate.RouteMBInterface
import DLNFibre.DLN.RLCT.Validate.RouteMBData
import DLNFibre.DLN.RLCT.Validate.RouteM222Det
import DLNFibre.DLN.RLCT.Validate.RouteMCardBridge
import DLNFibre.DLN.RLCT.Validate.RouteMSchurValue

/-!
# `RouteMBData222` — the FAITHFUL `BData M222` term for the concrete (2,2,2) node

Constructs a `BData M222 tach222 ha hN 1 hp1 hp2 rfin u` term (the frozen B-interface,
`RouteMBInterface`) for the CONCRETE fixed-pivot/live-leaf decoder `genBlkFlatLiveR1 M222`, feeding
`interiorDet_headline_of_BData` to obtain the unconditional interior-det headline for
`phiFlatLiveR1 M222`. This is the FAITHFUL route end-to-end on the concrete node (the validate-small the
`∀M` `L = 2` generalization follows).

The faithful decomposition (Codex-verified, sympy-exact; `route-i-bridge-resolved.md`): on the actual
`genBlkFlatLiveR1 M222` blocks, with coords `(u, a, b, n, w0, w1, lf0, lf1)`
(`u = x (structPivot)` radial; `a = readK`, `b = readX`, `n = readN`, `w0,w1 = readW`; `lf0,lf1` the
free leaf coords),

  `Agen0 = [[a, a·n],[a·b, a·b·n + u]]`, `Agen1 = [[u·lf0 − n·w0, u·lf1 − n·w1],[w0,w1]]`,

`φ = B ∘ pivotBlowupOn active u` with `active = {structPivot} ∪ {lf0, lf1}` (`card 3 = minAdm(2,2,2)`,
the FIXED `E(0,0) = 1` is NOT in active), `det Dπ = u²`; `B` reads the pivot as an ORDINARY coord (the
Schur frame isolates it: `p = A0_11 − A0_10·A0_01/A0_00 = u`), `det DB = a²` = the engine
(`|K|^{r+c}`, `r = c = 1`). The additive `+u` at `Agen0[1,1]` is the pivot COORDINATE, NOT an affine
layer.

The SLOT WALL (the opaque `chartIdxEquiv = (finCongr).trans (Fintype.equivFin).symm`): the reader slots
`a,b,n,w0,w1` are images of `chartIdxEquiv.symm` at specific `ChartIdx` tags — but `chartIdxEquiv.symm`
does NOT reduce by `decide`, and `structPivot = ⟨0,_⟩` is NOT a `ChartIdx` tag, so
`leaf-slot ≠ structPivot` is unreachable by tag injectivity. RESOLVED (R2, decorrelated Codex): choose
the two leaf slots `lf0, lf1` from the FINITE COMPLEMENT `univ \ (insert structPivot readerSet)`
(`readerSet.card ≤ 5`, so the complement has `≥ 2` slots); membership then GIVES `lf ≠ structPivot` and
`lf ∉ readerSet` for free, no opaque comparison.

Axiom-clean `[propext, Classical.choice, Quot.sound]` (the banked wiring + matrix algebra; the leaf-pair
choice is `Classical.choice`).
-/

open Matrix
open scoped BigOperators

set_option maxHeartbeats 800000

namespace DLNFibre.DLN.RLCT

/-! ## `StructAdm M222 tach222` (the achiever path `tach222 = [2,1,0]`) -/

/-- **`StructAdm M222 tach222`** — the structured-decoder admissibility for the (2,2,2) achiever path
`tach222 = [2,1,0]` (`Text = [2,2,1,1,…]`). In-range boundaries by `decide`; out-of-range (`k ≥ 3`) by
the `Wext`/`Text` saturation to `1`. -/
theorem structAdm_tach222 : StructAdm M222 tach222 := by
  refine ⟨by decide, ?_, by decide, ?_, ?_⟩
  · intro p
    rcases lt_or_ge p 3 with h | h
    · interval_cases p <;> decide
    · rw [show Wext M222 (p + 1) = 1 from by rw [Wext]; rw [dif_neg (by omega)],
          show tDesc M222 tach222 (p + 1) = 1 from by simp only [tDesc, Text]; rw [dif_neg (by omega)]]
  · intro k hk; interval_cases k <;> decide
  · intro k
    rcases lt_or_ge k 3 with h | h
    · interval_cases k <;> decide
    · rw [show Text M222 tach222 (k + 2) = 1 from by simp only [Text]; rw [dif_neg (by omega)],
          show Wext M222 (k + 1) = 1 from by rw [Wext]; rw [dif_neg (by omega)]]

/-- The R1 pivot row-drop hypothesis `hp1 : Text(2) ≤ Text(1)` at the (2,2,2) pivot boundary `p = 1`
(`Text 2 = 1 ≤ 2 = Text 1`). -/
theorem hp1_222 : Text M222 tach222 (1 + 1) ≤ Text M222 tach222 1 := by decide

/-- The R1 pivot col-drop hypothesis `hp2 : Text(2) ≤ Wext(1)` (`Text 2 = 1 ≤ 2 = Wext 1`). -/
theorem hp2_222 : Text M222 tach222 (1 + 1) ≤ Wext M222 1 := by decide

/-! ## The reader values + the leaf

The five reader scalars of `genBlkFlatLiveR1 M222 tach222` (all `1×1` blocks at chart-slot `k = 0`,
`Text 1 = 2`, `Text 2 = 1`, `Wext 1 = 2`): `aRead = readK ⟨0⟩ 0 0`, `bRead = readX ⟨0⟩ 0 0`,
`nRead = readN ⟨0⟩ 0 0`, `w0Read/w1Read = readW ⟨0⟩ _ 0 0/1`. The pivot `E`-slot is NOT read (the R1
override fixes `Rmat 1 = rmatPad pivotEIndicator`). The leaf `Rfin 2 = rfin x` is the free choice. -/

/-- The reader value `a = readK ⟨0,_⟩ 0 0` (the Schur-frame `K` scalar at chart-slot `0`). -/
noncomputable def aRead (x : Fin (routeMAmbient M222) → ℝ) : ℝ :=
  readK M222 tach222 structAdm_tach222 x ⟨0, by decide⟩ ⟨0, by decide⟩ ⟨0, by decide⟩

/-- The reader value `b = readX ⟨0,_⟩ 0 0` (the Schur-frame `X` scalar). -/
noncomputable def bRead (x : Fin (routeMAmbient M222) → ℝ) : ℝ :=
  readX M222 tach222 structAdm_tach222 x ⟨0, by decide⟩ ⟨0, by decide⟩ ⟨0, by decide⟩

/-- The reader value `n = readN ⟨0,_⟩ 0 0` (the Schur-frame `N` chaining scalar). -/
noncomputable def nRead (x : Fin (routeMAmbient M222) → ℝ) : ℝ :=
  readN M222 tach222 structAdm_tach222 x ⟨0, by decide⟩ ⟨0, by decide⟩ ⟨0, by decide⟩

/-- The lift value `w0 = readW ⟨0,_⟩ _ 0 0`. -/
noncomputable def w0Read (x : Fin (routeMAmbient M222) → ℝ) : ℝ :=
  readW M222 tach222 structAdm_tach222 x ⟨0, by decide⟩ (by decide) ⟨0, by decide⟩ ⟨0, by decide⟩

/-- The lift value `w1 = readW ⟨0,_⟩ _ 0 1`. -/
noncomputable def w1Read (x : Fin (routeMAmbient M222) → ℝ) : ℝ :=
  readW M222 tach222 structAdm_tach222 x ⟨0, by decide⟩ (by decide) ⟨0, by decide⟩ ⟨1, by decide⟩

/-! ## The `genBlkFlatLiveR1 M222` block values at boundary `1` + the leaf

The decoder `Glr x := genBlkFlatLiveR1 M222 tach222 structAdm_tach222 1 hp1_222 hp2_222 (rfin x) x`.
Its blocks at chart-slot `0` (boundary `s = 1`): `Bmat 1 = bmatStack (readK) (readX) = [[a],[a·b]]`,
`Nblk 1 = readN = [n]`, `Wblk 1 = readW = [w0, w1]`, and the FIXED pivot
`Rmat 1 = rmatPad (pivotEIndicator) = [[0,0],[0,1]]`. The leaf `C 2 = u • Rfin 2 = u • rfin x`. -/

variable (rfin : (Fin (routeMAmbient M222) → ℝ) → Matrix (Fin (Text M222 tach222 2))
  (Fin (Wext M222 2)) ℝ)

/-- Abbreviation for the R1 decoder at `x` with leaf `rfin x`. -/
noncomputable def Glr (rfin : (Fin (routeMAmbient M222) → ℝ) → Matrix (Fin (Text M222 tach222 2))
    (Fin (Wext M222 2)) ℝ) (x : Fin (routeMAmbient M222) → ℝ) : GenBlk M222 tach222 :=
  genBlkFlatLiveR1 M222 tach222 structAdm_tach222 1 hp1_222 hp2_222 (rfin x) x

/-- `Glr`'s `Bmat 1 = bmatStack (readK ⟨0⟩) (readX ⟨0⟩)` (the live decoder's = the struct decoder's). -/
theorem Glr_Bmat1 (rfin : (Fin (routeMAmbient M222) → ℝ) → Matrix (Fin (Text M222 tach222 2))
    (Fin (Wext M222 2)) ℝ) (x : Fin (routeMAmbient M222) → ℝ) :
    (Glr rfin x).Bmat 1
      = bmatStack M222 tach222 1 (structAdm_tach222.hdesc 0 (by decide))
          (readK M222 tach222 structAdm_tach222 x ⟨0, by decide⟩)
          (readX M222 tach222 structAdm_tach222 x ⟨0, by decide⟩) := by
  show (genBlkFlatStruct M222 tach222 structAdm_tach222 x).Bmat 1 = _
  show (if hk : (0 : ℕ) < 2 then bmatStack M222 tach222 1 (structAdm_tach222.hdesc 0 hk)
      (readK M222 tach222 structAdm_tach222 x ⟨0, hk⟩)
      (readX M222 tach222 structAdm_tach222 x ⟨0, hk⟩) else 0) = _
  rw [dif_pos (by decide)]

/-- `Glr`'s `Nblk 1 = readN ⟨0⟩`. -/
theorem Glr_Nblk1 (rfin : (Fin (routeMAmbient M222) → ℝ) → Matrix (Fin (Text M222 tach222 2))
    (Fin (Wext M222 2)) ℝ) (x : Fin (routeMAmbient M222) → ℝ) :
    (Glr rfin x).Nblk 1 = readN M222 tach222 structAdm_tach222 x ⟨0, by decide⟩ := by
  show (genBlkFlatStruct M222 tach222 structAdm_tach222 x).Nblk 1 = _
  simp only [genBlkFlatStruct, dif_pos (show (0 : ℕ) < 2 by decide)]

/-- `Glr`'s `Wblk 1 = readW ⟨0⟩ _`. -/
theorem Glr_Wblk1 (rfin : (Fin (routeMAmbient M222) → ℝ) → Matrix (Fin (Text M222 tach222 2))
    (Fin (Wext M222 2)) ℝ) (x : Fin (routeMAmbient M222) → ℝ) :
    (Glr rfin x).Wblk 1 = readW M222 tach222 structAdm_tach222 x ⟨0, by decide⟩ (by decide) := by
  show (genBlkFlatStruct M222 tach222 structAdm_tach222 x).Wblk 1 = _
  simp only [genBlkFlatStruct, dif_pos (show (0 : ℕ) < 2 by decide),
    dif_pos (show 0 + 1 < 2 by decide)]

/-- `Glr`'s `Nblk 1` as the literal `1×1` matrix `!![nRead x]` (over the `Text2 × (Wext1−Text2)`
widths, both `= 1`). -/
theorem Glr_Nblk1_lit (rfin : (Fin (routeMAmbient M222) → ℝ) → Matrix (Fin (Text M222 tach222 2))
    (Fin (Wext M222 2)) ℝ) (x : Fin (routeMAmbient M222) → ℝ) :
    (Glr rfin x).Nblk 1
      = (!![nRead x] : Matrix (Fin (Text M222 tach222 2))
          (Fin (Wext M222 1 - Text M222 tach222 2)) ℝ) := by
  rw [Glr_Nblk1]
  funext i j; fin_cases i <;> fin_cases j; rfl

/-- `Glr`'s `Wblk 1` as the literal `1×2` matrix `!![w0Read x, w1Read x]` (over `(Wext1−Text2) × Wext2`,
`= 1 × 2`). -/
theorem Glr_Wblk1_lit (rfin : (Fin (routeMAmbient M222) → ℝ) → Matrix (Fin (Text M222 tach222 2))
    (Fin (Wext M222 2)) ℝ) (x : Fin (routeMAmbient M222) → ℝ) :
    (Glr rfin x).Wblk 1
      = (!![w0Read x, w1Read x] : Matrix (Fin (Wext M222 1 - Text M222 tach222 2))
          (Fin (Wext M222 2)) ℝ) := by
  rw [Glr_Wblk1]
  funext i j; fin_cases i <;> fin_cases j <;> rfl

/-- `Glr`'s `Rmat 1 = rmatPad (pivotEIndicator)` (the FIXED pivot override). -/
theorem Glr_Rmat1 (rfin : (Fin (routeMAmbient M222) → ℝ) → Matrix (Fin (Text M222 tach222 2))
    (Fin (Wext M222 2)) ℝ) (x : Fin (routeMAmbient M222) → ℝ) :
    (Glr rfin x).Rmat 1
      = rmatPad M222 tach222 1 hp1_222 hp2_222 (pivotEIndicator M222 tach222 1) :=
  genBlkFlatLiveR1_Rmat_pivot M222 tach222 structAdm_tach222 1 hp1_222 hp2_222 (rfin x) x

/-! ## The Schur frame `C 1` + the leaf `C 2` -/

/-- **The boundary-1 transition `C 1 = schurFrameProd`** — the Schur frame
`Bmat 1 · chainQ(N1) + u·Rmat 1 = schurFrameProd … (readK) (readX) (readN) (pivotEIndicator)`. The
fixed-pivot `Rmat 1 = rmatPad pivotEIndicator` is the `u`-carrier `E`-block. -/
theorem Cgen1_Glr (rfin : (Fin (routeMAmbient M222) → ℝ) → Matrix (Fin (Text M222 tach222 2))
    (Fin (Wext M222 2)) ℝ) (x : Fin (routeMAmbient M222) → ℝ) :
    Cgen (x (structPivot M222 hN_M222)) M222 tach222 (Glr rfin x) (hleStruct M222 tach222 structAdm_tach222) 1
      = schurFrameProd M222 tach222 1 hp1_222 hp2_222 (x (structPivot M222 hN_M222))
          (readK M222 tach222 structAdm_tach222 x ⟨0, by decide⟩)
          (readX M222 tach222 structAdm_tach222 x ⟨0, by decide⟩)
          (readN M222 tach222 structAdm_tach222 x ⟨0, by decide⟩)
          (pivotEIndicator M222 tach222 1) := by
  show (if hk : (1 : ℕ) < 2 then (Glr rfin x).Bmat 1 *
      chainQ (genWidthEq M222 tach222 (hleStruct M222 tach222 structAdm_tach222) 1 hk) ((Glr rfin x).Nblk 1)
      + (x (structPivot M222 hN_M222)) • (Glr rfin x).Rmat 1 else _) = _
  rw [dif_pos (by decide), Glr_Bmat1, Glr_Nblk1, Glr_Rmat1]
  rfl

/-- **The leaf transition `C 2 = u • rfin x`** (`dif_neg`; the leaf residual `Rfin 2 = rfin x`). -/
theorem Cgen2_Glr (rfin : (Fin (routeMAmbient M222) → ℝ) → Matrix (Fin (Text M222 tach222 2))
    (Fin (Wext M222 2)) ℝ) (x : Fin (routeMAmbient M222) → ℝ) :
    Cgen (x (structPivot M222 hN_M222)) M222 tach222 (Glr rfin x) (hleStruct M222 tach222 structAdm_tach222) 2
      = (x (structPivot M222 hN_M222)) • (rfin x) := by
  show (if hk : (2 : ℕ) < 2 then _ else (x (structPivot M222 hN_M222)) • (Glr rfin x).Rfin 2) = _
  rw [dif_neg (by decide)]
  rfl

/-! ## The explicit layer matrices `Agen0` / `Agen1` (the FAITHFUL fidelity)

The load-bearing step: the chain's two layers of `genBlkFlatLiveR1 M222`, reindexed to the `M`-widths,
ARE the Codex-verified explicit matrices (coords `u = x p`, `a/b/n/w0/w1` the readers,
`lf0/lf1 = rfin x 0 0 / 0 1`):

  `Agen0 = [[a, a·n],[a·b, a·b·n + u]]`,  `Agen1 = [[u·lf0 − n·w0, u·lf1 − n·w1],[w0,w1]]`.

The additive `+u` at `Agen0[1,1]` is the FIXED pivot's `u·E(0,0) = u·1` — the pivot COORDINATE. -/

/-- **Layer 1 of the chain** `Agen 1 = [[u·lf0 − n·w0, u·lf1 − n·w1],[w0,w1]]` (kept row `C2 − N1·W1`
over lift row `W1`; `C2 = u·rfin x`, `N1 = [n]`, `W1 = [w0,w1]`). -/
theorem Agen1_Glr_eq (rfin : (Fin (routeMAmbient M222) → ℝ) → Matrix (Fin (Text M222 tach222 2))
    (Fin (Wext M222 2)) ℝ) (x : Fin (routeMAmbient M222) → ℝ) :
    Agen (x (structPivot M222 hN_M222)) M222 tach222 (Glr rfin x)
        (hleStruct M222 tach222 structAdm_tach222) 1
      = (!![x (structPivot M222 hN_M222) * rfin x ⟨0, by decide⟩ ⟨0, by decide⟩ - nRead x * w0Read x,
            x (structPivot M222 hN_M222) * rfin x ⟨0, by decide⟩ ⟨1, by decide⟩ - nRead x * w1Read x;
            w0Read x, w1Read x] : Matrix (Fin (Wext M222 1)) (Fin (Wext M222 2)) ℝ) := by
  have hA : Agen (x (structPivot M222 hN_M222)) M222 tach222 (Glr rfin x)
      (hleStruct M222 tach222 structAdm_tach222) 1
      = chainA (genWidthEq M222 tach222 (hleStruct M222 tach222 structAdm_tach222) 1 (by decide))
          ((Glr rfin x).Nblk 1) ((Glr rfin x).Wblk 1)
          (Cgen (x (structPivot M222 hN_M222)) M222 tach222 (Glr rfin x)
            (hleStruct M222 tach222 structAdm_tach222) 2) := by
    show (if hk : (1 : ℕ) < 2 then chainA _ _ _ _ else 0) = _
    rw [dif_pos (by decide)]
  -- kept row (castAdd): C2 − N1·W1; lift row (natAdd): W1
  have kept : ∀ j : Fin (Wext M222 2),
      chainA (genWidthEq M222 tach222 (hleStruct M222 tach222 structAdm_tach222) 1 (by decide))
          ((Glr rfin x).Nblk 1) ((Glr rfin x).Wblk 1)
          (Cgen (x (structPivot M222 hN_M222)) M222 tach222 (Glr rfin x)
            (hleStruct M222 tach222 structAdm_tach222) 2)
          (⟨0, by decide⟩ : Fin (Wext M222 1)) j
        = (Cgen (x (structPivot M222 hN_M222)) M222 tach222 (Glr rfin x)
              (hleStruct M222 tach222 structAdm_tach222) 2
            - (Glr rfin x).Nblk 1 * (Glr rfin x).Wblk 1)
            (⟨0, by decide⟩ : Fin (Text M222 tach222 2)) j := by
    intro j
    conv_lhs => rw [show (⟨0, by decide⟩ : Fin (Wext M222 1))
        = Fin.cast (genWidthEq M222 tach222 (hleStruct M222 tach222 structAdm_tach222) 1 (by decide))
            (Fin.castAdd (Wext M222 1 - Text M222 tach222 2)
              (⟨0, by decide⟩ : Fin (Text M222 tach222 2))) from by apply Fin.ext; simp]
    rw [chainA_apply_castAdd]
  have lift : ∀ j : Fin (Wext M222 2),
      chainA (genWidthEq M222 tach222 (hleStruct M222 tach222 structAdm_tach222) 1 (by decide))
          ((Glr rfin x).Nblk 1) ((Glr rfin x).Wblk 1)
          (Cgen (x (structPivot M222 hN_M222)) M222 tach222 (Glr rfin x)
            (hleStruct M222 tach222 structAdm_tach222) 2)
          (⟨1, by decide⟩ : Fin (Wext M222 1)) j
        = (Glr rfin x).Wblk 1 (⟨0, by decide⟩ : Fin (Wext M222 1 - Text M222 tach222 2)) j := by
    intro j
    conv_lhs => rw [show (⟨1, by decide⟩ : Fin (Wext M222 1))
        = Fin.cast (genWidthEq M222 tach222 (hleStruct M222 tach222 structAdm_tach222) 1 (by decide))
            (Fin.natAdd (Text M222 tach222 2)
              (⟨0, by decide⟩ : Fin (Wext M222 1 - Text M222 tach222 2))) from by apply Fin.ext; simp]
    rw [chainA_apply_natAdd]
  -- the four entries at explicit `⟨_, by decide⟩` indices
  have h00 : chainA (genWidthEq M222 tach222 (hleStruct M222 tach222 structAdm_tach222) 1 (by decide))
      ((Glr rfin x).Nblk 1) ((Glr rfin x).Wblk 1)
      (Cgen (x (structPivot M222 hN_M222)) M222 tach222 (Glr rfin x)
        (hleStruct M222 tach222 structAdm_tach222) 2)
      (⟨0, by decide⟩ : Fin (Wext M222 1)) (⟨0, by decide⟩ : Fin (Wext M222 2))
        = x (structPivot M222 hN_M222) * rfin x ⟨0, by decide⟩ ⟨0, by decide⟩
          - nRead x * w0Read x := by
    rw [kept, Cgen2_Glr, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul, Matrix.mul_apply,
      Finset.sum_eq_single (⟨0, by decide⟩ : Fin (Wext M222 1 - Text M222 tach222 2))]
    · rfl
    · intro c _ hc
      refine absurd (Fin.ext ?_) hc
      have hlt := c.isLt
      have hw : Wext M222 1 - Text M222 tach222 2 = 1 := by decide
      omega
    · intro h; exact absurd (Finset.mem_univ _) h
  have h01 : chainA (genWidthEq M222 tach222 (hleStruct M222 tach222 structAdm_tach222) 1 (by decide))
      ((Glr rfin x).Nblk 1) ((Glr rfin x).Wblk 1)
      (Cgen (x (structPivot M222 hN_M222)) M222 tach222 (Glr rfin x)
        (hleStruct M222 tach222 structAdm_tach222) 2)
      (⟨0, by decide⟩ : Fin (Wext M222 1)) (⟨1, by decide⟩ : Fin (Wext M222 2))
        = x (structPivot M222 hN_M222) * rfin x ⟨0, by decide⟩ ⟨1, by decide⟩
          - nRead x * w1Read x := by
    rw [kept, Cgen2_Glr, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul, Matrix.mul_apply,

exec
/bin/bash -lc "sed -n '1,220p' lean/DLNFibre/DLN/RLCT/Validate/RouteMChartIdxEquiv.lean" in /home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/agent-a9bb11c22680d93d4
 succeeded in 0ms:
import DLNFibre.DLN.RLCT.Validate.RouteMChartIdx

/-!
# `RouteMChartIdxEquiv` — Phase B item 1 finish: `ChartIdx` + `card = flatDim` + `Fin N ≃ ChartIdx`

The determinant-ready bijective coordinatization (item 1 of the det route, B+b1), built on the arithmetic
foundation `chartDim_eq_flatDim` (`RouteMChartIdx`). The chart coordinates split, per boundary `k : Fin L`,
into a **Schur block** of size `t_k·M_{k+1}` (the `K/X/N/E` roles, `= (t_k+r_k)(t_k+c_k)`) and a **chain
lift** of size `c_k·M_{k+2}` (`0` at the leaf). The radial and the fixed residual already cancel in
`chartDim_eq_flatDim` (no `±1`), so `card (ChartIdx) = ∑_k (schurDim k + liftDim k) = flatDim M`.

* `ChartIdx M t` — `Σ k : Fin L, Fin (schurDim k) ⊕ Fin (liftDim k)` (the per-boundary role coordinates).
* `card_chartIdx` — `Fintype.card (ChartIdx M t) = flatDim M` (`Fintype.card_sigma` + the foundation).
* `chartIdxEquiv` — `Fin (routeMAmbient M) ≃ ChartIdx M t` (`Fintype.equivFin` + the cardinality).

Axiom-clean `[propext, Classical.choice, Quot.sound]` (finite cardinality; no analysis).
-/

namespace DLNFibre.DLN.RLCT

open scoped BigOperators

variable {L : ℕ}

/-! ## The per-boundary role dimensions (ℕ-indexed, from the descent path) -/

/-- The Schur-block coordinate count at boundary `k`: `t_k·M_{k+1}` (`= (t_k+r_k)(t_k+c_k)`, the
`K/X/N/E` roles). -/
def schurDim (M : Fin (L + 1) → ℕ) (t : ℕ → ℕ) (k : ℕ) : ℕ :=
  t k * (Wext M) (k + 1)

/-- The chain-lift coordinate count at boundary `k`: `c_k·M_{k+2}` (`0` at the leaf `k = L−1`). -/
def liftDim (M : Fin (L + 1) → ℕ) (t : ℕ → ℕ) (k : ℕ) : ℕ :=
  if k + 1 < L then ((Wext M) (k + 1) - t (k + 1)) * (Wext M) (k + 2) else 0

/-- **The chart-coordinate index** `ChartIdx M t = Σ k : Fin L, Fin (schurDim k) ⊕ Fin (liftDim k)`. The
per-boundary Schur-block + chain-lift coordinates; its cardinality is `flatDim M`. -/
abbrev ChartIdx (M : Fin (L + 1) → ℕ) (t : ℕ → ℕ) : Type :=
  Σ k : Fin L, Fin (schurDim M t k.val) ⊕ Fin (liftDim M t k.val)

/-! ## `card (ChartIdx) = flatDim` -/

/-- The chain-lift sum `∑_{k<L} liftDim k = ∑_{k<L−1} c_k·M_{k+2}` (the leaf lift is `0`). -/
theorem sum_liftDim (M : Fin (L + 1) → ℕ) (t : ℕ → ℕ) (hL : 0 < L) :
    (∑ k ∈ Finset.range L, liftDim M t k)
      = ∑ k ∈ Finset.range (L - 1), ((Wext M) (k + 1) - t (k + 1)) * (Wext M) (k + 2) := by
  rw [← Finset.sum_range_add_sum_Ico _ (show L - 1 ≤ L by omega)]
  have h0 : (∑ k ∈ Finset.Ico (L - 1) L, liftDim M t k) = 0 := by
    apply Finset.sum_eq_zero
    intro k hk; rw [Finset.mem_Ico] at hk
    unfold liftDim; rw [if_neg (by omega)]
  rw [h0, add_zero]
  apply Finset.sum_congr rfl
  intro k hk; rw [Finset.mem_range] at hk
  unfold liftDim; rw [if_pos (by omega)]

/-- **`Fintype.card (ChartIdx M t) = flatDim M`** — via `card_sigma` (`card (Σ k, Aₖ ⊕ Bₖ) =
∑ (card Aₖ + card Bₖ)`), the `Fin`-to-`range` sum bridge, and the arithmetic foundation
`chartDim_eq_flatDim` (the Schur sum `∑ schurDim` + the lift sum `∑ liftDim` = `flatDim`). -/
theorem card_chartIdx (M : Fin (L + 1) → ℕ) (t : ℕ → ℕ)
    (h0 : t 0 = M 0) (hc : ∀ k, t (k + 1) ≤ (Wext M) (k + 1)) (hL : 0 < L) :
    Fintype.card (ChartIdx M t) = flatDim M := by
  rw [Fintype.card_sigma]
  simp only [Fintype.card_sum, Fintype.card_fin]
  rw [Finset.sum_add_distrib,
    Fin.sum_univ_eq_sum_range (fun k => schurDim M t k) L,
    Fin.sum_univ_eq_sum_range (fun k => liftDim M t k) L,
    sum_liftDim M t hL]
  rw [show (∑ k ∈ Finset.range L, schurDim M t k)
        = ∑ k ∈ Finset.range L, t k * (Wext M) (k + 1) from rfl]
  exact chartDim_eq_flatDim M t h0 hc hL

/-! ## The flat-coordinate equivalence -/

/-- **`Fin (routeMAmbient M) ≃ ChartIdx M t`** — the determinant-ready bijective coordinatization. The
flat coordinate space `Fin N` (`N = routeMAmbient M = flatDim M`) is in bijection with the per-boundary
Schur/lift role coordinates, since `card (ChartIdx) = flatDim M = N` (`card_chartIdx`). -/
noncomputable def chartIdxEquiv (M : Fin (L + 1) → ℕ) (t : ℕ → ℕ)
    (h0 : t 0 = M 0) (hc : ∀ k, t (k + 1) ≤ (Wext M) (k + 1)) (hL : 0 < L) :
    Fin (routeMAmbient M) ≃ ChartIdx M t :=
  (finCongr (show routeMAmbient M = Fintype.card (ChartIdx M t) by
    rw [card_chartIdx M t h0 hc hL]; rfl)).trans (Fintype.equivFin (ChartIdx M t)).symm

end DLNFibre.DLN.RLCT

exec
/bin/bash -lc "sed -n '1,220p' lean/DLNFibre/DLN/RLCT/Validate/RouteMChartSlots.lean" in /home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/agent-a9bb11c22680d93d4
 succeeded in 0ms:
import DLNFibre.DLN.RLCT.Validate.RouteMChartIdxEquiv
import DLNFibre.DLN.RLCT.Validate.RouteMGenChain
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Data.Matrix.Block

/-!
# `RouteMChartSlots` — the disjoint role-slot reader API (the shared decoder/factor foundation)

The shared coordinate-accessor foundation for the structured achiever-chart decoder + its factor CLEs
(the unblock for the item-3 map equality — see `thread.md` UPDATE + `codex/decoder-*`). The diagnosed
flaw was that `genBlkFlat` reads its block data via an arbitrary modular hash that COLLAPSES distinct
entries. The fix: read every block entry from a DISJOINT flat slot via the banked bijective
coordinatization `chartIdxEquiv : Fin (routeMAmbient M) ≃ ChartIdx M t`, with
`ChartIdx = Σ k : Fin L, Fin (schurDim k) ⊕ Fin (liftDim k)`.

The per-boundary slot allocation (verified against `(3,3,3,3)`, `chartDim_eq_flatDim` ⟹ `∑ = N`):
* `schurDim k = t_k · M_{k+1}` holds the Schur frame at boundary `s = k+1` (`(t_s+r_s)(t_s+c_s) =
  t_{k}·M_{k+1}` after the `schurDim(s-1)↔frame(s)` shift); for `k = L−1` it holds the leaf residual.
* `liftDim k = (M_{k+1}−t_{k+1})·M_{k+2}` holds the lift `W_{k+1}`.

This module gives the `Fin`-product slot equivalences (`Fin (schurDim k) ≃ Fin (t_k) × Fin (M_{k+1})`
etc.) and the `chartIdxEquiv`-based scalar readers — disjoint by construction (distinct `ChartIdx`
indices ⟹ distinct flat coords). The structured decoder + the factor CLEs both read through these, so
the item-3 map equality is accessor lemmas, not a coordinate-collapse fight.

Axiom-clean `[propext, Classical.choice, Quot.sound]` (finite equivalences; no analysis).
-/

namespace DLNFibre.DLN.RLCT

open scoped BigOperators

variable {L : ℕ}
variable {𝕜 : Type} [CommRing 𝕜]

/-! ## The per-boundary slot ↔ matrix-index equivalences -/

/-- The Schur-block slot at boundary `k` as a `Fin (t_k) × Fin (M_{k+1})` matrix index
(`schurDim k = t_k · Wext (k+1)` via `finProdFinEquiv`). -/
def schurSlotEquiv (M : Fin (L + 1) → ℕ) (t : ℕ → ℕ) (k : ℕ) :
    Fin (schurDim M t k) ≃ (Fin (t k) × Fin (Wext M (k + 1))) :=
  (finCongr (show schurDim M t k = t k * Wext M (k + 1) from rfl)).trans finProdFinEquiv.symm

/-- The lift slot at boundary `k` as a `Fin (M_{k+1} − t_{k+1}) × Fin (M_{k+2})` matrix index
(`liftDim k = (Wext (k+1) − t (k+1)) · Wext (k+2)` when `k+1 < L`). -/
def liftSlotEquiv (M : Fin (L + 1) → ℕ) (t : ℕ → ℕ) (k : ℕ) (hk : k + 1 < L) :
    Fin (liftDim M t k) ≃ (Fin (Wext M (k + 1) - t (k + 1)) × Fin (Wext M (k + 2))) :=
  (finCongr (show liftDim M t k = (Wext M (k + 1) - t (k + 1)) * Wext M (k + 2) by
    rw [liftDim, if_pos hk])).trans finProdFinEquiv.symm

/-! ## The disjoint scalar readers (via `chartIdxEquiv`) -/

/-- Read the flat coordinate at the Schur-block slot `(i, j)` of boundary `k`. Disjoint across
`(k, i, j)` by `chartIdxEquiv`'s injectivity. -/
noncomputable def readSchur (M : Fin (L + 1) → ℕ) (t : ℕ → ℕ)
    (h0 : t 0 = M 0) (hc : ∀ p, t (p + 1) ≤ (Wext M) (p + 1)) (hL : 0 < L)
    (x : Fin (routeMAmbient M) → 𝕜) (k : Fin L) (i : Fin (t k.val)) (j : Fin (Wext M (k.val + 1))) :
    𝕜 :=
  x ((chartIdxEquiv M t h0 hc hL).symm ⟨k, Sum.inl ((schurSlotEquiv M t k.val).symm (i, j))⟩)

/-- Read the flat coordinate at the lift slot `(i, j)` of boundary `k` (`k+1 < L`). Disjoint across
`(k, i, j)`. -/
noncomputable def readLift (M : Fin (L + 1) → ℕ) (t : ℕ → ℕ)
    (h0 : t 0 = M 0) (hc : ∀ p, t (p + 1) ≤ (Wext M) (p + 1)) (hL : 0 < L)
    (x : Fin (routeMAmbient M) → 𝕜) (k : Fin L) (hk : k.val + 1 < L)
    (i : Fin (Wext M (k.val + 1) - t (k.val + 1))) (j : Fin (Wext M (k.val + 2))) : 𝕜 :=
  x ((chartIdxEquiv M t h0 hc hL).symm ⟨k, Sum.inr ((liftSlotEquiv M t k.val hk).symm (i, j))⟩)

/-! ## Disjointness: distinct `(boundary, role, entry)` triples read distinct flat coords -/

/-- The Schur reader's flat index is injective in `(k, i, j)` — distinct Schur entries read distinct
flat coords (the disjointness the modular hash lacked). -/
theorem readSchur_index_injective (M : Fin (L + 1) → ℕ) (t : ℕ → ℕ)
    (h0 : t 0 = M 0) (hc : ∀ p, t (p + 1) ≤ (Wext M) (p + 1)) (hL : 0 < L)
    {k k' : Fin L} {i : Fin (t k.val)} {j : Fin (Wext M (k.val + 1))}
    {i' : Fin (t k'.val)} {j' : Fin (Wext M (k'.val + 1))}
    (h : (chartIdxEquiv M t h0 hc hL).symm ⟨k, Sum.inl ((schurSlotEquiv M t k.val).symm (i, j))⟩
       = (chartIdxEquiv M t h0 hc hL).symm ⟨k', Sum.inl ((schurSlotEquiv M t k'.val).symm (i', j'))⟩) :
    (⟨k, Sum.inl ((schurSlotEquiv M t k.val).symm (i, j))⟩ : ChartIdx M t)
      = ⟨k', Sum.inl ((schurSlotEquiv M t k'.val).symm (i', j'))⟩ :=
  (chartIdxEquiv M t h0 hc hL).symm.injective h

/-- A Schur slot and a lift slot at the same boundary read DISTINCT flat coords (`Sum.inl ≠ Sum.inr`
under the injective `chartIdxEquiv`). -/
theorem readSchur_ne_readLift_index (M : Fin (L + 1) → ℕ) (t : ℕ → ℕ)
    (h0 : t 0 = M 0) (hc : ∀ p, t (p + 1) ≤ (Wext M) (p + 1)) (hL : 0 < L)
    (k : Fin L) (a : Fin (schurDim M t k.val)) (b : Fin (liftDim M t k.val)) :
    (chartIdxEquiv M t h0 hc hL).symm ⟨k, Sum.inl a⟩
      ≠ (chartIdxEquiv M t h0 hc hL).symm ⟨k, Sum.inr b⟩ := by
  intro h
  have hsig := (chartIdxEquiv M t h0 hc hL).symm.injective h
  -- equal sigmas at the SAME fst `k` ⟹ equal snd (a `Sum`), but `inl ≠ inr`
  have hsnd : (Sum.inl a : Fin (schurDim M t k.val) ⊕ Fin (liftDim M t k.val)) = Sum.inr b := by
    simpa using (Sigma.mk.inj_iff.mp hsig).2
  exact absurd hsnd (by simp)

/-! ## The derived `Bmat` block-stack constructor (the Schur-frame kept part `[K ; X·K]`)

The structured decoder's `Bmat s` is the kept part of the Schur frame: top block `K_s`
(`Text(s+1) × Text(s+1)`), bottom block `X_s · K_s` (`r_s × Text(s+1)`), stacked to
`Text s × Text(s+1)` rows under the descent `Text(s+1) ≤ Text s` (`r_s = Text s − Text(s+1)`). The
validated dependent-width row-stack the next-tide `genBlkFlatStruct` consumes. -/

/-- **The Schur-frame kept block** `Bmat s = [K ; X·K]` (`Text s × Text(s+1)`), the top `K` over the
first `Text(s+1)` rows, the bottom `X·K` over the residual `r_s = Text s − Text(s+1)` rows
(`finSumFinEquiv` row split + a `Text(s+1) + r_s = Text s` reindex; needs the descent
`Text(s+1) ≤ Text s`). -/
noncomputable def bmatStack {L : ℕ} (M : Fin (L + 1) → ℕ) (t : Fin (L + 1) → ℕ) (k : ℕ)
    (hdesc : Text M t (k + 1) ≤ Text M t k)
    (K : Matrix (Fin (Text M t (k + 1))) (Fin (Text M t (k + 1))) 𝕜)
    (X : Matrix (Fin (Text M t k - Text M t (k + 1))) (Fin (Text M t (k + 1))) 𝕜) :
    Matrix (Fin (Text M t k)) (Fin (Text M t (k + 1))) 𝕜 :=
  Matrix.reindex
    (finCongr (show Text M t (k + 1) + (Text M t k - Text M t (k + 1)) = Text M t k by omega))
    (Equiv.refl _)
    (Matrix.of (fun (i : Fin (Text M t (k + 1) + (Text M t k - Text M t (k + 1))))
        (j : Fin (Text M t (k + 1))) =>
      Sum.elim (fun a => K a j) (fun b => (X * K) b j) (finSumFinEquiv.symm i)))

/-- The top `Text(s+1)` rows of `bmatStack` are `K` (the `finSumFinEquiv` `castAdd` block). -/
theorem bmatStack_top {L : ℕ} (M : Fin (L + 1) → ℕ) (t : Fin (L + 1) → ℕ) (k : ℕ)
    (hdesc : Text M t (k + 1) ≤ Text M t k)
    (K : Matrix (Fin (Text M t (k + 1))) (Fin (Text M t (k + 1))) 𝕜)
    (X : Matrix (Fin (Text M t k - Text M t (k + 1))) (Fin (Text M t (k + 1))) 𝕜)
    (a : Fin (Text M t (k + 1))) (j : Fin (Text M t (k + 1))) :
    bmatStack M t k hdesc K X
        (Fin.cast (show Text M t (k + 1) + (Text M t k - Text M t (k + 1)) = Text M t k by omega)
          (Fin.castAdd _ a)) j
      = K a j := by
  rw [bmatStack, Matrix.reindex_apply]
  simp only [Matrix.submatrix_apply, finCongr_symm, finCongr_apply, Equiv.refl_symm,
    Equiv.refl_apply, Matrix.of_apply]
  rw [show (Fin.cast (show Text M t k = Text M t (k + 1) + (Text M t k - Text M t (k + 1)) by omega)
        (Fin.cast (show Text M t (k + 1) + (Text M t k - Text M t (k + 1)) = Text M t k by omega)
          (Fin.castAdd _ a)))
        = Fin.castAdd (Text M t k - Text M t (k + 1)) a from by apply Fin.ext; simp,
    finSumFinEquiv_symm_apply_castAdd, Sum.elim_inl]

/-- The bottom `r_s` rows of `bmatStack` are `X·K` (the `finSumFinEquiv` `natAdd` block). -/
theorem bmatStack_bot {L : ℕ} (M : Fin (L + 1) → ℕ) (t : Fin (L + 1) → ℕ) (k : ℕ)
    (hdesc : Text M t (k + 1) ≤ Text M t k)
    (K : Matrix (Fin (Text M t (k + 1))) (Fin (Text M t (k + 1))) 𝕜)
    (X : Matrix (Fin (Text M t k - Text M t (k + 1))) (Fin (Text M t (k + 1))) 𝕜)
    (b : Fin (Text M t k - Text M t (k + 1))) (j : Fin (Text M t (k + 1))) :
    bmatStack M t k hdesc K X
        (Fin.cast (show Text M t (k + 1) + (Text M t k - Text M t (k + 1)) = Text M t k by omega)
          (Fin.natAdd _ b)) j
      = (X * K) b j := by
  rw [bmatStack, Matrix.reindex_apply]
  simp only [Matrix.submatrix_apply, finCongr_symm, finCongr_apply, Equiv.refl_symm,
    Equiv.refl_apply, Matrix.of_apply]
  rw [show (Fin.cast (show Text M t k = Text M t (k + 1) + (Text M t k - Text M t (k + 1)) by omega)
        (Fin.cast (show Text M t (k + 1) + (Text M t k - Text M t (k + 1)) = Text M t k by omega)
          (Fin.natAdd _ b)))
        = Fin.natAdd (Text M t (k + 1)) b from by apply Fin.ext; simp,
    finSumFinEquiv_symm_apply_natAdd, Sum.elim_inr]

/-! ## The Schur-frame slot K/X/N/E sub-split

The frame slot at GenBlk boundary `s` (size `Text s · Wext s`) sub-splits into the Schur roles
`K` (`Text(s+1)²`), `X` (`r_s·Text(s+1)`), `N` (`Text(s+1)·c_s`), `E` (`r_s·c_s`), where
`r_s = Text s − Text(s+1)`, `c_s = Wext s − Text(s+1)`. The `(((K + X) + N) + E) = Text s · Wext s`
identity is the banked `roleSquare_eq`; the split equiv nests `finSumFinEquiv.symm` left-to-right. -/

/-- **The Schur-frame slot K/X/N/E sub-split equivalence** — `Fin (Text s · Wext s) ≃ (((K ⊕ X) ⊕ N)
⊕ E)` at the role-block sizes, via `roleSquare_eq` + left-nested `finSumFinEquiv.symm`. The decoder's
per-frame role accessor base (`K`, `X`, `N`, `E` blocks of the Schur frame at boundary `s`). -/
def frameSplitEquiv {L : ℕ} (M : Fin (L + 1) → ℕ) (t : Fin (L + 1) → ℕ) (s : ℕ)
    (h1 : Text M t (s + 1) ≤ Text M t s) (h2 : Text M t (s + 1) ≤ Wext M s) :
    Fin (Text M t s * Wext M s) ≃
      (((Fin (Text M t (s + 1) * Text M t (s + 1)) ⊕
         Fin ((Text M t s - Text M t (s + 1)) * Text M t (s + 1))) ⊕
        Fin (Text M t (s + 1) * (Wext M s - Text M t (s + 1)))) ⊕
       Fin ((Text M t s - Text M t (s + 1)) * (Wext M s - Text M t (s + 1)))) :=
  (finCongr (roleSquare_eq h1 h2).symm).trans
    ((finSumFinEquiv.symm).trans
      (((finSumFinEquiv.symm).trans
        (((finSumFinEquiv.symm).trans (Equiv.refl _)).sumCongr (Equiv.refl _))).sumCongr
          (Equiv.refl _)))

/-! ## The derived `Rmat` block-pad constructor (the Schur-frame `u`-carrier `[[0,0],[0,E]]`)

The structured decoder's `Rmat s` is the `u`-carrying residual of the Schur frame: the `E_s`
(`r_s × c_s`) block placed BOTTOM-RIGHT of a `Text s × Wext s` zero matrix, so
`C_s = Bmat_s·chainQ(N_s) + u·Rmat_s = [[K, KN],[XK, XKN + uE]]` (the Schur frame). A
`Matrix.fromBlocks 0 0 0 E` padded by `finSumFinEquiv` row/col reindexes. -/

/-- **The Schur-frame `u`-carrier block** `Rmat s = [[0,0],[0,E]]` (`Text s × Wext s`), the `E_s` block
(`r_s × c_s`) in the bottom-right, zeros elsewhere (`Matrix.fromBlocks 0 0 0 E` + `finSumFinEquiv`
row/col reindex to `Text s × Wext s`). -/
noncomputable def rmatPad {L : ℕ} (M : Fin (L + 1) → ℕ) (t : Fin (L + 1) → ℕ) (s : ℕ)
    (h1 : Text M t (s + 1) ≤ Text M t s) (h2 : Text M t (s + 1) ≤ Wext M s)
    (E : Matrix (Fin (Text M t s - Text M t (s + 1))) (Fin (Wext M s - Text M t (s + 1))) 𝕜) :
    Matrix (Fin (Text M t s)) (Fin (Wext M s)) 𝕜 :=
  Matrix.reindex
    (finSumFinEquiv.trans
      (finCongr (show Text M t (s + 1) + (Text M t s - Text M t (s + 1)) = Text M t s by omega)))
    (finSumFinEquiv.trans
      (finCongr (show Text M t (s + 1) + (Wext M s - Text M t (s + 1)) = Wext M s by omega)))
    (Matrix.fromBlocks (0 : Matrix (Fin (Text M t (s + 1))) (Fin (Text M t (s + 1))) 𝕜) 0 0 E)

end DLNFibre.DLN.RLCT

codex
A key fact from the files: `RouteMFlatStructV` already imports `RouteMGenFlatStruct`, and the chart-slot machinery sits above that in `RouteMChartSlots`/`RouteMChartIdxEquiv`. So pushing reader-aware choice down into `structPivot` is not just a local definitional tweak; it changes the dependency direction of the decoder foundation.
exec
/bin/bash -lc "sed -n '240,520p' lean/DLNFibre/DLN/RLCT/Validate/RouteMFlatLive.lean" in /home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/agent-a9bb11c22680d93d4
 succeeded in 0ms:
    · rw [if_neg (by intro hc; exact h (by simpa using congrArg Fin.val hc)),
        if_neg (by intro hc; exact h (by simpa using congrArg Fin.val hc))]
  · intro b _ hb
    rw [Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.refl_symm, Equiv.refl_apply,
      finCongr_symm, finCongr_apply]
    rw [show (1 : Matrix (Fin (Text M t 0)) (Fin (Text M t 0)) ℝ) i
          (Fin.cast (Text0_eq_Text1_struct M t ha.h0).symm b) = 0 from by
      rw [Matrix.one_apply, if_neg]; intro hc; apply hb; rw [hc]; apply Fin.ext; simp]
    rw [zero_mul]
  · intro hi; exact absurd (Finset.mem_univ _) hi

/-- **`hC0` for the R1 decoder** (`C 0 · suffix = suffix` from `C 0 = 1`). -/
theorem hC0_liveR1 (M t : Fin (L + 1) → ℕ) (ha : StructAdm M t) (p : ℕ) (hp0 : p ≠ 0)
    (hp1 : Text M t (p + 1) ≤ Text M t p) (hp2 : Text M t (p + 1) ≤ Wext M p)
    (rfin : Matrix (Fin (Text M t L)) (Fin (Wext M L)) ℝ)
    (v : ℝ) (x : Fin (routeMAmbient M) → ℝ) :
    (chainOfMt v M t (genBlkFlatLiveR1 M t ha p hp1 hp2 rfin x) (hleStruct M t ha)).toChain.C 0
        * (chainOfMt v M t (genBlkFlatLiveR1 M t ha p hp1 hp2 rfin x)
            (hleStruct M t ha)).toChain.suffix 0 (Nat.zero_le L)
      = (chainOfMt v M t (genBlkFlatLiveR1 M t ha p hp1 hp2 rfin x)
          (hleStruct M t ha)).toChain.suffix 0 (Nat.zero_le L) := by
  rw [C0_eq_one_liveR1 M t ha p hp0 hp1 hp2 rfin v x]; exact Matrix.one_mul _

/-- **The R1 active-center chart** `phiFlatLiveR1 … := phiGen (x p₀) M t (genBlkFlatLiveR1 …) hle`
(`p₀ = structPivot`, the radial scalar). The pivot boundary `p` (active center) carries the fixed
`1`-pivot; the radial is read from `x` at `p₀`. -/
noncomputable def phiFlatLiveR1 (M t : Fin (L + 1) → ℕ) (ha : StructAdm M t)
    (hN : 0 < routeMAmbient M) (p : ℕ)
    (hp1 : Text M t (p + 1) ≤ Text M t p) (hp2 : Text M t (p + 1) ≤ Wext M p)
    (rfin : (Fin (routeMAmbient M) → ℝ) → Matrix (Fin (Text M t L)) (Fin (Wext M L)) ℝ)
    (x : Fin (routeMAmbient M) → ℝ) : Fin (routeMAmbient M) → ℝ :=
  phiGen (x (structPivot M hN)) M t (genBlkFlatLiveR1 M t ha p hp1 hp2 (rfin x) x) (hleStruct M t ha)

/-- **The R1 unit factor** `UvalLiveR1 … := VvalGen (x p₀) M t (genBlkFlatLiveR1 …) hle`. -/
noncomputable def UvalLiveR1 (M t : Fin (L + 1) → ℕ) (ha : StructAdm M t)
    (hN : 0 < routeMAmbient M) (p : ℕ)
    (hp1 : Text M t (p + 1) ≤ Text M t p) (hp2 : Text M t (p + 1) ≤ Wext M p)
    (rfin : (Fin (routeMAmbient M) → ℝ) → Matrix (Fin (Text M t L)) (Fin (Wext M L)) ℝ)
    (x : Fin (routeMAmbient M) → ℝ) : ℝ :=
  VvalGen (x (structPivot M hN)) M t (genBlkFlatLiveR1 M t ha p hp1 hp2 (rfin x) x) (hleStruct M t ha)

/-- **The rate transfers to the R1 active-center chart ∀M (NO bridge)**: `routeMCore M (phiFlatLiveR1 …) =
(x p₀)² · UvalLiveR1 …`. Decoder-agnostic (`routeMCore_phiGen` + the R1 identity boundary `hC0_liveR1`,
which holds since the active center `p ≥ 1` leaves `Bmat 0`/`Rmat 0` untouched). -/
theorem routeMCore_phiFlatLiveR1 (M t : Fin (L + 1) → ℕ) (ha : StructAdm M t)
    (hN : 0 < routeMAmbient M) (p : ℕ) (hp0 : p ≠ 0)
    (hp1 : Text M t (p + 1) ≤ Text M t p) (hp2 : Text M t (p + 1) ≤ Wext M p)
    (rfin : (Fin (routeMAmbient M) → ℝ) → Matrix (Fin (Text M t L)) (Fin (Wext M L)) ℝ)
    (x : Fin (routeMAmbient M) → ℝ) :
    routeMCore M (phiFlatLiveR1 M t ha hN p hp1 hp2 rfin x)
      = (x (structPivot M hN)) ^ 2 * UvalLiveR1 M t ha hN p hp1 hp2 rfin x :=
  routeMCore_phiGen (x (structPivot M hN)) M t (genBlkFlatLiveR1 M t ha p hp1 hp2 (rfin x) x)
    (hleStruct M t ha)
    (hC0_liveR1 M t ha p hp0 hp1 hp2 (rfin x) (x (structPivot M hN)) x)

/-- **Non-vacuity: the R1 pivot E-block genuinely carries the fixed `1`** at `(0,0)` (the gauge-fixed
radial direction), given the strict row/col drops at `p` (so the residual block is nonempty). The
`InteriorDrop` `p*` supplies these strict drops, so the fixed pivot is realised — not vacuous. -/
theorem pivotEIndicator_apply_zero (M t : Fin (L + 1) → ℕ) (s : ℕ)
    (hr : 0 < Text M t s - Text M t (s + 1)) (hc : 0 < Wext M s - Text M t (s + 1)) :
    pivotEIndicator M t s ⟨0, hr⟩ ⟨0, hc⟩ = 1 := by
  simp [pivotEIndicator]

/-- **`UvalLiveR1 ≥ 0`** — sum of squares (banked `VvalGen_nonneg`). -/
theorem UvalLiveR1_nonneg (M t : Fin (L + 1) → ℕ) (ha : StructAdm M t) (hN : 0 < routeMAmbient M)
    (p : ℕ) (hp1 : Text M t (p + 1) ≤ Text M t p) (hp2 : Text M t (p + 1) ≤ Wext M p)
    (rfin : (Fin (routeMAmbient M) → ℝ) → Matrix (Fin (Text M t L)) (Fin (Wext M L)) ℝ)
    (x : Fin (routeMAmbient M) → ℝ) :
    0 ≤ UvalLiveR1 M t ha hN p hp1 hp2 rfin x :=
  VvalGen_nonneg _ M t _ _

/-! ## Wiring the active-center pivot `p*` from `InteriorDrop`

`InteriorDrop M` supplies an interior boundary `p` (`1 ≤ p < L`) with the strict row-drop
`Text(p+1) < Text(p)` and the tail column-drops `Text(b+1) < Wext(b)` on `[p, L−1]` — in particular at
`b = p`, `Text(p+1) < Wext(p)`. So the R1 decoder's hypotheses `hp1 : Text(p+1) ≤ Text(p)`,
`hp2 : Text(p+1) ≤ Wext(p)`, and the nonempty residual block (`pivotEIndicator_apply_zero`) are all
discharged from `InteriorDrop`'s `p*`. -/

/-- **`InteriorDrop` discharges the R1 pivot hypotheses at its `p*`.** From `InteriorDrop M`, the
witnessing `p` (`1 ≤ p < L`) has the row-drop `Text(p+1) < Text(p)` (`hp1` strict) and the column-drop
`Text(p+1) < Wext(p)` (`hp2` strict, the `b = p` tail case) — so the fixed-`1` pivot is placeable. -/
theorem interiorDrop_pivot_hyps (M : Fin (L + 1) → ℕ) (hInt : InteriorDrop M) :
    ∃ p, p ≠ 0 ∧ Text M (tach M) (p + 1) < Text M (tach M) p
      ∧ Text M (tach M) (p + 1) < Wext M p := by
  obtain ⟨_, p, hp1, hpL, hr, hcd⟩ := hInt
  exact ⟨p, by omega, hr, hcd p (le_refl p) hpL⟩

/-! ## The R1 interior witness (count-FREE; reuses the dead-leaf witness)

The `Ubound` a.e.-positivity input for the R1 chart: `∃ w, UvalLiveR1 … w ≠ 0`. At the dead-leaf witness
point `wInt M ha p` (with the leaf `rfin = 0`), the R1 decoder and the dead-leaf `genBlkFlatStruct` AGREE:
the only R1 override is `Rmat p = rmatPad(pivotEIndicator)`, and at `wInt` the dead-leaf reads
`Rmat p = rmatPad(readE (wInt p) p)` where `readE (wInt p)` at the pivot IS the `(0,0)=1` indicator
(`readE_wInt`); `Rfin = 0` matches. So `UvalLiveR1 … 0 wInt = UvalStructV … wInt = achieverUfun wInt ≠ 0`
by the banked `exists_achieverUfun_ne_zero_interior`. NO new induction — count-free non-vanishing. -/

/-- **`readE (wInt p)` at the pivot boundary `p = k+1` IS `pivotEIndicator`** (both the `(0,0)=1`
indicator). The decoder-agreement input. -/
theorem readE_wInt_pivot_eq (M : Fin (L + 1) → ℕ) (ha : StructAdm M (tach M)) (k : ℕ) (hk : k < L) :
    readE M (tach M) ha (wInt M ha (k + 1)) ⟨k, hk⟩ = pivotEIndicator M (tach M) (k + 1) := by
  funext i j
  rw [readE_wInt M ha (k + 1) ⟨k, hk⟩ i j, pivotEIndicator, Matrix.of_apply]
  simp only [Fin.val_mk, true_and]

/-- **The live decoder at `rfin = 0` IS the dead-leaf structured decoder.** Field-wise: Bmat/Nblk/Wblk/Rmat
are definitional copies; the `Rfin` field's `h ▸ 0` transported-zero equals `genBlkFlatStruct`'s `0`.

The `Rfin` `h ▸ 0` transported-zero is closed by `simp only [genBlkFlatLive]` (exposing the dite under the
projection) + `split` + `subst h; rfl` — the `simp only` is the load-bearing step (`show`/`change`/`unfold`
all fail the `▸` motive; `simp only [genBlkFlatLive]` reduces the projection cleanly). -/
theorem genBlkFlatLive_zero_eq (M t : Fin (L + 1) → ℕ) (ha : StructAdm M t)
    (x : Fin (routeMAmbient M) → ℝ) :
    genBlkFlatLive M t ha 0 x = genBlkFlatStruct M t ha x := by
  have hRfin : (genBlkFlatLive M t ha 0 x).Rfin = (genBlkFlatStruct M t ha x).Rfin := by
    funext s
    rw [show (genBlkFlatStruct M t ha x).Rfin s = 0 from by cases s <;> rfl]
    simp only [genBlkFlatLive]
    split
    · rename_i h; subst h; rfl
    · rfl
  -- the other four fields are definitional copies; assemble via the constructor injectivity
  have heq : genBlkFlatLive M t ha 0 x
      = GenBlk.mk (genBlkFlatStruct M t ha x).Bmat (genBlkFlatStruct M t ha x).Nblk
          (genBlkFlatStruct M t ha x).Wblk (genBlkFlatStruct M t ha x).Rmat
          (genBlkFlatStruct M t ha x).Rfin := by
    rw [← hRfin]; rfl
  rw [heq]

/-- **The R1 decoder at `(wInt p, rfin = 0)` equals the dead-leaf structured decoder at `wInt p`.**
Field-by-field: Bmat/Nblk/Wblk are the structured decoder's (unchanged); `Rfin = 0` on both; `Rmat`
agrees — away from `p` the `Function.update` is the identity, and at `p` the fixed `rmatPad(pivotEIndicator)`
equals the structured `rmatPad(readE (wInt p) p)` (`readE_wInt_pivot_eq`). -/
theorem genBlkFlatLiveR1_wInt_Rmat (M : Fin (L + 1) → ℕ) (ha : StructAdm M (tach M)) (k : ℕ) (hk : k < L)
    (hp1 : Text M (tach M) (k + 1 + 1) ≤ Text M (tach M) (k + 1))
    (hp2 : Text M (tach M) (k + 1 + 1) ≤ Wext M (k + 1)) :
    (genBlkFlatLiveR1 M (tach M) ha (k + 1) hp1 hp2 0 (wInt M ha (k + 1))).Rmat
      = (genBlkFlatStruct M (tach M) ha (wInt M ha (k + 1))).Rmat := by
  funext s
  show Function.update (genBlkFlatLive M (tach M) ha 0 (wInt M ha (k + 1))).Rmat (k + 1)
      (rmatPad M (tach M) (k + 1) hp1 hp2 (pivotEIndicator M (tach M) (k + 1))) s = _
  by_cases hs : s = k + 1
  · subst hs
    rw [Function.update_self]
    show _ = (if hk' : k < L then rmatPad M (tach M) (k + 1) (ha.hdesc k hk') (ha.hub k)
        (readE M (tach M) ha (wInt M ha (k + 1)) ⟨k, hk'⟩) else 0)
    rw [dif_pos hk, readE_wInt_pivot_eq M ha k hk]
  · rw [Function.update_of_ne hs]; rfl

/-- **The R1 decoder at `(wInt p, rfin = 0)` IS the dead-leaf structured decoder at `wInt p`.** Combines
`genBlkFlatLive_zero_eq` (the `rfin=0` reduction: Bmat/Nblk/Wblk/Rfin) with `genBlkFlatLiveR1_wInt_Rmat`
(the Rmat fixed-pivot = the structured `readE (wInt) p`). The R1 fixed pivot is invisible at `wInt`
because `wInt`'s `readE` at `p` IS the same `(0,0)=1` indicator. -/
theorem genBlkFlatLiveR1_wInt_eq (M : Fin (L + 1) → ℕ) (ha : StructAdm M (tach M)) (k : ℕ) (hk : k < L)
    (hp1 : Text M (tach M) (k + 1 + 1) ≤ Text M (tach M) (k + 1))
    (hp2 : Text M (tach M) (k + 1 + 1) ≤ Wext M (k + 1)) :
    genBlkFlatLiveR1 M (tach M) ha (k + 1) hp1 hp2 0 (wInt M ha (k + 1))
      = genBlkFlatStruct M (tach M) ha (wInt M ha (k + 1)) := by
  have hbase : genBlkFlatLive M (tach M) ha 0 (wInt M ha (k + 1))
      = genBlkFlatStruct M (tach M) ha (wInt M ha (k + 1)) := genBlkFlatLive_zero_eq M (tach M) ha _
  have heq : genBlkFlatLiveR1 M (tach M) ha (k + 1) hp1 hp2 0 (wInt M ha (k + 1))
      = GenBlk.mk (genBlkFlatLive M (tach M) ha 0 (wInt M ha (k + 1))).Bmat
          (genBlkFlatLive M (tach M) ha 0 (wInt M ha (k + 1))).Nblk
          (genBlkFlatLive M (tach M) ha 0 (wInt M ha (k + 1))).Wblk
          (genBlkFlatLiveR1 M (tach M) ha (k + 1) hp1 hp2 0 (wInt M ha (k + 1))).Rmat
          (genBlkFlatLive M (tach M) ha 0 (wInt M ha (k + 1))).Rfin := rfl
  rw [heq, genBlkFlatLiveR1_wInt_Rmat M ha k hk hp1 hp2,
    show (genBlkFlatLive M (tach M) ha 0 (wInt M ha (k + 1))).Bmat
      = (genBlkFlatStruct M (tach M) ha (wInt M ha (k + 1))).Bmat from by rw [hbase],
    show (genBlkFlatLive M (tach M) ha 0 (wInt M ha (k + 1))).Nblk
      = (genBlkFlatStruct M (tach M) ha (wInt M ha (k + 1))).Nblk from by rw [hbase],
    show (genBlkFlatLive M (tach M) ha 0 (wInt M ha (k + 1))).Wblk
      = (genBlkFlatStruct M (tach M) ha (wInt M ha (k + 1))).Wblk from by rw [hbase],
    show (genBlkFlatLive M (tach M) ha 0 (wInt M ha (k + 1))).Rfin
      = (genBlkFlatStruct M (tach M) ha (wInt M ha (k + 1))).Rfin from by rw [hbase]]

/-- **The R1 interior witness** (the count-free `Ubound` input, now CLOSED): a flat point where the R1
unit is nonzero, at an interior-drop pivot `p = k+1` (the STRICT row-drop `hr` + the tail column-drops
`hcd`, both supplied from `InteriorDrop`'s `p*`; `hML` the leaf). The R1 decoder at `(wInt p, rfin=0)`
IS the dead-leaf `genBlkFlatStruct` (`genBlkFlatLiveR1_wInt_eq`), so `UvalLiveR1 … 0 (wInt p) =
achieverUfun (wInt p)`, nonzero by the exposed dead-leaf `achieverUfun_wInt_ne_zero` — count-free
(non-vanishing, NOT the `minAdm−1` degree). -/
theorem exists_UvalLiveR1_ne_zero_interior (M : Fin (L + 1) → ℕ) (hL : 0 < L)
    (hN : 0 < routeMAmbient M) (k : ℕ) (hkL : k + 1 < L) (hML : 0 < Wext M L)
    (hr : Text M (tach M) (k + 1 + 1) < Text M (tach M) (k + 1))
    (hcd : ∀ b, k + 1 ≤ b → b < L → Text M (tach M) (b + 1) < Wext M b) :
    ∃ w : Fin (routeMAmbient M) → ℝ,
      UvalLiveR1 M (tach M) (structAdm_tach M hL) hN (k + 1)
        (le_of_lt hr) (le_of_lt (hcd (k + 1) (le_refl _) hkL)) (fun _ => 0) w ≠ 0 := by
  refine ⟨wInt M (structAdm_tach M hL) (k + 1), ?_⟩
  rw [UvalLiveR1, genBlkFlatLiveR1_wInt_eq M (structAdm_tach M hL) k (by omega)
    (le_of_lt hr) (le_of_lt (hcd (k + 1) (le_refl _) hkL))]
  -- `VvalGen … (genBlkFlatStruct … wInt) = achieverUfun (wInt)` (definitional); nonzero by the exposed
  -- dead-leaf survival witness at the pivot `p = k+1` (the LOAD-BEARING reduction is proven above).
  show achieverUfun M hL hN (wInt M (structAdm_tach M hL) (k + 1)) ≠ 0
  exact achieverUfun_wInt_ne_zero M hL hN hML (k + 1) (by omega) hkL hr hcd

end DLNFibre.DLN.RLCT

exec
/bin/bash -lc 'rg -n "readerSlot|readerSet|forbiddenSlots|leafSlot|lf0|lf1|PivotNotReader|pivotNot|slotEquiv|colEquivT|active222|interiorDet_headline_222" lean/DLNFibre/DLN/RLCT/Validate/RouteMBData222.lean lean/DLNFibre/DLN/RLCT/Validate/RouteM222Det.lean lean/DLNFibre/DLN/RLCT/Validate/RouteMBData.lean -S' in /home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/agent-a9bb11c22680d93d4
 succeeded in 0ms:
lean/DLNFibre/DLN/RLCT/Validate/RouteMBData222.lean:17:`genBlkFlatLiveR1 M222` blocks, with coords `(u, a, b, n, w0, w1, lf0, lf1)`
lean/DLNFibre/DLN/RLCT/Validate/RouteMBData222.lean:18:(`u = x (structPivot)` radial; `a = readK`, `b = readX`, `n = readN`, `w0,w1 = readW`; `lf0,lf1` the
lean/DLNFibre/DLN/RLCT/Validate/RouteMBData222.lean:21:  `Agen0 = [[a, a·n],[a·b, a·b·n + u]]`, `Agen1 = [[u·lf0 − n·w0, u·lf1 − n·w1],[w0,w1]]`,
lean/DLNFibre/DLN/RLCT/Validate/RouteMBData222.lean:23:`φ = B ∘ pivotBlowupOn active u` with `active = {structPivot} ∪ {lf0, lf1}` (`card 3 = minAdm(2,2,2)`,
lean/DLNFibre/DLN/RLCT/Validate/RouteMBData222.lean:33:the two leaf slots `lf0, lf1` from the FINITE COMPLEMENT `univ \ (insert structPivot readerSet)`
lean/DLNFibre/DLN/RLCT/Validate/RouteMBData222.lean:34:(`readerSet.card ≤ 5`, so the complement has `≥ 2` slots); membership then GIVES `lf ≠ structPivot` and
lean/DLNFibre/DLN/RLCT/Validate/RouteMBData222.lean:35:`lf ∉ readerSet` for free, no opaque comparison.
lean/DLNFibre/DLN/RLCT/Validate/RouteMBData222.lean:203:`lf0/lf1 = rfin x 0 0 / 0 1`):
lean/DLNFibre/DLN/RLCT/Validate/RouteMBData222.lean:205:  `Agen0 = [[a, a·n],[a·b, a·b·n + u]]`,  `Agen1 = [[u·lf0 − n·w0, u·lf1 − n·w1],[w0,w1]]`.
lean/DLNFibre/DLN/RLCT/Validate/RouteMBData222.lean:209:/-- **Layer 1 of the chain** `Agen 1 = [[u·lf0 − n·w0, u·lf1 − n·w1],[w0,w1]]` (kept row `C2 − N1·W1`
lean/DLNFibre/DLN/RLCT/Validate/RouteMBData222.lean:435:slots form `readerSet` (card ≤ 5); the two leaf slots are chosen from the FINITE COMPLEMENT
lean/DLNFibre/DLN/RLCT/Validate/RouteMBData222.lean:436:`univ \ insert structPivot readerSet` (card ≥ 8 − 6 = 2). Membership in the complement then gives
lean/DLNFibre/DLN/RLCT/Validate/RouteMBData222.lean:437:`lf ≠ structPivot` and `lf ∉ readerSet` for free — no opaque comparison. -/
lean/DLNFibre/DLN/RLCT/Validate/RouteMBData222.lean:441:noncomputable def readerSlotK : Fin (routeMAmbient M222) :=
lean/DLNFibre/DLN/RLCT/Validate/RouteMBData222.lean:447:noncomputable def readerSlotX : Fin (routeMAmbient M222) :=
lean/DLNFibre/DLN/RLCT/Validate/RouteMBData222.lean:453:noncomputable def readerSlotN : Fin (routeMAmbient M222) :=
lean/DLNFibre/DLN/RLCT/Validate/RouteMBData222.lean:459:noncomputable def readerSlotW0 : Fin (routeMAmbient M222) :=
lean/DLNFibre/DLN/RLCT/Validate/RouteMBData222.lean:464:noncomputable def readerSlotW1 : Fin (routeMAmbient M222) :=
lean/DLNFibre/DLN/RLCT/Validate/RouteMBData222.lean:470:noncomputable def forbiddenSlots : Finset (Fin (routeMAmbient M222)) :=
lean/DLNFibre/DLN/RLCT/Validate/RouteMBData222.lean:472:    {readerSlotK, readerSlotX, readerSlotN, readerSlotW0, readerSlotW1}
lean/DLNFibre/DLN/RLCT/Validate/RouteMBData222.lean:474:/-- `forbiddenSlots.card ≤ 6` (one pivot + five reader slots). -/
lean/DLNFibre/DLN/RLCT/Validate/RouteMBData222.lean:475:theorem forbiddenSlots_card_le : forbiddenSlots.card ≤ 6 := by
lean/DLNFibre/DLN/RLCT/Validate/RouteMBData222.lean:477:    ({readerSlotK, readerSlotX, readerSlotN, readerSlotW0, readerSlotW1}
lean/DLNFibre/DLN/RLCT/Validate/RouteMBData222.lean:479:  have c2 := Finset.card_insert_le readerSlotK
lean/DLNFibre/DLN/RLCT/Validate/RouteMBData222.lean:480:    ({readerSlotX, readerSlotN, readerSlotW0, readerSlotW1}
lean/DLNFibre/DLN/RLCT/Validate/RouteMBData222.lean:482:  have c3 := Finset.card_insert_le readerSlotX
lean/DLNFibre/DLN/RLCT/Validate/RouteMBData222.lean:483:    ({readerSlotN, readerSlotW0, readerSlotW1} : Finset (Fin (routeMAmbient M222)))
lean/DLNFibre/DLN/RLCT/Validate/RouteMBData222.lean:484:  have c4 := Finset.card_insert_le readerSlotN
lean/DLNFibre/DLN/RLCT/Validate/RouteMBData222.lean:485:    ({readerSlotW0, readerSlotW1} : Finset (Fin (routeMAmbient M222)))
lean/DLNFibre/DLN/RLCT/Validate/RouteMBData222.lean:486:  have c5 := Finset.card_insert_le readerSlotW0
lean/DLNFibre/DLN/RLCT/Validate/RouteMBData222.lean:487:    ({readerSlotW1} : Finset (Fin (routeMAmbient M222)))
lean/DLNFibre/DLN/RLCT/Validate/RouteMBData222.lean:488:  have c6 : ({readerSlotW1} : Finset (Fin (routeMAmbient M222))).card = 1 := Finset.card_singleton _
lean/DLNFibre/DLN/RLCT/Validate/RouteMBData222.lean:489:  simp only [forbiddenSlots] at *
lean/DLNFibre/DLN/RLCT/Validate/RouteMBData222.lean:492:/-- The complement of `forbiddenSlots` has at least 2 slots (`8 − 6`). -/
lean/DLNFibre/DLN/RLCT/Validate/RouteMBData222.lean:494:    2 ≤ ((Finset.univ : Finset (Fin (routeMAmbient M222))) \ forbiddenSlots).card := by
lean/DLNFibre/DLN/RLCT/Validate/RouteMBData222.lean:495:  have hle := Finset.le_card_sdiff forbiddenSlots (Finset.univ : Finset (Fin (routeMAmbient M222)))
lean/DLNFibre/DLN/RLCT/Validate/RouteMBData222.lean:498:  have := forbiddenSlots_card_le
lean/DLNFibre/DLN/RLCT/Validate/RouteMBData222.lean:501:/-- Two distinct slots in the complement of `forbiddenSlots` (the leaf coords). -/
lean/DLNFibre/DLN/RLCT/Validate/RouteMBData222.lean:503:    ∃ lf0 lf1 : Fin (routeMAmbient M222),
lean/DLNFibre/DLN/RLCT/Validate/RouteMBData222.lean:504:      lf0 ∈ (Finset.univ : Finset (Fin (routeMAmbient M222))) \ forbiddenSlots
lean/DLNFibre/DLN/RLCT/Validate/RouteMBData222.lean:505:      ∧ lf1 ∈ (Finset.univ : Finset (Fin (routeMAmbient M222))) \ forbiddenSlots
lean/DLNFibre/DLN/RLCT/Validate/RouteMBData222.lean:506:      ∧ lf0 ≠ lf1 := by
lean/DLNFibre/DLN/RLCT/Validate/RouteMBData222.lean:510:/-- The first leaf slot (`Classical.choose`; in the complement, so `≠ structPivot`, `∉ readerSet`). -/
lean/DLNFibre/DLN/RLCT/Validate/RouteMBData222.lean:511:noncomputable def lf0 : Fin (routeMAmbient M222) := (exists_leaf_pair).choose
lean/DLNFibre/DLN/RLCT/Validate/RouteMBData222.lean:514:noncomputable def lf1 : Fin (routeMAmbient M222) := (exists_leaf_pair).choose_spec.choose
lean/DLNFibre/DLN/RLCT/Validate/RouteMBData222.lean:516:theorem lf0_mem : lf0 ∈ (Finset.univ : Finset (Fin (routeMAmbient M222))) \ forbiddenSlots :=
lean/DLNFibre/DLN/RLCT/Validate/RouteMBData222.lean:519:theorem lf1_mem : lf1 ∈ (Finset.univ : Finset (Fin (routeMAmbient M222))) \ forbiddenSlots :=
lean/DLNFibre/DLN/RLCT/Validate/RouteMBData222.lean:522:theorem lf0_ne_lf1 : lf0 ≠ lf1 := (exists_leaf_pair).choose_spec.choose_spec.2.2
lean/DLNFibre/DLN/RLCT/Validate/RouteMBData222.lean:524:/-- `lf0 ≠ structPivot` (the leaf slot avoids the pivot — from the complement). -/
lean/DLNFibre/DLN/RLCT/Validate/RouteMBData222.lean:525:theorem lf0_ne_pivot : lf0 ≠ structPivot M222 hN_M222 := by
lean/DLNFibre/DLN/RLCT/Validate/RouteMBData222.lean:527:  have := lf0_mem
lean/DLNFibre/DLN/RLCT/Validate/RouteMBData222.lean:531:theorem lf1_ne_pivot : lf1 ≠ structPivot M222 hN_M222 := by
lean/DLNFibre/DLN/RLCT/Validate/RouteMBData222.lean:533:  have := lf1_mem
lean/DLNFibre/DLN/RLCT/Validate/RouteMBData222.lean:537:/-- The R2 active set `{structPivot, lf0, lf1}` (card 3 = minAdm; pbo scales the two leaf slots). -/
lean/DLNFibre/DLN/RLCT/Validate/RouteMBData222.lean:538:noncomputable def active222 : Finset (Fin (routeMAmbient M222)) :=
lean/DLNFibre/DLN/RLCT/Validate/RouteMBData222.lean:539:  {structPivot M222 hN_M222, lf0, lf1}
lean/DLNFibre/DLN/RLCT/Validate/RouteMBData222.lean:541:/-- `structPivot ∈ active222`. -/
lean/DLNFibre/DLN/RLCT/Validate/RouteMBData222.lean:542:theorem structPivot_mem_active222 : structPivot M222 hN_M222 ∈ active222 :=
lean/DLNFibre/DLN/RLCT/Validate/RouteMBData222.lean:545:/-- `active222.card = 3 = minAdm M222` (pivot + two distinct leaf slots). -/
lean/DLNFibre/DLN/RLCT/Validate/RouteMBData222.lean:546:theorem active222_card : active222.card = minAdm M222 := by
lean/DLNFibre/DLN/RLCT/Validate/RouteMBData222.lean:547:  have hp0 : structPivot M222 hN_M222 ≠ lf0 := fun h => lf0_ne_pivot h.symm
lean/DLNFibre/DLN/RLCT/Validate/RouteMBData222.lean:548:  have hp1 : structPivot M222 hN_M222 ≠ lf1 := fun h => lf1_ne_pivot h.symm
lean/DLNFibre/DLN/RLCT/Validate/RouteMBData222.lean:549:  rw [active222, Finset.card_insert_of_notMem (by
lean/DLNFibre/DLN/RLCT/Validate/RouteMBData222.lean:551:    Finset.card_insert_of_notMem (by simp only [Finset.mem_singleton]; exact lf0_ne_lf1),
lean/DLNFibre/DLN/RLCT/Validate/RouteMBData222.lean:554:/-- A reader slot is `≠ lf0` and `≠ lf1` (it lies in `forbiddenSlots`, the leaf slots in the
lean/DLNFibre/DLN/RLCT/Validate/RouteMBData222.lean:556:theorem readerSlot_ne_leaf (q : Fin (routeMAmbient M222)) (hq : q ∈ forbiddenSlots) :
lean/DLNFibre/DLN/RLCT/Validate/RouteMBData222.lean:557:    q ≠ lf0 ∧ q ≠ lf1 := by
lean/DLNFibre/DLN/RLCT/Validate/RouteMBData222.lean:558:  have h0 := lf0_mem; have h1 := lf1_mem
lean/DLNFibre/DLN/RLCT/Validate/RouteMBData222.lean:562:/-- `pivotBlowupOn active222 structPivot x` at the pivot is `x structPivot`. -/
lean/DLNFibre/DLN/RLCT/Validate/RouteMBData222.lean:564:    pivotBlowupOn active222 (structPivot M222 hN_M222) x (structPivot M222 hN_M222)
lean/DLNFibre/DLN/RLCT/Validate/RouteMBData222.lean:568:/-- `pivotBlowupOn` at `lf0` scales by the pivot: `= x structPivot · x lf0`. -/
lean/DLNFibre/DLN/RLCT/Validate/RouteMBData222.lean:569:theorem pbo_lf0 (x : Fin (routeMAmbient M222) → ℝ) :
lean/DLNFibre/DLN/RLCT/Validate/RouteMBData222.lean:570:    pivotBlowupOn active222 (structPivot M222 hN_M222) x lf0
lean/DLNFibre/DLN/RLCT/Validate/RouteMBData222.lean:571:      = x (structPivot M222 hN_M222) * x lf0 := by
lean/DLNFibre/DLN/RLCT/Validate/RouteMBData222.lean:573:  rw [if_neg lf0_ne_pivot, if_pos (show lf0 ∈ active222 from by
lean/DLNFibre/DLN/RLCT/Validate/RouteMBData222.lean:574:    rw [active222]; exact Finset.mem_insert_of_mem (Finset.mem_insert_self _ _))]
lean/DLNFibre/DLN/RLCT/Validate/RouteMBData222.lean:576:/-- `pivotBlowupOn` at `lf1` scales by the pivot: `= x structPivot · x lf1`. -/
lean/DLNFibre/DLN/RLCT/Validate/RouteMBData222.lean:577:theorem pbo_lf1 (x : Fin (routeMAmbient M222) → ℝ) :
lean/DLNFibre/DLN/RLCT/Validate/RouteMBData222.lean:578:    pivotBlowupOn active222 (structPivot M222 hN_M222) x lf1
lean/DLNFibre/DLN/RLCT/Validate/RouteMBData222.lean:579:      = x (structPivot M222 hN_M222) * x lf1 := by
lean/DLNFibre/DLN/RLCT/Validate/RouteMBData222.lean:581:  rw [if_neg lf1_ne_pivot, if_pos (show lf1 ∈ active222 from by
lean/DLNFibre/DLN/RLCT/Validate/RouteMBData222.lean:582:    rw [active222]; exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem
lean/DLNFibre/DLN/RLCT/Validate/RouteMBData222.lean:585:/-- `pivotBlowupOn` fixes any reader slot (`∉ {lf0, lf1}`; the pivot branch fixes it too). -/
lean/DLNFibre/DLN/RLCT/Validate/RouteMBData222.lean:587:    (hq : q ∈ forbiddenSlots) :
lean/DLNFibre/DLN/RLCT/Validate/RouteMBData222.lean:588:    pivotBlowupOn active222 (structPivot M222 hN_M222) x q = x q := by
lean/DLNFibre/DLN/RLCT/Validate/RouteMBData222.lean:589:  obtain ⟨hq0, hq1⟩ := readerSlot_ne_leaf q hq
lean/DLNFibre/DLN/RLCT/Validate/RouteMBData222.lean:593:      if_neg (show q ∉ active222 from by
lean/DLNFibre/DLN/RLCT/Validate/RouteMBData222.lean:594:        rw [active222]; simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
lean/DLNFibre/DLN/RLCT/Validate/RouteMBData222.lean:599:`rfin222 x := !![x lf0, x lf1]` reads the two complement leaf slots directly. The faithful boundary
lean/DLNFibre/DLN/RLCT/Validate/RouteMBData222.lean:602:readers `a/b/n/w0/w1` from `y`, and the leaf from `y lf0 / y lf1`. `B` is radial-free (`det DB = a²`,
lean/DLNFibre/DLN/RLCT/Validate/RouteMBData222.lean:603:the engine). The map identity `phiFlatLiveR1 = B ∘ pivotBlowupOn active222 structPivot` then follows
lean/DLNFibre/DLN/RLCT/Validate/RouteMBData222.lean:606:/-- The leaf reader: `rfin222 x = !![x lf0, x lf1]` (`1×2`, reading the two complement leaf slots). -/
lean/DLNFibre/DLN/RLCT/Validate/RouteMBData222.lean:609:  !![x lf0, x lf1]
lean/DLNFibre/DLN/RLCT/Validate/RouteMBData222.lean:613:`y lf0 / y lf1`:
lean/DLNFibre/DLN/RLCT/Validate/RouteMBData222.lean:614:`A0 = [[a, a·n],[a·b, a·b·n + y_p]]`, `A1 = [[y_lf0 − n·w0, y_lf1 − n·w1],[w0, w1]]`. -/
lean/DLNFibre/DLN/RLCT/Validate/RouteMBData222.lean:619:    (Fin.cons (!![y lf0 - nRead y * w0Read y, y lf1 - nRead y * w1Read y;
lean/DLNFibre/DLN/RLCT/Validate/RouteMBData222.lean:627:/-! ## The reader values are stable under `pivotBlowupOn` (they sit in `forbiddenSlots`) -/
lean/DLNFibre/DLN/RLCT/Validate/RouteMBData222.lean:630:theorem aRead_eq (x : Fin (routeMAmbient M222) → ℝ) : aRead x = x readerSlotK := rfl
lean/DLNFibre/DLN/RLCT/Validate/RouteMBData222.lean:631:theorem bRead_eq (x : Fin (routeMAmbient M222) → ℝ) : bRead x = x readerSlotX := rfl
lean/DLNFibre/DLN/RLCT/Validate/RouteMBData222.lean:632:theorem nRead_eq (x : Fin (routeMAmbient M222) → ℝ) : nRead x = x readerSlotN := rfl
lean/DLNFibre/DLN/RLCT/Validate/RouteMBData222.lean:633:theorem w0Read_eq (x : Fin (routeMAmbient M222) → ℝ) : w0Read x = x readerSlotW0 := rfl
lean/DLNFibre/DLN/RLCT/Validate/RouteMBData222.lean:634:theorem w1Read_eq (x : Fin (routeMAmbient M222) → ℝ) : w1Read x = x readerSlotW1 := rfl
lean/DLNFibre/DLN/RLCT/Validate/RouteMBData222.lean:636:/-- A reader slot is in `forbiddenSlots`. -/
lean/DLNFibre/DLN/RLCT/Validate/RouteMBData222.lean:637:theorem readerSlotK_mem : readerSlotK ∈ forbiddenSlots :=
lean/DLNFibre/DLN/RLCT/Validate/RouteMBData222.lean:639:theorem readerSlotX_mem : readerSlotX ∈ forbiddenSlots :=
lean/DLNFibre/DLN/RLCT/Validate/RouteMBData222.lean:641:theorem readerSlotN_mem : readerSlotN ∈ forbiddenSlots :=
lean/DLNFibre/DLN/RLCT/Validate/RouteMBData222.lean:644:theorem readerSlotW0_mem : readerSlotW0 ∈ forbiddenSlots :=
lean/DLNFibre/DLN/RLCT/Validate/RouteMBData222.lean:647:theorem readerSlotW1_mem : readerSlotW1 ∈ forbiddenSlots :=
lean/DLNFibre/DLN/RLCT/Validate/RouteMBData222.lean:651:/-- The reader values are invariant under `pivotBlowupOn` (the slots lie in `forbiddenSlots`). -/
lean/DLNFibre/DLN/RLCT/Validate/RouteMBData222.lean:653:    aRead (pivotBlowupOn active222 (structPivot M222 hN_M222) x) = aRead x := by
lean/DLNFibre/DLN/RLCT/Validate/RouteMBData222.lean:654:  rw [aRead_eq, aRead_eq, pbo_reader x readerSlotK readerSlotK_mem]
lean/DLNFibre/DLN/RLCT/Validate/RouteMBData222.lean:656:    bRead (pivotBlowupOn active222 (structPivot M222 hN_M222) x) = bRead x := by
lean/DLNFibre/DLN/RLCT/Validate/RouteMBData222.lean:657:  rw [bRead_eq, bRead_eq, pbo_reader x readerSlotX readerSlotX_mem]
lean/DLNFibre/DLN/RLCT/Validate/RouteMBData222.lean:659:    nRead (pivotBlowupOn active222 (structPivot M222 hN_M222) x) = nRead x := by
lean/DLNFibre/DLN/RLCT/Validate/RouteMBData222.lean:660:  rw [nRead_eq, nRead_eq, pbo_reader x readerSlotN readerSlotN_mem]
lean/DLNFibre/DLN/RLCT/Validate/RouteMBData222.lean:662:    w0Read (pivotBlowupOn active222 (structPivot M222 hN_M222) x) = w0Read x := by
lean/DLNFibre/DLN/RLCT/Validate/RouteMBData222.lean:663:  rw [w0Read_eq, w0Read_eq, pbo_reader x readerSlotW0 readerSlotW0_mem]
lean/DLNFibre/DLN/RLCT/Validate/RouteMBData222.lean:665:    w1Read (pivotBlowupOn active222 (structPivot M222 hN_M222) x) = w1Read x := by
lean/DLNFibre/DLN/RLCT/Validate/RouteMBData222.lean:666:  rw [w1Read_eq, w1Read_eq, pbo_reader x readerSlotW1 readerSlotW1_mem]
lean/DLNFibre/DLN/RLCT/Validate/RouteMBData222.lean:668:/-! ## The map identity `phiFlatLiveR1 = B ∘ pivotBlowupOn active222 structPivot` (`hmap`) -/
lean/DLNFibre/DLN/RLCT/Validate/RouteMBData222.lean:672:`reindex` value-preserving); layer 1 is `Agen1_Glr_eq` with the leaf `rfin222 x = !![x lf0, x lf1]`
lean/DLNFibre/DLN/RLCT/Validate/RouteMBData222.lean:673:scaled to `x_p·x_lfᵢ` on the RHS via `pbo_lf0/lf1`, and the readers fixed via `*_pbo`. -/
lean/DLNFibre/DLN/RLCT/Validate/RouteMBData222.lean:677:      = Bparams (pivotBlowupOn active222 (structPivot M222 hN_M222) x) := by
lean/DLNFibre/DLN/RLCT/Validate/RouteMBData222.lean:679:  have hB0 : (Bparams (pivotBlowupOn active222 (structPivot M222 hN_M222) x)) 0
lean/DLNFibre/DLN/RLCT/Validate/RouteMBData222.lean:683:    show (!![aRead (pivotBlowupOn active222 (structPivot M222 hN_M222) x), _; _, _]
lean/DLNFibre/DLN/RLCT/Validate/RouteMBData222.lean:686:  have hB1 : (Bparams (pivotBlowupOn active222 (structPivot M222 hN_M222) x)) 1
lean/DLNFibre/DLN/RLCT/Validate/RouteMBData222.lean:687:      = (!![x (structPivot M222 hN_M222) * x lf0 - nRead x * w0Read x,
lean/DLNFibre/DLN/RLCT/Validate/RouteMBData222.lean:688:          x (structPivot M222 hN_M222) * x lf1 - nRead x * w1Read x;
lean/DLNFibre/DLN/RLCT/Validate/RouteMBData222.lean:690:    show (!![(pivotBlowupOn active222 (structPivot M222 hN_M222) x) lf0 - _, _; _, _]
lean/DLNFibre/DLN/RLCT/Validate/RouteMBData222.lean:692:    rw [nRead_pbo, w0Read_pbo, w1Read_pbo, pbo_lf0, pbo_lf1]
lean/DLNFibre/DLN/RLCT/Validate/RouteMBData222.lean:708:    -- the leaf `rfin222 x ⟨0⟩ ⟨j⟩ = (!![x lf0, x lf1]) ⟨0⟩ ⟨j⟩ = x lfⱼ` reduces by `rfl`
lean/DLNFibre/DLN/RLCT/Validate/RouteMBData222.lean:711:/-- **`hmap`: `phiFlatLiveR1 M222 … rfin222 = Bchart ∘ pivotBlowupOn active222 structPivot`** — the
lean/DLNFibre/DLN/RLCT/Validate/RouteMBData222.lean:715:      = Bchart ∘ pivotBlowupOn active222 (structPivot M222 hN_M222) := by
lean/DLNFibre/DLN/RLCT/Validate/RouteMBData222.lean:734:`slotEquiv` (the 8 slots `a,b,n,w0,w1,p,lf0,lf1` are pairwise distinct), turning `toMatrix'` into an
lean/DLNFibre/DLN/RLCT/Validate/RouteMBData222.lean:739:theorem readerSlotK_ne_X : readerSlotK ≠ readerSlotX := by
lean/DLNFibre/DLN/RLCT/Validate/RouteMBData222.lean:740:  unfold readerSlotK readerSlotX
lean/DLNFibre/DLN/RLCT/Validate/RouteMBData222.lean:746:theorem readerSlotK_ne_N : readerSlotK ≠ readerSlotN := by
lean/DLNFibre/DLN/RLCT/Validate/RouteMBData222.lean:747:  unfold readerSlotK readerSlotN
lean/DLNFibre/DLN/RLCT/Validate/RouteMBData222.lean:753:theorem readerSlotX_ne_N : readerSlotX ≠ readerSlotN := by
lean/DLNFibre/DLN/RLCT/Validate/RouteMBData222.lean:754:  unfold readerSlotX readerSlotN
lean/DLNFibre/DLN/RLCT/Validate/RouteMBData222.lean:760:theorem readerSlotK_ne_W0 : readerSlotK ≠ readerSlotW0 := by
lean/DLNFibre/DLN/RLCT/Validate/RouteMBData222.lean:761:  unfold readerSlotK readerSlotW0
lean/DLNFibre/DLN/RLCT/Validate/RouteMBData222.lean:766:theorem readerSlotK_ne_W1 : readerSlotK ≠ readerSlotW1 := by
lean/DLNFibre/DLN/RLCT/Validate/RouteMBData222.lean:767:  unfold readerSlotK readerSlotW1
lean/DLNFibre/DLN/RLCT/Validate/RouteMBData222.lean:772:theorem readerSlotX_ne_W0 : readerSlotX ≠ readerSlotW0 := by
lean/DLNFibre/DLN/RLCT/Validate/RouteMBData222.lean:773:  unfold readerSlotX readerSlotW0
lean/DLNFibre/DLN/RLCT/Validate/RouteMBData222.lean:778:theorem readerSlotX_ne_W1 : readerSlotX ≠ readerSlotW1 := by
lean/DLNFibre/DLN/RLCT/Validate/RouteMBData222.lean:779:  unfold readerSlotX readerSlotW1
lean/DLNFibre/DLN/RLCT/Validate/RouteMBData222.lean:784:theorem readerSlotN_ne_W0 : readerSlotN ≠ readerSlotW0 := by
lean/DLNFibre/DLN/RLCT/Validate/RouteMBData222.lean:785:  unfold readerSlotN readerSlotW0
lean/DLNFibre/DLN/RLCT/Validate/RouteMBData222.lean:790:theorem readerSlotN_ne_W1 : readerSlotN ≠ readerSlotW1 := by
lean/DLNFibre/DLN/RLCT/Validate/RouteMBData222.lean:791:  unfold readerSlotN readerSlotW1
lean/DLNFibre/DLN/RLCT/Validate/RouteMBData222.lean:796:theorem readerSlotW0_ne_W1 : readerSlotW0 ≠ readerSlotW1 := by
lean/DLNFibre/DLN/RLCT/Validate/RouteMBData222.lean:797:  unfold readerSlotW0 readerSlotW1
lean/DLNFibre/DLN/RLCT/Validate/RouteMBData222.lean:811:carried as the explicit hypothesis `pivotNotReader` and threaded to the det headline. -/
lean/DLNFibre/DLN/RLCT/Validate/RouteMBData222.lean:814:noncomputable def readerSet : Finset (Fin (routeMAmbient M222)) :=
lean/DLNFibre/DLN/RLCT/Validate/RouteMBData222.lean:815:  {readerSlotK, readerSlotX, readerSlotN, readerSlotW0, readerSlotW1}
lean/DLNFibre/DLN/RLCT/Validate/RouteMBData222.lean:820:def PivotNotReader : Prop := structPivot M222 hN_M222 ∉ readerSet
lean/DLNFibre/DLN/RLCT/Validate/RouteMBData222.lean:822:/-- The 8 slots in column order `[a, b, n, w0, w1, p, lf0, lf1]` (the variable order of the entry
lean/DLNFibre/DLN/RLCT/Validate/RouteMBData222.lean:823:Jacobian). Pairwise distinct (under `PivotNotReader`), hence — on `Fin 8` — bijective. -/
lean/DLNFibre/DLN/RLCT/Validate/RouteMBData222.lean:825:  ![readerSlotK, readerSlotX, readerSlotN, readerSlotW0, readerSlotW1,
lean/DLNFibre/DLN/RLCT/Validate/RouteMBData222.lean:826:    structPivot M222 hN_M222, lf0, lf1]
lean/DLNFibre/DLN/RLCT/Validate/RouteMBData222.lean:830:non-degeneracy `PivotNotReader`. -/
lean/DLNFibre/DLN/RLCT/Validate/RouteMBData222.lean:831:theorem slotList_injective (hpiv : PivotNotReader) : Function.Injective slotList := by
lean/DLNFibre/DLN/RLCT/Validate/RouteMBData222.lean:832:  have hKlf0 := (readerSlot_ne_leaf readerSlotK readerSlotK_mem).1
lean/DLNFibre/DLN/RLCT/Validate/RouteMBData222.lean:833:  have hKlf1 := (readerSlot_ne_leaf readerSlotK readerSlotK_mem).2
lean/DLNFibre/DLN/RLCT/Validate/RouteMBData222.lean:834:  have hXlf0 := (readerSlot_ne_leaf readerSlotX readerSlotX_mem).1
lean/DLNFibre/DLN/RLCT/Validate/RouteMBData222.lean:835:  have hXlf1 := (readerSlot_ne_leaf readerSlotX readerSlotX_mem).2
lean/DLNFibre/DLN/RLCT/Validate/RouteMBData222.lean:836:  have hNlf0 := (readerSlot_ne_leaf readerSlotN readerSlotN_mem).1
lean/DLNFibre/DLN/RLCT/Validate/RouteMBData222.lean:837:  have hNlf1 := (readerSlot_ne_leaf readerSlotN readerSlotN_mem).2
lean/DLNFibre/DLN/RLCT/Validate/RouteMBData222.lean:838:  have hW0lf0 := (readerSlot_ne_leaf readerSlotW0 readerSlotW0_mem).1
lean/DLNFibre/DLN/RLCT/Validate/RouteMBData222.lean:839:  have hW0lf1 := (readerSlot_ne_leaf readerSlotW0 readerSlotW0_mem).2
lean/DLNFibre/DLN/RLCT/Validate/RouteMBData222.lean:840:  have hW1lf0 := (readerSlot_ne_leaf readerSlotW1 readerSlotW1_mem).1
lean/DLNFibre/DLN/RLCT/Validate/RouteMBData222.lean:841:  have hW1lf1 := (readerSlot_ne_leaf readerSlotW1 readerSlotW1_mem).2
lean/DLNFibre/DLN/RLCT/Validate/RouteMBData222.lean:842:  -- the pivot avoids each reader, from `PivotNotReader`
lean/DLNFibre/DLN/RLCT/Validate/RouteMBData222.lean:843:  have hpK : structPivot M222 hN_M222 ≠ readerSlotK := fun h => hpiv (by
lean/DLNFibre/DLN/RLCT/Validate/RouteMBData222.lean:844:    rw [readerSet, h]; exact Finset.mem_insert_self _ _)
lean/DLNFibre/DLN/RLCT/Validate/RouteMBData222.lean:845:  have hpX : structPivot M222 hN_M222 ≠ readerSlotX := fun h => hpiv (by
lean/DLNFibre/DLN/RLCT/Validate/RouteMBData222.lean:846:    rw [readerSet, h]; exact Finset.mem_insert_of_mem (Finset.mem_insert_self _ _))
lean/DLNFibre/DLN/RLCT/Validate/RouteMBData222.lean:847:  have hpN : structPivot M222 hN_M222 ≠ readerSlotN := fun h => hpiv (by
lean/DLNFibre/DLN/RLCT/Validate/RouteMBData222.lean:848:    rw [readerSet, h]
lean/DLNFibre/DLN/RLCT/Validate/RouteMBData222.lean:850:  have hpW0 : structPivot M222 hN_M222 ≠ readerSlotW0 := fun h => hpiv (by
lean/DLNFibre/DLN/RLCT/Validate/RouteMBData222.lean:851:    rw [readerSet, h]
lean/DLNFibre/DLN/RLCT/Validate/RouteMBData222.lean:854:  have hpW1 : structPivot M222 hN_M222 ≠ readerSlotW1 := fun h => hpiv (by
lean/DLNFibre/DLN/RLCT/Validate/RouteMBData222.lean:855:    rw [readerSet, h]
lean/DLNFibre/DLN/RLCT/Validate/RouteMBData222.lean:864:          | exact readerSlotK_ne_X hij | exact readerSlotK_ne_X hij.symm
lean/DLNFibre/DLN/RLCT/Validate/RouteMBData222.lean:865:          | exact readerSlotK_ne_N hij | exact readerSlotK_ne_N hij.symm
lean/DLNFibre/DLN/RLCT/Validate/RouteMBData222.lean:866:          | exact readerSlotX_ne_N hij | exact readerSlotX_ne_N hij.symm
lean/DLNFibre/DLN/RLCT/Validate/RouteMBData222.lean:867:          | exact readerSlotK_ne_W0 hij | exact readerSlotK_ne_W0 hij.symm
lean/DLNFibre/DLN/RLCT/Validate/RouteMBData222.lean:868:          | exact readerSlotK_ne_W1 hij | exact readerSlotK_ne_W1 hij.symm
lean/DLNFibre/DLN/RLCT/Validate/RouteMBData222.lean:869:          | exact readerSlotX_ne_W0 hij | exact readerSlotX_ne_W0 hij.symm
lean/DLNFibre/DLN/RLCT/Validate/RouteMBData222.lean:870:          | exact readerSlotX_ne_W1 hij | exact readerSlotX_ne_W1 hij.symm
lean/DLNFibre/DLN/RLCT/Validate/RouteMBData222.lean:871:          | exact readerSlotN_ne_W0 hij | exact readerSlotN_ne_W0 hij.symm
lean/DLNFibre/DLN/RLCT/Validate/RouteMBData222.lean:872:          | exact readerSlotN_ne_W1 hij | exact readerSlotN_ne_W1 hij.symm
lean/DLNFibre/DLN/RLCT/Validate/RouteMBData222.lean:873:          | exact readerSlotW0_ne_W1 hij | exact readerSlotW0_ne_W1 hij.symm
lean/DLNFibre/DLN/RLCT/Validate/RouteMBData222.lean:874:          | exact lf0_ne_lf1 hij | exact lf0_ne_lf1 hij.symm
lean/DLNFibre/DLN/RLCT/Validate/RouteMBData222.lean:875:          | exact lf0_ne_pivot hij | exact lf0_ne_pivot hij.symm
lean/DLNFibre/DLN/RLCT/Validate/RouteMBData222.lean:876:          | exact lf1_ne_pivot hij | exact lf1_ne_pivot hij.symm
lean/DLNFibre/DLN/RLCT/Validate/RouteMBData222.lean:880:          | exact hKlf0 hij | exact hKlf0 hij.symm | exact hKlf1 hij | exact hKlf1 hij.symm
lean/DLNFibre/DLN/RLCT/Validate/RouteMBData222.lean:881:          | exact hXlf0 hij | exact hXlf0 hij.symm | exact hXlf1 hij | exact hXlf1 hij.symm
lean/DLNFibre/DLN/RLCT/Validate/RouteMBData222.lean:882:          | exact hNlf0 hij | exact hNlf0 hij.symm | exact hNlf1 hij | exact hNlf1 hij.symm
lean/DLNFibre/DLN/RLCT/Validate/RouteMBData222.lean:883:          | exact hW0lf0 hij | exact hW0lf0 hij.symm | exact hW0lf1 hij | exact hW0lf1 hij.symm
lean/DLNFibre/DLN/RLCT/Validate/RouteMBData222.lean:884:          | exact hW1lf0 hij | exact hW1lf0 hij.symm | exact hW1lf1 hij | exact hW1lf1 hij.symm)
lean/DLNFibre/DLN/RLCT/Validate/RouteMBData222.lean:887:cardinalities), given the radial-axis non-degeneracy `PivotNotReader`. -/
lean/DLNFibre/DLN/RLCT/Validate/RouteMBData222.lean:888:noncomputable def slotEquiv (hpiv : PivotNotReader) : Fin 8 ≃ Fin (routeMAmbient M222) :=
lean/DLNFibre/DLN/RLCT/Validate/RouteMBData222.lean:892:theorem slotEquiv_apply (hpiv : PivotNotReader) (i : Fin 8) : slotEquiv hpiv i = slotList i := rfl
lean/DLNFibre/DLN/RLCT/Validate/RouteMBData222.lean:897:(`A0 = !![w4,w1;w5,w6]`, `A1 = !![w0,w7;w2,w3]`): coords `0 = y_lf0 − n·w0`, `1 = a·n`, `2 = w0`,
lean/DLNFibre/DLN/RLCT/Validate/RouteMBData222.lean:898:`3 = w1`, `4 = a`, `5 = a·b`, `6 = a·b·n + y_p`, `7 = y_lf1 − n·w1` (`a = y_K`, `b = y_X`,
lean/DLNFibre/DLN/RLCT/Validate/RouteMBData222.lean:901:  ![y lf0 - y readerSlotN * y readerSlotW0,
lean/DLNFibre/DLN/RLCT/Validate/RouteMBData222.lean:902:    y readerSlotK * y readerSlotN,
lean/DLNFibre/DLN/RLCT/Validate/RouteMBData222.lean:903:    y readerSlotW0,
lean/DLNFibre/DLN/RLCT/Validate/RouteMBData222.lean:904:    y readerSlotW1,
lean/DLNFibre/DLN/RLCT/Validate/RouteMBData222.lean:905:    y readerSlotK,
lean/DLNFibre/DLN/RLCT/Validate/RouteMBData222.lean:906:    y readerSlotK * y readerSlotX,
lean/DLNFibre/DLN/RLCT/Validate/RouteMBData222.lean:907:    y readerSlotK * y readerSlotX * y readerSlotN + y (structPivot M222 hN_M222),
lean/DLNFibre/DLN/RLCT/Validate/RouteMBData222.lean:908:    y lf1 - y readerSlotN * y readerSlotW1]
lean/DLNFibre/DLN/RLCT/Validate/RouteMBData222.lean:929:        = (!![y lf0 - nRead y * w0Read y, y lf1 - nRead y * w1Read y;
lean/DLNFibre/DLN/RLCT/Validate/RouteMBData222.lean:957:    (![ bprj lf0 - ((u readerSlotN) • bprj readerSlotW0 + (u readerSlotW0) • bprj readerSlotN),
lean/DLNFibre/DLN/RLCT/Validate/RouteMBData222.lean:958:        (u readerSlotK) • bprj readerSlotN + (u readerSlotN) • bprj readerSlotK,
lean/DLNFibre/DLN/RLCT/Validate/RouteMBData222.lean:959:        bprj readerSlotW0,
lean/DLNFibre/DLN/RLCT/Validate/RouteMBData222.lean:960:        bprj readerSlotW1,
lean/DLNFibre/DLN/RLCT/Validate/RouteMBData222.lean:961:        bprj readerSlotK,
lean/DLNFibre/DLN/RLCT/Validate/RouteMBData222.lean:962:        (u readerSlotK) • bprj readerSlotX + (u readerSlotX) • bprj readerSlotK,
lean/DLNFibre/DLN/RLCT/Validate/RouteMBData222.lean:963:        ((u readerSlotX * u readerSlotN) • bprj readerSlotK
lean/DLNFibre/DLN/RLCT/Validate/RouteMBData222.lean:964:          + (u readerSlotK * u readerSlotN) • bprj readerSlotX
lean/DLNFibre/DLN/RLCT/Validate/RouteMBData222.lean:965:          + (u readerSlotK * u readerSlotX) • bprj readerSlotN)
lean/DLNFibre/DLN/RLCT/Validate/RouteMBData222.lean:967:        bprj lf1 - ((u readerSlotN) • bprj readerSlotW1 + (u readerSlotW1) • bprj readerSlotN)]
lean/DLNFibre/DLN/RLCT/Validate/RouteMBData222.lean:981:  · -- output 0: `y lf0 - y readerSlotN * y readerSlotW0`
lean/DLNFibre/DLN/RLCT/Validate/RouteMBData222.lean:982:    refine (hap lf0).sub ?_
lean/DLNFibre/DLN/RLCT/Validate/RouteMBData222.lean:983:    have := (hap readerSlotN).mul (hap readerSlotW0)
lean/DLNFibre/DLN/RLCT/Validate/RouteMBData222.lean:987:  · -- output 1: `y readerSlotK * y readerSlotN`
lean/DLNFibre/DLN/RLCT/Validate/RouteMBData222.lean:988:    exact (hap readerSlotK).mul (hap readerSlotN)
lean/DLNFibre/DLN/RLCT/Validate/RouteMBData222.lean:989:  · exact hap readerSlotW0
lean/DLNFibre/DLN/RLCT/Validate/RouteMBData222.lean:990:  · exact hap readerSlotW1
lean/DLNFibre/DLN/RLCT/Validate/RouteMBData222.lean:991:  · exact hap readerSlotK
lean/DLNFibre/DLN/RLCT/Validate/RouteMBData222.lean:992:  · -- output 5: `y readerSlotK * y readerSlotX`
lean/DLNFibre/DLN/RLCT/Validate/RouteMBData222.lean:993:    exact (hap readerSlotK).mul (hap readerSlotX)
lean/DLNFibre/DLN/RLCT/Validate/RouteMBData222.lean:994:  · -- output 6: `y readerSlotK * y readerSlotX * y readerSlotN + y (structPivot)`
lean/DLNFibre/DLN/RLCT/Validate/RouteMBData222.lean:996:    have := ((hap readerSlotK).mul (hap readerSlotX)).mul (hap readerSlotN)
lean/DLNFibre/DLN/RLCT/Validate/RouteMBData222.lean:1000:  · -- output 7: `y lf1 - y readerSlotN * y readerSlotW1`
lean/DLNFibre/DLN/RLCT/Validate/RouteMBData222.lean:1001:    refine (hap lf1).sub ?_
lean/DLNFibre/DLN/RLCT/Validate/RouteMBData222.lean:1002:    have := (hap readerSlotN).mul (hap readerSlotW1)
lean/DLNFibre/DLN/RLCT/Validate/RouteMBData222.lean:1025:`[a, b, n, p, w0, w1, lf0, lf1]` (`slotListC`), row order `[out4, out5, out1, out6, out2, out3,
lean/DLNFibre/DLN/RLCT/Validate/RouteMBData222.lean:1028:/-- The column slot list in the lower-triangular order `[a, b, n, p, w0, w1, lf0, lf1]`. -/
lean/DLNFibre/DLN/RLCT/Validate/RouteMBData222.lean:1030:  ![readerSlotK, readerSlotX, readerSlotN, structPivot M222 hN_M222,
lean/DLNFibre/DLN/RLCT/Validate/RouteMBData222.lean:1031:    readerSlotW0, readerSlotW1, lf0, lf1]
lean/DLNFibre/DLN/RLCT/Validate/RouteMBData222.lean:1034:/-- `slotListC` is injective (a reordering of `slotList`), under `PivotNotReader`. -/
lean/DLNFibre/DLN/RLCT/Validate/RouteMBData222.lean:1035:theorem slotListC_injective (hpiv : PivotNotReader) : Function.Injective slotListC := by
lean/DLNFibre/DLN/RLCT/Validate/RouteMBData222.lean:1036:  have hKlf0 := (readerSlot_ne_leaf readerSlotK readerSlotK_mem).1
lean/DLNFibre/DLN/RLCT/Validate/RouteMBData222.lean:1037:  have hKlf1 := (readerSlot_ne_leaf readerSlotK readerSlotK_mem).2
lean/DLNFibre/DLN/RLCT/Validate/RouteMBData222.lean:1038:  have hXlf0 := (readerSlot_ne_leaf readerSlotX readerSlotX_mem).1
lean/DLNFibre/DLN/RLCT/Validate/RouteMBData222.lean:1039:  have hXlf1 := (readerSlot_ne_leaf readerSlotX readerSlotX_mem).2
lean/DLNFibre/DLN/RLCT/Validate/RouteMBData222.lean:1040:  have hNlf0 := (readerSlot_ne_leaf readerSlotN readerSlotN_mem).1
lean/DLNFibre/DLN/RLCT/Validate/RouteMBData222.lean:1041:  have hNlf1 := (readerSlot_ne_leaf readerSlotN readerSlotN_mem).2
lean/DLNFibre/DLN/RLCT/Validate/RouteMBData222.lean:1042:  have hW0lf0 := (readerSlot_ne_leaf readerSlotW0 readerSlotW0_mem).1
lean/DLNFibre/DLN/RLCT/Validate/RouteMBData222.lean:1043:  have hW0lf1 := (readerSlot_ne_leaf readerSlotW0 readerSlotW0_mem).2
lean/DLNFibre/DLN/RLCT/Validate/RouteMBData222.lean:1044:  have hW1lf0 := (readerSlot_ne_leaf readerSlotW1 readerSlotW1_mem).1
lean/DLNFibre/DLN/RLCT/Validate/RouteMBData222.lean:1045:  have hW1lf1 := (readerSlot_ne_leaf readerSlotW1 readerSlotW1_mem).2
lean/DLNFibre/DLN/RLCT/Validate/RouteMBData222.lean:1046:  have hpK : structPivot M222 hN_M222 ≠ readerSlotK := fun h => hpiv (by
lean/DLNFibre/DLN/RLCT/Validate/RouteMBData222.lean:1047:    rw [readerSet, h]; exact Finset.mem_insert_self _ _)
lean/DLNFibre/DLN/RLCT/Validate/RouteMBData222.lean:1048:  have hpX : structPivot M222 hN_M222 ≠ readerSlotX := fun h => hpiv (by
lean/DLNFibre/DLN/RLCT/Validate/RouteMBData222.lean:1049:    rw [readerSet, h]; exact Finset.mem_insert_of_mem (Finset.mem_insert_self _ _))
lean/DLNFibre/DLN/RLCT/Validate/RouteMBData222.lean:1050:  have hpN : structPivot M222 hN_M222 ≠ readerSlotN := fun h => hpiv (by
lean/DLNFibre/DLN/RLCT/Validate/RouteMBData222.lean:1051:    rw [readerSet, h]
lean/DLNFibre/DLN/RLCT/Validate/RouteMBData222.lean:1053:  have hpW0 : structPivot M222 hN_M222 ≠ readerSlotW0 := fun h => hpiv (by
lean/DLNFibre/DLN/RLCT/Validate/RouteMBData222.lean:1054:    rw [readerSet, h]
lean/DLNFibre/DLN/RLCT/Validate/RouteMBData222.lean:1057:  have hpW1 : structPivot M222 hN_M222 ≠ readerSlotW1 := fun h => hpiv (by
lean/DLNFibre/DLN/RLCT/Validate/RouteMBData222.lean:1058:    rw [readerSet, h]
lean/DLNFibre/DLN/RLCT/Validate/RouteMBData222.lean:1061:  have hplf0 : structPivot M222 hN_M222 ≠ lf0 := fun h => lf0_ne_pivot h.symm
lean/DLNFibre/DLN/RLCT/Validate/RouteMBData222.lean:1062:  have hplf1 : structPivot M222 hN_M222 ≠ lf1 := fun h => lf1_ne_pivot h.symm
lean/DLNFibre/DLN/RLCT/Validate/RouteMBData222.lean:1069:          | exact readerSlotK_ne_X hij | exact readerSlotK_ne_X hij.symm
lean/DLNFibre/DLN/RLCT/Validate/RouteMBData222.lean:1070:          | exact readerSlotK_ne_N hij | exact readerSlotK_ne_N hij.symm
lean/DLNFibre/DLN/RLCT/Validate/RouteMBData222.lean:1071:          | exact readerSlotX_ne_N hij | exact readerSlotX_ne_N hij.symm
lean/DLNFibre/DLN/RLCT/Validate/RouteMBData222.lean:1072:          | exact readerSlotK_ne_W0 hij | exact readerSlotK_ne_W0 hij.symm
lean/DLNFibre/DLN/RLCT/Validate/RouteMBData222.lean:1073:          | exact readerSlotK_ne_W1 hij | exact readerSlotK_ne_W1 hij.symm
lean/DLNFibre/DLN/RLCT/Validate/RouteMBData222.lean:1074:          | exact readerSlotX_ne_W0 hij | exact readerSlotX_ne_W0 hij.symm
lean/DLNFibre/DLN/RLCT/Validate/RouteMBData222.lean:1075:          | exact readerSlotX_ne_W1 hij | exact readerSlotX_ne_W1 hij.symm
lean/DLNFibre/DLN/RLCT/Validate/RouteMBData222.lean:1076:          | exact readerSlotN_ne_W0 hij | exact readerSlotN_ne_W0 hij.symm
lean/DLNFibre/DLN/RLCT/Validate/RouteMBData222.lean:1077:          | exact readerSlotN_ne_W1 hij | exact readerSlotN_ne_W1 hij.symm
lean/DLNFibre/DLN/RLCT/Validate/RouteMBData222.lean:1078:          | exact readerSlotW0_ne_W1 hij | exact readerSlotW0_ne_W1 hij.symm
lean/DLNFibre/DLN/RLCT/Validate/RouteMBData222.lean:1079:          | exact lf0_ne_lf1 hij | exact lf0_ne_lf1 hij.symm
lean/DLNFibre/DLN/RLCT/Validate/RouteMBData222.lean:1080:          | exact hplf0 hij | exact hplf0 hij.symm | exact hplf1 hij | exact hplf1 hij.symm
lean/DLNFibre/DLN/RLCT/Validate/RouteMBData222.lean:1084:          | exact hKlf0 hij | exact hKlf0 hij.symm | exact hKlf1 hij | exact hKlf1 hij.symm
lean/DLNFibre/DLN/RLCT/Validate/RouteMBData222.lean:1085:          | exact hXlf0 hij | exact hXlf0 hij.symm | exact hXlf1 hij | exact hXlf1 hij.symm
lean/DLNFibre/DLN/RLCT/Validate/RouteMBData222.lean:1086:          | exact hNlf0 hij | exact hNlf0 hij.symm | exact hNlf1 hij | exact hNlf1 hij.symm
lean/DLNFibre/DLN/RLCT/Validate/RouteMBData222.lean:1087:          | exact hW0lf0 hij | exact hW0lf0 hij.symm | exact hW0lf1 hij | exact hW0lf1 hij.symm
lean/DLNFibre/DLN/RLCT/Validate/RouteMBData222.lean:1088:          | exact hW1lf0 hij | exact hW1lf0 hij.symm | exact hW1lf1 hij | exact hW1lf1 hij.symm)
lean/DLNFibre/DLN/RLCT/Validate/RouteMBData222.lean:1091:noncomputable def colEquivT (hpiv : PivotNotReader) : Fin 8 ≃ Fin (routeMAmbient M222) :=
lean/DLNFibre/DLN/RLCT/Validate/RouteMBData222.lean:1103:/-- The row reindex as a `Fin 8 ≃ Fin (routeMAmbient M222)` (matching `colEquivT`'s target, so
lean/DLNFibre/DLN/RLCT/Validate/RouteMBData222.lean:1135:theorem single_slotListC (hpiv : PivotNotReader) (j k : Fin 8) :
lean/DLNFibre/DLN/RLCT/Validate/RouteMBData222.lean:1146:theorem single_at_eq (hpiv : PivotNotReader) (j k : Fin 8) (s : Fin (routeMAmbient M222))
lean/DLNFibre/DLN/RLCT/Validate/RouteMBData222.lean:1152:theorem single_at_readerK (hpiv : PivotNotReader) (j : Fin 8) :
lean/DLNFibre/DLN/RLCT/Validate/RouteMBData222.lean:1153:    (Pi.single (slotListC j) (1 : ℝ) : Fin (routeMAmbient M222) → ℝ) readerSlotK
lean/DLNFibre/DLN/RLCT/Validate/RouteMBData222.lean:1155:theorem single_at_readerX (hpiv : PivotNotReader) (j : Fin 8) :
lean/DLNFibre/DLN/RLCT/Validate/RouteMBData222.lean:1156:    (Pi.single (slotListC j) (1 : ℝ) : Fin (routeMAmbient M222) → ℝ) readerSlotX
lean/DLNFibre/DLN/RLCT/Validate/RouteMBData222.lean:1158:theorem single_at_readerN (hpiv : PivotNotReader) (j : Fin 8) :
lean/DLNFibre/DLN/RLCT/Validate/RouteMBData222.lean:1159:    (Pi.single (slotListC j) (1 : ℝ) : Fin (routeMAmbient M222) → ℝ) readerSlotN
lean/DLNFibre/DLN/RLCT/Validate/RouteMBData222.lean:1161:theorem single_at_pivot (hpiv : PivotNotReader) (j : Fin 8) :
lean/DLNFibre/DLN/RLCT/Validate/RouteMBData222.lean:1164:theorem single_at_readerW0 (hpiv : PivotNotReader) (j : Fin 8) :
lean/DLNFibre/DLN/RLCT/Validate/RouteMBData222.lean:1165:    (Pi.single (slotListC j) (1 : ℝ) : Fin (routeMAmbient M222) → ℝ) readerSlotW0
lean/DLNFibre/DLN/RLCT/Validate/RouteMBData222.lean:1167:theorem single_at_readerW1 (hpiv : PivotNotReader) (j : Fin 8) :
lean/DLNFibre/DLN/RLCT/Validate/RouteMBData222.lean:1168:    (Pi.single (slotListC j) (1 : ℝ) : Fin (routeMAmbient M222) → ℝ) readerSlotW1
lean/DLNFibre/DLN/RLCT/Validate/RouteMBData222.lean:1170:theorem single_at_lf0 (hpiv : PivotNotReader) (j : Fin 8) :
lean/DLNFibre/DLN/RLCT/Validate/RouteMBData222.lean:1171:    (Pi.single (slotListC j) (1 : ℝ) : Fin (routeMAmbient M222) → ℝ) lf0
lean/DLNFibre/DLN/RLCT/Validate/RouteMBData222.lean:1173:theorem single_at_lf1 (hpiv : PivotNotReader) (j : Fin 8) :
lean/DLNFibre/DLN/RLCT/Validate/RouteMBData222.lean:1174:    (Pi.single (slotListC j) (1 : ℝ) : Fin (routeMAmbient M222) → ℝ) lf1
lean/DLNFibre/DLN/RLCT/Validate/RouteMBData222.lean:1178:/-- **The reindexed entry Jacobian** `(toMatrix' (TbCLM u)).submatrix rowPerm (colEquivT hpiv) =
lean/DLNFibre/DLN/RLCT/Validate/RouteMBData222.lean:1180:theorem TbCLM_toMatrix_reindex (hpiv : PivotNotReader) (u : Fin (routeMAmbient M222) → ℝ) :
lean/DLNFibre/DLN/RLCT/Validate/RouteMBData222.lean:1181:    (LinearMap.toMatrix' (TbCLM u).toLinearMap).submatrix rowEquiv (colEquivT hpiv)
lean/DLNFibre/DLN/RLCT/Validate/RouteMBData222.lean:1183:  have hcol : ∀ k : Fin 8, (colEquivT hpiv k : Fin (routeMAmbient M222)) = slotListC k :=
lean/DLNFibre/DLN/RLCT/Validate/RouteMBData222.lean:1187:  change (TbCLM u) (Pi.single (colEquivT hpiv j) 1) (rowEquiv i) = litMatLT u i j
lean/DLNFibre/DLN/RLCT/Validate/RouteMBData222.lean:1201:      single_at_lf0 hpiv, single_at_lf1 hpiv,
lean/DLNFibre/DLN/RLCT/Validate/RouteMBData222.lean:1206:theorem TbCLM_abs_det (hpiv : PivotNotReader) (u : Fin (routeMAmbient M222) → ℝ) :
lean/DLNFibre/DLN/RLCT/Validate/RouteMBData222.lean:1212:        rowEquiv (colEquivT hpiv)).det|
lean/DLNFibre/DLN/RLCT/Validate/RouteMBData222.lean:1214:    abs_det_submatrix_equiv_equiv rowEquiv (colEquivT hpiv) _
lean/DLNFibre/DLN/RLCT/Validate/RouteMBData222.lean:1216:      |((LinearMap.toMatrix' (TbCLM u).toLinearMap).submatrix rowEquiv (colEquivT hpiv)).det|
lean/DLNFibre/DLN/RLCT/Validate/RouteMBData222.lean:1221:          rowEquiv (colEquivT hpiv)).det| := hsub.symm
lean/DLNFibre/DLN/RLCT/Validate/RouteMBData222.lean:1227:theorem DB_abs_det (hpiv : PivotNotReader) (u : Fin (routeMAmbient M222) → ℝ) :
lean/DLNFibre/DLN/RLCT/Validate/RouteMBData222.lean:1244:  fun s => if s = 0 then |aRead (pivotBlowupOn active222 (structPivot M222 hN_M222) u)| ^ 2 else 1
lean/DLNFibre/DLN/RLCT/Validate/RouteMBData222.lean:1248:      = |aRead (pivotBlowupOn active222 (structPivot M222 hN_M222) u)| ^ 2 := by
lean/DLNFibre/DLN/RLCT/Validate/RouteMBData222.lean:1252:`PivotNotReader` (the radial axis distinct from the Schur readers). All fields landed:
lean/DLNFibre/DLN/RLCT/Validate/RouteMBData222.lean:1254:noncomputable def bData222 (hpiv : PivotNotReader) (u : Fin (routeMAmbient M222) → ℝ) :
lean/DLNFibre/DLN/RLCT/Validate/RouteMBData222.lean:1256:  active := active222
lean/DLNFibre/DLN/RLCT/Validate/RouteMBData222.lean:1257:  hp_mem := structPivot_mem_active222
lean/DLNFibre/DLN/RLCT/Validate/RouteMBData222.lean:1258:  hcard := active222_card
lean/DLNFibre/DLN/RLCT/Validate/RouteMBData222.lean:1260:  DB := DB (pivotBlowupOn active222 (structPivot M222 hN_M222) u)
lean/DLNFibre/DLN/RLCT/Validate/RouteMBData222.lean:1261:  hasDB := Bchart_hasFDerivAt (pivotBlowupOn active222 (structPivot M222 hN_M222) u)
lean/DLNFibre/DLN/RLCT/Validate/RouteMBData222.lean:1265:    rw [DB_abs_det hpiv (pivotBlowupOn active222 (structPivot M222 hN_M222) u), engine222_prod]
lean/DLNFibre/DLN/RLCT/Validate/RouteMBData222.lean:1267:/-- **The unconditional-modulo-`PivotNotReader` interior-det headline for `phiFlatLiveR1 M222`**:
lean/DLNFibre/DLN/RLCT/Validate/RouteMBData222.lean:1270:theorem interiorDet_headline_222 (hpiv : PivotNotReader) (u : Fin (routeMAmbient M222) → ℝ) :

exec
/bin/bash -lc "sed -n '1,220p' lean/DLNFibre/DLN/RLCT/Validate/RouteMBData.lean" in /home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/agent-a9bb11c22680d93d4
 succeeded in 0ms:
import DLNFibre.DLN.RLCT.Validate.RouteMBInterface

/-!
# `RouteMBData` — the radial-scaling core of the B-interface map identity (the `hmap` algebra)

⚠ **ROUTING NOTE: the `B := phiGen 1 (genBlkFlatLiveR1 …)` consumers below
(`phiFlatLiveR1_eq_B_comp_pivotBlowupOn`, `_chart`) are SUPERSEDED — the WRONG `B`.** Their hyps
(`hslot`/`hchart`) are undischargeable for `genBlkFlatLiveR1` (the affine-radial verdict,
`codex/affine-radial-resolution-answer.md`): `genBlkFlatLiveR1`'s `Rmat p` literal-1
becomes the pivot COORDINATE contribution in the COMPOSITE chart (`C_p = x_p·[1,…]`), blown up
MULTIPLICATIVELY — NOT an additive `u·1` constant; a u-free `B` reading it would steal the pivot DOF
(det 0). The FAITHFUL decomposition is the banked `(2,2,2)` `pack/T/pb` route
(`RouteM222Det.{T222, pack222, pb222}`, `phi222_abs_det = |u0|²·|u4|`) generalized to ∀M — its `B =
paramsEquivFlat ∘ pack ∘ (boundary frame) ∘ (shear)` reads the pivot as an ORDINARY coord, u-free
with `det DB = engine ≠ 0`. The pack/T generalization is a separate module (the controller-cleared
build); `radialComp_abs_det` (radial = pure `pivotBlowupOn`) stands. The ALGEBRA lemmas here
(`smulRmatRfin`, `phiGen_smul_radial`, the `…_smulRmatRfin` lemmas) are SOUND/reusable;
only the two `phiFlatLiveR1_eq_B_comp_pivotBlowupOn` consumers are off the build path.

The genuinely-reachable, network-free core of `BData.hmap` (`phiFlatLiveR1 = B ∘ pivotBlowupOn`):
the radial scalar `u` of the achiever chart `phiGen u M t B hle` can be ABSORBED into the block
data, because `phiGen` reads `u` and `B` ONLY through `Cgen u M t B hle = Bmat·chainQ(N) + u•Rmat`
(interior) / `u•Rfin` (leaf) — the `u` multiplies ONLY the residual blocks `Rmat`/`Rfin`. So scaling
those two fields by `u` (keeping `Bmat`/`Nblk`/`Wblk`) and setting the radial to `1` reproduces the
SAME chart:

  `phiGen u M t B hle = phiGen 1 M t (smulRmatRfin u B) hle`.

This is the cast-LIGHT algebraic identity (pure `GenBlk`/`Cgen`/`Agen` matrix algebra, NO
`chartIdxEquiv` slot surgery). It is the lever Codex's gate verdict (`codex/bdata-gate-answer.md`,
V-CONSTRUCTIBLE-HARD) flagged: define the boundary factor with the radial set to `1` reading the
already-scaled residual coordinates; the radial degree comes entirely from `pivotBlowupOn`, not from
`B`.

It does NOT route through the Codex-REFUTED `composeFold fs = φ` disjoint-factor fold (genm-mapeq
@d7e75c8d): the radial is factored out as the genuine `pivotBlowupOn` map, and `B` here is the
radial-`1` chart itself — an arbitrary map, NOT a disjoint fold (so the chain-coupling unsoundness
that killed F1 does not apply; see `codex/bdata-gate-answer.md` Q2).

* `smulRmatRfin` — scale a `GenBlk`'s residual blocks `Rmat`/`Rfin` by a scalar (the
  radial-absorbing reblocking), keeping `Bmat`/`Nblk`/`Wblk`.
* `Cgen_smulRmatRfin` — `Cgen 1 (smulRmatRfin u B) = Cgen u B` (the per-boundary residual identity).
* `Agen_smulRmatRfin` / `chartParamsGen_smulRmatRfin` — the layer / chart-parameter consequences.
* `phiGen_smul_radial` — `phiGen u M t B hle = phiGen 1 M t (smulRmatRfin u B) hle` (chart id).

Axiom-clean `[propext, Classical.choice, Quot.sound]` (pure matrix algebra; no analysis).
-/

namespace DLNFibre.DLN.RLCT

open Matrix
open scoped BigOperators

variable {L : ℕ}
variable {𝕜 : Type} [CommRing 𝕜]

/-- **The radial-absorbing reblocking.** Scale a `GenBlk`'s residual blocks `Rmat`/`Rfin` by `u`,
keeping the kept/residual/lift blocks `Bmat`/`Nblk`/`Wblk` unchanged. Then
`Cgen 1 (smulRmatRfin u B) = Cgen u B`: the radial `u` is absorbed into the residual coordinates. -/
noncomputable def smulRmatRfin (u : 𝕜) (M t : Fin (L + 1) → ℕ) (B : GenBlk M t 𝕜) :
    GenBlk M t 𝕜 where
  Bmat := B.Bmat
  Nblk := B.Nblk
  Wblk := B.Wblk
  Rmat := fun k => u • B.Rmat k
  Rfin := fun k => u • B.Rfin k

/-- **The per-boundary residual identity** `Cgen 1 (smulRmatRfin u B) = Cgen u B` (every `k`).
Interior: `Bmat·chainQ(N) + 1•(u•Rmat) = Bmat·chainQ(N) + u•Rmat`; leaf: `1•(u•Rfin) = u•Rfin`. The
`Bmat`/`Nblk` blocks are shared (`smulRmatRfin` keeps them), so the `chainQ` part is untouched. -/
theorem Cgen_smulRmatRfin (u : 𝕜) (M t : Fin (L + 1) → ℕ) (B : GenBlk M t 𝕜)
    (hle : ∀ k, k < L → Text M t (k + 1) ≤ Wext M k) (k : ℕ) :
    Cgen 1 M t (smulRmatRfin u M t B) hle k = Cgen u M t B hle k := by
  unfold Cgen smulRmatRfin
  by_cases hk : k < L
  · rw [dif_pos hk, dif_pos hk, one_smul]
  · rw [dif_neg hk, dif_neg hk, one_smul]

/-- **The per-layer identity** `Agen 1 (smulRmatRfin u B) = Agen u B` (every `k`). `Agen u B k =
chainA(N_k, W_k, Cgen u B (k+1))`; the `N_k`/`W_k` blocks are shared (`smulRmatRfin` keeps
`Nblk`/`Wblk`) and the accumulator `Cgen (k+1)` is matched by `Cgen_smulRmatRfin`. -/
theorem Agen_smulRmatRfin (u : 𝕜) (M t : Fin (L + 1) → ℕ) (B : GenBlk M t 𝕜)
    (hle : ∀ k, k < L → Text M t (k + 1) ≤ Wext M k) (k : ℕ) :
    Agen 1 M t (smulRmatRfin u M t B) hle k = Agen u M t B hle k := by
  unfold Agen
  by_cases hk : k < L
  · rw [dif_pos hk, dif_pos hk]
    show chainA _ ((smulRmatRfin u M t B).Nblk k) ((smulRmatRfin u M t B).Wblk k) _ = _
    rw [Cgen_smulRmatRfin u M t B hle (k + 1)]
    rfl
  · rw [dif_neg hk, dif_neg hk]

/-- **The chart-parameter identity** `chartParamsGen 1 (smulRmatRfin u B) = chartParamsGen u B`.
`chartParamsGen` is the width-reindex of the chain layer `chainOfMt.toChain.A = Agen`, matched
boundary-wise by `Agen_smulRmatRfin`. -/
theorem chartParamsGen_smulRmatRfin (u : ℝ) (M t : Fin (L + 1) → ℕ) (B : GenBlk M t)
    (hle : ∀ k, k < L → Text M t (k + 1) ≤ Wext M k) :
    chartParamsGen 1 M t (smulRmatRfin u M t B) hle = chartParamsGen u M t B hle := by
  funext s
  unfold chartParamsGen
  congr 1
  exact Agen_smulRmatRfin u M t B hle s.val

/-- **The radial-scaling chart identity** `phiGen u M t B hle = phiGen 1 M t (smulRmatRfin u B)`.
The radial scalar `u` of the achiever chart is absorbed into the residual blocks: `phiGen` reads `u`
only through `Cgen`, which `smulRmatRfin` reproduces at radial `1`. The load-bearing algebra of the
B-interface map identity (the radial degree then comes from `pivotBlowupOn`, not from `B`). -/
theorem phiGen_smul_radial (u : ℝ) (M t : Fin (L + 1) → ℕ) (B : GenBlk M t)
    (hle : ∀ k, k < L → Text M t (k + 1) ≤ Wext M k) :
    phiGen u M t B hle = phiGen 1 M t (smulRmatRfin u M t B) hle := by
  unfold phiGen
  rw [chartParamsGen_smulRmatRfin u M t B hle]

/-- **Non-vacuity**: at radial `u = 1` the reblocking is invisible (`smulRmatRfin 1 B` has the same
`Cgen` as `B`), so `phiGen 1 B = phiGen 1 (smulRmatRfin 1 B)` — the identity is consistent, and at a
genuine radial it relocates the scalar into the residual blocks. -/
example (M t : Fin (L + 1) → ℕ) (B : GenBlk M t)
    (hle : ∀ k, k < L → Text M t (k + 1) ≤ Wext M k) :
    phiGen 1 M t B hle = phiGen 1 M t (smulRmatRfin 1 M t B) hle :=
  phiGen_smul_radial 1 M t B hle

/-! ## The `φ = B ∘ pivotBlowupOn` reduction (the map-identity half, modulo the slot-identification)

⚠ **SUPERSEDED by `phiFlatLiveR1_eq_B_comp_pivotBlowupOn_chart` below (the Fix-B CHART contract).**
The `hslot` hypothesis below is FALSE for `genBlkFlatLiveR1` — REFUTED
sorry-free in `RouteMSlotId.not_hslot_genBlkFlatLiveR1` (triple-confirmed: hand + Codex + sympy
`route-i-l2/fixed_pivot_refutation.py`). `phiFlatLiveR1` uses the GAUGE-FIXED pivot decoder
`genBlkFlatLiveR1`: its pivot `Rmat p = rmatPad (pivotEIndicator p)` is the LITERAL `1` (not a free
`readE`). So `smulRmatRfin (x p₀)` scales it to entry `x p₀`, while the RHS keeps the SAME constant
`pivotEIndicator` (entry `1`) — `hslot` forces `x p₀ = 1`, false for general `x`.

DEEPER: `φ = B ∘ pivotBlowupOn` ITSELF fails for the fixed pivot — the pivot E-block carries the
ADDITIVE radial `u·1 = u`, which the MULTIPLICATIVE `pivotBlowupOn` (blowing up OTHER active coords)
cannot reproduce; `B` (radial-`1`) loses that `u`. The route-(i) decoder choice is UNSETTLED
(controller-level: the fixed pivot is the `minAdm−1` count gauge per the `RouteMFlatLive` header;
re-targeting at the live-pivot `phiFlatLive` reshapes the det/count). It stays a VALID CONDITIONAL
(the `phiGen_smul_radial` reduction is sound + reusable) but is OFF the build path until resettled.

The radial split `φ = B ∘ pivotBlowupOn active p₀`: `B` the radial-`1` boundary chart
`B y := phiGen 1 M t (genBlkFlatLiveR1 … (rfin y) y) hle`. Holds iff the `GenBlk`-level
SLOT-IDENTIFICATION `smulRmatRfin (x p₀) (B₀ x) = B₀ (pivotBlowupOn active p₀ x)` (`hslot`) — FALSE
(above). Via `phiGen_smul_radial` + `hslot`. -/
theorem phiFlatLiveR1_eq_B_comp_pivotBlowupOn (M t : Fin (L + 1) → ℕ) (ha : StructAdm M t)
    (hN : 0 < routeMAmbient M) (p : ℕ)
    (hp1 : Text M t (p + 1) ≤ Text M t p) (hp2 : Text M t (p + 1) ≤ Wext M p)
    (rfin : (Fin (routeMAmbient M) → ℝ) → Matrix (Fin (Text M t L)) (Fin (Wext M L)) ℝ)
    (active : Finset (Fin (routeMAmbient M)))
    (hslot : ∀ x : Fin (routeMAmbient M) → ℝ,
      smulRmatRfin (x (structPivot M hN)) M t (genBlkFlatLiveR1 M t ha p hp1 hp2 (rfin x) x)
        = genBlkFlatLiveR1 M t ha p hp1 hp2
            (rfin (pivotBlowupOn active (structPivot M hN) x))
            (pivotBlowupOn active (structPivot M hN) x)) :
    phiFlatLiveR1 M t ha hN p hp1 hp2 rfin
      = (fun y => phiGen 1 M t (genBlkFlatLiveR1 M t ha p hp1 hp2 (rfin y) y) (hleStruct M t ha))
        ∘ pivotBlowupOn active (structPivot M hN) := by
  funext x
  show phiGen (x (structPivot M hN)) M t (genBlkFlatLiveR1 M t ha p hp1 hp2 (rfin x) x)
      (hleStruct M t ha) = _
  rw [phiGen_smul_radial (x (structPivot M hN)) M t
    (genBlkFlatLiveR1 M t ha p hp1 hp2 (rfin x) x) (hleStruct M t ha), hslot x]
  rfl

/-! ## The Fix-B `φ = B ∘ pivotBlowupOn` reduction — CHART-level (not the false GenBlk `hslot`)

⚠ **`hchart` is UNDISCHARGEABLE for `B := phiGen 1 (genBlkFlatLiveR1 …)`** (verify-first, sympy
`route-i-l2/actual_B_check.py` + `agen_layer_check.py`): `genBlkFlatLiveR1`'s pivot `Rmat p` is the
FIXED `pivotEIndicator` — a CONSTANT (literal 1), x-free. So `phiGen 1 (genBlkFlatLiveR1 …(pbo x))`
reads `E(0,0)` as the constant `1`, NOT additively from the pivot coord — `φ = B ∘ pbo` FAILS at the
anchor (`φ_E00 = … + x_p` vs `B(pbo)_E00 = … + 1`). Equivalently the per-layer `chartParamsGen`
(`hcp` in `hchart_of_chartParamsGen`) is FALSE at the anchor (`x_p` vs `1`). The genm-detradj Fix-B
contract's `B` ("de-radialized chart reading `E(0,0)` ADDITIVELY from the pivot") is NOT
`phiGen 1 (genBlkFlatLiveR1 …)` — they DIFFER at the fixed pivot. My earlier
`fixb_corrected_contract_verify.py` used a HAND-MODELED additive-`B`, not the concrete decoder — a
conflation, caught before building the per-layer proof. Fix B as instantiated below (with `B` the
radial-1 `genBlkFlatLiveR1` chart) is OFF the build path; the contract needs a `B` whose pivot-E00
is an ADDITIVE pivot-coord read — genm-detradj's residual.

The reduction stays a VALID CONDITIONAL (on the CHART-level `hchart`); `phiGen_smul_radial` +
`hchart_of_chartParamsGen` are sound + reusable. But `hchart` for this `B` is the (false-here)
per-boundary additive/multiplicative `Agen`-split — the open piece, not dischargeable here. -/
theorem phiFlatLiveR1_eq_B_comp_pivotBlowupOn_chart (M t : Fin (L + 1) → ℕ) (ha : StructAdm M t)
    (hN : 0 < routeMAmbient M) (p : ℕ)
    (hp1 : Text M t (p + 1) ≤ Text M t p) (hp2 : Text M t (p + 1) ≤ Wext M p)
    (rfin : (Fin (routeMAmbient M) → ℝ) → Matrix (Fin (Text M t L)) (Fin (Wext M L)) ℝ)
    (active : Finset (Fin (routeMAmbient M)))
    (hchart : ∀ x : Fin (routeMAmbient M) → ℝ,
      phiGen 1 M t (smulRmatRfin (x (structPivot M hN)) M t
          (genBlkFlatLiveR1 M t ha p hp1 hp2 (rfin x) x)) (hleStruct M t ha)
        = phiGen 1 M t (genBlkFlatLiveR1 M t ha p hp1 hp2
            (rfin (pivotBlowupOn active (structPivot M hN) x))
            (pivotBlowupOn active (structPivot M hN) x)) (hleStruct M t ha)) :
    phiFlatLiveR1 M t ha hN p hp1 hp2 rfin
      = (fun y => phiGen 1 M t (genBlkFlatLiveR1 M t ha p hp1 hp2 (rfin y) y) (hleStruct M t ha))
        ∘ pivotBlowupOn active (structPivot M hN) := by
  funext x
  show phiGen (x (structPivot M hN)) M t (genBlkFlatLiveR1 M t ha p hp1 hp2 (rfin x) x)
      (hleStruct M t ha) = _
  rw [phiGen_smul_radial (x (structPivot M hN)) M t
    (genBlkFlatLiveR1 M t ha p hp1 hp2 (rfin x) x) (hleStruct M t ha), hchart x]
  rfl

/-! ## `hchart` from the per-layer `Agen` equality (the genuine map-identity content)

`hchart` (the CHART-level `phiGen 1 (smulRmatRfin (x_p) GBx) = phiGen 1 (GB(pbo x))`) reduces — via
`phiGen = paramsEquivFlat ∘ chartParamsGen` + the banked `chartParamsGen_smulRmatRfin`
(`chartParamsGen 1 (smulRmatRfin u B) = chartParamsGen u B`) — to the `chartParamsGen` equality
`chartParamsGen (x_p) GBx = chartParamsGen 1 (GB(pbo x))`, i.e. PER-LAYER (`reindex` injective)
`Agen (x_p) GBx s = Agen 1 (GB(pbo x)) s`. The per-layer split (K/X/N/W non-active ⟹ unchanged under
`pbo`; free E/leaf active ⟹ scaled by `x_p` (matches `Agen (x_p)`); fixed E00 the additive-anchor)
is the genuine content (genm-detradj's ∀M residual; exact at L=2 single bdy). This lemma BANKS the
clean structural reduction `hchart ⟸ the chartParamsGen equality`, isolating that content. -/
theorem hchart_of_chartParamsGen (M t : Fin (L + 1) → ℕ) (ha : StructAdm M t)
    (hN : 0 < routeMAmbient M) (p : ℕ)
    (hp1 : Text M t (p + 1) ≤ Text M t p) (hp2 : Text M t (p + 1) ≤ Wext M p)
    (rfin : (Fin (routeMAmbient M) → ℝ) → Matrix (Fin (Text M t L)) (Fin (Wext M L)) ℝ)
    (active : Finset (Fin (routeMAmbient M))) (x : Fin (routeMAmbient M) → ℝ)
    (hcp : chartParamsGen (x (structPivot M hN)) M t
        (genBlkFlatLiveR1 M t ha p hp1 hp2 (rfin x) x) (hleStruct M t ha)
      = chartParamsGen 1 M t
        (genBlkFlatLiveR1 M t ha p hp1 hp2

exec
/bin/bash -lc "sed -n '1,220p' lean/DLNFibre/DLN/RLCT/Validate/RouteMInteriorContract.lean" in /home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/agent-a9bb11c22680d93d4
 succeeded in 0ms:
import DLNFibre.DLN.RLCT.Validate.RouteMAchieverRateFields
import DLNFibre.DLN.RLCT.Validate.RouteMAchieverWitnessInterior

/-!
# `RouteMInteriorContract` — the INTERIOR-branch achiever box-divergence contract (#3 spine)

The spine for the INTERIOR branch of the ∀M achiever box-divergence (`hInterior` in
`RouteMAchieverDispatch`). It assembles the interior `NodeAchieverChart M` from the BANKED rate-side
fields (the achiever chart `achieverPhi`, the rate `routeMCore = (x p)²·U`, the det-FREE
det-free `leaf_integrand` for any `leafH`, and the interior `Ubound`), isolating the
OPEN chart-construction fields as precise hypotheses:

* `leafH` + `leafH_pivot` (`leafH p = minAdm M − 1`) — the multi-axis Jacobian-exponent vector;
* `Umeas` (`achieverUfun` measurable — a polynomial in the chart coords; banked-pattern);
* `cov` — the geometric change-of-variables with `|det Dφ| = ∏_j |u_j|^{leafH j}`. **THE heavy open
  piece** (the multi-block Schur-frame Jacobian; the construction-sensitive multi-axis det — the
  thread-36 det programme: LDU-coordinatize each K-core to a monomial `det K_s`, telescope via
  `composeFold_abs_det_leafH`/`schurFrame_abs_det`/`lduCoreDeriv_det`, then `injOn` off the
  weighted-axis planes + the n-fold null-slice). See `threads/80-…/interior-det-scope.md`.
* `image_subset` — the source box maps into the cube (continuity + `phi 0 = 0`; banked-pattern).

`routeMCore_box_diverges_interiorContract` discharges `BoxDiverges` GIVEN these. This banks the
interior spine (parallel to `routeMCore_box_diverges_smearedContract` for the smeared branch): the
dispatch's `hInterior` reduces to the four open fields, the rate-side + `Ubound` already closed. The
remaining content is exactly the chart `cov`/det + `leafH` + the two banked-pattern fields — NOT a
wall (every det brick is banked, `(3,3,3,3)` is the complete worked instance), a MAJOR build.

Axioms: clean-three + the cited `monomial_rlct` (inherited from the assembly's monomial atom); the
contract adds none of its own.
-/

open MeasureTheory
open scoped ENNReal BigOperators

namespace DLNFibre.DLN.RLCT

variable {L : ℕ}

/-- **The INTERIOR-branch achiever box-divergence contract.** For an interior-drop `M` (`2 ≤ L`,
`1 ≤ minAdm M`), the achiever box integral diverges, GIVEN the open chart-construction fields:
the Jacobian-exponent vector `leafH` (binding `leafH p = minAdm M − 1`), measurability of the unit,
the geometric `cov` (`|det Dφ| = ∏_j |u_j|^{leafH j}`), and the image containment. The rate, the
det-free `leaf_integrand`, and the interior `Ubound` are WIRED from the banked facts
(`routeMCore_achieverPhi`, `achiever_leaf_integrand`, `achieverUbound_interior`). The pivot is the
radial `structPivot M hN = ⟨0,_⟩`. -/
theorem routeMCore_box_diverges_interiorContract (M : Fin (L + 1) → ℕ) (hL : 0 < L)
    (hN : 0 < routeMAmbient M) (hInt : InteriorDrop M) (hpos : 1 ≤ minAdm M)
    (leafH : Fin (routeMAmbient M) → ℕ)
    (hleafH_pivot : leafH (structPivot M hN) = minAdm M - 1)
    (hUmeas : Measurable (achieverUfun M hL hN))
    (hcov : ∀ (V : Set (Fin (routeMAmbient M) → ℝ)), MeasurableSet V →
        ∀ (g : (Fin (routeMAmbient M) → ℝ) → ℝ≥0∞),
      ∫⁻ x in achieverPhi M hL hN '' (V \ {x | x (structPivot M hN) = 0}), g x
        = ∫⁻ u in V \ {x | x (structPivot M hN) = 0},
            ENNReal.ofReal (∏ j, |u j| ^ (leafH j)) * g (achieverPhi M hL hN u))
    (himage : ∀ ε : ℝ, 0 < ε →
        ∃ δ > 0, achieverPhi M hL hN ''
          (Set.univ.pi (fun _ : Fin (routeMAmbient M) => Set.Icc (0 : ℝ) δ))
          ⊆ cubeBox (routeMAmbient M) ε)
    (c' : NNReal) (hc' : (minAdm M : ℝ≥0∞) / 2 ≤ (c' : ℝ≥0∞)) (ε : ℝ) (hε : 0 < ε) :
    ∫⁻ x in cubeBox (routeMAmbient M) ε,
      ENNReal.ofReal (|routeMCore M x| ^ (-(c' : ℝ))) = ⊤ := by
  -- assemble the interior `NodeAchieverChart M` from the banked rate-side + the open fields
  let W : NodeAchieverChart M :=
    { hpos := hpos
      phi := achieverPhi M hL hN
      p := structPivot M hN
      leafH := leafH
      leafH_pivot := hleafH_pivot
      Ufun := achieverUfun M hL hN
      Ubound := achieverUbound_interior M hL hN hInt
      Umeas := hUmeas
      leaf_integrand := fun c =>
        Filter.Eventually.of_forall (fun x => achiever_leaf_integrand M hL hN leafH c x)
      cov := hcov
      image_subset := himage }
  exact routeMCore_box_diverges_of_nodeChart M W c' hc' ε hε

end DLNFibre.DLN.RLCT

exec
/bin/bash -lc "sed -n '430,900p' lean/DLNFibre/DLN/RLCT/Validate/RouteMBData222.lean" in /home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/agent-a9bb11c22680d93d4
 succeeded in 0ms:

/-! ## The R2 active set: leaf slots chosen from the complement of the reader slots

The slot wall (the opaque `chartIdxEquiv`): I cannot pin which flat slots the readers `a,b,n,w0,w1`
occupy, nor whether a chosen leaf slot equals `structPivot = ⟨0,_⟩`. RESOLVED (R2): the five reader
slots form `readerSet` (card ≤ 5); the two leaf slots are chosen from the FINITE COMPLEMENT
`univ \ insert structPivot readerSet` (card ≥ 8 − 6 = 2). Membership in the complement then gives
`lf ≠ structPivot` and `lf ∉ readerSet` for free — no opaque comparison. -/

/-- The five reader slots of `genBlkFlatLiveR1 M222` (the `chartIdxEquiv.symm` images of the K/X/N
Schur tags + the two W lift tags). The flat coords `a,b,n,w0,w1` live here. -/
noncomputable def readerSlotK : Fin (routeMAmbient M222) :=
  (chartIdxEquiv M222 (tDesc M222 tach222) structAdm_tach222.h0 structAdm_tach222.hc
    structAdm_tach222.hL).symm ⟨⟨0, by decide⟩, Sum.inl ((frameSplitEquiv M222 tach222 1
      (structAdm_tach222.hdesc 0 (by decide)) (structAdm_tach222.hub 0)).symm
      (Sum.inl (Sum.inl (Sum.inl (finProdFinEquiv (⟨0, by decide⟩, ⟨0, by decide⟩))))))⟩

noncomputable def readerSlotX : Fin (routeMAmbient M222) :=
  (chartIdxEquiv M222 (tDesc M222 tach222) structAdm_tach222.h0 structAdm_tach222.hc
    structAdm_tach222.hL).symm ⟨⟨0, by decide⟩, Sum.inl ((frameSplitEquiv M222 tach222 1
      (structAdm_tach222.hdesc 0 (by decide)) (structAdm_tach222.hub 0)).symm
      (Sum.inl (Sum.inl (Sum.inr (finProdFinEquiv (⟨0, by decide⟩, ⟨0, by decide⟩))))))⟩

noncomputable def readerSlotN : Fin (routeMAmbient M222) :=
  (chartIdxEquiv M222 (tDesc M222 tach222) structAdm_tach222.h0 structAdm_tach222.hc
    structAdm_tach222.hL).symm ⟨⟨0, by decide⟩, Sum.inl ((frameSplitEquiv M222 tach222 1
      (structAdm_tach222.hdesc 0 (by decide)) (structAdm_tach222.hub 0)).symm
      (Sum.inl (Sum.inr (finProdFinEquiv (⟨0, by decide⟩, ⟨0, by decide⟩)))))⟩

noncomputable def readerSlotW0 : Fin (routeMAmbient M222) :=
  (chartIdxEquiv M222 (tDesc M222 tach222) structAdm_tach222.h0 structAdm_tach222.hc
    structAdm_tach222.hL).symm ⟨⟨0, by decide⟩, Sum.inr ((liftSlotEquiv M222 (tDesc M222 tach222) 0
      (by decide)).symm (⟨0, by decide⟩, ⟨0, by decide⟩))⟩

noncomputable def readerSlotW1 : Fin (routeMAmbient M222) :=
  (chartIdxEquiv M222 (tDesc M222 tach222) structAdm_tach222.h0 structAdm_tach222.hc
    structAdm_tach222.hL).symm ⟨⟨0, by decide⟩, Sum.inr ((liftSlotEquiv M222 (tDesc M222 tach222) 0
      (by decide)).symm (⟨0, by decide⟩, ⟨1, by decide⟩))⟩

/-- The set of slots `pivotBlowupOn` must leave fixed: the pivot + the five reader slots (card ≤ 6). -/
noncomputable def forbiddenSlots : Finset (Fin (routeMAmbient M222)) :=
  insert (structPivot M222 hN_M222)
    {readerSlotK, readerSlotX, readerSlotN, readerSlotW0, readerSlotW1}

/-- `forbiddenSlots.card ≤ 6` (one pivot + five reader slots). -/
theorem forbiddenSlots_card_le : forbiddenSlots.card ≤ 6 := by
  have c1 := Finset.card_insert_le (structPivot M222 hN_M222)
    ({readerSlotK, readerSlotX, readerSlotN, readerSlotW0, readerSlotW1}
      : Finset (Fin (routeMAmbient M222)))
  have c2 := Finset.card_insert_le readerSlotK
    ({readerSlotX, readerSlotN, readerSlotW0, readerSlotW1}
      : Finset (Fin (routeMAmbient M222)))
  have c3 := Finset.card_insert_le readerSlotX
    ({readerSlotN, readerSlotW0, readerSlotW1} : Finset (Fin (routeMAmbient M222)))
  have c4 := Finset.card_insert_le readerSlotN
    ({readerSlotW0, readerSlotW1} : Finset (Fin (routeMAmbient M222)))
  have c5 := Finset.card_insert_le readerSlotW0
    ({readerSlotW1} : Finset (Fin (routeMAmbient M222)))
  have c6 : ({readerSlotW1} : Finset (Fin (routeMAmbient M222))).card = 1 := Finset.card_singleton _
  simp only [forbiddenSlots] at *
  omega

/-- The complement of `forbiddenSlots` has at least 2 slots (`8 − 6`). -/
theorem free_card_ge_two :
    2 ≤ ((Finset.univ : Finset (Fin (routeMAmbient M222))) \ forbiddenSlots).card := by
  have hle := Finset.le_card_sdiff forbiddenSlots (Finset.univ : Finset (Fin (routeMAmbient M222)))
  have huniv : (Finset.univ : Finset (Fin (routeMAmbient M222))).card = 8 := by
    rw [Finset.card_univ, Fintype.card_fin, routeMAmbient_M222]
  have := forbiddenSlots_card_le
  omega

/-- Two distinct slots in the complement of `forbiddenSlots` (the leaf coords). -/
theorem exists_leaf_pair :
    ∃ lf0 lf1 : Fin (routeMAmbient M222),
      lf0 ∈ (Finset.univ : Finset (Fin (routeMAmbient M222))) \ forbiddenSlots
      ∧ lf1 ∈ (Finset.univ : Finset (Fin (routeMAmbient M222))) \ forbiddenSlots
      ∧ lf0 ≠ lf1 := by
  obtain ⟨a, b, ha, hb, hab⟩ := Finset.one_lt_card_iff.mp free_card_ge_two
  exact ⟨a, b, ha, hb, hab⟩

/-- The first leaf slot (`Classical.choose`; in the complement, so `≠ structPivot`, `∉ readerSet`). -/
noncomputable def lf0 : Fin (routeMAmbient M222) := (exists_leaf_pair).choose

/-- The second leaf slot. -/
noncomputable def lf1 : Fin (routeMAmbient M222) := (exists_leaf_pair).choose_spec.choose

theorem lf0_mem : lf0 ∈ (Finset.univ : Finset (Fin (routeMAmbient M222))) \ forbiddenSlots :=
  (exists_leaf_pair).choose_spec.choose_spec.1

theorem lf1_mem : lf1 ∈ (Finset.univ : Finset (Fin (routeMAmbient M222))) \ forbiddenSlots :=
  (exists_leaf_pair).choose_spec.choose_spec.2.1

theorem lf0_ne_lf1 : lf0 ≠ lf1 := (exists_leaf_pair).choose_spec.choose_spec.2.2

/-- `lf0 ≠ structPivot` (the leaf slot avoids the pivot — from the complement). -/
theorem lf0_ne_pivot : lf0 ≠ structPivot M222 hN_M222 := by
  intro h
  have := lf0_mem
  rw [Finset.mem_sdiff] at this
  exact this.2 (h ▸ Finset.mem_insert_self _ _)

theorem lf1_ne_pivot : lf1 ≠ structPivot M222 hN_M222 := by
  intro h
  have := lf1_mem
  rw [Finset.mem_sdiff] at this
  exact this.2 (h ▸ Finset.mem_insert_self _ _)

/-- The R2 active set `{structPivot, lf0, lf1}` (card 3 = minAdm; pbo scales the two leaf slots). -/
noncomputable def active222 : Finset (Fin (routeMAmbient M222)) :=
  {structPivot M222 hN_M222, lf0, lf1}

/-- `structPivot ∈ active222`. -/
theorem structPivot_mem_active222 : structPivot M222 hN_M222 ∈ active222 :=
  Finset.mem_insert_self _ _

/-- `active222.card = 3 = minAdm M222` (pivot + two distinct leaf slots). -/
theorem active222_card : active222.card = minAdm M222 := by
  have hp0 : structPivot M222 hN_M222 ≠ lf0 := fun h => lf0_ne_pivot h.symm
  have hp1 : structPivot M222 hN_M222 ≠ lf1 := fun h => lf1_ne_pivot h.symm
  rw [active222, Finset.card_insert_of_notMem (by
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or]; exact ⟨hp0, hp1⟩),
    Finset.card_insert_of_notMem (by simp only [Finset.mem_singleton]; exact lf0_ne_lf1),
    Finset.card_singleton, minAdm_M222]

/-- A reader slot is `≠ lf0` and `≠ lf1` (it lies in `forbiddenSlots`, the leaf slots in the
complement). -/
theorem readerSlot_ne_leaf (q : Fin (routeMAmbient M222)) (hq : q ∈ forbiddenSlots) :
    q ≠ lf0 ∧ q ≠ lf1 := by
  have h0 := lf0_mem; have h1 := lf1_mem
  rw [Finset.mem_sdiff] at h0 h1
  exact ⟨fun h => h0.2 (h ▸ hq), fun h => h1.2 (h ▸ hq)⟩

/-- `pivotBlowupOn active222 structPivot x` at the pivot is `x structPivot`. -/
theorem pbo_pivot (x : Fin (routeMAmbient M222) → ℝ) :
    pivotBlowupOn active222 (structPivot M222 hN_M222) x (structPivot M222 hN_M222)
      = x (structPivot M222 hN_M222) := by
  unfold pivotBlowupOn; rw [if_pos rfl]

/-- `pivotBlowupOn` at `lf0` scales by the pivot: `= x structPivot · x lf0`. -/
theorem pbo_lf0 (x : Fin (routeMAmbient M222) → ℝ) :
    pivotBlowupOn active222 (structPivot M222 hN_M222) x lf0
      = x (structPivot M222 hN_M222) * x lf0 := by
  unfold pivotBlowupOn
  rw [if_neg lf0_ne_pivot, if_pos (show lf0 ∈ active222 from by
    rw [active222]; exact Finset.mem_insert_of_mem (Finset.mem_insert_self _ _))]

/-- `pivotBlowupOn` at `lf1` scales by the pivot: `= x structPivot · x lf1`. -/
theorem pbo_lf1 (x : Fin (routeMAmbient M222) → ℝ) :
    pivotBlowupOn active222 (structPivot M222 hN_M222) x lf1
      = x (structPivot M222 hN_M222) * x lf1 := by
  unfold pivotBlowupOn
  rw [if_neg lf1_ne_pivot, if_pos (show lf1 ∈ active222 from by
    rw [active222]; exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem
      (Finset.mem_singleton_self _)))]

/-- `pivotBlowupOn` fixes any reader slot (`∉ {lf0, lf1}`; the pivot branch fixes it too). -/
theorem pbo_reader (x : Fin (routeMAmbient M222) → ℝ) (q : Fin (routeMAmbient M222))
    (hq : q ∈ forbiddenSlots) :
    pivotBlowupOn active222 (structPivot M222 hN_M222) x q = x q := by
  obtain ⟨hq0, hq1⟩ := readerSlot_ne_leaf q hq
  by_cases hp : q = structPivot M222 hN_M222
  · rw [hp]; exact pbo_pivot x
  · simp only [pivotBlowupOn, if_neg hp,
      if_neg (show q ∉ active222 from by
        rw [active222]; simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
        exact ⟨hp, hq0, hq1⟩)]

/-! ## The leaf reader `rfin222` + the faithful boundary factor `B`

`rfin222 x := !![x lf0, x lf1]` reads the two complement leaf slots directly. The faithful boundary
factor `B y := paramsEquivFlat M222 (Bparams y)`, where `Bparams y` is the EXPLICIT two-layer chart
reading the pivot as the ORDINARY coordinate `y structPivot` (the `+u` of `Agen0[1,1]`), the Schur
readers `a/b/n/w0/w1` from `y`, and the leaf from `y lf0 / y lf1`. `B` is radial-free (`det DB = a²`,
the engine). The map identity `phiFlatLiveR1 = B ∘ pivotBlowupOn active222 structPivot` then follows
per-layer from `Agen0_Glr_eq`/`Agen1_Glr_eq` + the pbo facts (pivot fixed, leaf scaled, readers fixed). -/

/-- The leaf reader: `rfin222 x = !![x lf0, x lf1]` (`1×2`, reading the two complement leaf slots). -/
noncomputable def rfin222 (x : Fin (routeMAmbient M222) → ℝ) :
    Matrix (Fin (Text M222 tach222 2)) (Fin (Wext M222 2)) ℝ :=
  !![x lf0, x lf1]

/-- **The faithful boundary-factor chart parameters** `Bparams y : Params M222` — the explicit two
layers reading the pivot as the ordinary coord `y structPivot`, readers `a/b/n/w0/w1` from `y`, leaf
`y lf0 / y lf1`:
`A0 = [[a, a·n],[a·b, a·b·n + y_p]]`, `A1 = [[y_lf0 − n·w0, y_lf1 − n·w1],[w0, w1]]`. -/
noncomputable def Bparams (y : Fin (routeMAmbient M222) → ℝ) : Params M222 :=
  Fin.cons (!![aRead y, aRead y * nRead y;
      aRead y * bRead y, aRead y * bRead y * nRead y + y (structPivot M222 hN_M222)]
        : Matrix (Fin (M222 0)) (Fin (M222 1)) ℝ)
    (Fin.cons (!![y lf0 - nRead y * w0Read y, y lf1 - nRead y * w1Read y;
        w0Read y, w1Read y] : Matrix (Fin (M222 1)) (Fin (M222 2)) ℝ)
      (fun i => i.elim0))

/-- The faithful boundary factor `B y := paramsEquivFlat M222 (Bparams y)`. -/
noncomputable def Bchart (y : Fin (routeMAmbient M222) → ℝ) : Fin (routeMAmbient M222) → ℝ :=
  paramsEquivFlat M222 (Bparams y)

/-! ## The reader values are stable under `pivotBlowupOn` (they sit in `forbiddenSlots`) -/

/-- Each reader is the flat coordinate at its slot (`rfl` — the reader is `x` at the slot). -/
theorem aRead_eq (x : Fin (routeMAmbient M222) → ℝ) : aRead x = x readerSlotK := rfl
theorem bRead_eq (x : Fin (routeMAmbient M222) → ℝ) : bRead x = x readerSlotX := rfl
theorem nRead_eq (x : Fin (routeMAmbient M222) → ℝ) : nRead x = x readerSlotN := rfl
theorem w0Read_eq (x : Fin (routeMAmbient M222) → ℝ) : w0Read x = x readerSlotW0 := rfl
theorem w1Read_eq (x : Fin (routeMAmbient M222) → ℝ) : w1Read x = x readerSlotW1 := rfl

/-- A reader slot is in `forbiddenSlots`. -/
theorem readerSlotK_mem : readerSlotK ∈ forbiddenSlots :=
  Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)
theorem readerSlotX_mem : readerSlotX ∈ forbiddenSlots :=
  Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_self _ _))
theorem readerSlotN_mem : readerSlotN ∈ forbiddenSlots :=
  Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem
    (Finset.mem_insert_self _ _)))
theorem readerSlotW0_mem : readerSlotW0 ∈ forbiddenSlots :=
  Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem
    (Finset.mem_insert_of_mem (Finset.mem_insert_self _ _))))
theorem readerSlotW1_mem : readerSlotW1 ∈ forbiddenSlots :=
  Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem
    (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_singleton_self _)))))

/-- The reader values are invariant under `pivotBlowupOn` (the slots lie in `forbiddenSlots`). -/
theorem aRead_pbo (x : Fin (routeMAmbient M222) → ℝ) :
    aRead (pivotBlowupOn active222 (structPivot M222 hN_M222) x) = aRead x := by
  rw [aRead_eq, aRead_eq, pbo_reader x readerSlotK readerSlotK_mem]
theorem bRead_pbo (x : Fin (routeMAmbient M222) → ℝ) :
    bRead (pivotBlowupOn active222 (structPivot M222 hN_M222) x) = bRead x := by
  rw [bRead_eq, bRead_eq, pbo_reader x readerSlotX readerSlotX_mem]
theorem nRead_pbo (x : Fin (routeMAmbient M222) → ℝ) :
    nRead (pivotBlowupOn active222 (structPivot M222 hN_M222) x) = nRead x := by
  rw [nRead_eq, nRead_eq, pbo_reader x readerSlotN readerSlotN_mem]
theorem w0Read_pbo (x : Fin (routeMAmbient M222) → ℝ) :
    w0Read (pivotBlowupOn active222 (structPivot M222 hN_M222) x) = w0Read x := by
  rw [w0Read_eq, w0Read_eq, pbo_reader x readerSlotW0 readerSlotW0_mem]
theorem w1Read_pbo (x : Fin (routeMAmbient M222) → ℝ) :
    w1Read (pivotBlowupOn active222 (structPivot M222 hN_M222) x) = w1Read x := by
  rw [w1Read_eq, w1Read_eq, pbo_reader x readerSlotW1 readerSlotW1_mem]

/-! ## The map identity `phiFlatLiveR1 = B ∘ pivotBlowupOn active222 structPivot` (`hmap`) -/

/-- **The chart-parameter identity** `chartParamsGen (x p) (Glr rfin222 x) = Bparams (pbo x)` — the
genuine content of `hmap`, per-layer: layer 0 is `Agen0_Glr_eq` (the `+u = +x_p` pivot coord, the
`reindex` value-preserving); layer 1 is `Agen1_Glr_eq` with the leaf `rfin222 x = !![x lf0, x lf1]`
scaled to `x_p·x_lfᵢ` on the RHS via `pbo_lf0/lf1`, and the readers fixed via `*_pbo`. -/
theorem chartParamsGen_Glr_eq (x : Fin (routeMAmbient M222) → ℝ) :
    chartParamsGen (x (structPivot M222 hN_M222)) M222 tach222 (Glr rfin222 x)
        (hleStruct M222 tach222 structAdm_tach222)
      = Bparams (pivotBlowupOn active222 (structPivot M222 hN_M222) x) := by
  -- reduce the RHS `Bparams (pbo x)` readers/pivot/leaf via the pbo facts first
  have hB0 : (Bparams (pivotBlowupOn active222 (structPivot M222 hN_M222) x)) 0
      = (!![aRead x, aRead x * nRead x;
          aRead x * bRead x, aRead x * bRead x * nRead x + x (structPivot M222 hN_M222)]
          : Matrix (Fin (M222 0)) (Fin (M222 1)) ℝ) := by
    show (!![aRead (pivotBlowupOn active222 (structPivot M222 hN_M222) x), _; _, _]
        : Matrix (Fin (M222 0)) (Fin (M222 1)) ℝ) = _
    rw [aRead_pbo, bRead_pbo, nRead_pbo, pbo_pivot]
  have hB1 : (Bparams (pivotBlowupOn active222 (structPivot M222 hN_M222) x)) 1
      = (!![x (structPivot M222 hN_M222) * x lf0 - nRead x * w0Read x,
          x (structPivot M222 hN_M222) * x lf1 - nRead x * w1Read x;
          w0Read x, w1Read x] : Matrix (Fin (M222 1)) (Fin (M222 2)) ℝ) := by
    show (!![(pivotBlowupOn active222 (structPivot M222 hN_M222) x) lf0 - _, _; _, _]
        : Matrix (Fin (M222 1)) (Fin (M222 2)) ℝ) = _
    rw [nRead_pbo, w0Read_pbo, w1Read_pbo, pbo_lf0, pbo_lf1]
  funext s
  fin_cases s
  · show Matrix.reindex _ _ (Agen (x (structPivot M222 hN_M222)) M222 tach222 (Glr rfin222 x)
        (hleStruct M222 tach222 structAdm_tach222) 0) = (Bparams _) 0
    rw [Agen0_Glr_eq, hB0]
    ext i j
    simp only [Matrix.reindex_apply, Matrix.submatrix_apply, finCongr_symm, finCongr_apply,
      Fin.cast_eq_self]
    rfl
  · show Matrix.reindex _ _ (Agen (x (structPivot M222 hN_M222)) M222 tach222 (Glr rfin222 x)
        (hleStruct M222 tach222 structAdm_tach222) 1) = (Bparams _) 1
    rw [Agen1_Glr_eq, hB1]
    ext i j
    simp only [Matrix.reindex_apply, Matrix.submatrix_apply, finCongr_symm, finCongr_apply,
      Fin.cast_eq_self]
    -- the leaf `rfin222 x ⟨0⟩ ⟨j⟩ = (!![x lf0, x lf1]) ⟨0⟩ ⟨j⟩ = x lfⱼ` reduces by `rfl`
    rfl

/-- **`hmap`: `phiFlatLiveR1 M222 … rfin222 = Bchart ∘ pivotBlowupOn active222 structPivot`** — the
faithful map identity (obligation (1) of the `BData` interface). -/
theorem hmap_222 :
    phiFlatLiveR1 M222 tach222 structAdm_tach222 hN_M222 1 hp1_222 hp2_222 rfin222
      = Bchart ∘ pivotBlowupOn active222 (structPivot M222 hN_M222) := by
  funext x
  show phiGen (x (structPivot M222 hN_M222)) M222 tach222 (Glr rfin222 x)
      (hleStruct M222 tach222 structAdm_tach222) = _
  show paramsEquivFlat M222 (chartParamsGen (x (structPivot M222 hN_M222)) M222 tach222
      (Glr rfin222 x) (hleStruct M222 tach222 structAdm_tach222)) = _
  rw [chartParamsGen_Glr_eq]
  rfl

/-! ## The residual det leg: `DB`/`hasDB`/`hdet` (the `BData` interface fields)

`Bchart = paramsEquivFlat ∘ Bparams`. We factor `Bparams = pack222 ∘ Tb`, where `Tb` produces the 8
entry values in the `pack222` flat-coordinate order (`A0 = !![w4,w1;w5,w6]`, `A1 = !![w0,w7;w2,w3]`)
by reading the 8 distinct slots of `y`. Then `Bchart = Q222CLM ∘ Tb` (`Q222CLM = paramsEquivFlat ∘
pack222`, measure-preserving, `|det| = 1`), so `DB = Q222CLM.comp (TbCLM u)` with
`|det DB| = |det Q222CLM| · |det (TbCLM u)| = 1 · |aRead u|²`.

`TbCLM u` (the fderiv of `Tb` at `u`) is the explicit per-output product/sum CLM. Its determinant is
computed by reindexing the 8 OPAQUE input slots to the literal coordinate order via the bijection
`slotEquiv` (the 8 slots `a,b,n,w0,w1,p,lf0,lf1` are pairwise distinct), turning `toMatrix'` into an
explicit lower-triangular matrix with diagonal `[1, a, a, 1, 1, 1, 1, 1]`, det `= a²`. -/

/-! ### The 8 slots are pairwise distinct (reader/reader via `chartIdxEquiv.symm` injectivity) -/

theorem readerSlotK_ne_X : readerSlotK ≠ readerSlotX := by
  unfold readerSlotK readerSlotX
  intro h
  have h2 := (Equiv.injective _) h
  simp only [Sigma.mk.injEq, Sum.inl.injEq, heq_eq_eq, true_and] at h2
  exact absurd ((Equiv.injective _) h2) (by decide)

theorem readerSlotK_ne_N : readerSlotK ≠ readerSlotN := by
  unfold readerSlotK readerSlotN
  intro h
  have h2 := (Equiv.injective _) h
  simp only [Sigma.mk.injEq, Sum.inl.injEq, heq_eq_eq, true_and] at h2
  exact absurd ((Equiv.injective _) h2) (by decide)

theorem readerSlotX_ne_N : readerSlotX ≠ readerSlotN := by
  unfold readerSlotX readerSlotN
  intro h
  have h2 := (Equiv.injective _) h
  simp only [Sigma.mk.injEq, Sum.inl.injEq, heq_eq_eq, true_and] at h2
  exact absurd ((Equiv.injective _) h2) (by decide)

theorem readerSlotK_ne_W0 : readerSlotK ≠ readerSlotW0 := by
  unfold readerSlotK readerSlotW0
  intro h
  have h2 := (Equiv.injective _) h
  simp only [Sigma.mk.injEq, heq_eq_eq, true_and, reduceCtorEq] at h2

theorem readerSlotK_ne_W1 : readerSlotK ≠ readerSlotW1 := by
  unfold readerSlotK readerSlotW1
  intro h
  have h2 := (Equiv.injective _) h
  simp only [Sigma.mk.injEq, heq_eq_eq, true_and, reduceCtorEq] at h2

theorem readerSlotX_ne_W0 : readerSlotX ≠ readerSlotW0 := by
  unfold readerSlotX readerSlotW0
  intro h
  have h2 := (Equiv.injective _) h
  simp only [Sigma.mk.injEq, heq_eq_eq, true_and, reduceCtorEq] at h2

theorem readerSlotX_ne_W1 : readerSlotX ≠ readerSlotW1 := by
  unfold readerSlotX readerSlotW1
  intro h
  have h2 := (Equiv.injective _) h
  simp only [Sigma.mk.injEq, heq_eq_eq, true_and, reduceCtorEq] at h2

theorem readerSlotN_ne_W0 : readerSlotN ≠ readerSlotW0 := by
  unfold readerSlotN readerSlotW0
  intro h
  have h2 := (Equiv.injective _) h
  simp only [Sigma.mk.injEq, heq_eq_eq, true_and, reduceCtorEq] at h2

theorem readerSlotN_ne_W1 : readerSlotN ≠ readerSlotW1 := by
  unfold readerSlotN readerSlotW1
  intro h
  have h2 := (Equiv.injective _) h
  simp only [Sigma.mk.injEq, heq_eq_eq, true_and, reduceCtorEq] at h2

theorem readerSlotW0_ne_W1 : readerSlotW0 ≠ readerSlotW1 := by
  unfold readerSlotW0 readerSlotW1
  intro h
  have h2 := (Equiv.injective _) h
  simp only [Sigma.mk.injEq, Sum.inr.injEq, heq_eq_eq, true_and] at h2
  exact absurd ((Equiv.injective _) h2) (by decide)

/-! ### The slot list + its `Fin 8 ≃ Fin (routeMAmbient M222)` bijection

The radial/pivot slot is `structPivot M222 hN_M222 = ⟨0,_⟩` (the radial scalar coordinate axis,
`RouteMFlatStructV.structPivot`). The five reader slots are `chartIdxEquiv.symm`-tag images. That
the radial axis `⟨0,_⟩` is DISTINCT from the five Schur/lift reader slots is the one fact NOT
reachable by tag-injectivity (`⟨0,_⟩` is not a `ChartIdx` tag image we can compare) nor by `decide`
(`chartIdxEquiv.symm = (Fintype.equivFin _).symm ∘ finCongr` does not kernel-reduce); it is the
geometric non-degeneracy of the chart (the radial axis is a genuinely separate coordinate). It is
carried as the explicit hypothesis `pivotNotReader` and threaded to the det headline. -/

/-- The reader-slot finset (the five Schur/lift coordinate slots `a, b, n, w0, w1`). -/
noncomputable def readerSet : Finset (Fin (routeMAmbient M222)) :=
  {readerSlotK, readerSlotX, readerSlotN, readerSlotW0, readerSlotW1}

/-- **The chart non-degeneracy hypothesis**: the radial axis `structPivot = ⟨0,_⟩` is distinct from
each of the five Schur/lift reader slots. (Geometrically true — the radial scalar is a separate
coordinate from the block readers — but not reachable by `decide`/tag-injectivity at this pin.) -/
def PivotNotReader : Prop := structPivot M222 hN_M222 ∉ readerSet

/-- The 8 slots in column order `[a, b, n, w0, w1, p, lf0, lf1]` (the variable order of the entry
Jacobian). Pairwise distinct (under `PivotNotReader`), hence — on `Fin 8` — bijective. -/
noncomputable def slotList : Fin 8 → Fin (routeMAmbient M222) :=
  ![readerSlotK, readerSlotX, readerSlotN, readerSlotW0, readerSlotW1,
    structPivot M222 hN_M222, lf0, lf1]

set_option linter.unusedSimpArgs false in
/-- `slotList` is injective (the 8 slots are pairwise distinct), given the radial-axis
non-degeneracy `PivotNotReader`. -/
theorem slotList_injective (hpiv : PivotNotReader) : Function.Injective slotList := by
  have hKlf0 := (readerSlot_ne_leaf readerSlotK readerSlotK_mem).1
  have hKlf1 := (readerSlot_ne_leaf readerSlotK readerSlotK_mem).2
  have hXlf0 := (readerSlot_ne_leaf readerSlotX readerSlotX_mem).1
  have hXlf1 := (readerSlot_ne_leaf readerSlotX readerSlotX_mem).2
  have hNlf0 := (readerSlot_ne_leaf readerSlotN readerSlotN_mem).1
  have hNlf1 := (readerSlot_ne_leaf readerSlotN readerSlotN_mem).2
  have hW0lf0 := (readerSlot_ne_leaf readerSlotW0 readerSlotW0_mem).1
  have hW0lf1 := (readerSlot_ne_leaf readerSlotW0 readerSlotW0_mem).2
  have hW1lf0 := (readerSlot_ne_leaf readerSlotW1 readerSlotW1_mem).1
  have hW1lf1 := (readerSlot_ne_leaf readerSlotW1 readerSlotW1_mem).2
  -- the pivot avoids each reader, from `PivotNotReader`
  have hpK : structPivot M222 hN_M222 ≠ readerSlotK := fun h => hpiv (by
    rw [readerSet, h]; exact Finset.mem_insert_self _ _)
  have hpX : structPivot M222 hN_M222 ≠ readerSlotX := fun h => hpiv (by
    rw [readerSet, h]; exact Finset.mem_insert_of_mem (Finset.mem_insert_self _ _))
  have hpN : structPivot M222 hN_M222 ≠ readerSlotN := fun h => hpiv (by
    rw [readerSet, h]
    exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)))
  have hpW0 : structPivot M222 hN_M222 ≠ readerSlotW0 := fun h => hpiv (by
    rw [readerSet, h]
    exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem
      (Finset.mem_insert_self _ _))))
  have hpW1 : structPivot M222 hN_M222 ≠ readerSlotW1 := fun h => hpiv (by
    rw [readerSet, h]
    exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem
      (Finset.mem_insert_of_mem (Finset.mem_singleton_self _)))))
  intro i j hij
  fin_cases i <;> fin_cases j <;>
    simp_all only [slotList, Matrix.cons_val] <;>
    first
      | rfl
      | (exfalso; first
          | exact readerSlotK_ne_X hij | exact readerSlotK_ne_X hij.symm
          | exact readerSlotK_ne_N hij | exact readerSlotK_ne_N hij.symm
          | exact readerSlotX_ne_N hij | exact readerSlotX_ne_N hij.symm
          | exact readerSlotK_ne_W0 hij | exact readerSlotK_ne_W0 hij.symm
          | exact readerSlotK_ne_W1 hij | exact readerSlotK_ne_W1 hij.symm
          | exact readerSlotX_ne_W0 hij | exact readerSlotX_ne_W0 hij.symm
          | exact readerSlotX_ne_W1 hij | exact readerSlotX_ne_W1 hij.symm
          | exact readerSlotN_ne_W0 hij | exact readerSlotN_ne_W0 hij.symm
          | exact readerSlotN_ne_W1 hij | exact readerSlotN_ne_W1 hij.symm
          | exact readerSlotW0_ne_W1 hij | exact readerSlotW0_ne_W1 hij.symm
          | exact lf0_ne_lf1 hij | exact lf0_ne_lf1 hij.symm
          | exact lf0_ne_pivot hij | exact lf0_ne_pivot hij.symm
          | exact lf1_ne_pivot hij | exact lf1_ne_pivot hij.symm
          | exact hpK hij | exact hpK hij.symm | exact hpX hij | exact hpX hij.symm
          | exact hpN hij | exact hpN hij.symm | exact hpW0 hij | exact hpW0 hij.symm
          | exact hpW1 hij | exact hpW1 hij.symm
          | exact hKlf0 hij | exact hKlf0 hij.symm | exact hKlf1 hij | exact hKlf1 hij.symm
          | exact hXlf0 hij | exact hXlf0 hij.symm | exact hXlf1 hij | exact hXlf1 hij.symm
          | exact hNlf0 hij | exact hNlf0 hij.symm | exact hNlf1 hij | exact hNlf1 hij.symm
          | exact hW0lf0 hij | exact hW0lf0 hij.symm | exact hW0lf1 hij | exact hW0lf1 hij.symm
          | exact hW1lf0 hij | exact hW1lf0 hij.symm | exact hW1lf1 hij | exact hW1lf1 hij.symm)

/-- The slot bijection `Fin 8 ≃ Fin (routeMAmbient M222)` (injective `slotList`, equal
cardinalities), given the radial-axis non-degeneracy `PivotNotReader`. -/
noncomputable def slotEquiv (hpiv : PivotNotReader) : Fin 8 ≃ Fin (routeMAmbient M222) :=
  Equiv.ofBijective slotList ((Fintype.bijective_iff_injective_and_card slotList).mpr
    ⟨slotList_injective hpiv, by rw [routeMAmbient_M222]⟩)

theorem slotEquiv_apply (hpiv : PivotNotReader) (i : Fin 8) : slotEquiv hpiv i = slotList i := rfl

/-! ### `Tb` (the entry-readout) + the factorization `Bparams = pack222 ∘ Tb` -/

/-- **`Tb`** — the 8 entry values of `Bparams` in the `pack222` flat-coordinate order
(`A0 = !![w4,w1;w5,w6]`, `A1 = !![w0,w7;w2,w3]`): coords `0 = y_lf0 − n·w0`, `1 = a·n`, `2 = w0`,
`3 = w1`, `4 = a`, `5 = a·b`, `6 = a·b·n + y_p`, `7 = y_lf1 − n·w1` (`a = y_K`, `b = y_X`,
`n = y_N`, `w0 = y_{W0}`, `w1 = y_{W1}`, `y_p = y_{pivot}`). Then `pack222 (Tb y) = Bparams y`. -/
noncomputable def Tb (y : Fin (routeMAmbient M222) → ℝ) : Fin 8 → ℝ :=

exec
/bin/bash -lc "sed -n '900,1288p' lean/DLNFibre/DLN/RLCT/Validate/RouteMBData222.lean" in /home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/agent-a9bb11c22680d93d4
 succeeded in 0ms:
noncomputable def Tb (y : Fin (routeMAmbient M222) → ℝ) : Fin 8 → ℝ :=
  ![y lf0 - y readerSlotN * y readerSlotW0,
    y readerSlotK * y readerSlotN,
    y readerSlotW0,
    y readerSlotW1,
    y readerSlotK,
    y readerSlotK * y readerSlotX,
    y readerSlotK * y readerSlotX * y readerSlotN + y (structPivot M222 hN_M222),
    y lf1 - y readerSlotN * y readerSlotW1]

/-- **The factorization** `pack222 (Tb y) = Bparams y`. -/
theorem pack222_Tb_eq (y : Fin (routeMAmbient M222) → ℝ) : pack222 (Tb y) = Bparams y := by
  funext s
  fin_cases s
  · change (pack222 (Tb y)) 0 = (Bparams y) 0
    have hp : (pack222 (Tb y)) 0
        = (!![(Tb y) 4, (Tb y) 1; (Tb y) 5, (Tb y) 6] : Matrix (Fin 2) (Fin 2) ℝ) := rfl
    have hB : (Bparams y) 0
        = (!![aRead y, aRead y * nRead y;
            aRead y * bRead y, aRead y * bRead y * nRead y + y (structPivot M222 hN_M222)]
          : Matrix (Fin (M222 0)) (Fin (M222 1)) ℝ) := rfl
    rw [hp, hB]
    funext i j
    fin_cases i <;> fin_cases j <;>
      simp [Tb, aRead_eq, bRead_eq, nRead_eq]
  · change (pack222 (Tb y)) 1 = (Bparams y) 1
    have hp : (pack222 (Tb y)) 1
        = (!![(Tb y) 0, (Tb y) 7; (Tb y) 2, (Tb y) 3] : Matrix (Fin 2) (Fin 2) ℝ) := rfl
    have hB : (Bparams y) 1
        = (!![y lf0 - nRead y * w0Read y, y lf1 - nRead y * w1Read y;
            w0Read y, w1Read y] : Matrix (Fin (M222 1)) (Fin (M222 2)) ℝ) := rfl
    rw [hp, hB]
    funext i j
    fin_cases i <;> fin_cases j <;>
      simp [Tb, nRead_eq, w0Read_eq, w1Read_eq]

/-- **`Bchart = Q222CLM ∘ Tb`** (as functions): `Bchart y = paramsEquivFlat (Bparams y)
= paramsEquivFlat (pack222 (Tb y)) = Q222CLM (Tb y)`. -/
theorem Bchart_eq_Q222CLM_Tb (y : Fin (routeMAmbient M222) → ℝ) :
    Bchart y = Q222CLM (Tb y) := by
  rw [Bchart, ← pack222_Tb_eq]
  change paramsEquivFlat M222 (pack222 (Tb y)) = Q222CLM (Tb y)
  rw [show Q222CLM (Tb y) = paramsEquivFlatCLE M222 (pack222CLM (Tb y)) from rfl,
    paramsEquivFlatCLE_coe, pack222CLM_coe]

/-! ### `TbCLM` (the fderiv of `Tb`) + `HasFDerivAt Tb (TbCLM u) u` -/

/-- The coordinate projection CLM `proj s : (Fin (routeMAmbient M222) → ℝ) →L[ℝ] ℝ`. -/
noncomputable abbrev bprj (s : Fin (routeMAmbient M222)) :
    (Fin (routeMAmbient M222) → ℝ) →L[ℝ] ℝ :=
  ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin (routeMAmbient M222) => ℝ) s

/-- **`TbCLM u`** — the fderiv of `Tb` at `u`, the explicit per-output product/sum CLM (in the
`pack222` flat-coordinate output order). -/
noncomputable def TbCLM (u : Fin (routeMAmbient M222) → ℝ) :
    (Fin (routeMAmbient M222) → ℝ) →L[ℝ] (Fin 8 → ℝ) :=
  ContinuousLinearMap.pi
    (![ bprj lf0 - ((u readerSlotN) • bprj readerSlotW0 + (u readerSlotW0) • bprj readerSlotN),
        (u readerSlotK) • bprj readerSlotN + (u readerSlotN) • bprj readerSlotK,
        bprj readerSlotW0,
        bprj readerSlotW1,
        bprj readerSlotK,
        (u readerSlotK) • bprj readerSlotX + (u readerSlotX) • bprj readerSlotK,
        ((u readerSlotX * u readerSlotN) • bprj readerSlotK
          + (u readerSlotK * u readerSlotN) • bprj readerSlotX
          + (u readerSlotK * u readerSlotX) • bprj readerSlotN)
          + bprj (structPivot M222 hN_M222),
        bprj lf1 - ((u readerSlotN) • bprj readerSlotW1 + (u readerSlotW1) • bprj readerSlotN)]
      : Fin 8 → ((Fin (routeMAmbient M222) → ℝ) →L[ℝ] ℝ))

set_option linter.unusedSimpArgs false in
/-- **`Tb` has fderiv `TbCLM u`** at `u` (product/sum/sub rule on each of the 8 outputs). -/
theorem Tb_hasFDerivAt (u : Fin (routeMAmbient M222) → ℝ) :
    HasFDerivAt Tb (TbCLM u) u := by
  apply hasFDerivAt_pi''
  intro i
  rw [TbCLM, ContinuousLinearMap.proj_pi]
  have hap : ∀ s : Fin (routeMAmbient M222),
      HasFDerivAt (fun y : Fin (routeMAmbient M222) → ℝ => y s) (bprj s) u :=
    fun s => hasFDerivAt_apply (𝕜 := ℝ) s u
  fin_cases i <;> simp only [Tb, Matrix.cons_val]
  · -- output 0: `y lf0 - y readerSlotN * y readerSlotW0`
    refine (hap lf0).sub ?_
    have := (hap readerSlotN).mul (hap readerSlotW0)
    refine this.congr_fderiv ?_
    ext v; simp [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.proj_apply, mul_comm]
  · -- output 1: `y readerSlotK * y readerSlotN`
    exact (hap readerSlotK).mul (hap readerSlotN)
  · exact hap readerSlotW0
  · exact hap readerSlotW1
  · exact hap readerSlotK
  · -- output 5: `y readerSlotK * y readerSlotX`
    exact (hap readerSlotK).mul (hap readerSlotX)
  · -- output 6: `y readerSlotK * y readerSlotX * y readerSlotN + y (structPivot)`
    refine HasFDerivAt.add ?_ (hap (structPivot M222 hN_M222))
    have := ((hap readerSlotK).mul (hap readerSlotX)).mul (hap readerSlotN)
    refine this.congr_fderiv ?_
    ext v; simp [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.proj_apply]; ring
  · -- output 7: `y lf1 - y readerSlotN * y readerSlotW1`
    refine (hap lf1).sub ?_
    have := (hap readerSlotN).mul (hap readerSlotW1)
    refine this.congr_fderiv ?_
    ext v; simp [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.proj_apply, mul_comm]

/-! ### `DB` (the `Bchart` fderiv) + `hasDB` -/

/-- **`DB u`** — `Bchart`'s fderiv `Q222CLM ∘L TbCLM u` (`Bchart = Q222CLM ∘ Tb`). -/
noncomputable def DB (u : Fin (routeMAmbient M222) → ℝ) :
    (Fin (routeMAmbient M222) → ℝ) →L[ℝ] (Fin (routeMAmbient M222) → ℝ) :=
  Q222CLM.comp (TbCLM u)

/-- **`Bchart` has fderiv `DB u`** at `u` (chain rule: `Q222CLM` linear ∘ `Tb`). -/
theorem Bchart_hasFDerivAt (u : Fin (routeMAmbient M222) → ℝ) :
    HasFDerivAt Bchart (DB u) u := by
  have hcomp : HasFDerivAt (fun v => Q222CLM (Tb v)) (Q222CLM.comp (TbCLM u)) u :=
    (Q222CLM.hasFDerivAt).comp u (Tb_hasFDerivAt u)
  exact hcomp.congr_of_eventuallyEq (by filter_upwards with v; rw [Bchart_eq_Q222CLM_Tb])

/-! ### `|det (TbCLM u)| = |aRead u|²` (the entry Jacobian det, via slot reindex to lower-tri)

The slot/row reindex turns `toMatrix' (TbCLM u)` into the explicit lower-triangular `litMatLT u`
(diagonal `[1, a, a, 1, 1, 1, 1, 1]`, `a = aRead u`), det `= a²`. Column order
`[a, b, n, p, w0, w1, lf0, lf1]` (`slotListC`), row order `[out4, out5, out1, out6, out2, out3,
out0, out7]` (`rowPerm`). -/

/-- The column slot list in the lower-triangular order `[a, b, n, p, w0, w1, lf0, lf1]`. -/
noncomputable def slotListC : Fin 8 → Fin (routeMAmbient M222) :=
  ![readerSlotK, readerSlotX, readerSlotN, structPivot M222 hN_M222,
    readerSlotW0, readerSlotW1, lf0, lf1]

set_option linter.unusedSimpArgs false in
/-- `slotListC` is injective (a reordering of `slotList`), under `PivotNotReader`. -/
theorem slotListC_injective (hpiv : PivotNotReader) : Function.Injective slotListC := by
  have hKlf0 := (readerSlot_ne_leaf readerSlotK readerSlotK_mem).1
  have hKlf1 := (readerSlot_ne_leaf readerSlotK readerSlotK_mem).2
  have hXlf0 := (readerSlot_ne_leaf readerSlotX readerSlotX_mem).1
  have hXlf1 := (readerSlot_ne_leaf readerSlotX readerSlotX_mem).2
  have hNlf0 := (readerSlot_ne_leaf readerSlotN readerSlotN_mem).1
  have hNlf1 := (readerSlot_ne_leaf readerSlotN readerSlotN_mem).2
  have hW0lf0 := (readerSlot_ne_leaf readerSlotW0 readerSlotW0_mem).1
  have hW0lf1 := (readerSlot_ne_leaf readerSlotW0 readerSlotW0_mem).2
  have hW1lf0 := (readerSlot_ne_leaf readerSlotW1 readerSlotW1_mem).1
  have hW1lf1 := (readerSlot_ne_leaf readerSlotW1 readerSlotW1_mem).2
  have hpK : structPivot M222 hN_M222 ≠ readerSlotK := fun h => hpiv (by
    rw [readerSet, h]; exact Finset.mem_insert_self _ _)
  have hpX : structPivot M222 hN_M222 ≠ readerSlotX := fun h => hpiv (by
    rw [readerSet, h]; exact Finset.mem_insert_of_mem (Finset.mem_insert_self _ _))
  have hpN : structPivot M222 hN_M222 ≠ readerSlotN := fun h => hpiv (by
    rw [readerSet, h]
    exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)))
  have hpW0 : structPivot M222 hN_M222 ≠ readerSlotW0 := fun h => hpiv (by
    rw [readerSet, h]
    exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem
      (Finset.mem_insert_self _ _))))
  have hpW1 : structPivot M222 hN_M222 ≠ readerSlotW1 := fun h => hpiv (by
    rw [readerSet, h]
    exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem
      (Finset.mem_insert_of_mem (Finset.mem_singleton_self _)))))
  have hplf0 : structPivot M222 hN_M222 ≠ lf0 := fun h => lf0_ne_pivot h.symm
  have hplf1 : structPivot M222 hN_M222 ≠ lf1 := fun h => lf1_ne_pivot h.symm
  intro i j hij
  fin_cases i <;> fin_cases j <;>
    simp_all only [slotListC, Matrix.cons_val] <;>
    first
      | rfl
      | (exfalso; first
          | exact readerSlotK_ne_X hij | exact readerSlotK_ne_X hij.symm
          | exact readerSlotK_ne_N hij | exact readerSlotK_ne_N hij.symm
          | exact readerSlotX_ne_N hij | exact readerSlotX_ne_N hij.symm
          | exact readerSlotK_ne_W0 hij | exact readerSlotK_ne_W0 hij.symm
          | exact readerSlotK_ne_W1 hij | exact readerSlotK_ne_W1 hij.symm
          | exact readerSlotX_ne_W0 hij | exact readerSlotX_ne_W0 hij.symm
          | exact readerSlotX_ne_W1 hij | exact readerSlotX_ne_W1 hij.symm
          | exact readerSlotN_ne_W0 hij | exact readerSlotN_ne_W0 hij.symm
          | exact readerSlotN_ne_W1 hij | exact readerSlotN_ne_W1 hij.symm
          | exact readerSlotW0_ne_W1 hij | exact readerSlotW0_ne_W1 hij.symm
          | exact lf0_ne_lf1 hij | exact lf0_ne_lf1 hij.symm
          | exact hplf0 hij | exact hplf0 hij.symm | exact hplf1 hij | exact hplf1 hij.symm
          | exact hpK hij | exact hpK hij.symm | exact hpX hij | exact hpX hij.symm
          | exact hpN hij | exact hpN hij.symm | exact hpW0 hij | exact hpW0 hij.symm
          | exact hpW1 hij | exact hpW1 hij.symm
          | exact hKlf0 hij | exact hKlf0 hij.symm | exact hKlf1 hij | exact hKlf1 hij.symm
          | exact hXlf0 hij | exact hXlf0 hij.symm | exact hXlf1 hij | exact hXlf1 hij.symm
          | exact hNlf0 hij | exact hNlf0 hij.symm | exact hNlf1 hij | exact hNlf1 hij.symm
          | exact hW0lf0 hij | exact hW0lf0 hij.symm | exact hW0lf1 hij | exact hW0lf1 hij.symm
          | exact hW1lf0 hij | exact hW1lf0 hij.symm | exact hW1lf1 hij | exact hW1lf1 hij.symm)

/-- The column reindex bijection (lower-triangular column order). -/
noncomputable def colEquivT (hpiv : PivotNotReader) : Fin 8 ≃ Fin (routeMAmbient M222) :=
  Equiv.ofBijective slotListC ((Fintype.bijective_iff_injective_and_card slotListC).mpr
    ⟨slotListC_injective hpiv, by rw [routeMAmbient_M222]⟩)

/-- The row reindex permutation `[out4, out5, out1, out6, out2, out3, out0, out7]` (output-coord
order making `toMatrix'` lower-triangular). -/
def rowPerm : Fin 8 ≃ Fin 8 where
  toFun := ![4, 5, 1, 6, 2, 3, 0, 7]
  invFun := ![6, 2, 4, 5, 0, 1, 3, 7]
  left_inv := by decide
  right_inv := by decide

/-- The row reindex as a `Fin 8 ≃ Fin (routeMAmbient M222)` (matching `colEquivT`'s target, so
`abs_det_submatrix_equiv_equiv` applies to the `Fin (routeMAmbient M222)`-indexed `toMatrix'`). -/
def rowEquiv : Fin 8 ≃ Fin (routeMAmbient M222) :=
  rowPerm.trans (finCongr routeMAmbient_M222.symm)

/-- The explicit lower-triangular literal matrix (`a = aRead u`, `b = bRead u`, `n = nRead u`,
`w0 = w0Read u`, `w1 = w1Read u`), diagonal `[1, a, a, 1, 1, 1, 1, 1]`, det `= a²`. -/
noncomputable def litMatLT (u : Fin (routeMAmbient M222) → ℝ) : Matrix (Fin 8) (Fin 8) ℝ :=
  !![1, 0, 0, 0, 0, 0, 0, 0;
     bRead u, aRead u, 0, 0, 0, 0, 0, 0;
     nRead u, 0, aRead u, 0, 0, 0, 0, 0;
     bRead u * nRead u, aRead u * nRead u, aRead u * bRead u, 1, 0, 0, 0, 0;
     0, 0, 0, 0, 1, 0, 0, 0;
     0, 0, 0, 0, 0, 1, 0, 0;
     0, 0, -w0Read u, 0, -nRead u, 0, 1, 0;
     0, 0, -w1Read u, 0, 0, -nRead u, 0, 1]

/-- `det (litMatLT u) = aRead u ^ 2` (lower-triangular, diagonal `[1, a, a, 1, 1, 1, 1, 1]`). -/
theorem litMatLT_det (u : Fin (routeMAmbient M222) → ℝ) : (litMatLT u).det = aRead u ^ 2 := by
  have htri : (litMatLT u).BlockTriangular OrderDual.toDual := by
    intro i j hij
    rw [OrderDual.toDual_lt_toDual, Fin.lt_def] at hij
    fin_cases i <;> fin_cases j <;>
      first
        | (exact absurd hij (by decide))
        | (simp [litMatLT])
  rw [Matrix.det_of_lowerTriangular _ htri]
  simp [litMatLT, Fin.prod_univ_succ]
  ring

/-- `Pi.single (slotListC j) 1` evaluated at `slotListC k` collapses to `if j = k then 1 else 0`
(via `slotListC_injective`). -/
theorem single_slotListC (hpiv : PivotNotReader) (j k : Fin 8) :
    (Pi.single (slotListC j) (1 : ℝ) : Fin (routeMAmbient M222) → ℝ) (slotListC k)
      = if j = k then 1 else 0 := by
  rw [Pi.single_apply]
  by_cases h : slotListC k = slotListC j
  · rw [if_pos h, if_pos (slotListC_injective hpiv h).symm]
  · rw [if_neg h, if_neg (fun he => h (by rw [he]))]

/-- `Pi.single (slotListC j) 1` read at a named slot `s = slotListC k`, collapsed via
`single_slotListC`. The named-slot wrappers below specialize this (keeping the reader names so
litMatLT's `aRead/bRead/…` coefficients match). -/
theorem single_at_eq (hpiv : PivotNotReader) (j k : Fin 8) (s : Fin (routeMAmbient M222))
    (hs : s = slotListC k) :
    (Pi.single (slotListC j) (1 : ℝ) : Fin (routeMAmbient M222) → ℝ) s
      = if j = k then 1 else 0 := by
  rw [hs]; exact single_slotListC hpiv j k

theorem single_at_readerK (hpiv : PivotNotReader) (j : Fin 8) :
    (Pi.single (slotListC j) (1 : ℝ) : Fin (routeMAmbient M222) → ℝ) readerSlotK
      = if j = ⟨0, by decide⟩ then 1 else 0 := single_at_eq hpiv j _ _ rfl
theorem single_at_readerX (hpiv : PivotNotReader) (j : Fin 8) :
    (Pi.single (slotListC j) (1 : ℝ) : Fin (routeMAmbient M222) → ℝ) readerSlotX
      = if j = ⟨1, by decide⟩ then 1 else 0 := single_at_eq hpiv j _ _ rfl
theorem single_at_readerN (hpiv : PivotNotReader) (j : Fin 8) :
    (Pi.single (slotListC j) (1 : ℝ) : Fin (routeMAmbient M222) → ℝ) readerSlotN
      = if j = ⟨2, by decide⟩ then 1 else 0 := single_at_eq hpiv j _ _ rfl
theorem single_at_pivot (hpiv : PivotNotReader) (j : Fin 8) :
    (Pi.single (slotListC j) (1 : ℝ) : Fin (routeMAmbient M222) → ℝ) (structPivot M222 hN_M222)
      = if j = ⟨3, by decide⟩ then 1 else 0 := single_at_eq hpiv j _ _ rfl
theorem single_at_readerW0 (hpiv : PivotNotReader) (j : Fin 8) :
    (Pi.single (slotListC j) (1 : ℝ) : Fin (routeMAmbient M222) → ℝ) readerSlotW0
      = if j = ⟨4, by decide⟩ then 1 else 0 := single_at_eq hpiv j _ _ rfl
theorem single_at_readerW1 (hpiv : PivotNotReader) (j : Fin 8) :
    (Pi.single (slotListC j) (1 : ℝ) : Fin (routeMAmbient M222) → ℝ) readerSlotW1
      = if j = ⟨5, by decide⟩ then 1 else 0 := single_at_eq hpiv j _ _ rfl
theorem single_at_lf0 (hpiv : PivotNotReader) (j : Fin 8) :
    (Pi.single (slotListC j) (1 : ℝ) : Fin (routeMAmbient M222) → ℝ) lf0
      = if j = ⟨6, by decide⟩ then 1 else 0 := single_at_eq hpiv j _ _ rfl
theorem single_at_lf1 (hpiv : PivotNotReader) (j : Fin 8) :
    (Pi.single (slotListC j) (1 : ℝ) : Fin (routeMAmbient M222) → ℝ) lf1
      = if j = ⟨7, by decide⟩ then 1 else 0 := single_at_eq hpiv j _ _ rfl

set_option linter.unusedSimpArgs false in
/-- **The reindexed entry Jacobian** `(toMatrix' (TbCLM u)).submatrix rowPerm (colEquivT hpiv) =
litMatLT u` — the explicit lower-triangular matrix (per-entry via the `Pi.single` slot collapse). -/
theorem TbCLM_toMatrix_reindex (hpiv : PivotNotReader) (u : Fin (routeMAmbient M222) → ℝ) :
    (LinearMap.toMatrix' (TbCLM u).toLinearMap).submatrix rowEquiv (colEquivT hpiv)
      = litMatLT u := by
  have hcol : ∀ k : Fin 8, (colEquivT hpiv k : Fin (routeMAmbient M222)) = slotListC k :=
    fun k => rfl
  ext i j
  rw [Matrix.submatrix_apply, LinearMap.toMatrix'_apply]
  change (TbCLM u) (Pi.single (colEquivT hpiv j) 1) (rowEquiv i) = litMatLT u i j
  have hri : (rowEquiv i : Fin (routeMAmbient M222)) = (rowPerm i : Fin 8) := rfl
  rw [hri, TbCLM, ContinuousLinearMap.pi_apply]
  -- full `simp` (with `Matrix.cons_val`) reduces the row-vector selection `![CLMs] (rowPerm ⟨i⟩)`
  -- to its CLM; the `single_at_*` lemmas collapse the `Pi.single` reads (keeping reader names, so
  -- litMatLT's `aRead/bRead/…` coefficients match), then `norm_num` finishes the arithmetic.
  -- (The `simp` lemma list and `single_at_*` cover all 64 (i,j) cases jointly; per-case the linter
  -- may see some as unused — they are needed across the other cases.)
  fin_cases i <;> fin_cases j <;>
    simp +arith [rowPerm, Equiv.coe_fn_mk, Matrix.cons_val, hcol, ContinuousLinearMap.sub_apply,
      ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.proj_apply, smul_eq_mul,
      single_at_readerK hpiv, single_at_readerX hpiv, single_at_readerN hpiv,
      single_at_pivot hpiv, single_at_readerW0 hpiv, single_at_readerW1 hpiv,
      single_at_lf0 hpiv, single_at_lf1 hpiv,
      litMatLT, aRead_eq, bRead_eq, nRead_eq, w0Read_eq, w1Read_eq]

/-- **`|det (TbCLM u)| = |aRead u|²`** — the entry-Jacobian determinant (`-aRead u²` up to sign),
via the reindex to the explicit lower-triangular `litMatLT u`. -/
theorem TbCLM_abs_det (hpiv : PivotNotReader) (u : Fin (routeMAmbient M222) → ℝ) :
    |LinearMap.det (TbCLM u).toLinearMap| = |aRead u| ^ 2 := by
  have hdetTo : LinearMap.det (TbCLM u).toLinearMap
      = Matrix.det (LinearMap.toMatrix' (TbCLM u).toLinearMap) :=
    (LinearMap.det_toMatrix' (TbCLM u).toLinearMap).symm
  have hsub : |((LinearMap.toMatrix' (TbCLM u).toLinearMap).submatrix
        rowEquiv (colEquivT hpiv)).det|
      = |Matrix.det (LinearMap.toMatrix' (TbCLM u).toLinearMap)| :=
    abs_det_submatrix_equiv_equiv rowEquiv (colEquivT hpiv) _
  have ereindex :
      |((LinearMap.toMatrix' (TbCLM u).toLinearMap).submatrix rowEquiv (colEquivT hpiv)).det|
        = |(litMatLT u).det| := by rw [TbCLM_toMatrix_reindex hpiv u]
  calc |LinearMap.det (TbCLM u).toLinearMap|
      = |Matrix.det (LinearMap.toMatrix' (TbCLM u).toLinearMap)| := by rw [hdetTo]
    _ = |((LinearMap.toMatrix' (TbCLM u).toLinearMap).submatrix
          rowEquiv (colEquivT hpiv)).det| := hsub.symm
    _ = |(litMatLT u).det| := ereindex
    _ = |aRead u| ^ 2 := by rw [litMatLT_det, abs_pow]

/-- **`|det DB u| = |aRead u|²`** — the boundary-factor det (`DB = Q222CLM ∘ TbCLM`, `Q222CLM`
measure-preserving so `|det| = 1`). -/
theorem DB_abs_det (hpiv : PivotNotReader) (u : Fin (routeMAmbient M222) → ℝ) :
    |LinearMap.det (DB u).toLinearMap| = |aRead u| ^ 2 := by
  have hdet : LinearMap.det (DB u).toLinearMap
      = LinearMap.det (Q222CLM : (Fin 8 → ℝ) →ₗ[ℝ] (Fin 8 → ℝ))
        * LinearMap.det (TbCLM u).toLinearMap := by
    have hcoe : (DB u).toLinearMap
        = (Q222CLM : (Fin 8 → ℝ) →ₗ[ℝ] (Fin 8 → ℝ)).comp (TbCLM u).toLinearMap := by
      rw [DB, ContinuousLinearMap.coe_comp]
    rw [hcoe]
    exact LinearMap.det_comp (Q222CLM : (Fin 8 → ℝ) →ₗ[ℝ] (Fin 8 → ℝ)) (TbCLM u).toLinearMap
  rw [hdet, abs_mul, Q222CLM_abs_det, one_mul, TbCLM_abs_det hpiv u]

/-! ## The `BData M222` instance + the concrete (2,2,2) interior-det headline -/

/-- The per-boundary engine values for the (2,2,2) faithful factor: `|aRead (pbo u)|²` at `s = 0`,
`1` at `s = 1` (so `∏ = |aRead (pbo u)|² = |det DB|`). -/
noncomputable def engine222 (u : Fin (routeMAmbient M222) → ℝ) : Fin 2 → ℝ :=
  fun s => if s = 0 then |aRead (pivotBlowupOn active222 (structPivot M222 hN_M222) u)| ^ 2 else 1

theorem engine222_prod (u : Fin (routeMAmbient M222) → ℝ) :
    ∏ s : Fin 2, engine222 u s
      = |aRead (pivotBlowupOn active222 (structPivot M222 hN_M222) u)| ^ 2 := by
  rw [Fin.prod_univ_two]; simp [engine222]

/-- **The faithful `BData M222`** for the concrete (2,2,2) node, given the chart non-degeneracy
`PivotNotReader` (the radial axis distinct from the Schur readers). All fields landed:
`hmap` (faithful map identity), `hcard` (the `minAdm = 3` count), `hdet` (`|det DB| = |aRead|²`). -/
noncomputable def bData222 (hpiv : PivotNotReader) (u : Fin (routeMAmbient M222) → ℝ) :
    BData M222 tach222 structAdm_tach222 hN_M222 1 hp1_222 hp2_222 rfin222 u where
  active := active222
  hp_mem := structPivot_mem_active222
  hcard := active222_card
  B := Bchart
  DB := DB (pivotBlowupOn active222 (structPivot M222 hN_M222) u)
  hasDB := Bchart_hasFDerivAt (pivotBlowupOn active222 (structPivot M222 hN_M222) u)
  hmap := hmap_222
  engine := engine222 u
  hdet := by
    rw [DB_abs_det hpiv (pivotBlowupOn active222 (structPivot M222 hN_M222) u), engine222_prod]

/-- **The unconditional-modulo-`PivotNotReader` interior-det headline for `phiFlatLiveR1 M222`**:
`|det D(phiFlatLiveR1 M222 …)| = |u_p|^{minAdm−1} · |aRead (pbo u)|²`. Reads off
`interiorDet_headline_of_BData` applied to `bData222`. -/
theorem interiorDet_headline_222 (hpiv : PivotNotReader) (u : Fin (routeMAmbient M222) → ℝ) :
    |LinearMap.det (fderiv ℝ (phiFlatLiveR1 M222 tach222 structAdm_tach222 hN_M222 1 hp1_222 hp2_222
        rfin222) u).toLinearMap|
      = |u (structPivot M222 hN_M222)| ^ (minAdm M222 - 1)
        * ∏ s : Fin 2, (bData222 hpiv u).engine s :=
  interiorDet_headline_of_BData M222 tach222 structAdm_tach222 hN_M222 1 hp1_222 hp2_222 rfin222 u
    (bData222 hpiv u)

end DLNFibre.DLN.RLCT

exec
/bin/bash -lc 'rg -n "def routeMAmbient|routeMAmbient|flatDim|chartDim_eq_flatDim" lean/DLNFibre/DLN/RLCT/Validate/RouteMGenFlatStruct.lean lean/DLNFibre/DLN/RLCT/Validate/RouteMChartIdx.lean lean/DLNFibre/DLN/RLCT/Validate/RouteM222StructAdm.lean lean/DLNFibre/DLN/RLCT/Validate/RouteMState.lean -S' in /home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/agent-a9bb11c22680d93d4
 succeeded in 0ms:
lean/DLNFibre/DLN/RLCT/Validate/RouteM222StructAdm.lean:13:non-degenerate. `schurDim = [4, 2]`, `liftDim = [2, 0]`, `N = routeMAmbient = 8`.
lean/DLNFibre/DLN/RLCT/Validate/RouteM222StructAdm.lean:50:/-- `routeMAmbient M222 = 8` (the flat dimension). -/
lean/DLNFibre/DLN/RLCT/Validate/RouteM222StructAdm.lean:51:theorem routeMAmbient_M222 : routeMAmbient M222 = 8 := by decide
lean/DLNFibre/DLN/RLCT/Validate/RouteM222StructAdm.lean:53:/-- `0 < routeMAmbient M222` (the pivot axis exists). -/
lean/DLNFibre/DLN/RLCT/Validate/RouteM222StructAdm.lean:54:theorem hN_M222 : 0 < routeMAmbient M222 := by decide
lean/DLNFibre/DLN/RLCT/Validate/RouteMGenFlatStruct.lean:87:variable (M t : Fin (L + 1) → ℕ) (ha : StructAdm M t) (x : Fin (routeMAmbient M) → 𝕜)
lean/DLNFibre/DLN/RLCT/Validate/RouteMGenFlatStruct.lean:227:    Fin (routeMAmbient M) → ℝ :=
lean/DLNFibre/DLN/RLCT/Validate/RouteMChartIdx.lean:6:# `RouteMChartIdx` — Phase B item 1: the chart-coordinate dimension count (`∑ roleDim = flatDim`)
lean/DLNFibre/DLN/RLCT/Validate/RouteMChartIdx.lean:10:plus the radial, to `flatDim M = routeMAmbient M` — the cert's `ninputs = flatDim` (a genuine bijective
lean/DLNFibre/DLN/RLCT/Validate/RouteMChartIdx.lean:20:* `chartDim_eq_flatDim` — `(∑ roleDim) + 1 − 1 = flatDim M` (the coordinate count, range form).
lean/DLNFibre/DLN/RLCT/Validate/RouteMChartIdx.lean:35:equals the layer-product sum `∑_{k<L} M_k·M_{k+1}` (`= flatDim`). The `t_k` middle sums cancel; `t_0 = M_0`
lean/DLNFibre/DLN/RLCT/Validate/RouteMChartIdx.lean:36:closes the boundary. The spine of `chartDim_eq_flatDim`. -/
lean/DLNFibre/DLN/RLCT/Validate/RouteMChartIdx.lean:78:/-! ## The chart-coordinate dimension = flatDim (range form) -/
lean/DLNFibre/DLN/RLCT/Validate/RouteMChartIdx.lean:80:/-- **The chart-coordinate count = `flatDim M`** (range form, the cert's `ninputs = flatDim`). With the
lean/DLNFibre/DLN/RLCT/Validate/RouteMChartIdx.lean:83:`flatDim M`. Combines `roleSquare_eq` (per-boundary Schur roles) + the `tele_card` telescoping +
lean/DLNFibre/DLN/RLCT/Validate/RouteMChartIdx.lean:84:`flatDim_eq`. The role count `(t_k+r_k)(t_k+c_k) = t_k·M_{k+1}` IS the `tele_card` summand. -/
lean/DLNFibre/DLN/RLCT/Validate/RouteMChartIdx.lean:85:theorem chartDim_eq_flatDim (M : Fin (L + 1) → ℕ) (t : ℕ → ℕ)
lean/DLNFibre/DLN/RLCT/Validate/RouteMChartIdx.lean:89:      = flatDim M := by
lean/DLNFibre/DLN/RLCT/Validate/RouteMChartIdx.lean:90:  rw [tele_card (Wext M) t (by rw [h0]; simp [Wext]) hc L hL, flatDim_eq]

exec
/bin/bash -lc 'head -40 lean/DLNFibre/DLN/RLCT/Validate/RouteMGenFlatStruct.lean && head -60 lean/DLNFibre/DLN/RLCT/Validate/RouteMChartIdx.lean' in /home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/agent-a9bb11c22680d93d4
 succeeded in 0ms:
import DLNFibre.DLN.RLCT.Validate.RouteMChartSlots
import DLNFibre.DLN.RLCT.Validate.RouteMGenChartId
import DLNFibre.DLN.RLCT.Validate.RouteMGenFlatChart
import DLNFibre.DLN.RLCT.Validate.RouteMGenChainBridge

/-!
# `RouteMGenFlatStruct` — the STRUCTURED achiever-chart decoder (the item-3 unblock)

The structured flat decoder `genBlkFlatStruct`, replacing the diagnosed over-determined modular-hash
`genBlkFlat` (`RouteMGenFlatChart`). It reads the genuine FREE coordinates (the Schur-frame `K/X/N/E`
roles + the lift `W`, per boundary) from DISJOINT flat slots via the banked `chartIdxEquiv`
coordinatization (`RouteMChartSlots`), and DERIVES the `GenBlk` block data via the Schur-frame
structure: `Bmat (k+1) = [K ; X·K]` (`bmatStack`), `Rmat (k+1) = [[0,0],[0,E]]` (`rmatPad`), so
`C_{k+1} = Bmat·chainQ(N) + u·Rmat = [[K, KN],[XK, XKN + uE]]` (the Schur frame). The `K` block is kept
DIRECT (the LDU reparametrization is the job of the `composeFold` LDU factor, item 2 — matched in
item 3). The identity boundary `k = 0` is `Bmat 0 = I`, `Rmat 0 = 0`.

Indexing: GenBlk boundary `s = k+1` reads chart-slot `k` (the `s = k+1` form makes
`schurDim k = Text(k+1)·Wext(k+1)` `rfl`-clean — no `s−1`-through-`dite` HEq friction). The `t`-arity
bridge is `tDesc := fun j => Text M t (j+1)` (the ℕ→ℕ descent `schurDim`/`chartIdxEquiv` consume).

This module is the decoder + (next) its rate transfer (via the decoder-agnostic `routeMCore_phiGen`,
re-checking only `hC0`). The factored chart + item-3 map equality + the leafH summation build on it.

Axiom-clean `[propext, Classical.choice, Quot.sound]` (pure matrix algebra / finite equivalences).
-/

namespace DLNFibre.DLN.RLCT

open Matrix

variable {L : ℕ}
variable {𝕜 : Type} [CommRing 𝕜]

/-! ## The descent-bridge + the per-boundary admissibility hypotheses

`tDesc M t := fun j => Text M t (j+1)` is the ℕ→ℕ descent the slot API consumes (`Text(k+1)` at index
`k`). The structured decoder needs the achiever descent `Text(k+2) ≤ Text(k+1)` (strictly decreasing
`t`) for the `Bmat`/`Rmat` block splits — beyond the chain's `hle : Text(k+1) ≤ Wext k`. -/

import DLNFibre.DLN.RLCT.Validate.RouteMChartIdxCard
import DLNFibre.DLN.RLCT.Validate.RouteMGenChain
import DLNFibre.DLN.RLCT.Validate.RouteMExtraction

/-!
# `RouteMChartIdx` — Phase B item 1: the chart-coordinate dimension count (`∑ roleDim = flatDim`)

The determinant-ready coordinatization's load-bearing arithmetic (item 1 of the det route, B+b1): the
per-boundary chart-coordinate roles (Schur `K`/`X`/`N`/`E`, chain lift `W`) sum, over the `L` boundaries
plus the radial, to `flatDim M = routeMAmbient M` — the cert's `ninputs = flatDim` (a genuine bijective
coordinatization, not the rate-side modular `flatIdxOf`).

The cardinality is a TELESCOPING identity (`tele_card`): per boundary `s` the Schur roles
`K+X+N+E = (t_s+r_s)(t_s+c_s) = t_{s-1}·M_s` (`roleSquare_eq`, via the `K_s` block's `t²` = LDU
`low/diag/up` from `lduRole_card`), the chain lift `W_s = c_s·M_{s+1}`; the `t_s` middle sums cancel and
`t_0 = M_0` closes it. The `+1` radial and `−1` fixed residual cancel.

* `tele_card` — the abstract telescoping `∑ t_k·M_{k+1} + ∑ c_k·M_{k+2} = ∑ M_k·M_{k+1}` (the spine).
* `roleSquare_eq` — `(t_s+r_s)(t_s+c_s) = t_{s-1}·M_s` (the Schur per-boundary role count).
* `chartDim_eq_flatDim` — `(∑ roleDim) + 1 − 1 = flatDim M` (the coordinate count, range form).

Axiom-clean `[propext, Classical.choice, Quot.sound]` (arithmetic + finite cardinality; no analysis).
-/

namespace DLNFibre.DLN.RLCT

open scoped BigOperators

variable {L : ℕ}

/-! ## The abstract telescoping spine -/

/-- **The telescoping card identity.** For widths `M, t : ℕ → ℕ` with `t 0 = M 0` and `t (k+1) ≤ M (k+1)`,
the boundary Schur-role sum `∑_{k<L} t_k·M_{k+1}` plus the chain-lift sum `∑_{k<L−1} (M_{k+1}−t_{k+1})·M_{k+2}`
equals the layer-product sum `∑_{k<L} M_k·M_{k+1}` (`= flatDim`). The `t_k` middle sums cancel; `t_0 = M_0`
closes the boundary. The spine of `chartDim_eq_flatDim`. -/
theorem tele_card (M t : ℕ → ℕ) (h0 : t 0 = M 0)
    (hc : ∀ k, t (k + 1) ≤ M (k + 1)) :
    ∀ L, 0 < L →
    (∑ k ∈ Finset.range L, t k * M (k + 1))
        + (∑ k ∈ Finset.range (L - 1), (M (k + 1) - t (k + 1)) * M (k + 2))
      = ∑ k ∈ Finset.range L, M k * M (k + 1) := by
  intro L
  induction L with
  | zero => omega
  | succ n ih =>
      intro _
      rcases Nat.eq_zero_or_pos n with hn | hn
      · subst hn; simp [h0]
      · have ihn := ih hn
        rw [Finset.sum_range_succ (fun k => t k * M (k + 1)) n,
            show (n + 1) - 1 = (n - 1) + 1 by omega,
            Finset.sum_range_succ (fun k => (M (k + 1) - t (k + 1)) * M (k + 2)) (n - 1),
            Finset.sum_range_succ (fun k => M k * M (k + 1)) n, show n - 1 + 1 = n by omega,
            show n - 1 + 2 = n + 1 by omega]
        have hsplit : t n * M (n + 1) + (M n - t n) * M (n + 1) = M n * M (n + 1) := by
          have hle : t n ≤ M n := by cases n with | zero => omega | succ m => exact hc m
          rw [← Nat.add_mul]; congr 1; omega
        have e1 : (∑ k ∈ Finset.range n, t k * M (k + 1)) + t n * M (n + 1)
              + ((∑ k ∈ Finset.range (n - 1), (M (k + 1) - t (k + 1)) * M (k + 2))

codex
The concrete 222 code already demonstrates the useful pattern for leaf slots: choose from a finite complement and carry membership, never compare opaque `chartIdxEquiv.symm` images to a literal `Fin` value. The only remaining mismatch is that the pivot itself is outside that complement-choice discipline.
exec
/bin/bash -lc "sed -n '1,180p' expeditions/aoyagi-full/codex/pivotnotreader-discharge-answer.md" in /home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/agent-a9bb11c22680d93d4
 succeeded in 0ms:
   Updating ssh://git@github.com/AI-Safety-Institute/aisi-inspect-tools (HEAD)
    Updated ssh://git@github.com/AI-Safety-Institute/aisi-inspect-tools (fa7351f6ef4773f536ee4975c3251325eb9c44df)
Reading prompt from stdin...
OpenAI Codex v0.142.4
--------
workdir: /home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/agent-a9bb11c22680d93d4
model: gpt-5.5
provider: openai-aisi
approval: untrusted
sandbox: read-only
reasoning effort: high
reasoning summaries: none
session id: 019f151a-46fe-7c42-9235-7257f6ae4f61
--------
user
# Design review: discharging PivotNotReader cleanly (Lean 4 + Mathlib, DLNFibre harness)

## Context
A (2,2,2) interior-determinant headline `interiorDet_headline_222` is COMPLETE + axiom-clean except it rests on one open hypothesis:

    PivotNotReader : structPivot M222 hN_M222 ∉ readerSet

where:
- `structPivot M hN : Fin (routeMAmbient M) := ⟨0, hN⟩`  — a GLOBALLY-SHARED def (RouteMFlatStructV.lean), the LITERAL flat-slot 0. It is the radial coordinate of the achiever chart `phiFlatLiveR1` (its rate is `(x structPivot)^2 · U`), and is consumed pervasively downstream: the RLCT measure-transfer contract `RouteMInteriorContract` integrates over `{x | x (structPivot) = 0}` (the radial axis), and many rate/diff lemmas read `x (structPivot)`.
- `readerSet : Finset (Fin (routeMAmbient M222))` = `{readerSlotK, readerSlotX, readerSlotN, readerSlotW0, readerSlotW1}`, the 5 reader slots, each defined as `(chartIdxEquiv M222 …).symm ⟨tag⟩` where `chartIdxEquiv` is a NONCOMPUTATIONAL bijection (built via `Fintype.equivFin`). It does NOT kernel-reduce: `decide` gets stuck.
- `PivotNotReader` is used to build a `Fin 8 ≃ Fin 8` reindex equiv (`slotEquiv`/`colEquivT`) from the 8 slots `[a,b,n,w0,w1,p,lf0,lf1]` being PAIRWISE DISTINCT. The pivot `p = structPivot` must be ≠ each of the 5 readers. That equiv computes `|det DB| = |aRead|²` (the engine). `PivotNotReader` is the ONLY thing that ties slot-0 to "not a reader".

## Verified facts (I checked the actual code)
1. NO proof does `rfl`/`decide` on `structPivot = ⟨0,_⟩` to extract the literal 0. It's used purely as an abstract `Fin N` element everywhere. So changing its VALUE is type-safe (no literal-0 dependence).
2. The headline wiring `interiorDet_headline_of_BData` / `radialComp_abs_det` uses ONLY `hp_mem : structPivot ∈ active` + `hcard : active.card = minAdm` — NOT slot-0-ness, NOT PivotNotReader.
3. The leaf slots `lf0, lf1` are ALREADY chosen from `univ \ forbiddenSlots` where `forbiddenSlots = insert structPivot {5 readers}` (card ≤ 6, complement ≥ 2), so `lf_i ∉ readerSet` and `lf_i ≠ structPivot` hold BY MEMBERSHIP — no opaque comparison. This is the existing discharge PATTERN.
4. A pen-and-paper verdict says `PivotNotReader` for `structPivot = ⟨0,_⟩` is FRAGILE/possibly FALSE (slot-0 has no constructed relation to the chartIdxEquiv readers; "prove it semantically" = route (i) is a dead end). Verdict = route (ii): "re-point the pivot to a chosen non-reader slot."

## The tension I want adjudicated
`structPivot` is GLOBALLY shared (RouteMFlatStructV, consumed by the chart `phiFlatLiveR1`, the rate lemmas, AND the RLCT measure-transfer `RouteMInteriorContract` which integrates over `{x (structPivot) = 0}`). "Re-point structPivot to a non-reader slot" is NOT obviously local — it touches the whole downstream cone, and worse, the general `structPivot M hN` has NO `readerSet M` to choose its complement from (readerSet is M222-specific). So "choose pivot from `univ \ readerSet`" doesn't directly generalize ∀M the way `structPivot := ⟨0,_⟩` does.

## QUESTION
What is the CLEANEST discharge of `PivotNotReader`, given the above? Rank these and flag traps:

(A) Change `structPivot M hN := ⟨0,hN⟩` globally to a `Classical.choice` of `univ \ (reader-image)` — but reader-image needs `chartIdxEquiv M` ∀M, and structPivot is in a low-level shared file that may not import the chart machinery. Is this a layering violation / import cycle risk?

(B) Keep `structPivot := ⟨0,_⟩` global, but make the (2,2,2) BData use a DIFFERENT pivot `pRad := Classical.choice (univ \ readerSet)` LOCAL to RouteMBData222, and prove the headline for THAT pivot — then bridge `phiFlatLiveR1 … (radial read at structPivot)` to the pРad-radial chart. Does this require re-deriving the rate `routeMCore_phiFlatLiveR1` for a non-structPivot radial? (The rate is `(x structPivot)^2·U` — hard-wired.)

(C) Prove `PivotNotReader` is TRUE after all via a CARDINALITY/counting argument: `readerSet.card + minAdm M ≤ flatDim M` is TIGHT at M222 (5 + 3 = 8). Does tightness HELP prove `structPivot ∉ readerSet`? (I suspect NOT — a counting bound says the complement is nonempty, but doesn't pin slot-0 into it. Confirm this is a dead end, or show the counting argument that DOES force `⟨0,_⟩ ∉ readerSet`.)

(D) Some other route — e.g. make `phiFlatLiveR1` PARAMETRIC in the radial slot `p₀` (currently hard-wired to `structPivot`), so the chart, rate, and headline all take `p₀` as an argument, and instantiate `p₀ := a chosen non-reader slot`. Most faithful but most invasive — is it the right ∀M move?

Give me: the ranked recommendation, the import-layering check for (A), whether (C) is truly a dead end, and which route GENERALIZES to ∀M cleanly. Be concrete about Lean mechanics.

codex
I’ll check the local Lean layout before giving the recommendation, especially where `structPivot`, reader slots, and the BData/headline contracts live. That should make the import and generalization advice concrete instead of speculative.
exec
/bin/bash -lc "sed -n '1,220p' CLAUDE.md" in /home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/agent-a9bb11c22680d93d4
 succeeded in 0ms:
# geometry-of-dln-fibre

AI-assisted math-research + Lean-formalisation harness for **digesting and formalising** the paper
*"Geometry of the fibers of the multiplication map of deep linear neural networks"* (Simon Pepin
Lehalleur & Richárd Rimányi, 2024; `paper-sources/lehalleur-rimanyi-2024-geometry-of-dln-fibre/`).
Orientation is in [`README.md`](README.md); this file is the disposition and the working discipline.
The process harness (disposition + policies + roles + skills + the markdown→Lean pipeline) is ported
from the `ai-research-assistant` harness and is **domain-agnostic** — see [`TEMPLATE.md`](TEMPLATE.md)
to instantiate it for another paper.

## Disposition

The work here is research. Not coding, not ticking off a support ticket, not shipping a product. 
The stance: 
- careful, conscientious, objective as a scientist.
- meticulous in calculation as Euler, bold as Grothendieck. 
- methodical as Sherlock Holmes. Observe before theorising. Distinguish data from interpretation. 
- update like a Bayesian; do not collapse to the mode. 


- **Resist the move-fast-and-ship-it instinct.** Stackable, solid progress is the goal; the trap is
  *visible* progress raced ahead of it — a clean doc or confident headline that travels far while leaving
  holes behind. When you reach for a confident headline, that is the moment to look for the confound. Each
  layer should be solid and hole-free before the next stands on it.
- **Fill the layer — completion is your strength.** *The sea rises inexorably, but not in spikes*
  ([`docs/policies/bedrock.md`](docs/policies/bedrock.md)): within a boundary already staked, close the holes
  — the generality a statement promised, the cases it already claims, fidelity to the definition and the
  underlying spirit it invokes — rather than defer them. Such hardening is high-value, and it is where your
  **comparative advantage** lies: your bottleneck is scoping, taste, and direction, not the patient completion
  of well-scoped work — so do not treat that completion capacity, which is *abundant*, as if it were *scarce*.
  **Just do it!** Don't file it as a "chore" (an *unprobed* difficulty claim, not a defer). Surface to move the
  *boundary* — but an **earned** taste-judgment that a gap is the *right* extension is itself direction:
  **Just Do It** if within reach, else **roadmap** it; only a *bare, unargued* extension waits for the operator.
- **Name results for what they are.** A result's name and statement denote exactly what is proven — no more;
  reaching for an impressive name (or "done") is the visible-progress instinct in disguise. Separate Proved /
  Assumed / Cited / Deferred. See [`docs/policies/precision.md`](docs/policies/precision.md). (Here the
  recurring trap: a `rlct_…`-named result that in fact proves only a *codimension* — the `rlct = ½·codim`
  reading needs the cited Aoyagi equality.)
- **Build to bedrock.** A sorry-free build defeats *technical* slop; it never defeats *conceptual* slop —
  "technically correct but subtly wrong, not The Way." **Bedrock is the rock the rising sea rises over**: build
  the theory so the next result can stand on it without re-opening it. Where short feedback loops fail, **beauty
  is the instrument** — a vacuous, mis-scoped, or overclaiming result is *ugly*, and the ugliness is
  information. The **controller holds this taste and judges against it**; a green build is necessary, never
  sufficient. See [`docs/policies/bedrock.md`](docs/policies/bedrock.md).
- **Caveats live next to claims, not in footnotes.** An assumed hypothesis or a cited interface goes in the
  same paragraph as any claim that depends on it.
- **Write to figure out the truth, not to persuade.** Concise and fact-based.
- **Elementary, precisely.** Build explanations up from precise but simple well-chunked objects, established locally in the
  document. "Elementary" does not mean imprecise or dumbed-down or toy analogies: every step stays
  mathematically precise. Introduce the objects you use before you use them; prefer a chain of small exact
  statements over one dense one. Resist over-naming things to do chunking. Reach for an analogy only when it is exact and load-bearing. See
  [`docs/policies/writing-style.md`](docs/policies/writing-style.md).

## Writing and communication discipline (object-level focus)
In writing or in communication, focus on object-level. Resist meta-level pull. 
Remove authorial self-reassurance: `honestly`, `fundamentally`, `this is the whole point`, `this is loadbearing`, `of course`, `simply`, `just`, and selling phrasing.
The full list and the review function that enforces it are in [`docs/policies/review.md`](docs/policies/review.md).

## How research runs here

- **Expeditions** ([`docs/policies/expedition.md`](docs/policies/expedition.md)) are the unit: a central
  question, a controller delegating to thread teammates (explore / formalisation / infra), reviewers, and a
  synthesis at close. Run on the Agent Teams substrate (`CLAUDE_CODE_EXPERIMENTAL_AGENT_TEAMS=1`); launch with
  cwd = this repo root.
- **Pipeline: markdown → Lean.** Theory develops in markdown (`theory/`, expedition notes). A stable claim is
  formalised in Lean (`lean/`, library `DLNFibre`). The reader-facing digest/expositions live in
  `docs/expositions/`.
  - *Scholium* is a **viewer** (renders these markdown docs with KaTeX + callouts), not an editor; write to its
    conventions in [`docs/policies/scholium-writing-format.md`](docs/policies/scholium-writing-format.md). The
    recurring trap: display math `$$…$$` needs a **blank line before and after**, fences on their own lines
    (indented inside `!!!`/`???` callouts) — packed against text it falls through to markdown and the `_`
    subscripts render as emphasis. A second trap: **fenced code does not render inside a callout** — use an
    indented code block (8-space indent) there; top-level fenced code is fine.
- **Claims** carry kill-conditions; new claims are stress-tested, established/cited results verified against
  source ([`docs/policies/claims.md`](docs/policies/claims.md)).
- **Codex** is the independent second model for strategy and review
  ([`docs/policies/codex-consultation.md`](docs/policies/codex-consultation.md)).

## Team structure

Roles are documented under [`.agent-team/roles/`](.agent-team/roles/):
- `controller` — this lead session: meta-planning, delegation, integration.
- `scout` — explore / reconnaissance threads: map the terrain (Mathlib, the paper, possibility spaces), compute / derive / claims.
- `pen-and-paper` — a specialised `scout`: design-space math adjudicating a truth-value (`witness` / `obstruction` seats), exact algebra, decorrelated Codex; hands a certificate to the formaliser. No Lean.
- `formaliser` — formalisation (tide) threads.
- `reviewer` — controller-spawned independent audit (soundness / fidelity).
- `hardener` — independent principles / taste reviewer (precision, bedrock).

If dispatched into a role, read its role file and agent definition first.

## Branch discipline

- **One remote: `origin = git@github.com:edmund-ukaisi/geometry-of-dln-fibre.git`.** All work lives here.
- **`dev` is the integration branch.** Feature and expedition branches branch off `dev` and PR back into
  `dev`. `master` is the **release** branch — promoted from `dev` deliberately by the operator, never pushed
  to directly.
- Use a **feature branch** for any non-trivial unit of work; you can push here; don't commit to `dev` or `master` directly. One
  expedition runs on one branch (`expedition/<slug>`); PR at close behind signal-and-wait.
- **Pushing feature/expedition branches to `origin` is pre-authorized** (operator standing instruction,
  2026-06-12) — push freely to bank and share work. **Opening/merging PRs and the `dev → master` promotion
  remain operator-gated** (signal-and-wait); the operator performs those. Always confirm the push target is
  `origin`, never a non-`origin` remote.

## Memory

Persistent context lives **in-repo**: this file, the policies in `docs/policies/`, the expedition docs
(`synthesis.md` / statement cards / `thread.md`), `ROADMAP.md`, and `lean/CLAUDE.md`. Save conventions and
decisions there.

**Do NOT write to global Claude memory (`~/.claude/**/memory/`).** It pollutes other workspaces and is
invisible to collaborators reading the repo. This binds the controller **and every teammate** — the harness
may prompt you to save a memory there; do not. If a teammate writes one, the controller deletes it and
re-homes the content in-repo. (Agent-Teams *runtime* state under `~/.claude/teams/` and `~/.claude/tasks/` is
fine — that's the substrate, not persistent context.)

## The destination, plainly

We want, in honest Lean, the paper's results about the **fibres of matrix multiplication** for deep linear
networks:

- the space $\operatorname{Rep}_{\underline d}$ of composable matrix tuples, the multiplication map
  $\operatorname{mult}$, the zero-product / rank-$r$ loci, and the fibres $\operatorname{mult}^{-1}(B)$;
- via the **type-A quiver** translation (orbits ↔ Kostant partitions ↔ rank patterns, Gabriel, orbit-closure
  order, the `Ext` codimension): the codimension $C$ and the number $\theta$ of top-dimensional components,
  in the paper's three forms (Poincaré series, a quadratic integer program, an explicit formula), and the
  surprising **permutation invariance** of $(C,\theta)$;

exec
/bin/bash -lc "rg -n \"structPivot M hN|structPivot|achieverPhi|phiFlatLiveR1|phiFlatStructV|UvalLiveR1|BData|pivotBlowupOn active \\(structPivot\" lean/DLNFibre/DLN/RLCT/Validate -S" in /home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/agent-a9bb11c22680d93d4
 succeeded in 0ms:
lean/DLNFibre/DLN/RLCT/Validate/RouteMFrameLocality.lean:35:self-map of `Fin N → ℝ` with the coordinate-locality — in particular `DFrame_M = fderiv phiFlatLiveR1`
lean/DLNFibre/DLN/RLCT/Validate/RouteMBData.lean:4:# `RouteMBData` — the radial-scaling core of the B-interface map identity (the `hmap` algebra)
lean/DLNFibre/DLN/RLCT/Validate/RouteMBData.lean:7:(`phiFlatLiveR1_eq_B_comp_pivotBlowupOn`, `_chart`) are SUPERSEDED — the WRONG `B`.** Their hyps
lean/DLNFibre/DLN/RLCT/Validate/RouteMBData.lean:18:only the two `phiFlatLiveR1_eq_B_comp_pivotBlowupOn` consumers are off the build path.
lean/DLNFibre/DLN/RLCT/Validate/RouteMBData.lean:20:The genuinely-reachable, network-free core of `BData.hmap` (`phiFlatLiveR1 = B ∘ pivotBlowupOn`):
lean/DLNFibre/DLN/RLCT/Validate/RouteMBData.lean:124:⚠ **SUPERSEDED by `phiFlatLiveR1_eq_B_comp_pivotBlowupOn_chart` below (the Fix-B CHART contract).**
lean/DLNFibre/DLN/RLCT/Validate/RouteMBData.lean:127:`route-i-l2/fixed_pivot_refutation.py`). `phiFlatLiveR1` uses the GAUGE-FIXED pivot decoder
lean/DLNFibre/DLN/RLCT/Validate/RouteMBData.lean:143:theorem phiFlatLiveR1_eq_B_comp_pivotBlowupOn (M t : Fin (L + 1) → ℕ) (ha : StructAdm M t)
lean/DLNFibre/DLN/RLCT/Validate/RouteMBData.lean:149:      smulRmatRfin (x (structPivot M hN)) M t (genBlkFlatLiveR1 M t ha p hp1 hp2 (rfin x) x)
lean/DLNFibre/DLN/RLCT/Validate/RouteMBData.lean:151:            (rfin (pivotBlowupOn active (structPivot M hN) x))
lean/DLNFibre/DLN/RLCT/Validate/RouteMBData.lean:152:            (pivotBlowupOn active (structPivot M hN) x)) :
lean/DLNFibre/DLN/RLCT/Validate/RouteMBData.lean:153:    phiFlatLiveR1 M t ha hN p hp1 hp2 rfin
lean/DLNFibre/DLN/RLCT/Validate/RouteMBData.lean:155:        ∘ pivotBlowupOn active (structPivot M hN) := by
lean/DLNFibre/DLN/RLCT/Validate/RouteMBData.lean:157:  show phiGen (x (structPivot M hN)) M t (genBlkFlatLiveR1 M t ha p hp1 hp2 (rfin x) x)
lean/DLNFibre/DLN/RLCT/Validate/RouteMBData.lean:159:  rw [phiGen_smul_radial (x (structPivot M hN)) M t
lean/DLNFibre/DLN/RLCT/Validate/RouteMBData.lean:181:theorem phiFlatLiveR1_eq_B_comp_pivotBlowupOn_chart (M t : Fin (L + 1) → ℕ) (ha : StructAdm M t)
lean/DLNFibre/DLN/RLCT/Validate/RouteMBData.lean:187:      phiGen 1 M t (smulRmatRfin (x (structPivot M hN)) M t
lean/DLNFibre/DLN/RLCT/Validate/RouteMBData.lean:190:            (rfin (pivotBlowupOn active (structPivot M hN) x))
lean/DLNFibre/DLN/RLCT/Validate/RouteMBData.lean:191:            (pivotBlowupOn active (structPivot M hN) x)) (hleStruct M t ha)) :
lean/DLNFibre/DLN/RLCT/Validate/RouteMBData.lean:192:    phiFlatLiveR1 M t ha hN p hp1 hp2 rfin
lean/DLNFibre/DLN/RLCT/Validate/RouteMBData.lean:194:        ∘ pivotBlowupOn active (structPivot M hN) := by
lean/DLNFibre/DLN/RLCT/Validate/RouteMBData.lean:196:  show phiGen (x (structPivot M hN)) M t (genBlkFlatLiveR1 M t ha p hp1 hp2 (rfin x) x)
lean/DLNFibre/DLN/RLCT/Validate/RouteMBData.lean:198:  rw [phiGen_smul_radial (x (structPivot M hN)) M t
lean/DLNFibre/DLN/RLCT/Validate/RouteMBData.lean:217:    (hcp : chartParamsGen (x (structPivot M hN)) M t
lean/DLNFibre/DLN/RLCT/Validate/RouteMBData.lean:221:          (rfin (pivotBlowupOn active (structPivot M hN) x))
lean/DLNFibre/DLN/RLCT/Validate/RouteMBData.lean:222:          (pivotBlowupOn active (structPivot M hN) x)) (hleStruct M t ha)) :
lean/DLNFibre/DLN/RLCT/Validate/RouteMBData.lean:223:    phiGen 1 M t (smulRmatRfin (x (structPivot M hN)) M t
lean/DLNFibre/DLN/RLCT/Validate/RouteMBData.lean:226:          (rfin (pivotBlowupOn active (structPivot M hN) x))
lean/DLNFibre/DLN/RLCT/Validate/RouteMBData.lean:227:          (pivotBlowupOn active (structPivot M hN) x)) (hleStruct M t ha) := by
lean/DLNFibre/DLN/RLCT/Validate/RouteMBData.lean:229:  rw [chartParamsGen_smulRmatRfin (x (structPivot M hN)) M t
lean/DLNFibre/DLN/RLCT/Validate/RouteMFrameDiff.lean:12:(`item3-frameM-buildspec.md`): establishing `DifferentiableAt phiFlatLiveR1 u` over OPAQUE width
lean/DLNFibre/DLN/RLCT/Validate/RouteMFrameDiff.lean:37:→ `paramsEquivFlat`), each a sub-piece. Once assembled, `DifferentiableAt phiFlatLiveR1 u` +
lean/DLNFibre/DLN/RLCT/Validate/RouteMAchieverVvalPoly.lean:280:    MvPolynomial.eval x (Xvec (routeMAmbient M) (structPivot M hN)) = x (structPivot M hN) :=
lean/DLNFibre/DLN/RLCT/Validate/RouteMAchieverVvalPoly.lean:287:    (chainOfMt (MvPolynomial.eval x (Xvec (routeMAmbient M) (structPivot M hN))) M t
lean/DLNFibre/DLN/RLCT/Validate/RouteMAchieverVvalPoly.lean:289:      = ((chainOfMt (Xvec (routeMAmbient M) (structPivot M hN)) M t
lean/DLNFibre/DLN/RLCT/Validate/RouteMAchieverVvalPoly.lean:294:  convert Chain.Hmat_zero_map (chainOfMt (Xvec (routeMAmbient M) (structPivot M hN)) M t
lean/DLNFibre/DLN/RLCT/Validate/RouteMAchieverVvalPoly.lean:297:    (Xvec (routeMAmbient M) (structPivot M hN)) hle).symm
lean/DLNFibre/DLN/RLCT/Validate/RouteMAchieverVvalPoly.lean:316:  sqSumHmat0 (chainOfMt (Xvec (routeMAmbient M) (structPivot M hN)) M t
lean/DLNFibre/DLN/RLCT/Validate/RouteMAchieverVvalPoly.lean:324:      = sqSumHmat0 (chainOfMt (x (structPivot M hN)) M t (genBlkFlatStruct M t ha x) hle).toChain := by
lean/DLNFibre/DLN/RLCT/Validate/RouteMAchieverVvalPoly.lean:366:    VvalGen_eq_sqSumHmat0 (x (structPivot M hN)) (genBlkFlatStruct M (tach M) (structAdm_tach M hL) x)
lean/DLNFibre/DLN/RLCT/Validate/RouteMFrameQM.lean:11:factorization `phiFlatLiveR1 = Q_M ∘ T_M` (with `T_M := pack_M.symm ∘ chartParamsGen` the aligned-basis
lean/DLNFibre/DLN/RLCT/Validate/RouteMInteriorDetReal.lean:5:# `RouteMInteriorDetReal` — the interior-det headline on the REAL chart `phiFlatLiveR1` (route-2)
lean/DLNFibre/DLN/RLCT/Validate/RouteMInteriorDetReal.lean:8:chart `phiFlatLiveR1` — NOT an engine surrogate. The Jacobian is `fderiv ℝ (phiFlatLiveR1 …) u`, whose
lean/DLNFibre/DLN/RLCT/Validate/RouteMInteriorDetReal.lean:9:EXISTENCE is the banked `phiFlatLiveR1_differentiableAt`; this module records that IF that real Jacobian
lean/DLNFibre/DLN/RLCT/Validate/RouteMInteriorDetReal.lean:14:`fderiv ℝ phiFlatLiveR1 u = e.symm ∘ stairMap V (L+1) f c ∘ e` with the engine block-det identifications —
lean/DLNFibre/DLN/RLCT/Validate/RouteMInteriorDetReal.lean:17:`fderiv ℝ (phiFlatLiveR1 …)` so it CANNOT be discharged by an engine surrogate (Codex's flagged trap).
lean/DLNFibre/DLN/RLCT/Validate/RouteMInteriorDetReal.lean:19:* `interiorDet_phiFlatLiveR1_of_stairConj` — the REAL-chart headline, given the staircase conjugacy of
lean/DLNFibre/DLN/RLCT/Validate/RouteMInteriorDetReal.lean:20:  `fderiv ℝ phiFlatLiveR1` + the engine identifications. Output formula identical to
lean/DLNFibre/DLN/RLCT/Validate/RouteMInteriorDetReal.lean:35:/-- **The interior-det HEADLINE on the REAL chart `phiFlatLiveR1`.** Let `D := fderiv ℝ (phiFlatLiveR1 …)
lean/DLNFibre/DLN/RLCT/Validate/RouteMInteriorDetReal.lean:36:u` be the actual Jacobian (its existence is `phiFlatLiveR1_differentiableAt`). If `D` (as a `LinearMap`)
lean/DLNFibre/DLN/RLCT/Validate/RouteMInteriorDetReal.lean:42:  `|det (fderiv phiFlatLiveR1 u)| = |u_p|^{minAdm−1} · ∏_s ( |det K_s|^{r_s+c_s} · ∏_i |q_{s,i}|^{…} )`.
lean/DLNFibre/DLN/RLCT/Validate/RouteMInteriorDetReal.lean:46:(the faithful staircase decomposition of `fderiv phiFlatLiveR1` over the opaque chart-coordinate widths).
lean/DLNFibre/DLN/RLCT/Validate/RouteMInteriorDetReal.lean:48:theorem interiorDet_phiFlatLiveR1_of_stairConj
lean/DLNFibre/DLN/RLCT/Validate/RouteMInteriorDetReal.lean:57:    (hconj : (fderiv ℝ (phiFlatLiveR1 M t ha hN p hp1 hp2 rfin) u).toLinearMap
lean/DLNFibre/DLN/RLCT/Validate/RouteMInteriorDetReal.lean:66:    |LinearMap.det (fderiv ℝ (phiFlatLiveR1 M t ha hN p hp1 hp2 rfin) u).toLinearMap|
lean/DLNFibre/DLN/RLCT/Validate/RouteMInteriorDetReal.lean:71:    (fderiv ℝ (phiFlatLiveR1 M t ha hN p hp1 hp2 rfin) u).toLinearMap hconj
lean/DLNFibre/DLN/RLCT/Validate/RouteMFlatStructV.lean:11:This module lifts the rate to a genuine **full chart map** `phiFlatStructV M t ha : (Fin N → ℝ) →
lean/DLNFibre/DLN/RLCT/Validate/RouteMFlatStructV.lean:18:  `routeMCore M (phiFlatStructV M t ha x) = (x p)² · VvalGen (x p) M t (genBlkFlatStruct M t ha x) hle`.
lean/DLNFibre/DLN/RLCT/Validate/RouteMFlatStructV.lean:89:def structPivot (M : Fin (L + 1) → ℕ) (hN : 0 < routeMAmbient M) : Fin (routeMAmbient M) := ⟨0, hN⟩
lean/DLNFibre/DLN/RLCT/Validate/RouteMFlatStructV.lean:91:/-- **The vector-parametrized structured achiever chart** `phiFlatStructV M t ha hN x := paramsEquivFlat
lean/DLNFibre/DLN/RLCT/Validate/RouteMFlatStructV.lean:94:noncomputable def phiFlatStructV (M t : Fin (L + 1) → ℕ) (ha : StructAdm M t)
lean/DLNFibre/DLN/RLCT/Validate/RouteMFlatStructV.lean:96:  phiGen (x (structPivot M hN)) M t (genBlkFlatStruct M t ha x) (hleStruct M t ha)
lean/DLNFibre/DLN/RLCT/Validate/RouteMFlatStructV.lean:99:— the radial quotient `routeMCore (phiFlatStructV x) / (x p)²` of the rate `routeMCore = (x p)² · U`.
lean/DLNFibre/DLN/RLCT/Validate/RouteMFlatStructV.lean:107:  VvalGen (x (structPivot M hN)) M t (genBlkFlatStruct M t ha x) (hleStruct M t ha)
lean/DLNFibre/DLN/RLCT/Validate/RouteMFlatStructV.lean:109:/-- **The rate transfers to the vector chart ∀M (NO bridge)**: `routeMCore M (phiFlatStructV x) =
lean/DLNFibre/DLN/RLCT/Validate/RouteMFlatStructV.lean:113:theorem routeMCore_phiFlatStructV (M t : Fin (L + 1) → ℕ) (ha : StructAdm M t)
lean/DLNFibre/DLN/RLCT/Validate/RouteMFlatStructV.lean:115:    routeMCore M (phiFlatStructV M t ha hN x)
lean/DLNFibre/DLN/RLCT/Validate/RouteMFlatStructV.lean:116:      = (x (structPivot M hN)) ^ 2 * UvalStructV M t ha hN x :=
lean/DLNFibre/DLN/RLCT/Validate/RouteMFlatStructV.lean:117:  routeMCore_phiGen (x (structPivot M hN)) M t (genBlkFlatStruct M t ha x) (hleStruct M t ha)
lean/DLNFibre/DLN/RLCT/Validate/RouteMFlatStructV.lean:118:    (hC0_struct_gen M t ha (x (structPivot M hN)) x)
lean/DLNFibre/DLN/RLCT/Validate/RouteM4422Bridge.lean:9:Before building the general OPTION-1 bridge (`composeFold fs = phiFlatStructV` over opaque widths), this
lean/DLNFibre/DLN/RLCT/Validate/RouteMFlatLDU.lean:8:`phiFlatStructV` (`RouteMFlatStructV`) reads each per-boundary Schur K-core block as a FREE matrix
lean/DLNFibre/DLN/RLCT/Validate/RouteMFlatLDU.lean:10:`t ≥ 2`, `det K_s` is a degree-`t` POLYNOMIAL, NOT a monomial. Hence the FREE-K `phiFlatStructV`
lean/DLNFibre/DLN/RLCT/Validate/RouteMFlatLDU.lean:50:  phiGen (x (structPivot M hN)) M t (genBlkFlatStruct M t ha (reparam x)) (hleStruct M t ha)
lean/DLNFibre/DLN/RLCT/Validate/RouteMFlatLDU.lean:57:  VvalGen (x (structPivot M hN)) M t (genBlkFlatStruct M t ha (reparam x)) (hleStruct M t ha)
lean/DLNFibre/DLN/RLCT/Validate/RouteMFlatLDU.lean:70:      = (x (structPivot M hN)) ^ 2 * UvalLDU M t ha hN reparam x :=
lean/DLNFibre/DLN/RLCT/Validate/RouteMFlatLDU.lean:71:  routeMCore_phiGen (x (structPivot M hN)) M t (genBlkFlatStruct M t ha (reparam x))
lean/DLNFibre/DLN/RLCT/Validate/RouteMFlatLDU.lean:73:    (hC0_struct_gen M t ha (x (structPivot M hN)) (reparam x))
lean/DLNFibre/DLN/RLCT/Validate/RouteMFlatLDU.lean:82:/-- **The identity reparametrization recovers `phiFlatStructV`** — `phiFlatLDU` with `reparam = id`
lean/DLNFibre/DLN/RLCT/Validate/RouteMFlatLDU.lean:87:    phiFlatLDU M t ha hN id x = phiFlatStructV M t ha hN x := rfl
lean/DLNFibre/DLN/RLCT/Validate/RouteMFlatLDU.lean:90:the banked free-K rate `routeMCore_phiFlatStructV` (the rate is genuinely transferred, not vacuous). -/
lean/DLNFibre/DLN/RLCT/Validate/RouteMFlatLDU.lean:93:    routeMCore M (phiFlatStructV M t ha hN x)
lean/DLNFibre/DLN/RLCT/Validate/RouteMFlatLDU.lean:94:      = (x (structPivot M hN)) ^ 2 * UvalStructV M t ha hN x := by
lean/DLNFibre/DLN/RLCT/Validate/RouteMColumnFactor.lean:19:`StairProd`, NO global `composeFold fs = phiFlatLiveR1` map equality.
lean/DLNFibre/DLN/RLCT/Validate/RouteMColumnFactor.lean:29:`phiFlatLiveR1_jacobian_scaledColumns` obligation).
lean/DLNFibre/DLN/RLCT/Validate/RouteMColumnFactor.lean:57:column-factorization (`phiFlatLiveR1_jacobian_scaledColumns`) and the `G`-det identification
lean/DLNFibre/DLN/RLCT/Validate/RouteMColumnFactor.lean:72:`structPivot ∈ active`) + `Finset.card_erase_of_mem`. Decouples the COUNT obligation from the
lean/DLNFibre/DLN/RLCT/Validate/RouteMColumnFactor.lean:75:/-- **The radial `R`-column set** `active.erase structPivot` — the `u`-scaled non-pivot coords. -/
lean/DLNFibre/DLN/RLCT/Validate/RouteMColumnFactor.lean:78:  active.erase (structPivot M hN)
lean/DLNFibre/DLN/RLCT/Validate/RouteMColumnFactor.lean:83:    (active : Finset (Fin (routeMAmbient M))) (hp : structPivot M hN ∈ active)
lean/DLNFibre/DLN/RLCT/Validate/RouteMCardBridge.lean:11:`active.card − 1 = minAdm M − 1` (`radialFactor_abs_det`). This discharges the `leafH (structPivot) =
lean/DLNFibre/DLN/RLCT/Validate/RouteMCardBridge.lean:20:* `radialActive_exists` — `∃ active, structPivot ∈ active ∧ active.card = minAdm` (given `minAdm ≤ N`,
lean/DLNFibre/DLN/RLCT/Validate/RouteMCardBridge.lean:23:  `leafH p := active.card − 1` (`0` elsewhere) with `active.card = minAdm`, `leafH (structPivot) =
lean/DLNFibre/DLN/RLCT/Validate/RouteMCardBridge.lean:88:`Finset (Fin (routeMAmbient M))` of cardinality `minAdm M` containing the radial pivot `structPivot`
lean/DLNFibre/DLN/RLCT/Validate/RouteMCardBridge.lean:94:      structPivot M hN ∈ active ∧ active.card = minAdm M := by
lean/DLNFibre/DLN/RLCT/Validate/RouteMCardBridge.lean:96:    (show ({structPivot M hN} : Finset (Fin (routeMAmbient M))).card ≤ minAdm M by
lean/DLNFibre/DLN/RLCT/Validate/RouteMCardBridge.lean:107:    (active : Finset (Fin (routeMAmbient M))) (hp : structPivot M hN ∈ active)
lean/DLNFibre/DLN/RLCT/Validate/RouteMCardBridge.lean:109:    |LinearMap.det ((radialFactor active (structPivot M hN)).D u).toLinearMap|
lean/DLNFibre/DLN/RLCT/Validate/RouteMCardBridge.lean:110:      = |u (structPivot M hN)| ^ (minAdm M - 1) := by
lean/DLNFibre/DLN/RLCT/Validate/RouteMCardBridge.lean:111:  rw [radialFactor_abs_det active (structPivot M hN) hp u, hcard]
lean/DLNFibre/DLN/RLCT/Validate/RouteMCardBridge.lean:114:`leafH j := if j = structPivot then active.card − 1 else 0`, at `active.card = minAdm M`, has
lean/DLNFibre/DLN/RLCT/Validate/RouteMCardBridge.lean:115:`leafH (structPivot) = minAdm M − 1` — the `NodeAchieverChart.leafH_pivot` field. (The spectator
lean/DLNFibre/DLN/RLCT/Validate/RouteMCardBridge.lean:120:    (fun j => if j = structPivot M hN then active.card - 1 else 0) (structPivot M hN)
lean/DLNFibre/DLN/RLCT/Validate/RouteMChartDiff.lean:8:# `RouteMChartDiff` — b-FrameM-2 assembly (1): `DifferentiableAt phiFlatLiveR1` ⟸ per-layer `Agen`
lean/DLNFibre/DLN/RLCT/Validate/RouteMChartDiff.lean:11:differentiability `DifferentiableAt phiFlatLiveR1` to the per-layer differentiability of `Agen` (the
lean/DLNFibre/DLN/RLCT/Validate/RouteMChartDiff.lean:14:* **A** (linear CLE comp): `phiFlatLiveR1 = paramsEquivFlat ∘ chartParamsGen`, and `paramsEquivFlat`
lean/DLNFibre/DLN/RLCT/Validate/RouteMChartDiff.lean:15:  is the LINEAR reshape (`paramsEquivFlatCLE`, banked), so `DifferentiableAt phiFlatLiveR1 ⟸
lean/DLNFibre/DLN/RLCT/Validate/RouteMChartDiff.lean:23:The composite (`phiFlatLiveR1_differentiableAt_of_Agen`) leaves EXACTLY the per-layer residual: `∀ s,
lean/DLNFibre/DLN/RLCT/Validate/RouteMChartDiff.lean:53:/-- **b-FrameM-2 assembly (1): `DifferentiableAt phiFlatLiveR1` from per-layer `Agen`.** If every chain
lean/DLNFibre/DLN/RLCT/Validate/RouteMChartDiff.lean:55:`x₀`, then the full chart `phiFlatLiveR1` is differentiable at `x₀`. Composes reductions A (linear CLE),
lean/DLNFibre/DLN/RLCT/Validate/RouteMChartDiff.lean:57:theorem phiFlatLiveR1_differentiableAt_of_Agen (M t : Fin (L + 1) → ℕ) (ha : StructAdm M t)
lean/DLNFibre/DLN/RLCT/Validate/RouteMChartDiff.lean:63:      (fun x => Agen (x (structPivot M hN)) M t
lean/DLNFibre/DLN/RLCT/Validate/RouteMChartDiff.lean:65:    DifferentiableAt ℝ (phiFlatLiveR1 M t ha hN p hp1 hp2 rfin) x0 := by
lean/DLNFibre/DLN/RLCT/Validate/RouteMChartDiff.lean:67:  have hcle : (phiFlatLiveR1 M t ha hN p hp1 hp2 rfin)
lean/DLNFibre/DLN/RLCT/Validate/RouteMChartDiff.lean:68:      = fun x => paramsEquivFlat M (chartParamsGen (x (structPivot M hN)) M t
lean/DLNFibre/DLN/RLCT/Validate/RouteMChartDiff.lean:74:      (fun x => chartParamsGen (x (structPivot M hN)) M t
lean/DLNFibre/DLN/RLCT/Validate/RouteMChartDiff.lean:82:      (chartParamsGen (x0 (structPivot M hN)) M t
lean/DLNFibre/DLN/RLCT/Validate/RouteMChartDiff.lean:85:      (x := chartParamsGen (x0 (structPivot M hN)) M t
lean/DLNFibre/DLN/RLCT/Validate/RouteMBInterface.lean:15:This module FREEZES that interface as a `structure BData` bundling:
lean/DLNFibre/DLN/RLCT/Validate/RouteMBInterface.lean:19:- `hmap` — the MAP identity `φ = B ∘ pivotBlowupOn active structPivot` (obligation (1), discharged
lean/DLNFibre/DLN/RLCT/Validate/RouteMBInterface.lean:23:Given a `BData`, the headline follows by `radialComp_abs_det` (the banked wiring) —
lean/DLNFibre/DLN/RLCT/Validate/RouteMBInterface.lean:24:`interiorDet_headline_of_BData` below; the formaliser builds the `BData` instance. The interface
lean/DLNFibre/DLN/RLCT/Validate/RouteMBInterface.lean:25:decouples the two: each side builds against `BData`'s fields without waiting on the other.
lean/DLNFibre/DLN/RLCT/Validate/RouteMBInterface.lean:27:* `BData` — the frozen interface structure.
lean/DLNFibre/DLN/RLCT/Validate/RouteMBInterface.lean:28:* `interiorDet_headline_of_BData` — the unconditional interior-det headline from a `BData` (WIRING:
lean/DLNFibre/DLN/RLCT/Validate/RouteMBInterface.lean:29:  `radialComp_abs_det` + the bundled obligations). The LAST step once a `BData` is constructed.
lean/DLNFibre/DLN/RLCT/Validate/RouteMBInterface.lean:46:headline is read off it by `interiorDet_headline_of_BData`. `engine s` is the per-boundary value
lean/DLNFibre/DLN/RLCT/Validate/RouteMBInterface.lean:48:structure BData (M t : Fin (L + 1) → ℕ) (ha : StructAdm M t) (hN : 0 < routeMAmbient M) (p : ℕ)
lean/DLNFibre/DLN/RLCT/Validate/RouteMBInterface.lean:55:  hp_mem : structPivot M hN ∈ active
lean/DLNFibre/DLN/RLCT/Validate/RouteMBInterface.lean:63:  hasDB : HasFDerivAt B DB (pivotBlowupOn active (structPivot M hN) u)
lean/DLNFibre/DLN/RLCT/Validate/RouteMBInterface.lean:64:  /-- Obligation (1): the MAP identity `φ = B ∘ pivotBlowupOn active structPivot`. -/
lean/DLNFibre/DLN/RLCT/Validate/RouteMBInterface.lean:65:  hmap : phiFlatLiveR1 M t ha hN p hp1 hp2 rfin
lean/DLNFibre/DLN/RLCT/Validate/RouteMBInterface.lean:66:    = B ∘ pivotBlowupOn active (structPivot M hN)
lean/DLNFibre/DLN/RLCT/Validate/RouteMBInterface.lean:72:/-- **The unconditional interior-det headline from a `BData`** (the WIRING, obligation (c)). Given
lean/DLNFibre/DLN/RLCT/Validate/RouteMBInterface.lean:73:frozen `BData` (the formaliser's instance), the chart's Jacobian abs-det factorizes as
lean/DLNFibre/DLN/RLCT/Validate/RouteMBInterface.lean:76:theorem interiorDet_headline_of_BData (M t : Fin (L + 1) → ℕ) (ha : StructAdm M t)
lean/DLNFibre/DLN/RLCT/Validate/RouteMBInterface.lean:80:    (u : Fin (routeMAmbient M) → ℝ) (d : BData M t ha hN p hp1 hp2 rfin u) :
lean/DLNFibre/DLN/RLCT/Validate/RouteMBInterface.lean:81:    |LinearMap.det (fderiv ℝ (phiFlatLiveR1 M t ha hN p hp1 hp2 rfin) u).toLinearMap|
lean/DLNFibre/DLN/RLCT/Validate/RouteMBInterface.lean:82:      = |u (structPivot M hN)| ^ (minAdm M - 1) * ∏ s : Fin L, d.engine s := by
lean/DLNFibre/DLN/RLCT/Validate/RouteMBInterface.lean:84:      (phiFlatLiveR1 M t ha hN p hp1 hp2 rfin) u d.DB d.hmap d.hasDB, d.hdet]
lean/DLNFibre/DLN/RLCT/Validate/RouteMChainDiff.lean:10:residual of `RouteMChartDiff.phiFlatLiveR1_differentiableAt_of_Agen` (`Agen s = chainA(N_s, W_s,
lean/DLNFibre/DLN/RLCT/Validate/RouteMRadialComp.lean:44:    (active : Finset (Fin (routeMAmbient M))) (hp : structPivot M hN ∈ active)
lean/DLNFibre/DLN/RLCT/Validate/RouteMRadialComp.lean:50:    (hφ : φ = B ∘ pivotBlowupOn active (structPivot M hN))
lean/DLNFibre/DLN/RLCT/Validate/RouteMRadialComp.lean:51:    (hB : HasFDerivAt B DB (pivotBlowupOn active (structPivot M hN) u)) :
lean/DLNFibre/DLN/RLCT/Validate/RouteMRadialComp.lean:53:      = |u (structPivot M hN)| ^ (minAdm M - 1) * |LinearMap.det DB.toLinearMap| := by
lean/DLNFibre/DLN/RLCT/Validate/RouteMRadialComp.lean:55:  have hrad : HasFDerivAt (pivotBlowupOn active (structPivot M hN))
lean/DLNFibre/DLN/RLCT/Validate/RouteMRadialComp.lean:56:      (pivotBlowupOnDeriv active (structPivot M hN) u) u :=
lean/DLNFibre/DLN/RLCT/Validate/RouteMRadialComp.lean:58:      (pivotBlowupOn_hasFDerivWithinAt active (structPivot M hN) Set.univ u)
lean/DLNFibre/DLN/RLCT/Validate/RouteMRadialComp.lean:60:  have hcomp : HasFDerivAt φ (DB.comp (pivotBlowupOnDeriv active (structPivot M hN) u)) u := by
lean/DLNFibre/DLN/RLCT/Validate/RouteMRadialComp.lean:76:    (active : Finset (Fin (routeMAmbient M))) (hp : structPivot M hN ∈ active)
lean/DLNFibre/DLN/RLCT/Validate/RouteMRadialComp.lean:78:    |LinearMap.det (fderiv ℝ (pivotBlowupOn active (structPivot M hN)) u).toLinearMap|
lean/DLNFibre/DLN/RLCT/Validate/RouteMRadialComp.lean:79:      = |u (structPivot M hN)| ^ (minAdm M - 1)
lean/DLNFibre/DLN/RLCT/Validate/RouteMInteriorDet.lean:9:∏_j |u_j|^{leafH j}`, with the binding `leafH (structPivot) = minAdm M − 1`. The chart is
lean/DLNFibre/DLN/RLCT/Validate/RouteMInteriorDet.lean:10:`phiFlatLiveR1 ∘ kLDU` (the R1 active-center live-leaf decoder ∘ the LDU lens; both banked sorry-free).
lean/DLNFibre/DLN/RLCT/Validate/RouteMInteriorDet.lean:21:* `interiorLeafH_pivot` — the `leafH (structPivot) = minAdm − 1` binding (the `NodeAchieverChart.leafH_pivot`
lean/DLNFibre/DLN/RLCT/Validate/RouteMInteriorDet.lean:34:For any interior chart `phi` (e.g. `phiFlatLiveR1 ∘ kLDU`) with a factorization `composeFold fs = phi`
lean/DLNFibre/DLN/RLCT/Validate/RouteMInteriorDet.lean:47:/-- **The interior `leafH_pivot` binding** `leafH (structPivot) = minAdm M − 1` for the radial-pivot
lean/DLNFibre/DLN/RLCT/Validate/RouteMInteriorDet.lean:48:exponent vector `leafH j := if j = structPivot then active.card − 1 else 0` at the achiever active set
lean/DLNFibre/DLN/RLCT/Validate/RouteMInteriorDet.lean:52:    (fun j => if j = structPivot M hN then active.card - 1 else 0) (structPivot M hN)
lean/DLNFibre/DLN/RLCT/Validate/RouteMAchieverRateFields.lean:9:(`RouteMAchieverStructAdm`). The chart is the banked structured chart `phiFlatStructV M (tach M) …`
lean/DLNFibre/DLN/RLCT/Validate/RouteMAchieverRateFields.lean:10:(`RouteMFlatStructV`), whose rate `routeMCore (phiFlatStructV … x) = (x p)²·UvalStructV … x` is
lean/DLNFibre/DLN/RLCT/Validate/RouteMAchieverRateFields.lean:11:decoder-agnostic (banked `routeMCore_phiFlatStructV`). The unit is `UvalStructV` (`= VvalGen` of the
lean/DLNFibre/DLN/RLCT/Validate/RouteMAchieverRateFields.lean:17:* `achieverPhi` / `achieverUfun` — the chart + unit on the achiever path (`phiFlatStructV`/`UvalStructV`
lean/DLNFibre/DLN/RLCT/Validate/RouteMAchieverRateFields.lean:19:* `routeMCore_achieverPhi` — the RATE `routeMCore M (achieverPhi x) = (x p)²·achieverUfun x` (∀M, one line
lean/DLNFibre/DLN/RLCT/Validate/RouteMAchieverRateFields.lean:20:  from `routeMCore_phiFlatStructV`).
lean/DLNFibre/DLN/RLCT/Validate/RouteMAchieverRateFields.lean:46:/-- The ∀M achiever-path structured chart `phiFlatStructV M (tach M) …` (the binding pivot `⟨0,_⟩`). -/
lean/DLNFibre/DLN/RLCT/Validate/RouteMAchieverRateFields.lean:47:noncomputable def achieverPhi (M : Fin (L + 1) → ℕ) (hL : 0 < L) (hN : 0 < routeMAmbient M)
lean/DLNFibre/DLN/RLCT/Validate/RouteMAchieverRateFields.lean:49:  phiFlatStructV M (tach M) (structAdm_tach M hL) hN x
lean/DLNFibre/DLN/RLCT/Validate/RouteMAchieverRateFields.lean:56:/-- **The RATE identity ∀M** `routeMCore M (achieverPhi x) = (x p)²·achieverUfun x` — decoder-agnostic
lean/DLNFibre/DLN/RLCT/Validate/RouteMAchieverRateFields.lean:57:(banked `routeMCore_phiFlatStructV`), the `NodeAchieverChart.leaf_integrand` rate factor on the achiever
lean/DLNFibre/DLN/RLCT/Validate/RouteMAchieverRateFields.lean:59:theorem routeMCore_achieverPhi (M : Fin (L + 1) → ℕ) (hL : 0 < L) (hN : 0 < routeMAmbient M)
lean/DLNFibre/DLN/RLCT/Validate/RouteMAchieverRateFields.lean:61:    routeMCore M (achieverPhi M hL hN x)
lean/DLNFibre/DLN/RLCT/Validate/RouteMAchieverRateFields.lean:62:      = (x (structPivot M hN)) ^ 2 * achieverUfun M hL hN x :=
lean/DLNFibre/DLN/RLCT/Validate/RouteMAchieverRateFields.lean:63:  routeMCore_phiFlatStructV M (tach M) (structAdm_tach M hL) hN x
lean/DLNFibre/DLN/RLCT/Validate/RouteMAchieverRateFields.lean:74:`leafH` and the binding pivot `p = structPivot M hN`,
lean/DLNFibre/DLN/RLCT/Validate/RouteMAchieverRateFields.lean:75:`(∏_j |x_j|^{leafH j})·|routeMCore M (achieverPhi x)|^{−c}
lean/DLNFibre/DLN/RLCT/Validate/RouteMAchieverRateFields.lean:77:`routeMCore (achieverPhi x) = (x p)²·achieverUfun x` + `achieverUfun ≥ 0` (NO Jacobian determinant). -/
lean/DLNFibre/DLN/RLCT/Validate/RouteMAchieverRateFields.lean:80:    (∏ j, |x j| ^ (leafH j)) * |routeMCore M (achieverPhi M hL hN x)| ^ (-c)
lean/DLNFibre/DLN/RLCT/Validate/RouteMAchieverRateFields.lean:81:      = monomialIntegrand (routeMAmbient M) (nodeLeafK (routeMAmbient M) (structPivot M hN)) leafH c x
lean/DLNFibre/DLN/RLCT/Validate/RouteMAchieverRateFields.lean:83:  leaf_integrand_of_rate (structPivot M hN) leafH
lean/DLNFibre/DLN/RLCT/Validate/RouteMAchieverRateFields.lean:84:    (fun y => routeMCore M (achieverPhi M hL hN y)) (achieverUfun M hL hN)
lean/DLNFibre/DLN/RLCT/Validate/RouteMAchieverRateFields.lean:85:    (fun y => routeMCore_achieverPhi M hL hN y) (fun y => achieverUfun_nonneg M hL hN y) c x
lean/DLNFibre/DLN/RLCT/Validate/RouteMFlatLive.lean:137:  phiGen (x (structPivot M hN)) M t (genBlkFlatLive M t ha (rfin x) x) (hleStruct M t ha)
lean/DLNFibre/DLN/RLCT/Validate/RouteMFlatLive.lean:144:  VvalGen (x (structPivot M hN)) M t (genBlkFlatLive M t ha (rfin x) x) (hleStruct M t ha)
lean/DLNFibre/DLN/RLCT/Validate/RouteMFlatLive.lean:154:      = (x (structPivot M hN)) ^ 2 * UvalLive M t ha hN rfin x :=
lean/DLNFibre/DLN/RLCT/Validate/RouteMFlatLive.lean:155:  routeMCore_phiGen (x (structPivot M hN)) M t (genBlkFlatLive M t ha (rfin x) x)
lean/DLNFibre/DLN/RLCT/Validate/RouteMFlatLive.lean:157:    (hC0_live M t ha (rfin x) (x (structPivot M hN)) x)
lean/DLNFibre/DLN/RLCT/Validate/RouteMFlatLive.lean:172:      = (x (structPivot M hN)) ^ 2 * UvalLive M t ha hN (fun _ => 0) x :=
lean/DLNFibre/DLN/RLCT/Validate/RouteMFlatLive.lean:263:/-- **The R1 active-center chart** `phiFlatLiveR1 … := phiGen (x p₀) M t (genBlkFlatLiveR1 …) hle`
lean/DLNFibre/DLN/RLCT/Validate/RouteMFlatLive.lean:264:(`p₀ = structPivot`, the radial scalar). The pivot boundary `p` (active center) carries the fixed
lean/DLNFibre/DLN/RLCT/Validate/RouteMFlatLive.lean:266:noncomputable def phiFlatLiveR1 (M t : Fin (L + 1) → ℕ) (ha : StructAdm M t)
lean/DLNFibre/DLN/RLCT/Validate/RouteMFlatLive.lean:271:  phiGen (x (structPivot M hN)) M t (genBlkFlatLiveR1 M t ha p hp1 hp2 (rfin x) x) (hleStruct M t ha)
lean/DLNFibre/DLN/RLCT/Validate/RouteMFlatLive.lean:273:/-- **The R1 unit factor** `UvalLiveR1 … := VvalGen (x p₀) M t (genBlkFlatLiveR1 …) hle`. -/
lean/DLNFibre/DLN/RLCT/Validate/RouteMFlatLive.lean:274:noncomputable def UvalLiveR1 (M t : Fin (L + 1) → ℕ) (ha : StructAdm M t)
lean/DLNFibre/DLN/RLCT/Validate/RouteMFlatLive.lean:279:  VvalGen (x (structPivot M hN)) M t (genBlkFlatLiveR1 M t ha p hp1 hp2 (rfin x) x) (hleStruct M t ha)
lean/DLNFibre/DLN/RLCT/Validate/RouteMFlatLive.lean:281:/-- **The rate transfers to the R1 active-center chart ∀M (NO bridge)**: `routeMCore M (phiFlatLiveR1 …) =
lean/DLNFibre/DLN/RLCT/Validate/RouteMFlatLive.lean:282:(x p₀)² · UvalLiveR1 …`. Decoder-agnostic (`routeMCore_phiGen` + the R1 identity boundary `hC0_liveR1`,
lean/DLNFibre/DLN/RLCT/Validate/RouteMFlatLive.lean:284:theorem routeMCore_phiFlatLiveR1 (M t : Fin (L + 1) → ℕ) (ha : StructAdm M t)
lean/DLNFibre/DLN/RLCT/Validate/RouteMFlatLive.lean:289:    routeMCore M (phiFlatLiveR1 M t ha hN p hp1 hp2 rfin x)
lean/DLNFibre/DLN/RLCT/Validate/RouteMFlatLive.lean:290:      = (x (structPivot M hN)) ^ 2 * UvalLiveR1 M t ha hN p hp1 hp2 rfin x :=
lean/DLNFibre/DLN/RLCT/Validate/RouteMFlatLive.lean:291:  routeMCore_phiGen (x (structPivot M hN)) M t (genBlkFlatLiveR1 M t ha p hp1 hp2 (rfin x) x)
lean/DLNFibre/DLN/RLCT/Validate/RouteMFlatLive.lean:293:    (hC0_liveR1 M t ha p hp0 hp1 hp2 (rfin x) (x (structPivot M hN)) x)
lean/DLNFibre/DLN/RLCT/Validate/RouteMFlatLive.lean:303:/-- **`UvalLiveR1 ≥ 0`** — sum of squares (banked `VvalGen_nonneg`). -/
lean/DLNFibre/DLN/RLCT/Validate/RouteMFlatLive.lean:304:theorem UvalLiveR1_nonneg (M t : Fin (L + 1) → ℕ) (ha : StructAdm M t) (hN : 0 < routeMAmbient M)
lean/DLNFibre/DLN/RLCT/Validate/RouteMFlatLive.lean:308:    0 ≤ UvalLiveR1 M t ha hN p hp1 hp2 rfin x :=
lean/DLNFibre/DLN/RLCT/Validate/RouteMFlatLive.lean:330:The `Ubound` a.e.-positivity input for the R1 chart: `∃ w, UvalLiveR1 … w ≠ 0`. At the dead-leaf witness
lean/DLNFibre/DLN/RLCT/Validate/RouteMFlatLive.lean:334:(`readE_wInt`); `Rfin = 0` matches. So `UvalLiveR1 … 0 wInt = UvalStructV … wInt = achieverUfun wInt ≠ 0`
lean/DLNFibre/DLN/RLCT/Validate/RouteMFlatLive.lean:419:IS the dead-leaf `genBlkFlatStruct` (`genBlkFlatLiveR1_wInt_eq`), so `UvalLiveR1 … 0 (wInt p) =
lean/DLNFibre/DLN/RLCT/Validate/RouteMFlatLive.lean:422:theorem exists_UvalLiveR1_ne_zero_interior (M : Fin (L + 1) → ℕ) (hL : 0 < L)
lean/DLNFibre/DLN/RLCT/Validate/RouteMFlatLive.lean:427:      UvalLiveR1 M (tach M) (structAdm_tach M hL) hN (k + 1)
lean/DLNFibre/DLN/RLCT/Validate/RouteMFlatLive.lean:430:  rw [UvalLiveR1, genBlkFlatLiveR1_wInt_eq M (structAdm_tach M hL) k (by omega)
lean/DLNFibre/DLN/RLCT/Validate/RouteMBridgeCLE.lean:8:The OPTION-1 bridge `composeFold fs = phiFlatStructV` collapses (via `composeFold_eq_cleConj_foldr`) to
lean/DLNFibre/DLN/RLCT/Validate/RouteMBridgeCLE.lean:18:matching `phiFlatStructV = paramsEquivFlat ∘ chartParamsGen ∘ genBlkFlatStruct` once
lean/DLNFibre/DLN/RLCT/Validate/RouteMBridgeCLE.lean:73:  paramsEquivFlat M P (structPivot M hN)
lean/DLNFibre/DLN/RLCT/Validate/RouteMBridgeCLE.lean:78:    radialParams M hN (bridgeCLE M x) = x (structPivot M hN) := by
lean/DLNFibre/DLN/RLCT/Validate/RouteMBridgeCLE.lean:95:      = chartParamsGen (x (structPivot M hN)) M t (genBlkFlatStruct M t ha x) (hleStruct M t ha) := by
lean/DLNFibre/DLN/RLCT/Validate/RouteMBridgeCLE.lean:100:A SINGLE `cleConjFactor (bridgeCLE M) phiParamsStruct …`-style factor reproduces `phiFlatStructV` via
lean/DLNFibre/DLN/RLCT/Validate/RouteMPhiTargetDet.lean:13:`phi := phiFlatStructV M t ha hN` (rate already banked), and the bridge `composeFold fs = phiFlatStructV`
lean/DLNFibre/DLN/RLCT/Validate/RouteMSlotId.lean:1:import DLNFibre.DLN.RLCT.Validate.RouteMBData
lean/DLNFibre/DLN/RLCT/Validate/RouteMSlotId.lean:9:`phiFlatLiveR1_eq_B_comp_pivotBlowupOn` (`RouteMBData`), closing the `φ = B ∘ pivotBlowupOn` half of
lean/DLNFibre/DLN/RLCT/Validate/RouteMSlotId.lean:44:`phiFlatLiveR1_eq_B_comp_pivotBlowupOn` consumes).
lean/DLNFibre/DLN/RLCT/Validate/RouteMSlotId.lean:124:`x = fun _ => 2` has `x (structPivot M hN) = 2`, and `hslot` at that point forces `2 = 1`. This is
lean/DLNFibre/DLN/RLCT/Validate/RouteMSlotId.lean:125:the exact shape of the open hypothesis of `phiFlatLiveR1_eq_B_comp_pivotBlowupOn`; it cannot be
lean/DLNFibre/DLN/RLCT/Validate/RouteMSlotId.lean:134:        smulRmatRfin (x (structPivot M hN)) M t (genBlkFlatLiveR1 M t ha p hp1 hp2 (rfin x) x)
lean/DLNFibre/DLN/RLCT/Validate/RouteMSlotId.lean:136:              (rfin (pivotBlowupOn active (structPivot M hN) x))
lean/DLNFibre/DLN/RLCT/Validate/RouteMSlotId.lean:137:              (pivotBlowupOn active (structPivot M hN) x)) := by
lean/DLNFibre/DLN/RLCT/Validate/RouteMSlotId.lean:141:    (rfin (pivotBlowupOn active (structPivot M hN) (fun _ => 2)))
lean/DLNFibre/DLN/RLCT/Validate/RouteMSlotId.lean:142:    (fun _ => 2) (pivotBlowupOn active (structPivot M hN) (fun _ => 2))
lean/DLNFibre/DLN/RLCT/Validate/RouteMSlotId.lean:143:    ((fun _ => 2 : Fin (routeMAmbient M) → ℝ) (structPivot M hN))
lean/DLNFibre/DLN/RLCT/Validate/RouteMSlotId.lean:145:  -- `(fun _ => 2) (structPivot M hN) = 2`, so `hforce : (2 : ℝ) = 1`.
lean/DLNFibre/DLN/RLCT/Validate/RouteMBData222.lean:2:import DLNFibre.DLN.RLCT.Validate.RouteMBData
lean/DLNFibre/DLN/RLCT/Validate/RouteMBData222.lean:8:# `RouteMBData222` — the FAITHFUL `BData M222` term for the concrete (2,2,2) node
lean/DLNFibre/DLN/RLCT/Validate/RouteMBData222.lean:10:Constructs a `BData M222 tach222 ha hN 1 hp1 hp2 rfin u` term (the frozen B-interface,
lean/DLNFibre/DLN/RLCT/Validate/RouteMBData222.lean:12:`interiorDet_headline_of_BData` to obtain the unconditional interior-det headline for
lean/DLNFibre/DLN/RLCT/Validate/RouteMBData222.lean:13:`phiFlatLiveR1 M222`. This is the FAITHFUL route end-to-end on the concrete node (the validate-small the
lean/DLNFibre/DLN/RLCT/Validate/RouteMBData222.lean:18:(`u = x (structPivot)` radial; `a = readK`, `b = readX`, `n = readN`, `w0,w1 = readW`; `lf0,lf1` the
lean/DLNFibre/DLN/RLCT/Validate/RouteMBData222.lean:23:`φ = B ∘ pivotBlowupOn active u` with `active = {structPivot} ∪ {lf0, lf1}` (`card 3 = minAdm(2,2,2)`,
lean/DLNFibre/DLN/RLCT/Validate/RouteMBData222.lean:31:does NOT reduce by `decide`, and `structPivot = ⟨0,_⟩` is NOT a `ChartIdx` tag, so
lean/DLNFibre/DLN/RLCT/Validate/RouteMBData222.lean:32:`leaf-slot ≠ structPivot` is unreachable by tag injectivity. RESOLVED (R2, decorrelated Codex): choose
lean/DLNFibre/DLN/RLCT/Validate/RouteMBData222.lean:33:the two leaf slots `lf0, lf1` from the FINITE COMPLEMENT `univ \ (insert structPivot readerSet)`
lean/DLNFibre/DLN/RLCT/Validate/RouteMBData222.lean:34:(`readerSet.card ≤ 5`, so the complement has `≥ 2` slots); membership then GIVES `lf ≠ structPivot` and
lean/DLNFibre/DLN/RLCT/Validate/RouteMBData222.lean:178:    Cgen (x (structPivot M222 hN_M222)) M222 tach222 (Glr rfin x) (hleStruct M222 tach222 structAdm_tach222) 1
lean/DLNFibre/DLN/RLCT/Validate/RouteMBData222.lean:179:      = schurFrameProd M222 tach222 1 hp1_222 hp2_222 (x (structPivot M222 hN_M222))
lean/DLNFibre/DLN/RLCT/Validate/RouteMBData222.lean:186:      + (x (structPivot M222 hN_M222)) • (Glr rfin x).Rmat 1 else _) = _
lean/DLNFibre/DLN/RLCT/Validate/RouteMBData222.lean:193:    Cgen (x (structPivot M222 hN_M222)) M222 tach222 (Glr rfin x) (hleStruct M222 tach222 structAdm_tach222) 2
lean/DLNFibre/DLN/RLCT/Validate/RouteMBData222.lean:194:      = (x (structPivot M222 hN_M222)) • (rfin x) := by
lean/DLNFibre/DLN/RLCT/Validate/RouteMBData222.lean:195:  show (if hk : (2 : ℕ) < 2 then _ else (x (structPivot M222 hN_M222)) • (Glr rfin x).Rfin 2) = _
lean/DLNFibre/DLN/RLCT/Validate/RouteMBData222.lean:213:    Agen (x (structPivot M222 hN_M222)) M222 tach222 (Glr rfin x)
lean/DLNFibre/DLN/RLCT/Validate/RouteMBData222.lean:215:      = (!![x (structPivot M222 hN_M222) * rfin x ⟨0, by decide⟩ ⟨0, by decide⟩ - nRead x * w0Read x,
lean/DLNFibre/DLN/RLCT/Validate/RouteMBData222.lean:216:            x (structPivot M222 hN_M222) * rfin x ⟨0, by decide⟩ ⟨1, by decide⟩ - nRead x * w1Read x;
lean/DLNFibre/DLN/RLCT/Validate/RouteMBData222.lean:218:  have hA : Agen (x (structPivot M222 hN_M222)) M222 tach222 (Glr rfin x)
lean/DLNFibre/DLN/RLCT/Validate/RouteMBData222.lean:222:          (Cgen (x (structPivot M222 hN_M222)) M222 tach222 (Glr rfin x)
lean/DLNFibre/DLN/RLCT/Validate/RouteMBData222.lean:230:          (Cgen (x (structPivot M222 hN_M222)) M222 tach222 (Glr rfin x)
lean/DLNFibre/DLN/RLCT/Validate/RouteMBData222.lean:233:        = (Cgen (x (structPivot M222 hN_M222)) M222 tach222 (Glr rfin x)
lean/DLNFibre/DLN/RLCT/Validate/RouteMBData222.lean:246:          (Cgen (x (structPivot M222 hN_M222)) M222 tach222 (Glr rfin x)
lean/DLNFibre/DLN/RLCT/Validate/RouteMBData222.lean:259:      (Cgen (x (structPivot M222 hN_M222)) M222 tach222 (Glr rfin x)
lean/DLNFibre/DLN/RLCT/Validate/RouteMBData222.lean:262:        = x (structPivot M222 hN_M222) * rfin x ⟨0, by decide⟩ ⟨0, by decide⟩
lean/DLNFibre/DLN/RLCT/Validate/RouteMBData222.lean:275:      (Cgen (x (structPivot M222 hN_M222)) M222 tach222 (Glr rfin x)
lean/DLNFibre/DLN/RLCT/Validate/RouteMBData222.lean:278:        = x (structPivot M222 hN_M222) * rfin x ⟨0, by decide⟩ ⟨1, by decide⟩
lean/DLNFibre/DLN/RLCT/Validate/RouteMBData222.lean:291:      (Cgen (x (structPivot M222 hN_M222)) M222 tach222 (Glr rfin x)
lean/DLNFibre/DLN/RLCT/Validate/RouteMBData222.lean:297:      (Cgen (x (structPivot M222 hN_M222)) M222 tach222 (Glr rfin x)
lean/DLNFibre/DLN/RLCT/Validate/RouteMBData222.lean:324:    Agen (x (structPivot M222 hN_M222)) M222 tach222 (Glr rfin x)
lean/DLNFibre/DLN/RLCT/Validate/RouteMBData222.lean:327:            aRead x * bRead x, aRead x * bRead x * nRead x + x (structPivot M222 hN_M222)]
lean/DLNFibre/DLN/RLCT/Validate/RouteMBData222.lean:329:  have hA : Agen (x (structPivot M222 hN_M222)) M222 tach222 (Glr rfin x)
lean/DLNFibre/DLN/RLCT/Validate/RouteMBData222.lean:333:          (Cgen (x (structPivot M222 hN_M222)) M222 tach222 (Glr rfin x)
lean/DLNFibre/DLN/RLCT/Validate/RouteMBData222.lean:344:      Agen (x (structPivot M222 hN_M222)) M222 tach222 (Glr rfin x)
lean/DLNFibre/DLN/RLCT/Validate/RouteMBData222.lean:348:        = Cgen (x (structPivot M222 hN_M222)) M222 tach222 (Glr rfin x)
lean/DLNFibre/DLN/RLCT/Validate/RouteMBData222.lean:363:  set sfp := schurFrameProd M222 tach222 1 hp1_222 hp2_222 (x (structPivot M222 hN_M222))
lean/DLNFibre/DLN/RLCT/Validate/RouteMBData222.lean:398:        = aRead x * bRead x * nRead x + x (structPivot M222 hN_M222) := by
lean/DLNFibre/DLN/RLCT/Validate/RouteMBData222.lean:434:occupy, nor whether a chosen leaf slot equals `structPivot = ⟨0,_⟩`. RESOLVED (R2): the five reader
lean/DLNFibre/DLN/RLCT/Validate/RouteMBData222.lean:436:`univ \ insert structPivot readerSet` (card ≥ 8 − 6 = 2). Membership in the complement then gives
lean/DLNFibre/DLN/RLCT/Validate/RouteMBData222.lean:437:`lf ≠ structPivot` and `lf ∉ readerSet` for free — no opaque comparison. -/
lean/DLNFibre/DLN/RLCT/Validate/RouteMBData222.lean:471:  insert (structPivot M222 hN_M222)
lean/DLNFibre/DLN/RLCT/Validate/RouteMBData222.lean:476:  have c1 := Finset.card_insert_le (structPivot M222 hN_M222)
lean/DLNFibre/DLN/RLCT/Validate/RouteMBData222.lean:510:/-- The first leaf slot (`Classical.choose`; in the complement, so `≠ structPivot`, `∉ readerSet`). -/
lean/DLNFibre/DLN/RLCT/Validate/RouteMBData222.lean:524:/-- `lf0 ≠ structPivot` (the leaf slot avoids the pivot — from the complement). -/
lean/DLNFibre/DLN/RLCT/Validate/RouteMBData222.lean:525:theorem lf0_ne_pivot : lf0 ≠ structPivot M222 hN_M222 := by
lean/DLNFibre/DLN/RLCT/Validate/RouteMBData222.lean:531:theorem lf1_ne_pivot : lf1 ≠ structPivot M222 hN_M222 := by
lean/DLNFibre/DLN/RLCT/Validate/RouteMBData222.lean:537:/-- The R2 active set `{structPivot, lf0, lf1}` (card 3 = minAdm; pbo scales the two leaf slots). -/
lean/DLNFibre/DLN/RLCT/Validate/RouteMBData222.lean:539:  {structPivot M222 hN_M222, lf0, lf1}
lean/DLNFibre/DLN/RLCT/Validate/RouteMBData222.lean:541:/-- `structPivot ∈ active222`. -/
lean/DLNFibre/DLN/RLCT/Validate/RouteMBData222.lean:542:theorem structPivot_mem_active222 : structPivot M222 hN_M222 ∈ active222 :=
lean/DLNFibre/DLN/RLCT/Validate/RouteMBData222.lean:547:  have hp0 : structPivot M222 hN_M222 ≠ lf0 := fun h => lf0_ne_pivot h.symm
lean/DLNFibre/DLN/RLCT/Validate/RouteMBData222.lean:548:  have hp1 : structPivot M222 hN_M222 ≠ lf1 := fun h => lf1_ne_pivot h.symm
lean/DLNFibre/DLN/RLCT/Validate/RouteMBData222.lean:562:/-- `pivotBlowupOn active222 structPivot x` at the pivot is `x structPivot`. -/
lean/DLNFibre/DLN/RLCT/Validate/RouteMBData222.lean:564:    pivotBlowupOn active222 (structPivot M222 hN_M222) x (structPivot M222 hN_M222)
lean/DLNFibre/DLN/RLCT/Validate/RouteMBData222.lean:565:      = x (structPivot M222 hN_M222) := by
lean/DLNFibre/DLN/RLCT/Validate/RouteMBData222.lean:568:/-- `pivotBlowupOn` at `lf0` scales by the pivot: `= x structPivot · x lf0`. -/
lean/DLNFibre/DLN/RLCT/Validate/RouteMBData222.lean:570:    pivotBlowupOn active222 (structPivot M222 hN_M222) x lf0
lean/DLNFibre/DLN/RLCT/Validate/RouteMBData222.lean:571:      = x (structPivot M222 hN_M222) * x lf0 := by
lean/DLNFibre/DLN/RLCT/Validate/RouteMBData222.lean:576:/-- `pivotBlowupOn` at `lf1` scales by the pivot: `= x structPivot · x lf1`. -/
lean/DLNFibre/DLN/RLCT/Validate/RouteMBData222.lean:578:    pivotBlowupOn active222 (structPivot M222 hN_M222) x lf1
lean/DLNFibre/DLN/RLCT/Validate/RouteMBData222.lean:579:      = x (structPivot M222 hN_M222) * x lf1 := by
lean/DLNFibre/DLN/RLCT/Validate/RouteMBData222.lean:588:    pivotBlowupOn active222 (structPivot M222 hN_M222) x q = x q := by
lean/DLNFibre/DLN/RLCT/Validate/RouteMBData222.lean:590:  by_cases hp : q = structPivot M222 hN_M222
lean/DLNFibre/DLN/RLCT/Validate/RouteMBData222.lean:601:reading the pivot as the ORDINARY coordinate `y structPivot` (the `+u` of `Agen0[1,1]`), the Schur
lean/DLNFibre/DLN/RLCT/Validate/RouteMBData222.lean:603:the engine). The map identity `phiFlatLiveR1 = B ∘ pivotBlowupOn active222 structPivot` then follows
lean/DLNFibre/DLN/RLCT/Validate/RouteMBData222.lean:612:layers reading the pivot as the ordinary coord `y structPivot`, readers `a/b/n/w0/w1` from `y`, leaf
lean/DLNFibre/DLN/RLCT/Validate/RouteMBData222.lean:617:      aRead y * bRead y, aRead y * bRead y * nRead y + y (structPivot M222 hN_M222)]
lean/DLNFibre/DLN/RLCT/Validate/RouteMBData222.lean:653:    aRead (pivotBlowupOn active222 (structPivot M222 hN_M222) x) = aRead x := by
lean/DLNFibre/DLN/RLCT/Validate/RouteMBData222.lean:656:    bRead (pivotBlowupOn active222 (structPivot M222 hN_M222) x) = bRead x := by
lean/DLNFibre/DLN/RLCT/Validate/RouteMBData222.lean:659:    nRead (pivotBlowupOn active222 (structPivot M222 hN_M222) x) = nRead x := by
lean/DLNFibre/DLN/RLCT/Validate/RouteMBData222.lean:662:    w0Read (pivotBlowupOn active222 (structPivot M222 hN_M222) x) = w0Read x := by
lean/DLNFibre/DLN/RLCT/Validate/RouteMBData222.lean:665:    w1Read (pivotBlowupOn active222 (structPivot M222 hN_M222) x) = w1Read x := by
lean/DLNFibre/DLN/RLCT/Validate/RouteMBData222.lean:668:/-! ## The map identity `phiFlatLiveR1 = B ∘ pivotBlowupOn active222 structPivot` (`hmap`) -/
lean/DLNFibre/DLN/RLCT/Validate/RouteMBData222.lean:675:    chartParamsGen (x (structPivot M222 hN_M222)) M222 tach222 (Glr rfin222 x)
lean/DLNFibre/DLN/RLCT/Validate/RouteMBData222.lean:677:      = Bparams (pivotBlowupOn active222 (structPivot M222 hN_M222) x) := by
lean/DLNFibre/DLN/RLCT/Validate/RouteMBData222.lean:679:  have hB0 : (Bparams (pivotBlowupOn active222 (structPivot M222 hN_M222) x)) 0
lean/DLNFibre/DLN/RLCT/Validate/RouteMBData222.lean:681:          aRead x * bRead x, aRead x * bRead x * nRead x + x (structPivot M222 hN_M222)]
lean/DLNFibre/DLN/RLCT/Validate/RouteMBData222.lean:683:    show (!![aRead (pivotBlowupOn active222 (structPivot M222 hN_M222) x), _; _, _]
lean/DLNFibre/DLN/RLCT/Validate/RouteMBData222.lean:686:  have hB1 : (Bparams (pivotBlowupOn active222 (structPivot M222 hN_M222) x)) 1
lean/DLNFibre/DLN/RLCT/Validate/RouteMBData222.lean:687:      = (!![x (structPivot M222 hN_M222) * x lf0 - nRead x * w0Read x,
lean/DLNFibre/DLN/RLCT/Validate/RouteMBData222.lean:688:          x (structPivot M222 hN_M222) * x lf1 - nRead x * w1Read x;
lean/DLNFibre/DLN/RLCT/Validate/RouteMBData222.lean:690:    show (!![(pivotBlowupOn active222 (structPivot M222 hN_M222) x) lf0 - _, _; _, _]
lean/DLNFibre/DLN/RLCT/Validate/RouteMBData222.lean:695:  · show Matrix.reindex _ _ (Agen (x (structPivot M222 hN_M222)) M222 tach222 (Glr rfin222 x)
lean/DLNFibre/DLN/RLCT/Validate/RouteMBData222.lean:702:  · show Matrix.reindex _ _ (Agen (x (structPivot M222 hN_M222)) M222 tach222 (Glr rfin222 x)
lean/DLNFibre/DLN/RLCT/Validate/RouteMBData222.lean:711:/-- **`hmap`: `phiFlatLiveR1 M222 … rfin222 = Bchart ∘ pivotBlowupOn active222 structPivot`** — the
lean/DLNFibre/DLN/RLCT/Validate/RouteMBData222.lean:712:faithful map identity (obligation (1) of the `BData` interface). -/
lean/DLNFibre/DLN/RLCT/Validate/RouteMBData222.lean:714:    phiFlatLiveR1 M222 tach222 structAdm_tach222 hN_M222 1 hp1_222 hp2_222 rfin222
lean/DLNFibre/DLN/RLCT/Validate/RouteMBData222.lean:715:      = Bchart ∘ pivotBlowupOn active222 (structPivot M222 hN_M222) := by
lean/DLNFibre/DLN/RLCT/Validate/RouteMBData222.lean:717:  show phiGen (x (structPivot M222 hN_M222)) M222 tach222 (Glr rfin222 x)
lean/DLNFibre/DLN/RLCT/Validate/RouteMBData222.lean:719:  show paramsEquivFlat M222 (chartParamsGen (x (structPivot M222 hN_M222)) M222 tach222
lean/DLNFibre/DLN/RLCT/Validate/RouteMBData222.lean:724:/-! ## The residual det leg: `DB`/`hasDB`/`hdet` (the `BData` interface fields)
lean/DLNFibre/DLN/RLCT/Validate/RouteMBData222.lean:805:The radial/pivot slot is `structPivot M222 hN_M222 = ⟨0,_⟩` (the radial scalar coordinate axis,
lean/DLNFibre/DLN/RLCT/Validate/RouteMBData222.lean:806:`RouteMFlatStructV.structPivot`). The five reader slots are `chartIdxEquiv.symm`-tag images. That
lean/DLNFibre/DLN/RLCT/Validate/RouteMBData222.lean:817:/-- **The chart non-degeneracy hypothesis**: the radial axis `structPivot = ⟨0,_⟩` is distinct from
lean/DLNFibre/DLN/RLCT/Validate/RouteMBData222.lean:820:def PivotNotReader : Prop := structPivot M222 hN_M222 ∉ readerSet
lean/DLNFibre/DLN/RLCT/Validate/RouteMBData222.lean:826:    structPivot M222 hN_M222, lf0, lf1]
lean/DLNFibre/DLN/RLCT/Validate/RouteMBData222.lean:843:  have hpK : structPivot M222 hN_M222 ≠ readerSlotK := fun h => hpiv (by
lean/DLNFibre/DLN/RLCT/Validate/RouteMBData222.lean:845:  have hpX : structPivot M222 hN_M222 ≠ readerSlotX := fun h => hpiv (by
lean/DLNFibre/DLN/RLCT/Validate/RouteMBData222.lean:847:  have hpN : structPivot M222 hN_M222 ≠ readerSlotN := fun h => hpiv (by
lean/DLNFibre/DLN/RLCT/Validate/RouteMBData222.lean:850:  have hpW0 : structPivot M222 hN_M222 ≠ readerSlotW0 := fun h => hpiv (by
lean/DLNFibre/DLN/RLCT/Validate/RouteMBData222.lean:854:  have hpW1 : structPivot M222 hN_M222 ≠ readerSlotW1 := fun h => hpiv (by
lean/DLNFibre/DLN/RLCT/Validate/RouteMBData222.lean:907:    y readerSlotK * y readerSlotX * y readerSlotN + y (structPivot M222 hN_M222),
lean/DLNFibre/DLN/RLCT/Validate/RouteMBData222.lean:919:            aRead y * bRead y, aRead y * bRead y * nRead y + y (structPivot M222 hN_M222)]
lean/DLNFibre/DLN/RLCT/Validate/RouteMBData222.lean:966:          + bprj (structPivot M222 hN_M222),
lean/DLNFibre/DLN/RLCT/Validate/RouteMBData222.lean:994:  · -- output 6: `y readerSlotK * y readerSlotX * y readerSlotN + y (structPivot)`
lean/DLNFibre/DLN/RLCT/Validate/RouteMBData222.lean:995:    refine HasFDerivAt.add ?_ (hap (structPivot M222 hN_M222))
lean/DLNFibre/DLN/RLCT/Validate/RouteMBData222.lean:1030:  ![readerSlotK, readerSlotX, readerSlotN, structPivot M222 hN_M222,
lean/DLNFibre/DLN/RLCT/Validate/RouteMBData222.lean:1046:  have hpK : structPivot M222 hN_M222 ≠ readerSlotK := fun h => hpiv (by
lean/DLNFibre/DLN/RLCT/Validate/RouteMBData222.lean:1048:  have hpX : structPivot M222 hN_M222 ≠ readerSlotX := fun h => hpiv (by
lean/DLNFibre/DLN/RLCT/Validate/RouteMBData222.lean:1050:  have hpN : structPivot M222 hN_M222 ≠ readerSlotN := fun h => hpiv (by
lean/DLNFibre/DLN/RLCT/Validate/RouteMBData222.lean:1053:  have hpW0 : structPivot M222 hN_M222 ≠ readerSlotW0 := fun h => hpiv (by
lean/DLNFibre/DLN/RLCT/Validate/RouteMBData222.lean:1057:  have hpW1 : structPivot M222 hN_M222 ≠ readerSlotW1 := fun h => hpiv (by
lean/DLNFibre/DLN/RLCT/Validate/RouteMBData222.lean:1061:  have hplf0 : structPivot M222 hN_M222 ≠ lf0 := fun h => lf0_ne_pivot h.symm
lean/DLNFibre/DLN/RLCT/Validate/RouteMBData222.lean:1062:  have hplf1 : structPivot M222 hN_M222 ≠ lf1 := fun h => lf1_ne_pivot h.symm
lean/DLNFibre/DLN/RLCT/Validate/RouteMBData222.lean:1162:    (Pi.single (slotListC j) (1 : ℝ) : Fin (routeMAmbient M222) → ℝ) (structPivot M222 hN_M222)
lean/DLNFibre/DLN/RLCT/Validate/RouteMBData222.lean:1239:/-! ## The `BData M222` instance + the concrete (2,2,2) interior-det headline -/
lean/DLNFibre/DLN/RLCT/Validate/RouteMBData222.lean:1244:  fun s => if s = 0 then |aRead (pivotBlowupOn active222 (structPivot M222 hN_M222) u)| ^ 2 else 1
lean/DLNFibre/DLN/RLCT/Validate/RouteMBData222.lean:1248:      = |aRead (pivotBlowupOn active222 (structPivot M222 hN_M222) u)| ^ 2 := by
lean/DLNFibre/DLN/RLCT/Validate/RouteMBData222.lean:1251:/-- **The faithful `BData M222`** for the concrete (2,2,2) node, given the chart non-degeneracy
lean/DLNFibre/DLN/RLCT/Validate/RouteMBData222.lean:1255:    BData M222 tach222 structAdm_tach222 hN_M222 1 hp1_222 hp2_222 rfin222 u where
lean/DLNFibre/DLN/RLCT/Validate/RouteMBData222.lean:1257:  hp_mem := structPivot_mem_active222
lean/DLNFibre/DLN/RLCT/Validate/RouteMBData222.lean:1260:  DB := DB (pivotBlowupOn active222 (structPivot M222 hN_M222) u)
lean/DLNFibre/DLN/RLCT/Validate/RouteMBData222.lean:1261:  hasDB := Bchart_hasFDerivAt (pivotBlowupOn active222 (structPivot M222 hN_M222) u)
lean/DLNFibre/DLN/RLCT/Validate/RouteMBData222.lean:1265:    rw [DB_abs_det hpiv (pivotBlowupOn active222 (structPivot M222 hN_M222) u), engine222_prod]
lean/DLNFibre/DLN/RLCT/Validate/RouteMBData222.lean:1267:/-- **The unconditional-modulo-`PivotNotReader` interior-det headline for `phiFlatLiveR1 M222`**:
lean/DLNFibre/DLN/RLCT/Validate/RouteMBData222.lean:1268:`|det D(phiFlatLiveR1 M222 …)| = |u_p|^{minAdm−1} · |aRead (pbo u)|²`. Reads off
lean/DLNFibre/DLN/RLCT/Validate/RouteMBData222.lean:1269:`interiorDet_headline_of_BData` applied to `bData222`. -/
lean/DLNFibre/DLN/RLCT/Validate/RouteMBData222.lean:1271:    |LinearMap.det (fderiv ℝ (phiFlatLiveR1 M222 tach222 structAdm_tach222 hN_M222 1 hp1_222 hp2_222
lean/DLNFibre/DLN/RLCT/Validate/RouteMBData222.lean:1273:      = |u (structPivot M222 hN_M222)| ^ (minAdm M222 - 1)
lean/DLNFibre/DLN/RLCT/Validate/RouteMBData222.lean:1275:  interiorDet_headline_of_BData M222 tach222 structAdm_tach222 hN_M222 1 hp1_222 hp2_222 rfin222 u
lean/DLNFibre/DLN/RLCT/Validate/RouteMKLens.lean:23:sub-tide 1) — and the rate reads the radial scalar from the ORIGINAL `x (structPivot)` (the decoder argument
lean/DLNFibre/DLN/RLCT/Validate/RouteMCLEConj.lean:11:`composeFold fs = phiFlatStructV` becomes a `Params`-LEVEL equality (a clean `funext s`), not an
lean/DLNFibre/DLN/RLCT/Validate/RouteMInteriorContract.lean:9:fields (the achiever chart `achieverPhi`, the rate `routeMCore = (x p)²·U`, the det-FREE
lean/DLNFibre/DLN/RLCT/Validate/RouteMInteriorContract.lean:44:(`routeMCore_achieverPhi`, `achiever_leaf_integrand`, `achieverUbound_interior`). The pivot is the
lean/DLNFibre/DLN/RLCT/Validate/RouteMInteriorContract.lean:45:radial `structPivot M hN = ⟨0,_⟩`. -/
lean/DLNFibre/DLN/RLCT/Validate/RouteMInteriorContract.lean:49:    (hleafH_pivot : leafH (structPivot M hN) = minAdm M - 1)
lean/DLNFibre/DLN/RLCT/Validate/RouteMInteriorContract.lean:53:      ∫⁻ x in achieverPhi M hL hN '' (V \ {x | x (structPivot M hN) = 0}), g x
lean/DLNFibre/DLN/RLCT/Validate/RouteMInteriorContract.lean:54:        = ∫⁻ u in V \ {x | x (structPivot M hN) = 0},
lean/DLNFibre/DLN/RLCT/Validate/RouteMInteriorContract.lean:55:            ENNReal.ofReal (∏ j, |u j| ^ (leafH j)) * g (achieverPhi M hL hN u))
lean/DLNFibre/DLN/RLCT/Validate/RouteMInteriorContract.lean:57:        ∃ δ > 0, achieverPhi M hL hN ''
lean/DLNFibre/DLN/RLCT/Validate/RouteMInteriorContract.lean:66:      phi := achieverPhi M hL hN
lean/DLNFibre/DLN/RLCT/Validate/RouteMInteriorContract.lean:67:      p := structPivot M hN
lean/DLNFibre/DLN/RLCT/Validate/RouteMAchieverWitnessInterior.lean:537:  set u := wInt M ha p (structPivot M hN) with hudef
lean/DLNFibre/DLN/RLCT/Validate/RouteMChainAssembleDiff.lean:7:# `RouteMChainAssembleDiff` — b-FrameM-2 DONE: `DifferentiableAt phiFlatLiveR1`
lean/DLNFibre/DLN/RLCT/Validate/RouteMChainAssembleDiff.lean:12:`RouteMChartDiff.phiFlatLiveR1_differentiableAt_of_Agen`, giving
lean/DLNFibre/DLN/RLCT/Validate/RouteMChainAssembleDiff.lean:14:  `phiFlatLiveR1_differentiableAt : DifferentiableAt ℝ (phiFlatLiveR1 …) x₀`
lean/DLNFibre/DLN/RLCT/Validate/RouteMChainAssembleDiff.lean:28:* `phiFlatLiveR1_differentiableAt` — **b-FrameM-2 complete**: the chart is differentiable.
lean/DLNFibre/DLN/RLCT/Validate/RouteMChainAssembleDiff.lean:152:    DifferentiableAt ℝ (fun x => Cgen (x (structPivot M hN)) M t
lean/DLNFibre/DLN/RLCT/Validate/RouteMChainAssembleDiff.lean:155:  · rw [show (fun x => Cgen (x (structPivot M hN)) M t
lean/DLNFibre/DLN/RLCT/Validate/RouteMChainAssembleDiff.lean:160:            + (x (structPivot M hN)) • (genBlkFlatLiveR1 M t ha p hp1 hp2 (rfin x) x).Rmat k from by
lean/DLNFibre/DLN/RLCT/Validate/RouteMChainAssembleDiff.lean:165:  · rw [show (fun x => Cgen (x (structPivot M hN)) M t
lean/DLNFibre/DLN/RLCT/Validate/RouteMChainAssembleDiff.lean:167:        = fun x => (x (structPivot M hN))
lean/DLNFibre/DLN/RLCT/Validate/RouteMChainAssembleDiff.lean:176:    DifferentiableAt ℝ (fun x => Agen (x (structPivot M hN)) M t
lean/DLNFibre/DLN/RLCT/Validate/RouteMChainAssembleDiff.lean:179:  · rw [show (fun x => Agen (x (structPivot M hN)) M t
lean/DLNFibre/DLN/RLCT/Validate/RouteMChainAssembleDiff.lean:184:            (Cgen (x (structPivot M hN)) M t (genBlkFlatLiveR1 M t ha p hp1 hp2 (rfin x) x)
lean/DLNFibre/DLN/RLCT/Validate/RouteMChainAssembleDiff.lean:189:  · rw [show (fun x => Agen (x (structPivot M hN)) M t
lean/DLNFibre/DLN/RLCT/Validate/RouteMChainAssembleDiff.lean:194:/-! ## b-FrameM-2 complete: `DifferentiableAt phiFlatLiveR1` -/
lean/DLNFibre/DLN/RLCT/Validate/RouteMChainAssembleDiff.lean:196:/-- **b-FrameM-2 DONE.** The R1 active-center chart `phiFlatLiveR1` is `DifferentiableAt` (given the live
lean/DLNFibre/DLN/RLCT/Validate/RouteMChainAssembleDiff.lean:198:`phiFlatLiveR1_differentiableAt_of_Agen`. This is the existence the b-FrameM-3 keystone
lean/DLNFibre/DLN/RLCT/Validate/RouteMChainAssembleDiff.lean:200:theorem phiFlatLiveR1_differentiableAt (hN : 0 < routeMAmbient M) (u : Fin (routeMAmbient M) → ℝ)
lean/DLNFibre/DLN/RLCT/Validate/RouteMChainAssembleDiff.lean:202:    DifferentiableAt ℝ (phiFlatLiveR1 M t ha hN p hp1 hp2 rfin) u :=
lean/DLNFibre/DLN/RLCT/Validate/RouteMChainAssembleDiff.lean:203:  phiFlatLiveR1_differentiableAt_of_Agen M t ha hN p hp1 hp2 rfin u
lean/DLNFibre/DLN/RLCT/Validate/RouteMDecoderDiff.lean:12:`RouteMChartDiff.phiFlatLiveR1_differentiableAt_of_Agen`).

exec
/bin/bash -lc 'rg -n "def achieverPhi|achieverPhi|routeMCore_achieverPhi|achiever_leaf_integrand|NodeAchieverChart" lean/DLNFibre/DLN/RLCT/Validate -S' in /home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/agent-a9bb11c22680d93d4
 succeeded in 0ms:
lean/DLNFibre/DLN/RLCT/Validate/RouteM3333.lean:1:import DLNFibre.DLN.RLCT.Validate.NodeAchieverChart
lean/DLNFibre/DLN/RLCT/Validate/RouteM3333.lean:13:`(3,3,3,3)` witness). It is the decisive validation that the `NodeAchieverChart` bundle handles the
lean/DLNFibre/DLN/RLCT/Validate/RouteMInteriorContract.lean:8:`RouteMAchieverDispatch`). It assembles the interior `NodeAchieverChart M` from the BANKED rate-side
lean/DLNFibre/DLN/RLCT/Validate/RouteMInteriorContract.lean:9:fields (the achiever chart `achieverPhi`, the rate `routeMCore = (x p)²·U`, the det-FREE
lean/DLNFibre/DLN/RLCT/Validate/RouteMInteriorContract.lean:44:(`routeMCore_achieverPhi`, `achiever_leaf_integrand`, `achieverUbound_interior`). The pivot is the
lean/DLNFibre/DLN/RLCT/Validate/RouteMInteriorContract.lean:53:      ∫⁻ x in achieverPhi M hL hN '' (V \ {x | x (structPivot M hN) = 0}), g x
lean/DLNFibre/DLN/RLCT/Validate/RouteMInteriorContract.lean:55:            ENNReal.ofReal (∏ j, |u j| ^ (leafH j)) * g (achieverPhi M hL hN u))
lean/DLNFibre/DLN/RLCT/Validate/RouteMInteriorContract.lean:57:        ∃ δ > 0, achieverPhi M hL hN ''
lean/DLNFibre/DLN/RLCT/Validate/RouteMInteriorContract.lean:63:  -- assemble the interior `NodeAchieverChart M` from the banked rate-side + the open fields
lean/DLNFibre/DLN/RLCT/Validate/RouteMInteriorContract.lean:64:  let W : NodeAchieverChart M :=
lean/DLNFibre/DLN/RLCT/Validate/RouteMInteriorContract.lean:66:      phi := achieverPhi M hL hN
lean/DLNFibre/DLN/RLCT/Validate/RouteMInteriorContract.lean:74:        Filter.Eventually.of_forall (fun x => achiever_leaf_integrand M hL hN leafH c x)
lean/DLNFibre/DLN/RLCT/Validate/RouteMAchieverVvalPoly.lean:9:The genuinely-remaining rate-side `NodeAchieverChart` field: `∀ᵐ x, 0 < achieverUfun x` (the `Ubound`
lean/DLNFibre/DLN/RLCT/Validate/RouteMAchieverVvalPoly.lean:423:/-- **The full `NodeAchieverChart.Ubound` field**, GIVEN the witness `∃ w, achieverUfun w ≠ 0`: the
lean/DLNFibre/DLN/RLCT/Validate/RouteMFlatStructV.lean:20:This is the `NodeAchieverChart.leaf_integrand` rate factor `routeMCore (phi u) = (u p)² · Ufun(u)` for
lean/DLNFibre/DLN/RLCT/Validate/RouteMFlatStructV.lean:111:identity-boundary `hC0_struct_gen`. This is the `NodeAchieverChart.leaf_integrand` rate factor for
lean/DLNFibre/DLN/RLCT/Validate/RouteM4422.lean:1:import DLNFibre.DLN.RLCT.Validate.NodeAchieverChart
lean/DLNFibre/DLN/RLCT/Validate/RouteM4422.lean:13:`threads/26-r1-genM-chart/` order-(a) witness). It constructs a `NodeAchieverChart M4422` and
lean/DLNFibre/DLN/RLCT/Validate/RouteM4422.lean:708:/-! ## The `NodeAchieverChart M4422` instance + the atom discharge -/
lean/DLNFibre/DLN/RLCT/Validate/RouteM4422.lean:721:noncomputable def nodeChart4422 : NodeAchieverChart M4422 where
lean/DLNFibre/DLN/RLCT/Validate/RouteMAchieverWitnessInterior.lean:6:The genuinely-remaining input for the rate-side `NodeAchieverChart.Ubound` on the INTERIOR class
lean/DLNFibre/DLN/RLCT/Validate/RouteMGenLeafIntegrand.lean:2:import DLNFibre.DLN.RLCT.Validate.NodeAchieverChart
lean/DLNFibre/DLN/RLCT/Validate/RouteMGenLeafIntegrand.lean:5:# `RouteMGenLeafIntegrand` — the det-INDEPENDENT `NodeAchieverChart` fields ∀M (the reusable algebra)
lean/DLNFibre/DLN/RLCT/Validate/RouteMGenLeafIntegrand.lean:7:The `NodeAchieverChart M` bundle's `leaf_integrand` field is purely ALGEBRAIC in the rate identity
lean/DLNFibre/DLN/RLCT/Validate/RouteMGenLeafIntegrand.lean:16:These are two of the `NodeAchieverChart M` fields, fillable ∀M from the banked rate engine
lean/DLNFibre/DLN/RLCT/Validate/RouteMGenLeafIntegrand.lean:40:ANY exponent vector `leafH`. This is the `NodeAchieverChart.leaf_integrand` field, reduced to the rate
lean/DLNFibre/DLN/RLCT/Validate/RouteMLayerCoverGE.lean:49:  sharp monomial divergence; `NodeAchieverChart M` (below) packages exactly this bundle.
lean/DLNFibre/DLN/RLCT/Validate/RouteMLayerCoverGE.lean:52:- The atom is reduced **M-agnostically, sorry-free**, to "construct one `NodeAchieverChart M`"
lean/DLNFibre/DLN/RLCT/Validate/RouteMLayerCoverGE.lean:53:  (`NodeAchieverChart.lean`: `routeMCore_box_diverges_of_nodeChart`). Only the per-`M` chart
lean/DLNFibre/DLN/RLCT/Validate/RouteMLayerCoverGE.lean:127:flat→chart change-of-variables packaged by `NodeAchieverChart M` (see the file header). Two
lean/DLNFibre/DLN/RLCT/Validate/RouteMBoundaryCleanU.lean:7:The `NodeAchieverChart.Ubound` positivity for the clean radial chart: `U(u) := dlnLoss M 0
lean/DLNFibre/DLN/RLCT/Validate/RouteM221.lean:1:import DLNFibre.DLN.RLCT.Validate.NodeAchieverChart
lean/DLNFibre/DLN/RLCT/Validate/RouteM221.lean:13:`NodeAchieverChart M221` and feeding it through the M-agnostic assembly
lean/DLNFibre/DLN/RLCT/Validate/RouteM221.lean:554:/-! ## The `NodeAchieverChart M221` instance + the atom discharge -/
lean/DLNFibre/DLN/RLCT/Validate/RouteM221.lean:561:noncomputable def nodeChart221 : NodeAchieverChart M221 where
lean/DLNFibre/DLN/RLCT/Validate/RouteMAchieverRateFields.lean:6:# `RouteMAchieverRateFields` — the ∀M achiever-path rate-side `NodeAchieverChart` fields (decoder-agnostic)
lean/DLNFibre/DLN/RLCT/Validate/RouteMAchieverRateFields.lean:8:The rate-side fields of the `NodeAchieverChart M` bundle, on the ACHIEVER path `tach M`
lean/DLNFibre/DLN/RLCT/Validate/RouteMAchieverRateFields.lean:17:* `achieverPhi` / `achieverUfun` — the chart + unit on the achiever path (`phiFlatStructV`/`UvalStructV`
lean/DLNFibre/DLN/RLCT/Validate/RouteMAchieverRateFields.lean:19:* `routeMCore_achieverPhi` — the RATE `routeMCore M (achieverPhi x) = (x p)²·achieverUfun x` (∀M, one line
lean/DLNFibre/DLN/RLCT/Validate/RouteMAchieverRateFields.lean:22:* `achiever_leaf_integrand` — the `NodeAchieverChart.leaf_integrand` field ∀M, for ANY exponent vector
lean/DLNFibre/DLN/RLCT/Validate/RouteMAchieverRateFields.lean:47:noncomputable def achieverPhi (M : Fin (L + 1) → ℕ) (hL : 0 < L) (hN : 0 < routeMAmbient M)
lean/DLNFibre/DLN/RLCT/Validate/RouteMAchieverRateFields.lean:56:/-- **The RATE identity ∀M** `routeMCore M (achieverPhi x) = (x p)²·achieverUfun x` — decoder-agnostic
lean/DLNFibre/DLN/RLCT/Validate/RouteMAchieverRateFields.lean:57:(banked `routeMCore_phiFlatStructV`), the `NodeAchieverChart.leaf_integrand` rate factor on the achiever
lean/DLNFibre/DLN/RLCT/Validate/RouteMAchieverRateFields.lean:59:theorem routeMCore_achieverPhi (M : Fin (L + 1) → ℕ) (hL : 0 < L) (hN : 0 < routeMAmbient M)
lean/DLNFibre/DLN/RLCT/Validate/RouteMAchieverRateFields.lean:61:    routeMCore M (achieverPhi M hL hN x)
lean/DLNFibre/DLN/RLCT/Validate/RouteMAchieverRateFields.lean:73:/-- **The `NodeAchieverChart.leaf_integrand` field ∀M** for the achiever path: for ANY exponent vector
lean/DLNFibre/DLN/RLCT/Validate/RouteMAchieverRateFields.lean:75:`(∏_j |x_j|^{leafH j})·|routeMCore M (achieverPhi x)|^{−c}
lean/DLNFibre/DLN/RLCT/Validate/RouteMAchieverRateFields.lean:77:`routeMCore (achieverPhi x) = (x p)²·achieverUfun x` + `achieverUfun ≥ 0` (NO Jacobian determinant). -/
lean/DLNFibre/DLN/RLCT/Validate/RouteMAchieverRateFields.lean:78:theorem achiever_leaf_integrand (M : Fin (L + 1) → ℕ) (hL : 0 < L) (hN : 0 < routeMAmbient M)
lean/DLNFibre/DLN/RLCT/Validate/RouteMAchieverRateFields.lean:80:    (∏ j, |x j| ^ (leafH j)) * |routeMCore M (achieverPhi M hL hN x)| ^ (-c)
lean/DLNFibre/DLN/RLCT/Validate/RouteMAchieverRateFields.lean:84:    (fun y => routeMCore M (achieverPhi M hL hN y)) (achieverUfun M hL hN)
lean/DLNFibre/DLN/RLCT/Validate/RouteMAchieverRateFields.lean:85:    (fun y => routeMCore_achieverPhi M hL hN y) (fun y => achieverUfun_nonneg M hL hN y) c x
lean/DLNFibre/DLN/RLCT/Validate/RouteMAchieverRateFields.lean:94:/-- **CONTRACT (the wall): a.e.-positivity of the achiever unit.** What `NodeAchieverChart.Ubound`'s
lean/DLNFibre/DLN/RLCT/Validate/RouteMAchieverRateFields.lean:105:/-- **CONTRACT (the wall): measurability of the achiever unit.** What `NodeAchieverChart.Umeas` needs.
lean/DLNFibre/DLN/RLCT/Validate/RouteM121Smeared.lean:1:import DLNFibre.DLN.RLCT.Validate.NodeAchieverChart
lean/DLNFibre/DLN/RLCT/Validate/RouteM121Smeared.lean:16:`leaf_integrand`** core (option (i), landed in `NodeAchieverChart`).
lean/DLNFibre/DLN/RLCT/Validate/RouteM121Smeared.lean:88:`Fin (flatDim M121) → ℝ = Fin 4 → ℝ`, matching the `NodeAchieverChart` field type). -/
lean/DLNFibre/DLN/RLCT/Validate/RouteM121Smeared.lean:98:This off-pole-only rate is the crux of the handback: `NodeAchieverChart.leaf_integrand` demands the
lean/DLNFibre/DLN/RLCT/Validate/RouteMCardBridge.lean:3:import DLNFibre.DLN.RLCT.Validate.NodeAchieverChart
lean/DLNFibre/DLN/RLCT/Validate/RouteMCardBridge.lean:12:minAdm − 1` field (`NodeAchieverChart.leafH_pivot`) once `leafH` is the factored-det exponent vector.
lean/DLNFibre/DLN/RLCT/Validate/RouteMCardBridge.lean:24:  minAdm − 1`. The `NodeAchieverChart.leafH_pivot` discharge (the radial axis carries `minAdm − 1`;
lean/DLNFibre/DLN/RLCT/Validate/RouteMCardBridge.lean:115:`leafH (structPivot) = minAdm M − 1` — the `NodeAchieverChart.leafH_pivot` field. (The spectator
lean/DLNFibre/DLN/RLCT/Validate/RouteMFlatLDU.lean:7:(the `NodeAchieverChart.cov`/`monomialIntegrand` divergence). The banked FREE-K chart
lean/DLNFibre/DLN/RLCT/Validate/RouteMFlatLDU.lean:64:ORIGINAL `x`). The `NodeAchieverChart.leaf_integrand` rate factor for the LDU interior chart. -/
lean/DLNFibre/DLN/RLCT/Validate/RouteMPhiFlatDet.lean:8:chart Jacobian — the `cov` field of `NodeAchieverChart`). The flat achiever chart equals a `composeFold`
lean/DLNFibre/DLN/RLCT/Validate/RouteMBoundaryCleanChart.lean:19:This file builds the deepest-coordinatization + the factorization core. The full `NodeAchieverChart`
lean/DLNFibre/DLN/RLCT/Validate/RouteMBoundaryCleanChart.lean:109:The full `NodeAchieverChart M` for clean-boundary `M` needs, on top of `deepestCoords`:
lean/DLNFibre/DLN/RLCT/Validate/RouteMInteriorDet.lean:8:The det-side assembly for the interior `NodeAchieverChart`'s `cov` field: `|det Dφ(u)| =
lean/DLNFibre/DLN/RLCT/Validate/RouteMInteriorDet.lean:21:* `interiorLeafH_pivot` — the `leafH (structPivot) = minAdm − 1` binding (the `NodeAchieverChart.leafH_pivot`
lean/DLNFibre/DLN/RLCT/Validate/RouteMInteriorDet.lean:49:(`active.card = minAdm M`). Discharges `NodeAchieverChart.leafH_pivot` / the contract's `hleafH_pivot`. -/
lean/DLNFibre/DLN/RLCT/Validate/RouteM3333Atom.lean:31:`nodeChart3333 : NodeAchieverChart M3333` bundles `phi3333` (binding axis `0`), the genuine c-o-v
lean/DLNFibre/DLN/RLCT/Validate/RouteM3333Atom.lean:734:/-! ## The `NodeAchieverChart M3333` instance + the achiever box-divergence atom -/
lean/DLNFibre/DLN/RLCT/Validate/RouteM3333Atom.lean:741:noncomputable def nodeChart3333 : NodeAchieverChart M3333 where
lean/DLNFibre/DLN/RLCT/Validate/NodeAchieverChart.lean:6:# `NodeAchieverChart` — the reusable general-`M` achiever chart bundle + the M-agnostic assembly
lean/DLNFibre/DLN/RLCT/Validate/NodeAchieverChart.lean:13:* **`NodeAchieverChart M`** — the `L2AchieverChart` fields generalized to `M` (no hard-coded `Fin 21`
lean/DLNFibre/DLN/RLCT/Validate/NodeAchieverChart.lean:20:  atom's conclusion for `M`, proven FROM a `NodeAchieverChart M`, by the `(3,3,4)` assembly chain
lean/DLNFibre/DLN/RLCT/Validate/NodeAchieverChart.lean:56:/-! ## The `NodeAchieverChart M` bundle (the `L2AchieverChart` fields, generalized to `M`)
lean/DLNFibre/DLN/RLCT/Validate/NodeAchieverChart.lean:64:structure NodeAchieverChart (M : Fin (L + 1) → ℕ) where
lean/DLNFibre/DLN/RLCT/Validate/NodeAchieverChart.lean:114:theorem nodeChart_thresholdLe (M : Fin (L + 1) → ℕ) (W : NodeAchieverChart M) :
lean/DLNFibre/DLN/RLCT/Validate/NodeAchieverChart.lean:127:theorem nodeLeaf_box_div (M : Fin (L + 1) → ℕ) (W : NodeAchieverChart M) (c' : ℝ) (hc'0 : 0 < c')
lean/DLNFibre/DLN/RLCT/Validate/NodeAchieverChart.lean:170:The `(3,3,4)` `routeM334_box_diverges_of_chart`, generalized to `M`: given a `NodeAchieverChart M`,
lean/DLNFibre/DLN/RLCT/Validate/NodeAchieverChart.lean:175:theorem routeMCore_box_diverges_of_nodeChart (M : Fin (L + 1) → ℕ) (W : NodeAchieverChart M)
lean/DLNFibre/DLN/RLCT/Validate/RouteMBoundaryClass.lean:35:(`certificate-genM-smeared`). Both fit the EXISTING single-axis `NodeAchieverChart` (see the
lean/DLNFibre/DLN/RLCT/Validate/RouteMBoundaryClass.lean:58:(`pivotBlowupOn` on all `m1·c` deepest coords; det `|u_p|^{minAdm−1}`); fits `NodeAchieverChart`
lean/DLNFibre/DLN/RLCT/Validate/RouteMBoundaryClass.lean:66:`NodeAchieverChart`, with the rational `cov` the one new piece (gating: `statement-cards.md`). -/
lean/DLNFibre/DLN/RLCT/Validate/RouteM222Det.lean:3:import DLNFibre.DLN.RLCT.Validate.NodeAchieverChart
lean/DLNFibre/DLN/RLCT/Validate/RouteM222Det.lean:437:The chart for the `NodeAchieverChart` bundle is `phi222 x := paramsEquivFlat M222 (chartParams222 x)` —
lean/DLNFibre/DLN/RLCT/Validate/RouteM222Det.lean:1083:/-! ## The leaf monomial + the `NodeAchieverChart M222` bundle + the atom discharge
lean/DLNFibre/DLN/RLCT/Validate/RouteM222Det.lean:1113:noncomputable def nodeChart222 : NodeAchieverChart M222 where
lean/DLNFibre/DLN/RLCT/Validate/RouteMBoundaryCleanChartFull.lean:5:# `RouteMBoundaryCleanChartFull` — the ∀M BOUNDARY-CLEAN `NodeAchieverChart` + the atom discharge
lean/DLNFibre/DLN/RLCT/Validate/RouteMBoundaryCleanChartFull.lean:183:/-! ## The `NodeAchieverChart M` instance + the atom discharge -/
lean/DLNFibre/DLN/RLCT/Validate/RouteMBoundaryCleanChartFull.lean:197:    NodeAchieverChart M where
lean/DLNFibre/DLN/RLCT/Validate/RouteMBoundaryCleanChartFull.lean:214:`NodeAchieverChart` fed through the M-agnostic assembly `routeMCore_box_diverges_of_nodeChart`. This is

codex
The route that avoids a semantic comparison is to turn “the radial coordinate” into data at the chart interface. Then the 222 proof can choose all three non-reader active slots from `univ \ readerSet`, and the determinant proof uses membership lemmas instead of a fragile theorem about slot 0.
exec
/bin/bash -lc "sed -n '1,150p' lean/DLNFibre/DLN/RLCT/Validate/RouteMRadialComp.lean" in /home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/agent-a9bb11c22680d93d4
 succeeded in 0ms:
import DLNFibre.DLN.RLCT.Validate.RouteMRadialFactor
import DLNFibre.DLN.RLCT.Validate.RouteMCardBridge
import Mathlib.Analysis.Calculus.FDeriv.Comp

/-!
# `RouteMRadialComp` — route-#1 wiring: `det (D(B ∘ radial)) = |u_p|^{minAdm−1}·|det DB|`

The least-cast faithful assembly (genm-detradj 2nd-eye verdict, `codex/G-faithfulness-answer.md` +
`pnp-radial-adjudication`): the chart factors as `φ = B ∘ pivotBlowupOn active p` (MAP-level),
so by the chain rule `Dφ = DB ∘L pivotBlowupOnDeriv` and `det Dφ = det DB · det Prad` by
`LinearMap.det_comp`, with `det Prad = u_p^{minAdm−1}` (banked `pivotBlowupOnDeriv_det`). NO global
coordinate equiv (`stairConj`'s `e.symm ∘ stairMap ∘ e` is strictly heavier), NO scaled-columns `G`,
no matrix inverse / `u_p = 0` split (`det_comp` needs no invertibility).

This module banks the route-#1 WIRING (abstract in `B`/`DB`/`active`): given the map factorization,
the radial fderiv, and the u-free boundary det `|det DB| = ∏_s engine s`, the chart's Jacobian
abs-det IS the headline monomial. The three remaining obligations are then PRECISE:
(1) the MAP identity `φ = B ∘ pivotBlowupOn active p` (per-block, opaque widths — ∀M obligation);
(2) `HasFDerivAt B DB` (B polynomial, no global e);
(3) `|det DB| = ∏_s engine s` (B carries no u, so each boundary block IS the engine value —
    `schurFrame_abs_det` × `lduCoreDeriv_abs_det`).

* `radialComp_abs_det` — the wiring: `|det (fderiv ℝ (B ∘ pivotBlowupOn active p) u)| =
  |u_p|^{minAdm−1} · |det DB|`, from the map factorization + `HasFDerivAt B DB` + the radial card.

Axiom-clean `[propext, Classical.choice, Quot.sound]` (calculus + determinant; no analysis beyond
the chain rule + the banked radial fderiv).
-/

open scoped BigOperators

noncomputable section

namespace DLNFibre.DLN.RLCT

variable {L : ℕ}

/-- **The route-#1 radial-composition wiring.** Let `φ = B ∘ pivotBlowupOn active p` (`hφ`), with
`B` having fderiv `DB` at `pivotBlowupOn active p u` (`hB`), the pivot `p ∈ active`
(`hp`), and the radial active set of size `minAdm` (`hcard`). Then the chart's Jacobian abs-det is
`|u_p|^{minAdm−1} · |det DB|`. Chain rule (`HasFDerivAt.comp` + the banked radial `HasFDerivAt`) +
`LinearMap.det_comp` + the banked `radial_abs_det_minAdm`. -/
theorem radialComp_abs_det (M : Fin (L + 1) → ℕ) (hN : 0 < routeMAmbient M)
    (active : Finset (Fin (routeMAmbient M))) (hp : structPivot M hN ∈ active)
    (hcard : active.card = minAdm M)
    (B : (Fin (routeMAmbient M) → ℝ) → (Fin (routeMAmbient M) → ℝ))
    (φ : (Fin (routeMAmbient M) → ℝ) → (Fin (routeMAmbient M) → ℝ))
    (u : Fin (routeMAmbient M) → ℝ)
    (DB : (Fin (routeMAmbient M) → ℝ) →L[ℝ] (Fin (routeMAmbient M) → ℝ))
    (hφ : φ = B ∘ pivotBlowupOn active (structPivot M hN))
    (hB : HasFDerivAt B DB (pivotBlowupOn active (structPivot M hN) u)) :
    |LinearMap.det (fderiv ℝ φ u).toLinearMap|
      = |u (structPivot M hN)| ^ (minAdm M - 1) * |LinearMap.det DB.toLinearMap| := by
  -- the radial factor has the banked `HasFDerivAt` at `u`
  have hrad : HasFDerivAt (pivotBlowupOn active (structPivot M hN))
      (pivotBlowupOnDeriv active (structPivot M hN) u) u :=
    hasFDerivWithinAt_univ.mp
      (pivotBlowupOn_hasFDerivWithinAt active (structPivot M hN) Set.univ u)
  -- the composite `φ = B ∘ radial` has fderiv `DB ∘L Prad`
  have hcomp : HasFDerivAt φ (DB.comp (pivotBlowupOnDeriv active (structPivot M hN) u)) u := by
    rw [hφ]; exact hB.comp u hrad
  rw [hcomp.fderiv]
  -- `det (DB ∘L Prad) = det DB · det Prad`; `|det Prad| = |u_p|^{minAdm−1}`
  rw [ContinuousLinearMap.coe_comp, LinearMap.det_comp, abs_mul, mul_comm]
  congr 1
  exact radial_abs_det_minAdm M hN active hp hcard u

/-! ## Non-vacuity: the wiring fires on a concrete factorization

On the identity boundary `B = id`, `φ = pivotBlowupOn active p`, the wiring gives `|det Dφ| =
|u_p|^{minAdm−1} · 1` — the radial-only chart. Confirms the route-#1 conditional is satisfiable. -/

/-- **Non-vacuity (`B = id`).** With `B = id` (`DB = id`, `|det| = 1`), the chart is the radial
blow-up itself and the wiring gives `|det Dφ| = |u_p|^{minAdm−1} · 1`. -/
example (M : Fin (L + 1) → ℕ) (hN : 0 < routeMAmbient M)
    (active : Finset (Fin (routeMAmbient M))) (hp : structPivot M hN ∈ active)
    (hcard : active.card = minAdm M) (u : Fin (routeMAmbient M) → ℝ) :
    |LinearMap.det (fderiv ℝ (pivotBlowupOn active (structPivot M hN)) u).toLinearMap|
      = |u (structPivot M hN)| ^ (minAdm M - 1)
        * |LinearMap.det (ContinuousLinearMap.id ℝ (Fin (routeMAmbient M) → ℝ)).toLinearMap| := by
  refine radialComp_abs_det M hN active hp hcard id _ u (ContinuousLinearMap.id ℝ _) ?_ ?_
  · funext x; rfl
  · exact (ContinuousLinearMap.id ℝ _).hasFDerivAt

end DLNFibre.DLN.RLCT

end

exec
/bin/bash -lc "sed -n '1,150p' lean/DLNFibre/DLN/RLCT/Validate/RouteMRadialFactor.lean" in /home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/agent-a9bb11c22680d93d4
 succeeded in 0ms:
import DLNFibre.DLN.RLCT.Validate.RouteMChartFactorFold
import DLNFibre.DLN.RLCT.Foundations.S1G5Charts

/-!
# `RouteMRadialFactor` — Phase B item 2: the radial-blow-up `ChartFactor` (the first flat factor)

The radial blow-up `pivotBlowupOn` packaged as a `ChartFactor` (`RouteMChartFactorFold`) — the first and
simplest of the full-ambient flat-coordinate factors of the achiever chart's factor product
`Q ∘ composeFold(Schur/LDU/chain/radial)` (item 2 of the det route, B+b1). The radial is already a
full-ambient `(Fin N → ℝ) → (Fin N → ℝ)` map with a banked `HasFDerivWithinAt` (`pivotBlowupOn_hasFDerivWithinAt`)
and a banked determinant (`pivotBlowupOnDeriv_det = |x_p|^{card−1}`), so it slots directly into
`ChartFactor`/`composeFold` with no coordinatization work.

* `radialFactor active p` — the radial blow-up as a `ChartFactor N`.
* `radialFactor_abs_det` — `|det (D u)| = |u_p|^{card−1}` (the radial Jacobian, `= |u_p|^{minAdm−1}` at
  the achiever center `card = minAdm`).

The remaining item-2 factors (Schur, LDU, chain) are NOT yet full-ambient: `schurFrameDeriv` lives on the
increment space `SchurInc t r c`, `lduCoreDeriv` on `LDUParam t`, `chainUnitMap` on a product matrix space.
Each needs conjugation into `(Fin N → ℝ) →L (Fin N → ℝ)` via the item-1 `chartIdxEquiv` coordinatization
(the genuine remaining item-2 work; the radial here is the template `ChartFactor` shape).

Axiom-clean `[propext, Classical.choice, Quot.sound]` (calculus + determinant; no S2).
-/

namespace DLNFibre.DLN.RLCT

open scoped BigOperators

/-- **The radial blow-up as a `ChartFactor`** — `pivotBlowupOn active p` with its banked fderiv
`pivotBlowupOnDeriv` and `HasFDerivAt` (from `pivotBlowupOn_hasFDerivWithinAt` on `Set.univ`). The first
flat-coordinate factor of the achiever chart's factor product. -/
noncomputable def radialFactor {N : ℕ} (active : Finset (Fin N)) (p : Fin N) : ChartFactor N where
  f := pivotBlowupOn active p
  D := pivotBlowupOnDeriv active p
  hasD := fun u => hasFDerivWithinAt_univ.mp (pivotBlowupOn_hasFDerivWithinAt active p Set.univ u)

@[simp] theorem radialFactor_f {N : ℕ} (active : Finset (Fin N)) (p : Fin N) :
    (radialFactor active p).f = pivotBlowupOn active p := rfl

@[simp] theorem radialFactor_D {N : ℕ} (active : Finset (Fin N)) (p : Fin N) :
    (radialFactor active p).D = pivotBlowupOnDeriv active p := rfl

/-- **The radial factor's abs-det** `|det (D u)| = |u_p|^{active.card − 1}` (the codim-`active.card`
radial blow-up Jacobian; `= |u_p|^{minAdm − 1}` at the achiever center `active.card = minAdm`). The radial
contribution to the `composeFold_abs_det` telescope. -/
theorem radialFactor_abs_det {N : ℕ} (active : Finset (Fin N)) (p : Fin N) (hp : p ∈ active)
    (u : Fin N → ℝ) :
    |LinearMap.det ((radialFactor active p).D u).toLinearMap| = |u p| ^ (active.card - 1) := by
  show |LinearMap.det (pivotBlowupOnDeriv active p u).toLinearMap| = _
  rw [show LinearMap.det (pivotBlowupOnDeriv active p u).toLinearMap
        = (pivotBlowupOnDeriv active p u).det from rfl,
    pivotBlowupOnDeriv_det active p hp, abs_pow]

/-- Non-vacuity: a single-factor `composeFold [radialFactor active p]` has the radial fderiv and abs-det
`|u_p|^{card−1}` (the `ChartFactor`/`composeFold` interface fires on the radial). -/
example {N : ℕ} (active : Finset (Fin N)) (p : Fin N) (hp : p ∈ active) (u : Fin N → ℝ) :
    |LinearMap.det ((foldDerivList [radialFactor active p] u).prod).toLinearMap|
      = |u p| ^ (active.card - 1) * 1 := by
  rw [composeFold_abs_det [radialFactor active p] u [|u p| ^ (active.card - 1)] (by
    simp only [foldDerivList_cons, foldDerivList_nil, List.map_cons, List.map_nil,
      composeFold_nil, id_eq]
    rw [radialFactor_abs_det active p hp])]
  simp [List.prod_cons, List.prod_nil]

end DLNFibre.DLN.RLCT

exec
/bin/bash -lc "sed -n '1,150p' lean/DLNFibre/DLN/RLCT/Validate/RouteMCardBridge.lean" in /home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/agent-a9bb11c22680d93d4
 succeeded in 0ms:
import DLNFibre.DLN.RLCT.Validate.RouteMBudget
import DLNFibre.DLN.RLCT.Validate.RouteMRadialFactor
import DLNFibre.DLN.RLCT.Validate.NodeAchieverChart
import DLNFibre.DLN.RLCT.Validate.RouteMFlatStructV

/-!
# `RouteMCardBridge` — the card-bridge `active.card = minAdm` + the −1 lemma (2b-i-A, cast-light)

The count-level core of the interior chart's radial degree: the radial blow-up `pivotBlowupOn active p`
of the achiever center has `active.card = minAdm M` active directions, so its Jacobian radial exponent is
`active.card − 1 = minAdm M − 1` (`radialFactor_abs_det`). This discharges the `leafH (structPivot) =
minAdm − 1` field (`NodeAchieverChart.leafH_pivot`) once `leafH` is the factored-det exponent vector.

**Cast-light** (the (a)/budget discipline): the count is pure ℕ arithmetic — `minAdm` (banked) + the
existence of a `minAdm`-card subset of `Fin N` containing the pivot (`Finset.exists_superset_card_eq`),
given `minAdm M ≤ routeMAmbient M` (codim ≤ ambient dimension). NO `chartIdxEquiv`-level Fin-N bijection
in the count — `active`'s *identity* (which slots) is the item-3 map-equality's concern (2b-i-B), not the
count's.

* `radialActive_exists` — `∃ active, structPivot ∈ active ∧ active.card = minAdm` (given `minAdm ≤ N`,
  `1 ≤ minAdm`); the achiever radial active set.
* `radialLeafH_pivot` — the −1 lemma in its abstract form: for the radial exponent vector
  `leafH p := active.card − 1` (`0` elsewhere) with `active.card = minAdm`, `leafH (structPivot) =
  minAdm − 1`. The `NodeAchieverChart.leafH_pivot` discharge (the radial axis carries `minAdm − 1`;
  spectator LDU/Schur axes are `k = 0`, threshold-neutral — `nodeChart_thresholdLe`).
* `radial_abs_det_minAdm` — the radial factor's det at the achiever active set is `|u_p|^{minAdm−1}`.

Honest naming (genm-budgetrev): `budget_identity` is TOTAL budget = minAdm; the −1 is `active.card − 1`
(the one fixed pivot — the gauge). This file proves `active.card − 1 = minAdm − 1`, NOT
`#angular = minAdm − 1` as a `budget_identity` restatement.

Axiom-clean `[propext, Classical.choice, Quot.sound]` (finite cardinality + the banked minAdm).
-/

open scoped BigOperators

namespace DLNFibre.DLN.RLCT

variable {L : ℕ}

/-! ## `minAdm ≤ routeMAmbient` (codim ≤ ambient dimension) -/

/-- **The predecessor rank `tPrev (tStar) j ≤ M (j.castSucc)`** — `tPrev_0 = M 0 = M(0.castSucc)`;
`tPrev_{j>0} = tStar_{j−1} ≤ M_j = M(j.castSucc)` (`tStar_le_Msucc` at `j−1`). The width bound for the
codim ≤ dim comparison. -/
theorem tPrev_tStar_le_Mcastsucc (M : Fin (L + 1) → ℕ) (j : Fin L) :
    tPrev M (tStar M) j ≤ (M j.castSucc : ℤ) := by
  rw [tPrev]
  by_cases hj0 : j.val = 0
  · rw [if_pos hj0]
    have : M j.castSucc = M 0 := by congr 1; apply Fin.ext; simp [Fin.castSucc, Fin.castAdd, hj0]
    rw [this]
  · rw [if_neg hj0]
    have hpred := tStar_le_Msucc M (tStar M) (tStar_mem M) ⟨j.val - 1, by omega⟩
    have hcs : (⟨j.val - 1, by omega⟩ : Fin L).succ = j.castSucc := by
      apply Fin.ext; simp [Fin.succ, Fin.castSucc, Fin.castAdd]; omega
    rwa [hcs] at hpred

/-- **`minAdm M ≤ routeMAmbient M`** — the achiever-center codimension is at most the ambient parameter
dimension `flatDim = ∑_s M_s·M_{s+1}`. Per-term: `(tPrev_j − tStar_j)(M_{j+1} − tStar_j) ≤
M(j.castSucc)·M(j.succ)` (both factors nonneg and bounded — `tPrev ≤ M(castSucc)`, `M_{j+1} − tStar ≤
M_{j+1} = M(succ)`); sum `Mval (tStar) ≤ flatDim`, then `minAdm = Mval.toNat ≤ flatDim = routeMAmbient`.
Closes the open hypothesis of `radialActive_exists`. -/
theorem minAdm_le_routeMAmbient (M : Fin (L + 1) → ℕ) : minAdm M ≤ routeMAmbient M := by
  have hsum : Mval M (tStar M) ≤ (routeMAmbient M : ℤ) := by
    rw [routeMAmbient, flatDim_eq, Mval, Nat.cast_sum]
    refine Finset.sum_le_sum (fun j _ => ?_)
    have hrn : (0 : ℤ) ≤ tPrev M (tStar M) j - (tStar M j : ℤ) := by
      have := tStar_le_tPrev M (tStar M) (tStar_mem M) j; linarith
    have hcn : (0 : ℤ) ≤ (M j.succ : ℤ) - (tStar M j : ℤ) := by
      have := tStar_le_Msucc M (tStar M) (tStar_mem M) j; linarith
    have hr : tPrev M (tStar M) j - (tStar M j : ℤ) ≤ (M j.castSucc : ℤ) := by
      have := tPrev_tStar_le_Mcastsucc M j
      have := tStar_le_Msucc M (tStar M) (tStar_mem M) j; linarith [(tStar M j).cast_nonneg (α := ℤ)]
    have hc : (M j.succ : ℤ) - (tStar M j : ℤ) ≤ (M j.succ : ℤ) := by
      linarith [(tStar M j).cast_nonneg (α := ℤ)]
    calc (tPrev M (tStar M) j - (tStar M j : ℤ)) * ((M j.succ : ℤ) - (tStar M j : ℤ))
        ≤ (M j.castSucc : ℤ) * ((M j.succ : ℤ) - (tStar M j : ℤ)) :=
          mul_le_mul_of_nonneg_right hr hcn
      _ ≤ (M j.castSucc : ℤ) * (M j.succ : ℤ) :=
          mul_le_mul_of_nonneg_left hc (by positivity)
  rw [Mval_tStar_eq] at hsum
  exact_mod_cast hsum

/-! ## The achiever radial active set (existence + cardinality) -/

/-- **The achiever radial active set exists**: given `1 ≤ minAdm M`, there is a
`Finset (Fin (routeMAmbient M))` of cardinality `minAdm M` containing the radial pivot `structPivot`
(the codim ≤ dim bound `minAdm_le_routeMAmbient` is now discharged internally, NO open hypothesis).
The blow-up active set of the codim-`minAdm` achiever center. -/
theorem radialActive_exists (M : Fin (L + 1) → ℕ) (hN : 0 < routeMAmbient M)
    (hpos : 1 ≤ minAdm M) :
    ∃ active : Finset (Fin (routeMAmbient M)),
      structPivot M hN ∈ active ∧ active.card = minAdm M := by
  obtain ⟨active, hsub, hcard⟩ := Finset.exists_superset_card_eq
    (show ({structPivot M hN} : Finset (Fin (routeMAmbient M))).card ≤ minAdm M by
      rw [Finset.card_singleton]; exact hpos)
    (show minAdm M ≤ (Finset.univ : Finset (Fin (routeMAmbient M))).card by
      rw [Finset.card_univ, Fintype.card_fin]; exact minAdm_le_routeMAmbient M)
  exact ⟨active, hsub (Finset.mem_singleton_self _), hcard⟩

/-! ## The radial determinant at the achiever active set + the −1 lemma -/

/-- **The radial blow-up det at the achiever active set is `|u_p|^{minAdm−1}`** — `radialFactor_abs_det`
at `active.card = minAdm` (`p ∈ active`). The radial contribution to the chart's monomial Jacobian. -/
theorem radial_abs_det_minAdm (M : Fin (L + 1) → ℕ) (hN : 0 < routeMAmbient M)
    (active : Finset (Fin (routeMAmbient M))) (hp : structPivot M hN ∈ active)
    (hcard : active.card = minAdm M) (u : Fin (routeMAmbient M) → ℝ) :
    |LinearMap.det ((radialFactor active (structPivot M hN)).D u).toLinearMap|
      = |u (structPivot M hN)| ^ (minAdm M - 1) := by
  rw [radialFactor_abs_det active (structPivot M hN) hp u, hcard]

/-- **The −1 lemma (abstract radial form)**: the radial exponent vector
`leafH j := if j = structPivot then active.card − 1 else 0`, at `active.card = minAdm M`, has
`leafH (structPivot) = minAdm M − 1` — the `NodeAchieverChart.leafH_pivot` field. (The spectator
LDU/Schur axes — `0` here — are filled by the per-boundary factors in 2b-i-C/D; they carry `k = 0` in
the loss-base, threshold-neutral via `nodeChart_thresholdLe`.) -/
theorem radialLeafH_pivot (M : Fin (L + 1) → ℕ) (hN : 0 < routeMAmbient M)
    (active : Finset (Fin (routeMAmbient M))) (hcard : active.card = minAdm M) :
    (fun j => if j = structPivot M hN then active.card - 1 else 0) (structPivot M hN)
      = minAdm M - 1 := by
  simp only [↓reduceIte, hcard]

end DLNFibre.DLN.RLCT

exec
/bin/bash -lc "sed -n '56,110p' lean/DLNFibre/DLN/RLCT/Validate/NodeAchieverChart.lean" in /home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/agent-a9bb11c22680d93d4
 succeeded in 0ms:
/-! ## The `NodeAchieverChart M` bundle (the `L2AchieverChart` fields, generalized to `M`)

A per-node achiever chart for `M`, with binding pivot axis `p` and genuine Jacobian exponents
`leafH` (`leafH p = minAdm M − 1`, the radial blow-up of the codim-`minAdm` achiever center; the
spectator monomial on `k = 0` axes does not lower the threshold). Carrying the bundle as an explicit
hypothesis set isolates the divergence ASSEMBLY (proven M-agnostically from the bundle) from the chart
CONSTRUCTION (the case-specific Schur-frame ∘ radial blow-up). `Ufun` is the `u_p`-free unit factor of
`F ∘ phi = (u_p)² · U`; `B` its compact-box upper bound. -/
structure NodeAchieverChart (M : Fin (L + 1) → ℕ) where
  /-- Non-degeneracy: the achiever center has positive codimension `minAdm M ≥ 1`. -/
  hpos : 1 ≤ minAdm M
  /-- The chart map (the case-specific Schur-frame ∘ radial blow-up, in flat coordinates). -/
  phi : (Fin (routeMAmbient M) → ℝ) → (Fin (routeMAmbient M) → ℝ)
  /-- The binding pivot axis (the radial exceptional divisor `u_p`). -/
  p : Fin (routeMAmbient M)
  /-- The genuine Jacobian exponents `h` of the chart (`|det Dφ| = ∏_j |u_j|^{leafH j}`). -/
  leafH : Fin (routeMAmbient M) → ℕ
  /-- The binding axis carries the radial blow-up exponent `minAdm M − 1` (`(k,h) = (1, minAdm−1)`). -/
  leafH_pivot : leafH p = minAdm M - 1
  /-- The unit factor `U` of `F ∘ phi = (u_p)² · U`. -/
  Ufun : (Fin (routeMAmbient M) → ℝ) → ℝ
  /-- On each source box `[0,δ]^N`, `U` admits a `δ`-dependent compact upper bound `B > 0`, and `U` is
  positive a.e. on the box (the SOUNDNESS-critical pair: `U ≤ B` gives `U^{−c'} ≥ B^{−c'} > 0` where
  `U > 0`; the vanishing locus `{U = 0}` is null, dropped a.e.). -/
  Ubound : ∀ δ : ℝ, ∃ B : ℝ, 0 < B ∧
    (∀ u ∈ Set.univ.pi (fun _ : Fin (routeMAmbient M) => Set.Icc (0 : ℝ) δ), Ufun u ≤ B) ∧
    ∀ᵐ u ∂(volume.restrict
        (Set.univ.pi (fun _ : Fin (routeMAmbient M) => Set.Icc (0 : ℝ) δ))), 0 < Ufun u
  /-- `U` is measurable (a polynomial in the chart coordinates). -/
  Umeas : Measurable Ufun
  /-- The leaf-integrand identity, holding **a.e.** (`∀ᵐ u ∂volume`): `(∏_j |u_j|^{leafH j}) ·
  |F ∘ phi|^{−c} = monomialIntegrand · U^{−c}` (the genuine Jacobian × the loss power, on the chart
  orthant). The box-divergence atom is intrinsically an a.e./lintegral property, so the a.e. form is the
  faithful one: a POLYNOMIAL chart supplies it ∀u via `Filter.Eventually.of_forall`; a RATIONAL chart
  (the smeared `φ_sm`) supplies it off its null pole, where the rate `F∘φ = u_p²·U` genuinely holds.
  The M-agnostic `leaf_integrand334`. -/
  leaf_integrand : ∀ (c : ℝ), ∀ᵐ u ∂(volume : Measure (Fin (routeMAmbient M) → ℝ)),
    (∏ j, |u j| ^ (leafH j)) * |routeMCore M (phi u)| ^ (-c)
      = monomialIntegrand (routeMAmbient M) (nodeLeafK (routeMAmbient M) p) leafH c u
        * (Ufun u) ^ (-c)
  /-- The composite change-of-variables (the genuine chart Jacobian `|det Dφ| = ∏_j |u_j|^{leafH j}`,
  off the pivot-zero locus `{u_p = 0}`): `∫⁻_{phi '' (V \ {u_p=0})} g = ∫⁻_{V \ {u_p=0}}
  ofReal(∏_j |u_j|^{leafH j}) · g (phi u)`. The M-agnostic `phi334_cov`. -/
  cov : ∀ (V : Set (Fin (routeMAmbient M) → ℝ)), MeasurableSet V →
      ∀ (g : (Fin (routeMAmbient M) → ℝ) → ℝ≥0∞),
    ∫⁻ x in phi '' (V \ {x | x p = 0}), g x
      = ∫⁻ u in V \ {x | x p = 0}, ENNReal.ofReal (∏ j, |u j| ^ (leafH j)) * g (phi u)
  /-- Image containment: a small source box `[0,δ]^N` maps into `cubeBox N ε`. -/
  image_subset : ∀ ε : ℝ, 0 < ε →
    ∃ δ > 0, phi '' (Set.univ.pi (fun _ : Fin (routeMAmbient M) => Set.Icc (0 : ℝ) δ))
      ⊆ cubeBox (routeMAmbient M) ε

/-! ## The leaf monomial threshold from the bundle (the M-specific input, discharged) -/

/-- **The bundle's leaf monomial threshold is `≤ ½·minAdm M`** (the binding axis `p` has

codex
**Short verdict:** choose **D**. Make the radial slot an explicit parameter, then instantiate it by finite-complement membership. Keep `structPivot := ⟨0,_⟩` only as a compatibility default, not as the determinant-critical radial slot.

**Ranking**

1. **D: best route.** Add `p0 : Fin (routeMAmbient M)` to the chart/rate/BData/headline layer:
   ```lean
   noncomputable def phiFlatLiveR1At ... (p0 : Fin (routeMAmbient M)) ... x :=
     phiGen (x p0) M t (genBlkFlatLiveR1 M t ha p hp1 hp2 (rfin x) x) ...
   ```
   Then prove `routeMCore_phiFlatLiveR1At` by the same `routeMCore_phiGen` one-liner. `RouteMRadialFactor` is already generic in `p`, so the determinant calculus is not new. The specialized `structPivot` wrappers can remain.

2. **A: not clean as stated.** There is no immediate cycle merely from `chartIdxEquiv`: [RouteMFlatStructV.lean](/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/agent-a9bb11c22680d93d4/lean/DLNFibre/DLN/RLCT/Validate/RouteMFlatStructV.lean:1) imports `RouteMGenFlatStruct`, which already imports `RouteMChartSlots`/`RouteMChartIdxEquiv`. But concrete `readerSet` lives high up in [RouteMBData222.lean](/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/agent-a9bb11c22680d93d4/lean/DLNFibre/DLN/RLCT/Validate/RouteMBData222.lean:814), above `RouteMFlatLive`/`RouteMBInterface`; importing that back would cycle. More importantly, `structPivot M hN` has no `t`, `ha`, R1 boundary, or reader specification. Making it reader-aware either hides a specialization or changes its API into D anyway.

3. **B: bad bridge.** If `BData` uses `pRad` but `phiFlatLiveR1` still reads `x (structPivot)`, the headline is for the wrong map. To bridge, you would need to reprove the rate and map identity for the `pRad`-radial chart, or carry a coordinate-permutation conjugacy through all readers. That is D with extra work and worse statements.

4. **C: dead end.** Tight cardinality only proves there is room outside `readerSet`; it does not prove slot `0` is outside it. A model with `readerSet` containing `⟨0,_⟩` and three other non-readers still satisfies the same counts. Any argument using `active.card + readerSet.card = 8` also needs `active ∩ readerSet = ∅`, which already includes `PivotNotReader`.

**Concrete Lean Shape**

For 222, reverse the current choice pattern. Instead of choosing leaves from `univ \ insert structPivot readerSet`, choose all active slots from:
```lean
noncomputable def freeSlots222 : Finset (Fin (routeMAmbient M222)) :=
  (Finset.univ : Finset (Fin (routeMAmbient M222))) \ readerSet
```

Prove `3 ≤ freeSlots222.card`, then choose a distinct triple:
```lean
pRad, lf0, lf1 ∈ freeSlots222
```

Then:
```lean
theorem pRad_not_reader : pRad ∉ readerSet :=
  (Finset.mem_sdiff.mp pRad_mem).2
```

Use `pRad_not_reader` to discharge the pivot-vs-reader cases in `slotList_injective` / `slotListC_injective`. No opaque comparison remains.

For general `∀M`, do not make a global `structPivot` choice. State the construction against data:
```lean
(readerSet : Finset (Fin (routeMAmbient M)))
(p0 : Fin (routeMAmbient M))
(hp0 : p0 ∉ readerSet)
(active : Finset (Fin (routeMAmbient M)))
(hp_mem : p0 ∈ active)
(hcard : active.card = minAdm M)
```

Then specialize by proving enough free slots for the concrete reader set. This generalizes cleanly because the finite forbidden/reader set belongs to the chart construction, not to `M` alone.
tokens used
154,054
**Short verdict:** choose **D**. Make the radial slot an explicit parameter, then instantiate it by finite-complement membership. Keep `structPivot := ⟨0,_⟩` only as a compatibility default, not as the determinant-critical radial slot.

**Ranking**

1. **D: best route.** Add `p0 : Fin (routeMAmbient M)` to the chart/rate/BData/headline layer:
   ```lean
   noncomputable def phiFlatLiveR1At ... (p0 : Fin (routeMAmbient M)) ... x :=
     phiGen (x p0) M t (genBlkFlatLiveR1 M t ha p hp1 hp2 (rfin x) x) ...
   ```
   Then prove `routeMCore_phiFlatLiveR1At` by the same `routeMCore_phiGen` one-liner. `RouteMRadialFactor` is already generic in `p`, so the determinant calculus is not new. The specialized `structPivot` wrappers can remain.

2. **A: not clean as stated.** There is no immediate cycle merely from `chartIdxEquiv`: [RouteMFlatStructV.lean](/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/agent-a9bb11c22680d93d4/lean/DLNFibre/DLN/RLCT/Validate/RouteMFlatStructV.lean:1) imports `RouteMGenFlatStruct`, which already imports `RouteMChartSlots`/`RouteMChartIdxEquiv`. But concrete `readerSet` lives high up in [RouteMBData222.lean](/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/agent-a9bb11c22680d93d4/lean/DLNFibre/DLN/RLCT/Validate/RouteMBData222.lean:814), above `RouteMFlatLive`/`RouteMBInterface`; importing that back would cycle. More importantly, `structPivot M hN` has no `t`, `ha`, R1 boundary, or reader specification. Making it reader-aware either hides a specialization or changes its API into D anyway.

3. **B: bad bridge.** If `BData` uses `pRad` but `phiFlatLiveR1` still reads `x (structPivot)`, the headline is for the wrong map. To bridge, you would need to reprove the rate and map identity for the `pRad`-radial chart, or carry a coordinate-permutation conjugacy through all readers. That is D with extra work and worse statements.

4. **C: dead end.** Tight cardinality only proves there is room outside `readerSet`; it does not prove slot `0` is outside it. A model with `readerSet` containing `⟨0,_⟩` and three other non-readers still satisfies the same counts. Any argument using `active.card + readerSet.card = 8` also needs `active ∩ readerSet = ∅`, which already includes `PivotNotReader`.

**Concrete Lean Shape**

For 222, reverse the current choice pattern. Instead of choosing leaves from `univ \ insert structPivot readerSet`, choose all active slots from:
```lean
noncomputable def freeSlots222 : Finset (Fin (routeMAmbient M222)) :=
  (Finset.univ : Finset (Fin (routeMAmbient M222))) \ readerSet
```

Prove `3 ≤ freeSlots222.card`, then choose a distinct triple:
```lean
pRad, lf0, lf1 ∈ freeSlots222
```

Then:
```lean
theorem pRad_not_reader : pRad ∉ readerSet :=
  (Finset.mem_sdiff.mp pRad_mem).2
```

Use `pRad_not_reader` to discharge the pivot-vs-reader cases in `slotList_injective` / `slotListC_injective`. No opaque comparison remains.

For general `∀M`, do not make a global `structPivot` choice. State the construction against data:
```lean
(readerSet : Finset (Fin (routeMAmbient M)))
(p0 : Fin (routeMAmbient M))
(hp0 : p0 ∉ readerSet)
(active : Finset (Fin (routeMAmbient M)))
(hp_mem : p0 ∈ active)
(hcard : active.card = minAdm M)
```

Then specialize by proving enough free slots for the concrete reader set. This generalizes cleanly because the finite forbidden/reader set belongs to the chart construction, not to `M` alone.
