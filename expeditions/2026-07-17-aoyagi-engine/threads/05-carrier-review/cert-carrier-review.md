# cert-carrier-review — fresh round on the edge-labelled carrier restructure

**Reviewer:** independent audit seat (rev2 worktree, branch `expedition/aoyagi-engine--rev2`,
merge `dd8280f91`). **Target:** the council-adopted edge-labelled resolution-tree carrier +
the six obligations (increments `49a1f34bd` + `41373f8e5`). **Functions:** fidelity +
claim-soundness + precision + wording, to the bedrock bar.

**Decorrelated Codex read:** `codex/carrier-shape-prompt.md` / `carrier-shape-answer.md` (xhigh).
Codex independently reached findings 1 and 2 below (case-1(1) drop; residual-Morse omission) with
its own counterexamples, and added findings 3–8. Its stated verdict: "reject the current
obligations as a faithful resolution certificate … the edge-labelled tree is an appropriate carrier."

---

## VERDICT: VALIDATE-WITH-CHANGES

- **The CARRIER datatype is VALIDATED** (edge-labelled shape, typed sharing fields, `chartDom`
  removed, coherence clause, witness split + axiom footprints, circularity guard) — keep it; it may
  flip `resolution-tree → validated`.
- **The OBLIGATION PREDICATES are NOT yet correctly stated.** Findings **1 and 2 are CRITICAL**
  (a fidelity mismatch and a soundness break, each with a counterexample). They **block
  merge-to-canonical of the obligation predicates and the flip of the six obligations to
  "stated/validated"** until fixed and re-reviewed. Findings 3–7 are major statement gaps that
  should land in the same pass.

The carrier gained the *ability* to express edge-relational transitions; the obligations do not yet
*use* it. As written, a wrong resolution satisfies `StepRel`, and `region_glue` is false-as-stated
and owns the singular change-of-variables itself.

---

## CRITICAL findings (block the obligation-status flip)

### 1. `StepRel` does not certify the paper's transitions — fidelity mismatch + counterexample

`StepRel n e` (`EngineObligations.lean:76`) reads only the parent node `n` and `e.case`. It **never
reads `e.child` or `e.subst`.** Consequences:

- **Case-1(1) merge dropped.** The paper's Case-1(1) is `t̃_{s,k}=J` **and** the exponent-merge
  `M'_{s,k} = M_{s,k} + J₁·(M^{(S+1)}−J)` (child exponent = parent's + increment; worked.tex:505–507).
  The Lean clause is only `∃ k, n.divTilde k = n.cleared`. Codex counterexample: parent one divisor,
  `divExp 0 = 5`, `divTilde 0 = cleared`, `J₁=2`, `resCols=3` → correct child exponent 11, but a
  Case-1(1) edge whose child exponent is 0, 11, **or 99** satisfies the identical `StepRel`. So
  `∀ p ∈ stepEdges, StepRel` permits wrong child exponents. This is precisely the parent-referencing
  merge the restructure was justified to pin (compass fork 7 WHY).
- **Case-2 searches the wrong ledger.** Case-2 creates a *child* divisor of exponent
  `(M(S)−J)(M^{(S+1)}−J)`, but the clause searches `n` (the parent). (The exponent *value*
  `resRows·resCols` is faithful to the paper — worked.tex:516 — but it is asserted of the parent's
  ledger, not the emitted child's.)
- **Case-1(2) under-asserts.** It checks a parent `bExp` entry but never asserts the child advances
  `cleared` or contains the new pivot.
- **Docstring overclaims.** "edge-relational per-step invariant", "case-keyed identities", "the
  exponent-merge at level J" all describe content the clause does not state.

The in-file `(2,2,4)` witness is a warning symptom, not evidence: `rootNode224` declares a `1×1`
residual (`resRows=resCols=1`) though `layer=cleared=0` on `M=(2,2,4)` gives a `≥2×2` residual, uses
`localSub=id`, and still proves Case-2 `StepRel` — it passes only because `StepRel` is this weak.

**FIX.** Give `Edge`/`StepRel` an edge-transition record: the run length `J₁` and a parent→child
divisor-index embedding (`Fin n.numDiv ↪ Fin (child root).numDiv`, or a stable divisor id). Then make
`StepRel` read `e.child`'s root ledger and require the case-specific child update explicitly
(case-1(1): child `divExp = parent divExp + J₁·(resCols)`; case-2: the *child*'s new divisor has
exponent `resRows·resCols`; case-1(2): child `cleared` advanced + the new pivot present).

### 2. `region_glue` is under-provisioned — residual-Morse threshold absent + transport inapplicable

Two coupled defects; either alone makes `region_glue` not "assembly only" (violating the compass
region-glue fence).

**(a) Residual-Morse ratio guard missing — soundness break + counterexample.**
`terminalExponents` (`ResolutionTree.lean:188`) ranges over `divExp` only. There is **no `resRank`
ratio guard and no `resRank ≥ minAdm` conjunct anywhere** (grep-confirmed). Yet `residualBaseForm`
(`EngineObligations.lean:36`) and `LeafPullback` make the Morse core `‖z‖²` over the `resRank`
coordinates contribute `resRank/2` to each leaf's threshold. So `region_glue`'s `hrat` (over divisor
exponents) does not bound the Morse-core integral. Codex counterexample (independent): pullback
`u²z²`, Jacobian `|u|^{e−1}`, `resRank=1`, `e=2`, `c'=3/4` → `hrat` holds (`3/4 < 1`) but
`∫|z|^{−3/2}dz` diverges → **`region_glue` as stated is FALSE** for a `ChartBridge`-satisfying tree
with such a leaf. This is exactly the **elder-ratified amendment that did not land** (journal
tick 20/25: "residual folded into `terminalExponents`, keeping the single `hrat` interface"; compass
region-glue: "`resRank ≥ minAdm` is a THEOREM of the tide, never assumed").
**FIX.** Append every positive `resRank` to `terminalExponents` (so `hrat` covers `resRank/2` and
`exponent_ledger_bridge` extends to `minAdm ≤ resRank`), OR add
`∀ l ∈ leaves t, l.resRank = 0 ∨ minAdm M ≤ l.resRank` as a `CanonicalResolution` conjunct.

**(b) Transport lemma inapplicable to the singular factor — laundering risk.**
`rlctAtOn_boundedUnit_localHomeomorph` (`Foundations/S1NonMPTransport.lean:292`) needs a full local
diffeomorphism: forward `π`, inverse `πsymm`, both `C¹` on open `V`, `π wstar = wstar`, left/right
inverse identities, and Jacobian determinants **bounded away from 0 and ∞ in BOTH directions**.
`LeafJacobian` supplies only the forward `Dφ`, `HasFDerivAt`, and `|det Dφ| = (∏ u^{divExp−1})·jacUnit`
— no inverse map/derivative/bound, and `|det Dφ|` is **not** bounded-unit (it carries the vanishing
`∏ u^{divExp−1}`). For the singular blow-up factor `π(u,y)=(u,uy)`, `|det Dπ|=|u|` has no positive
lower bound on any neighbourhood of `u=0` and no local inverse there — the lemma's hypotheses are
**mathematically false** on the exceptional locus, which is where the RLCT basepoint sits. So
`region_glue`'s `sorry` currently owns the singular change-of-variables theorem, not "assembly".
**FIX (Codex, either):** expose the factorization `chartMap = ψ ∘ β` (ψ a bounded-unit local diffeo
carrying full inverse data; β the monomial blow-up) and apply the transport to ψ only + direct
monomial integration to β; OR strengthen the leaf certificate to a direct area-formula form
(measurable bounded product `srcBox`, a.e. injectivity, measurable Jacobian).

---

## MAJOR findings (statement gaps; fix in the same pass)

### 3. Phantom attainment via empty `srcBox` (vacuity)
A leaf with `srcBox = ∅` satisfies `InjOn`/`LeafPullback`/`LeafJacobian` vacuously and contributes
`chartMap '' ∅ = ∅` to the image cover, yet its `divExp` still enters `terminalExponents`. So
`minAdm M ∈ terminalExponents t` can hold via a leaf that plays no analytic role — structurally
on-tree but analytically phantom. (The r1 fake-`chartMap` vacuity is closed at the pullback level;
this empty-domain vacuity is new.) **FIX.** For the attaining leaf require `divProfile k = tStar M`,
`divExp k = minAdm M`, **and** a live source domain (`srcBox` with nonempty interior / the binding
coordinate reaching 0 on a positive-measure region).

### 4. `divProfile` not required admissible (fidelity)
`IsFullMonomialization` ties `divExp k = (Mval M (divProfile k)).toNat` but never requires
`divProfile k ∈ Adm M`. For `M=(2,2,4)` the non-admissible `T=(0,4)` has `Mval=4=minAdm`, so a
legitimate exponent-4 leaf can be relabelled by an impossible profile with every predicate preserved
(Codex). **FIX.** Require `divProfile k ∈ Adm M`.

### 5. `divCoord`/`resCoord` need injectivity + disjoint ranges (soundness)
The pullback monomial `∏ (paramsEquivFlat w (divCoord k))²` and the Jacobian `∏ (…)^{divExp k−1}`
assume distinct coordinates; if `divCoord` is non-injective or overlaps `resCoord`, per-divisor
thresholds do not combine and the base form double-counts (Codex). **FIX.** Add
`Function.Injective l.divCoord`, `Function.Injective l.resCoord`, and disjointness of their ranges.

### 6. Full `Set.InjOn` is wrong for genuine blow-up charts (fidelity)
A blow-up chart is not injective on the exceptional fibre (`π(0,y)=(0,0)`). `Set.InjOn chartMap
srcBox` over a `srcBox` reaching the exceptional locus is unsatisfiable, while a `srcBox` avoiding it
fails to cover the singular locus (Codex). **FIX.** Replace with a.e.-injectivity / injectivity off a
specified null set.

### 7. Jacobian sign (precision)
`|det Dφ| = ∏ (paramsEquivFlat w (divCoord k))^{divExp k−1} · jacUnit`: for odd `divExp k − 1` and a
negative coordinate the RHS can be negative while the LHS `≥ 0`, forcing an implicit sign restriction
or unsatisfiability off the positive sector (Codex). **FIX.** Use `∏ |·|^{divExp k−1}` or restrict
`srcBox` to a fixed-sign sector.

---

## MINOR / precision / wording

- **8. Ledger fields decorative.** `jacPow` is never related to `Dφ` or folded into leaf `divExp`;
  `StepRel` never reads `subst`; `bExp`/`support` are unconnected to `LeafPullback`. Fork 3 named the
  sharing maps "the content", yet no obligation constrains them — they can be corrupted without
  changing the certificate. Wire them, or state plainly that they are construction-side bookkeeping,
  not certificate constraints.
- **9. Item-10 false-premise strike NOT done.** `threads/01-skeleton/necessity-and-encodings.md:96`
  still asserts "Hard given (my probe): `Params M` has no `NormedAddCommGroup`/`NormedSpace`" as a
  live premise; the correction appears only at line 109. Rewrite/strike line 96. (Engine docstrings
  are clean — they correctly state Params is normed via `ParamsFlatLinear`.)
- **10. Banned wording.** `EngineDriver.lean:77` "load-bearing" — borderline (object-level use);
  optional scrub. No other banned-list hits in the Engine files.
- **11. `(2,2,4)` witness root step is a toy** (`resRows=resCols=1`, `divExp=1`, `localSub=id`)
  presented by `rootNode224`'s docstring as "The root blow-up node"; the documented semantics give a
  `≥2×2` residual. It is a valid satisfiability witness for the four conjuncts (which
  `canonicalResolution224_arithmetic` correctly claims), but reads as the real resolution. Reframe as
  an explicit satisfiability toy, or build the real root step. (Non-blocking.)
- **12. Long-line cosmetics** (`ResolutionTree.lean:9,11`, etc.) still present — cosmetic follow-up.

---

## PASSES (verified)

- **Carrier shape (item 1):** mutual `ResolutionTree | leaf (LeafData) | branch (StepData) (List
  Edge)`; `Edge {case, subst, child}`; `StepData` has no `case`; `LeafData` gains
  `chartMap`/`srcBox`/`resRank`, `bChain : Monotone` typed on both `StepData` and `LeafData`;
  `chartDom` fully removed from the carrier (grep clean in `Engine/`).
- **Edge data = monomial ledger only (item 5):** `ChartSubst = localSub` (plain map) `+ jacDivCount
  + jacPow`; no opaque derivative field stored as tree data. The derivative lives only as an
  existential inside `LeafJacobian` (a Prop).
- **ChartBridge shape (item 3):** upstairs-open `U` + IMAGE cover `⋃ chartMap '' srcBox` (not
  abstract) + per-leaf `InjOn`/`LeafPullback`/`LeafJacobian` + the NEW coherence clause (leaf
  `chartMap` = `leafPaths id t` fold). No downstairs-openness of images. (See findings 2b/6 for the
  InjOn/transport content.)
- **LeafJacobian shape (item 4, route (b)):** `∃ Dφ, HasFDerivAt chartMap … ∧ |det| = ∏
  u^{divExp−1} · (positive-bounded unit)`. Shape as pinned; see finding 2b for signature-fit.
- **Attainment via emitted path (item 6):** `minAdm ∈ terminalExponents t`, `terminalExponents`
  ranges over EMITTED leaves only (via `edgesLeaves`); membership is non-empty and structurally
  on-tree, realizing "attainment via an emitted path" — the explicit List-Edge path form is NOT
  required. (See finding 3 for the empty-`srcBox` phantom.)
- **Non-vacuity witnesses (item 7):** (b) `stepRel_rejects_mismatched_case2` is a real rejection
  (`badNode224.divExp=2 ≠ resRows·resCols=1`); (c) `mixedCaseTree_records_both` is a real two-edge
  positive witness (distinct cases + distinct substs). (a) the r1 fake-`chartMap` now fails
  `LeafPullback`/coherence/`InjOn` by reading, but no in-file Lean example or updated battery pins it
  (re-scope note owed) — PARTIAL.
- **Witness split + footprints (item 8), forced `#print axioms` (own build, Engine oleans fresh):**
  - `canonicalResolution224_arithmetic` → `[propext, Classical.choice, Quot.sound]` (clean-three; no
    `@[blueprint]` in its cone).
  - `canonicalResolution224` → `[propext, sorryAx, Classical.choice, Quot.sound]` (forecast + sorryAx).
  - `engine_box_threshold_finite` → `[propext, sorryAx, Classical.choice, Quot.sound]` (watch entry;
    flips clean-three when both engine holes land).
  AxCheck entries are `Engine.`-qualified and follow the split, incl. the `engine_box_threshold_finite`
  watch entry.
- **Circularity guard (item 9):** no Engine reference to `cited_aoyagi_dln` / `RlctInterface` /
  `rlct = c*` (only a docstring "WITHOUT `rlct = c*`"). The two engine holes are exactly
  `monomialization_terminates` + `region_glue` (map-tagged); plus the `(2,2,4)` witness's ChartBridge
  forecast `sorry` (documented). Total sorries in Engine: 3 (2 engine holes + 1 documented forecast
  conjunct).
- **Case-2 exponent (item 2):** `divExp k = resRows·resCols` faithfully matches Aoyagi's
  `M'_{S,J+1}=(M(S)−J)(M^{(S+1)}−J)` (residual codim; worked.tex:516, image-pinned); shared-δ over
  all generators via `∀ g, k ∈ n.support g`. No Def-3 inequality transcription.
- **Termination hooks (item 11):** the carrier is a finite nested inductive; nothing in it
  contradicts the construction-side lex measure `μ`.

## Batteries re-run (review policy)
- `map/battery/g-chartscover-vacuity.py` — reproduces: OLD `ChartsCover` has a counterexample
  (hyps hold, conclusion false at `c'=8/5` on `(2,2,2)`); the strengthening is necessary.
- `map/battery/g-chart-bridge-pullback.py` — reproduces: three real charts satisfy pullback =
  monomial×residual, Jacobian = pure monomial, threshold = ½·minAdm, incl. corank-2 shared divisor.
  (Note: these witnesses have `resRank` = 5, ∞, 8 ≥ `minAdm` = 3, 3, 4 — confirming finding 2a's
  `resRank ≥ minAdm` is TRUE, hence a fact that must be *carried*, not the current silent assumption.)

## Re-review scope
Findings 1 and 2 changed, plus 3–7, require a ripple re-check of `CanonicalResolution`,
`resolutionOf_spec`'s projections, and the `(2,2,4)` witness. The carrier-shape flip may proceed now;
the six-obligation flip waits on the re-review.

---

## ADDENDUM (post-cosmetic commit `14927ae91`, independently re-diffed)

The trailing cosmetic commit (docstring reflow + g-chartscover-vacuity re-scope note, merged into
`expedition/aoyagi-engine`) is **verified cosmetic-only**: `git show 14927ae91` — the only
non-comment diffs are term/signature line-splits (`canonicalResolution224_arithmetic`'s conjunct-3
`exact ⟨…⟩`; the `canonicalResolution224` signature), no semantic change; AxCheck untouched; and a
12-line appended re-scope section in `necessity-and-encodings.md` (nothing above line 127 changed).
The substance of all 12 findings is unaffected. Two status updates:

- **Finding 12 (long lines) — RESOLVED.** All three Engine modules now have 0 lines >100 chars.
- **Finding 7(a) — re-scope note now landed** (prose, `necessity-and-encodings.md` § post-restructure).
  The vacuity-closure argument is documented; a mechanical in-file `¬`-theorem for the constant/`univ`
  `chartMap` case (analogous to `stepRel_rejects_mismatched_case2`) would still upgrade it from
  argued to pinned. Non-blocking.
- **Finding 9 (item-10 false-premise strike) — STILL OPEN.** `14927ae91` added the re-scope note but
  did NOT touch `necessity-and-encodings.md:96`, which still asserts "**Hard given (my probe): `Params
  M` has no `NormedAddCommGroup`/`NormedSpace`**" as a live premise (contradicted only at line 109).
  Do not conflate the landed re-scope cosmetic with this strike; the strike is still owed.

**Refreshed line citations at the new tip** (`origin/expedition/aoyagi-engine`; the cert body cites
`dd8280f91`, pre-reflow — symbols are stable, line numbers shifted): `StepRel` → `:88`; `region_glue`
→ `:177`; `residualBaseForm` → `:41`; `terminalExponents` (ResolutionTree) → `:200`; `LeafPullback`
/`LeafJacobian`/`ChartBridge`/`IsFullMonomialization`/`CanonicalResolution` moved by the same reflow
offset — cite by symbol. `EngineDriver.lean:77` ("load-bearing", finding 10) unchanged.

---

# r2 RE-CHECK — repair pass `72deeac34` (merged into `expedition/aoyagi-engine`)

**Reviewer:** same seat, rev2 worktree (repair merged in, HEAD `198b3b458`). **Own forced
`#print axioms`** (targeted scratch over freshly-built Engine oleans) + **decorrelated Codex** on the
existential-vs-embedding judgment flag (`codex/steprel-existential-{prompt,answer}.md`) + the two new
batteries re-run.

## VERDICT: VALIDATE

The finiteness certificate is **sound**. All r1 findings 1–7 are addressed at the statement level, and
minors 8–12 are cleared. The six-obligation flip, merge-to-canonical, and construction-tide
commissioning **may proceed**. One precision-scope finding (the existential `StepRel`) is recorded as
a controller/elder scope decision, **not a blocker** — see the judgment-flag adjudication.

## Judgment flag — existential child-read in `StepRel`: SUFFICIENT for the certificate

Adjudicated with decorrelated Codex (its verdict converges with mine, independently):

- **Finiteness soundness — the existential is sufficient.** `engine_box_threshold_finite`
  (`EngineDriver.lean:44`) consumes ONLY `region_glue` (needs `ChartBridge` + the ratio side-condition)
  and the lower-bound half `.1` of `exponent_ledger_bridge`. It does **not** consume
  `case_step_invariant`/`StepRel` at all — `StepRel` "could be replaced by `True` without changing the
  driver's argument" (Codex, verified against the code). The finiteness guards are: `minAdm` banked
  independently as `min` over `Adm M` (`RouteMLayerSplit.lean:51`); the exponent hooks forcing every
  terminal exponent `≥ minAdm` with `minAdm` attained (so the terminal minimum is *literally* `minAdm`
  — it cannot be "wrong and too large"); `IsFullMonomialization` forcing each terminal exponent
  `= Mval(admissible profile)`; and `ChartBridge`'s genuine cover. None depend on `StepRel`'s strength.
- **Sharing-mistrack (fork-3 / g-coverage-sharing-killcond) cannot raise the certified threshold.**
  Corrupted `support` metadata *is* reachable through the bundle (it is read only by `StepRel`'s
  case-2 clause, not by `LeafPullback`/`LeafJacobian`/`terminalExponents`/`IsFullMonomialization`), but
  it cannot change `minAdm` or `terminalExponents`, and the `⟨δx,δy⟩`-vs-`⟨δ₁x,δ₂y⟩` obstruction is
  blocked by the exact `LeafPullback` identity (Codex: `δ²(x²+y²)` is a valid leaf form; `δ₁²x²+δ₂²y²`
  cannot masquerade as it — divisibility by `δ₁²δ₂²` fails at `δ₂=0, δ₁x≠0`). The guard is
  `ChartBridge` + `IsFullMonomialization` + banked `minAdm`, **not** `StepRel`.
- **Fidelity — the existential is insufficient (recorded, not blocking).** For the claim that
  `case-step-lemmas` certifies *a faithful Aoyagi transition*, the existential is too weak. Codex's
  disappearing-divisor schema: take any `CanonicalResolution` tree, append one dummy divisor to the
  root ledger (constant-zero `bExp` coord, arbitrary `divExp`/`divTilde`/`support`); every old
  existential `StepRel` witness embeds into the enlarged parent, every other conjunct is unchanged, yet
  the dummy divisor vanishes at every child — so the **full bundle admits a non-faithful tree**. The
  case-1(1) form also lets a second parent divisor (e.g. exponent 37 alongside the merged 5→11) simply
  disappear, unrecorded. This is a fidelity defect, **not** a finiteness-soundness defect.
- **Recommendation (controller/elder scope call).** Either (a) strengthen `StepRel` to Codex's Q4
  form — a parent→child divisor injection + equality on unchanged divisors + a distinguished
  updated/new divisor with the case-specific exponent + an exact `support`-propagation equation (a
  typed `stepUpdate` with child root ledger `= stepUpdate n e` is the clean shape); OR (b) downscope
  the `case_step_invariant` name/docstring to state what it proves (a per-edge existence consistency
  check, necessary but not sufficient for faithfulness) and record that the bundle does not certify
  tree-fidelity. Since the restructure's founding WHY (compass fork 7) was "pin the parent-referencing
  merge", (a) matches that intent; but neither blocks the finiteness certificate. Codex notes the clean
  architectural split: an `AnalyticCertificate` (what the driver consumes) + a stronger
  `FaithfulAoyagiResolution`.

## Findings 1–7 disposition (repaired)

- **1 (StepRel reads `e.child`) — FIXED for soundness.** `StepRel` (`EngineObligations.lean:95`) now
  reads the child root (`rootNumDiv`/`rootDivExp`/`rootCleared`) + `e.subst.runLen`: case-2 pins the
  CHILD divisor exponent `= resRows·resCols`; case-1(1) pins the merge `child = parent divExp +
  runLen·resCols`; case-1(2) pins the `cleared` advance. The `{0,11,99}` counterexample is killed
  (`mergeEdge_stepRel`: child `= 11 = 5+2·3`, clean-three; `stepRel_rejects_mismatched_case2`: a child
  exponent `2 ≠ 4` is rejected, clean-three). Residual = the fidelity-scope item above.
- **2a (resRank fold) — FIXED.** `terminalExponents` (`ResolutionTree.lean:234`) folds every positive
  `resRank`; `region_glue`'s `hrat` and `exponent_ledger_bridge` now cover `resRank/2`, pinning
  `minAdm ≤ resRank` as a bundle obligation (the elder-ratified form).
- **2b (transport factorization / ψ inverse constructibility) — FIXED; fallback correctly NOT
  triggered.** `LeafJacobian` (`EngineObligations.lean:63`) is now `chartMap = ψ ∘ β` with `β` the
  explicit monomial blow-up (`|det Dβ| = ∏ |u|^{divExp−1}`, only `HasFDerivAt` — no inverse required,
  integrated directly) and `ψ` a bounded-unit local diffeo carrying FULL inverse data (`ψsymm` + both
  identities + `HasFDerivAt` + `|det Dψ| ∈ [lo,hi]`) on `β '' srcBox`. This separates the singular
  factor (β) from the bounded-unit factor (ψ) — the sound route. I verified ψ's inverse data IS
  constructible on the exceptional fibre: the singular vanishing is entirely in β; ψ is the regular
  gauge/shear (Q,P-reduction) part, invertible everywhere including over `β '' {exceptional}`, so its
  bounded-unit inverse data is genuine, not relocated into a fresh opaque hole. The transport lemma's
  hypotheses fit ψ. (Analytic sufficiency of `region_glue` remains an inference until that sorried hole
  is filled — expected; it is a sanctioned hole.)
- **3 (live attainment) — FIXED for the empty-phantom; residual on measure-zero.**
  `CanonicalResolution` gains a 6th conjunct + `exponent_ledger_liveAttainment` (`:186`): `minAdm` is a
  divisor exponent of a leaf with `srcBox.Nonempty`. This kills the strictly-empty phantom. RESIDUAL:
  `Nonempty` is weaker than nonempty-*interior* / cover-participation — a measure-zero (e.g. singleton)
  `srcBox` attaining-leaf still satisfies it while contributing `chartMap '' {pt}` (measure zero) to
  the cover. This does NOT break finiteness (a measure-zero leaf does not bind the integral, and the
  exponent hooks keep the threshold at `½·minAdm`), so it is a precision note on the *attainment/
  tightness* story, not a blocker. Optional: `(interior l.srcBox).Nonempty`.
- **4 (`divProfile ∈ Adm`) — FIXED for soundness.** `IsFullMonomialization` (`:110`) now requires
  `divProfile k ∈ Adm M` (witness discharges `(0,0) ∈ Adm (2,2,4)` by `decide`). Closes the impossible
  -profile relabelling. Residual (fidelity nicety, not soundness): a DIFFERENT admissible profile with
  the same `Mval` could still relabel a leaf — but `divExp` remains a genuine admissible codimension
  `≥ minAdm`, so finiteness is unaffected.
- **5 (coord injectivity/disjointness) — FIXED.** `ChartBridge` (`:78`) requires
  `Function.Injective divCoord`, `Function.Injective resCoord`, `Disjoint` ranges.
- **6 (a.e.-injectivity) — FIXED.** `ChartBridge` replaces full `InjOn` with `∃ N, volume N = 0 ∧
  InjOn chartMap (srcBox \ N)` — correct for blow-up charts (not injective on the exceptional fibre).
- **7 (Jacobian sign) — FIXED.** `LeafJacobian`'s `β` uses `∏ |paramsEquivFlat …|^{divExp−1}`
  (abs-value); `LeafPullback` uses `^2` (sign-safe).

## Minors 8–12

- **8 (decorative fields) — ADDRESSED (docstrings).** `jacDivCount`/`jacPow`/`bExp` marked
  CONSTRUCTION-SIDE BOOKKEEPING; `support` marked read-by-`StepRel`-case-2. Accurate, with the caveat
  (from the judgment flag) that "read by `StepRel`" is not finiteness-load-bearing.
- **9 (line-96 strike) — FIXED.** `necessity-and-encodings.md:96` is now struck (`~~…~~`) and annotated
  "STRUCK, FALSE" in place.
- **10 (banned wording) — FIXED.** "load-bearing" removed; the full banned-list grep over `Engine/`
  returns NONE.
- **11 (toy root step) — FIXED.** `rootNode224` is now a REAL Case-2 step (`resRows=resCols=2`,
  `divExp=4`); `rootEdge224_stepRel` discharges the strengthened `StepRel` against the real child.
- **12 (long lines) — FIXED** (`14927ae91`).

## Verification evidence
- **Own forced `#print axioms`** (scratch over fresh oleans, exit 0, no errors):
  `canonicalResolution224_arithmetic` → `[propext, Classical.choice, Quot.sound]` (clean-three, WITH
  the new 5th live-attainment conjunct); `canonicalResolution224` / `engine_box_threshold_finite` /
  `exponent_ledger_liveAttainment` → `+ sorryAx` (expected); the three in-file witnesses
  `mergeEdge_stepRel` / `stepRel_rejects_mismatched_case2` / `mixedCaseTree_records_both` →
  clean-three (real theorems).
- **Circularity** still clean (only the docstring guard "WITHOUT `rlct = c*`"); the two engine holes
  are exactly `monomialization_terminates` + `region_glue` (map-tagged) + the documented `(2,2,4)`
  forecast conjunct.
- **Batteries re-run:** `g-case11-merge.py` (merge formula `5+2·3=11`; childless admits `[0,11,99]`,
  child-reading admits `[11]` — child must be read) and `g-fake-chartmap-reject.py` (identity/fake
  `chartMap` fails `LeafPullback` since order>2 non-Morse `F` has no dividing coordinate) both
  reproduce their headlines.

---

# RUNG-1 SPOT-CHECK — `stepUpdate` / faithful `StepRel` re-point (`5b0966b11`, merged at `f0b691cbb`)

**Reviewer:** same seat, rev2 (merged the rung-1 tip after a stale-fetch reconciliation — the earlier
`origin/expedition/aoyagi-engine` tip `d5f9b7ece` predated the rung-1 merge; re-fetched to `f0b691cbb`
which contains `5b0966b11`). Scoped change class: `stepUpdate` + faithful `StepRel` + the two
`¬`-theorems + witnesses + footprints. Own forced `#print axioms` + two decorrelated Codex consults
(`steprel-existential`, `mergeidx-oob`). The ChartBridge srcBox strengthening is NOT in this HEAD
(grep-confirmed) — out of scope, as directed.

## VERDICT: scoped-VALIDATE-WITH-CHANGES

The faithful `StepRel := rootLedger e.child = stepUpdate n e.case e.subst` (`EngineObligations.lean:129`)
is the right shape and a genuine upgrade — it retires the existential form and makes the disappearing
-divisor schema fail. But `stepUpdate` carries **two fidelity defects** (one paper-verified) that should
land before `case-step-lemmas` flips to genuinely *faithful*. Neither affects finiteness soundness
(`StepRel` is off the driver's critical path — the r2 VALIDATE stands).

## Spot-check items

- **(1) Disappearing-divisor schema now FAILS — PASS.** `StepRel` is a FULL `RootLedger` structural
  equality (`numDiv`, `divExp`, `divTilde`, `cleared`). `dummyDivisor_not_stepRel` (extra divisor) and
  `vanishingDivisor_not_stepRel` (missing divisor) are real `¬`-theorems (own `#print`: clean-three),
  rejecting via `numDiv`. **Content-rejection for free — confirmed:** a `numDiv`-preserving corruption
  (right count, shuffled/wrong `divExp`/`divTilde`/`cleared`) also fails, because `RootLedger` equality
  is componentwise — the landed two theorems exercise the `numDiv` route, the `divExp`/`divTilde`/
  `cleared` routes are the same equality (Codex Q3, verified independently; a `numDiv`-preserving,
  exponent-wrong child cannot satisfy the equality). The witnesses are genuinely `rfl`-class (leaf
  ledgers are DEFINITIONALLY `stepUpdate` projections).
- **(2) mergeIdx out-of-range = CHANGE (fidelity, Q1).** `σ.mergeIdx : ℕ` (raw, out-of-range = no-op).
  `stepUpdate` case-1(1) with `mergeIdx ≥ numDiv` is the IDENTITY, so `StepRel` ACCEPTS a no-op
  "case-1(1)" (mechanically confirmed: an out-of-range edge whose child ledger equals the parent's is
  `StepRel` by `rfl`, child `divExp` stays `5` not the faithful `11`); case-1(2) out-of-range drops the
  `divExp(mergeIdx)` base (new pivot exponent `= runLen·resCols`). "The construction never emits it" is
  unencoded intent — it cannot back a *faithful* certificate (Codex: "block the rung-1 fidelity
  spot-check"). Sound for finiteness (driver never consumes `StepRel`). **FIX (Codex minimal):** a
  `StepApplicable` guard conjoined into `StepRel` — `mergeIdx < n.numDiv` for case11/case12, `True` for
  case2 (case2 must allow `numDiv = 0`, as the base witness `rootNode224` shows). Typed `Fin n.numDiv`
  is stronger but a larger carrier change (`Edge`/`ChartSubst` don't depend on `n`) — defer to a planned
  redesign.
- **(3) support scope-out — HONEST, minor staleness.** `stepUpdate`/`RootLedger` docstrings state
  support propagation is STOP-AND-SURFACEd (not modelled; deferred to a `genDivExp` rung) — honest, no
  overclaim. Minor: the `StepRel` docstring calls it "the faithful per-step transition relation" without
  the "ledger core, NOT support" qualifier inline; and the `case-step-lemmas` map note (`claims.yaml`)
  still describes the RETIRED existential form ("per-edge existence-CONSISTENCY check (existential child
  index)") — update it to the landed `rootLedger child = stepUpdate parent` form.
- **(4) footprints — PASS (own forced `#print`).** `canonicalResolution224_arithmetic` clean-three
  `[propext, Classical.choice, Quot.sound]`; `canonicalResolution224` + `engine_box_threshold_finite`
  `+ sorryAx`; `rootEdge224_stepRel`, `mergeEdge_stepRel`, `dummyDivisor_not_stepRel`,
  `vanishingDivisor_not_stepRel`, `mixedCaseTree_records_both` all clean-three.

## NEW finding beyond the four items

- **(Q4) case-2 `cleared` advance is WRONG — CHANGE (fidelity, paper-verified).** `stepUpdate` case-2
  sets `cleared := n.cleared + n.resRows` (`EngineObligations.lean:123`), but the paper advances `J` by
  **one** per case-2 step: extracted-text:1499 "the inductive statement **with `J` increased by one**";
  worked.tex:517-518 "Regular Q,P then reduce `D_J'' → diag(1, D_{J+1})`, advancing `J` (or `S`)". The
  full block is cleared over MULTIPLE case-2 steps (each `+1`), not one macro `+resRows` step. The
  current formula agrees only when `resRows = 1`. This is the architect's own flagged page-reading
  choice — **adjudicated: use `cleared := n.cleared + 1`.** (Codex Q4 independently; verified against the
  source.) case-1(1) `cleared` unchanged and case-1(2) `+1` are both correct.

## Deferred (elder ratification, not adjudicable from the reproduction)

- **case-1(2) new-pivot exponent** (`divExp(mergeIdx) + runLen·resCols`): the architect flagged it;
  worked.tex:761-762 says the "full Case-1(2) increment bookkeeping is referenced to the images" and it
  belongs to the ρ_order (θ) computation, **off the RLCT critical path**. Not verifiable from the
  available reproduction — defer to elder ratification (as intended). Not a finiteness concern.

**Summary for the flip:** finiteness soundness intact (r2 VALIDATE stands). For `case-step-lemmas` to
flip to genuinely faithful: land Q1 (`StepApplicable` guard) + Q4 (`cleared += 1`), ratify the
case-1(2) exponent, and refresh the `StepRel` docstring / `claims.yaml` note. All cheap; none block the
finiteness certificate or the region-glue tide.

---

# CONSOLIDATED PASS — fix commit `6d0956655` + ChartBridge strengthening `f8a5933d9` (merged `1c7a1fa1a`)

**Reviewer:** same seat, rev2 (merged the fix + strengthening). Items (a)–(e) from the scope
extension. Own forced `#print axioms` on the post-fix state (footprint authority for this pass) +
paper cross-check + one probe.

## VERDICT: scoped-VALIDATE with ONE follow-up change (case-1(2) eligibility)

The rung-1 changes are sound and the two prior fidelity findings are FIXED. One residual of the
eligibility fix remains: it guards case-1(1) but not case-1(2). Fidelity-class (StepRel is off the
finiteness critical path — the certificate is sound), cheap, same shape as the (now-closed) case11
gap. Recommend landing it before `case-step-lemmas` flips to genuinely faithful; it does not block
rung 2 structurally.

## Items

- **(a) ChartBridge strengthening — PASS.** `ChartBridge`'s per-leaf clause gains `MeasurableSet
  l.srcBox ∧ ∃ R>0, l.srcBox ⊆ paramsEquivFlat⁻¹' (cubeBox (flatDim M) R)` (bounded-in-flat-cube;
  `EngineObligations.lean:87-88`) — closes the r1 srcBox residual (measurable + bounded ⇒ the
  monomial/radial reads run over a compact box). The 224 witness's `leaf224.srcBox` is now
  `paramsEquivFlat⁻¹' (cubeBox (flatDim M224) 1)` (was `Set.univ`), `Nonempty` reproved via
  `Set.Nonempty.preimage ⟨0,…⟩ + surjectivity`. The footprint (below) confirms this Nonempty proof
  keeps the arithmetic bank piece clean-three.
- **(b) case-2 `cleared += 1` — PASS (Q4 fixed).** `stepUpdate` case2 is `cleared := n.cleared + 1`
  (`EngineObligations.lean:132`); docstring carries the elder's dropped-divisor justification
  (successive Case-2 steps, each a distinct pivot of strictly smaller exponent
  `(M(S)−J−i)(M^{(S+1)}−J−i)`; a `+= resRows` fast-forward drops them). Faithful to p.21.
- **(c) eligibility conjunct — PASS for case11; ONE CHANGE for case12.**
  `StepRel := rootLedger e.child = stepUpdate n e.case e.subst ∧ (e.case = case11 → ∃ h : mergeIdx <
  n.numDiv, n.divTilde ⟨mergeIdx,h⟩ = n.cleared + runLen)` (`:142-146`). The case11 clause faithfully
  encodes p.15 (`t̃_{s,k} = J + J₁`: in-range + `divTilde(mergeIdx) = cleared + runLen`), closing the
  no-op-acceptance gap. Witnesses survive: `mergeNode.divTilde = fun _ => 2` (`= cleared 0 + runLen
  2`), `mergeEdge_stepRel = ⟨rfl, fun _ => ⟨by decide, by decide⟩⟩`; `rootEdge224_stepRel = ⟨rfl, fun
  h => by simp [Edge.case] at h⟩` (vacuous case11 branch for a case2 edge); `dummyDivisor_/
  vanishingDivisor_not_stepRel` reject via `h.1` (the ledger conjunct). **CHANGE:** the conjunct
  guards case11 ONLY, but `stepUpdate` **case12** also reads `divExp(σ.mergeIdx)` (`:124`, dite
  -defaults to 0) as the split divisor's base exponent (`M_{sk} + J₁·resCols`, p.17). With no case12
  guard, an out-of-range case12 `mergeIdx` drops the base (new pivot exp `= runLen·resCols`) and
  `StepRel` ACCEPTS it — **mechanically confirmed** (`oobSplit_stepRel_accepted` proved by
  `⟨rfl, fun h => simp [Edge.case] at h⟩`; the new pivot exp is `6 = 0+2·3`, not the faithful
  `11 = 5+2·3`). Since case-1(1)/1(2) are the two charts of the SAME case-1 blow-up on `u_{s,k}`
  (`t̃ = J+J₁`), case12 should carry the identical eligibility; at minimum the in-range guard (it reads
  `divExp(mergeIdx)`). This is NOT the "strict superset of StepApplicable" it was reported as —
  StepApplicable guarded case11 AND case12; the landed conjunct dropped case12. Fix: extend to
  `(e.case = case11 ∨ e.case = case12) → ∃ h : mergeIdx < n.numDiv, n.divTilde ⟨mergeIdx,h⟩ =
  n.cleared + runLen` (elder to page-confirm case12 carries the same `t̃` precondition; the in-range
  half is required regardless).
- **(d) docstrings — PASS.** `StepRel` docstring now carries the inline scope-qualifier ("FAITHFUL for
  the exponent/clearing ledger CORE … NOT modelled here: support propagation … and layer-`S`
  advancement"). `region_glue` docstring de-staled to the area-formula route ("the Mathlib area
  formula on the `ψ ∘ β` chart (consuming the upper det bound; elder-ratified fork-8 revision) + the
  scaling-bridge globalization"). The `case-step-lemmas` `claims.yaml` staleness was fixed by the
  controller.
- **(e) footprints — PASS (own forced `#print`, post-fix).** `canonicalResolution224_arithmetic` →
  `[propext, Classical.choice, Quot.sound]` (clean-three, incl. the case-2 fix, the eligibility
  conjunct, and the cube-preimage `Nonempty` proof); `canonicalResolution224` +
  `engine_box_threshold_finite` → `+ sorryAx`; `rootEdge224_stepRel`, `mergeEdge_stepRel`,
  `dummyDivisor_not_stepRel`, `vanishingDivisor_not_stepRel` → clean-three.

**Summary:** case-2 (Q4) and the case11 no-op (Q1) are fixed; the strengthening is sound; footprints
hold. The one follow-up — extend the eligibility conjunct to case-1(2) — is a cheap fidelity residual
(same class as the case11 gap it mirrors), off the finiteness path. rung 2 may proceed; the case12
guard should land before the `case-step-lemmas` faithful-flip.
