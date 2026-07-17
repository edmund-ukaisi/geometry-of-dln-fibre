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
