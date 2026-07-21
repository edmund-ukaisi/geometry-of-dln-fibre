# Statement cards — thread 36 (leaf-fidelity), rung-C monument REIFICATION

Commit SHA: **pending this repair-round bake** (branch `expedition/aoyagi-engine-rung-c`, parent
`dc658a1bc`). Gate for this thread = **elaboration + cone-shape, NOT sorry-free** (a typed/sorried/wired
forecast ladder). Bump the SHA at controller integration.

---

## FIDELITY: BROKEN (2026-07-21) → REPAIRED except L7-bridge-gated (2026-07-21, same day)

**History.** The first render was mechanically green but content-BROKEN — L3/L4/L6/L7 false-as-stated,
L5/L8 under-claims (rev-rungc-fidelity, decorrelated Codex + machine-checked; single root cause: the
construction's FIXED structural fields left FREE in the leaf hypotheses — `ed.center`, `GeoAtlasData.jac`,
the chart↔path identification — with guards too weak to exclude the bad instances). The elder re-statement
+ two follow fixes repaired all but the coordinate axis:

- **L3/L4 — FIXED (elder re-statement).** The leaves now carry `FoldStepInvAt ed.center p`, whose
  `Deg1SupportedOn (foldResid p) C` conjunct forces the residual **center-exact degree-1** (each monomial
  EXACTLY one center factor; Core `Deg1SupportedOn` = `SupportedOn` + coefficients `IgnoresCoords` the
  center, strictly subsuming ideal-membership). Degree-1 is a CARRIED invariant, NOT deferrable content;
  the (A′) "no-obligation" framing is retracted. The size-axis witness (`d=![1,2,1]`, `center={0,1,2}`)
  DIES: `u₀u₂` has no center-disjoint center-linear form. `FoldStepInv := ∃ C, FoldStepInvAt C p`.
- **L6 — FIXED (FIX 1).** `leafPath_chartGeometry` now takes `hfold : FoldProduced d e atlas`; the
  Jacobian tie is `FoldProduced.hjac_tie` (`atlas.jac = ∑ steps.jexp`) + `GeoStep.hσ_jac`, so
  `chart.jac = atlas.jac c` is dischargeable. The bare-atlas false-witness is excluded.
- **L5 — STRENGTHENED (FIX 2).** L5 now emits `FoldProduced ∧ FoldRealizes` (single conjunction). New
  `FoldRealizes := ∃ pathOf leafOf, (∀ c, gmap c = foldG (pathOf c) ∧ (pathOf c).reachesLeaf (leafOf c))
  ∧ (leafOf surjective onto tree leaves)`, with `reachesLeaf` = per-edge structural-branch-membership
  against `conOracle`'s combinatorial dispatch (`ecase`/`child`, bridge-free) + terminal-leaf match. The
  **path-axis** collision witness (all charts one branch) DIES via surjectivity (⟹ `leafOf` constant ⟹
  not surjective once the tree branches). Root non-vacuity: `reachesLeaf root = False` for `0<N`.
  *Deviation from spec (accepted):* `FoldRealizes` is self-contained (its own `leafOf`) to avoid touching
  the elder-locked `FoldProduced`; its `leafOf` and `FoldProduced`'s need not coincide — a coupling the
  `canonCenter` follow-round will add (documented at the def).
- **L7 — HONEST BRIDGE-GATED (not fixed, correctly labelled).** `leafPath_compactCover` takes both
  `hfold`/`hreal` and concludes the ball-cover, but the FULL cover is a COORDINATE-level fact (which
  coordinate each chart blows up) that neither ℕ-valued `FoldProduced` nor the combinatorial `FoldRealizes`
  pins. The **coordinate-axis** witness (every `gmap c` on one coordinate `x`, `y`-directions uncovered)
  passes both hypotheses yet falsifies the `⋃` — so L7 is HONEST **false-as-stated-pending-bridge**. It
  closes when the Engine↔Aoyagi coordinate bridge lands. Decorrelated check (reviewer + Codex) confirmed:
  the counterexample is real, and L7 is bridge-dependent under the current (free-`GeoAtlasData` +
  ℕ-exponent-`FoldProduced`) architecture. The (c)-road — **`canonCenter`** (the paper's DLN-side slot
  bookkeeping from `(S,J,mergeIdx,d)`, NOT the engine `divCoord`) — had its rollover slot-transfer
  checkpoint return **STABLE**, so it is the scheduled follow-round that lifts L7 bridge-free.

**MONUMENT BRIDGE-DEPENDENCE.** `exists_coreResolution_via_monument` closes bridge-free EXCEPT L7's
coordinate-coverage; the driver is "done modulo the `canonCenter` follow-round." L7 is the ONLY
bridge-dependent leaf — nothing about it blocks the wall (L4), L3, L5's proof-content, L6, or L8.

**Severance taxonomy (COMPLETE — one exemplar per axis).** content (`Σw²`, kernel-refuted) / size
(`center={0,1,2}`, dies at `Deg1SupportedOn`) / path (all-charts-one-branch, dies at `FoldRealizes`
surjectivity) / coordinate (all-charts-one-coordinate, bridge-gated at L7). Each is a free-field
severance on a distinct axis; the guardrail is the elder line "every free field on a quantified structure
is its own severance axis — the audit is per-FIELD, never per-statement."

**FAITHFUL (verified):** L1 `principalInv_regionRepresents`; `terminal_bezout`; item-7 edge-analyticity;
Core `IgnoresCoords`/`Deg1SupportedOn` (sorry-free, bridge lemmas closed). L8 matches
`AtlasRealizesExponents` (Type 0). Mechanical re-gate at this bake: build green 8449; `#audit_blueprint`
both drivers rest on exactly the 8 leaves; `#print axioms` = `[propext, sorryAx, Classical.choice,
Quot.sound]`; cordon OK (0 axiom-viol, 0 native_decide, 27 blueprint sites).

Artefacts: Codex prompt/answer under `…/threads/36-leaf-fidelity/codex/`. The cards below record the
leaves AS RENDERED; this status banner supersedes their per-leaf annotations.

---

## Card 0 — the composition driver (SKELETON PROVED; leaves FORECAST)

> **Claim.** The full `exists_coreResolution` statement (the residual `LearningCoefficient` goal for
> `∑(coreGen d e)ᵢ²` at `0`, general monotone `d`, `0 < N`) is discharged by a composition that folds
> the 8 rung-C leaves and nothing else.
>
> - **Lean.** `DLNFibre.DLN.Aoyagi.exists_coreResolution_via_monument` (the full statement) and
>   `DLNFibre.DLN.Aoyagi.exists_atlasRealizesExponents` (the residual goal, general `d`), both
>   `@[blueprint]`, `lean/DLNFibre/DLN/Aoyagi/MonumentAtlas.lean` @ `27ef12c25`.
> - **Proved (the skeleton).** The driver body is `sorry`-free *modulo the leaves*: the reduction of
>   `exists_coreResolution` to exactly the 8 forecast leaves is real Lean, via the banked salvage
>   adapter `exists_hlb_hattain_of_exists_atlasRealizesExponents`. Verified by `#audit_blueprint`:
>   both drivers rest on EXACTLY the 8 leaves below (blueprint-internal — permitted), and
>   `#print axioms exists_coreResolution_via_monument = [propext, sorryAx, Classical.choice,
>   Quot.sound]` (the `sorryAx` is the leaf set; no unaccounted axiom, no `native_decide`).
> - **Assumed / Forecast.** the 8 leaves (Cards 1–8). Nothing else.
> - **Cited.** none new (rests on the banked adapter + Engine combinatorics, axiom-clean).
> - **Status.** Skeleton REIFIED (green, cone = 8) but **content BROKEN** — see the ⚠ FIDELITY REVIEW
>   banner above. The driver's REDUCTION to the 8 leaves is sound Lean; 4 of the 8 leaves it reduces to
>   are false-as-stated, so the driver cannot be discharged until they are re-stated (elder call routed).

---

## The 8 forecast leaves (each `@[blueprint]`, `-- map:`-tagged, sorried)

**L1 — `Core.Aoyagi.principalInv_regionRepresents`** (`PrincipalInv.lean`). A terminal `PrincipalInv`
(divisibility + Bézout, `M'=1`) on an open region `V` yields the two `RegionRepresents` inclusions
(`fun i ↦ Fᵢ∘g` vs the `Fin 1` monomial family `fun _ ↦ b`), region-quantified throughout — no germ.
*Kill:* fails if `V` is not open / not `∋0`; the `Fin 1` repackaging is the `Chart.hideal_fwd/bwd` shape.

**`Core.Aoyagi.terminal_bezout : TerminalBezout`** (`PrincipalInv.lean`). Bézout/principality is BORN at
the terminal node: the cleared pivot gives `(F i₀∘g) = b·unit`, `unit 0 ≠ 0`, inverting on the open
`V' = V ∩ {unit≠0}` to upgrade `StepInv` (divisibility) to terminal `PrincipalInv`. `unit⁻¹`-continuity
is `ContinuousOn.inv₀` (named, NOT assumed). Region-shrinks to `V' ∋ 0`. *Kill:* the constant-family
S3 refute (`b=∏u` vanishes at 0 while `unit 0 ≠ 0` — no tension) dies here.

**L3 — `case2_preserves_stepInv`** and **L4 — `case1_preserves_stepInv`** (`MonumentAtlas.lean`). The two
one-step preservations: a case-2 / case-1 edge carries the folded `FoldStepInv` (divisibility only) from
parent to child state, with the δ-conditional ideal-membership `hsupp` (`edgeδ = true → SupportedOn
(foldResid …) center region`). Edge-indexed + state-bound to the DEFINED `foldState` (not a free `∀`).
**L4 is THE WALL** — the single frontier leaf. *Kill:* the free-center / free-state refutes die by the
FoldStepInv definitional binding; the Σw² Case-2 refute is kernel-refuted; Case-1 is shear-rescued
(UNRESOLVED at pen-and-paper, hence the wall). The (A′) degree-1-preservation obligation lives HERE
(the δ=1 `foldResid` substitution stand-in's re-factoring content), not as a separate item.

**L5 — `leaf_stepInv_of_path`** (`MonumentAtlas.lean`). Folding L3/L4 + `terminal_bezout` along a real
`buildTree` path produces the atlas + per-chart terminal `PrincipalInv` + the `FoldProduced`
provenance record. *Kill:* the ∀-atlas refutes die by anchoring to `buildTree d (conOracle d) conRoot`
via `FoldProduced` (a bare atlas carries no provenance).

**L6 — `leafPath_chartGeometry`** (`MonumentAtlas.lean`). Each provenance-carried leaf assembles a
certified `Chart`: analytic `gmap` (rides `PathAtoms.analyticOnNhd_pathMap` + the edge-level
`analyticOnNhd_stepMap`), Jacobian read-off, and — **L6 HARD LOCK** — `Chart.nbhd` = the
`terminal_bezout`-shrunk `V′`, never `univ`. *Kill:* the univ-nbhd overclaim is gate-locked out.

**L7 — `leafPath_compactCover`** (`MonumentAtlas.lean`). The provenance-indexed charts give the full
compact cover (σ-provenance inclusion form). *Kill:* the ∀-atlas cover refute dies by σ-indexing.

**L8 — `leafPath_realizesExponents`** (`MonumentAtlas.lean`). The folded atlas realizes the tree's
terminal exponents (`AtlasRealizesExponents`), generalizing the LANDED `d=![1,2]` match to all `d`.
*Kill:* must match the landed d12 shape (Type 0, not Type u — a universe-mismatch masks as a whnf
timeout otherwise).

---

## Reification conditions met (this thread's obligation)

- Region-quantifiers throughout; **no germ-at-0** anywhere.
- Leaf-6 shear∘blow-up shape: `|det Dσ|` a pure `|S|`-center monomial, **unit ≡ 1**.
- Leaf-5 fold inside the C1 import boundary (no `Geo*`/`Canonical*` re-entry).
- **`M'=1`** compression visible (the `Fin 1` monomial family).
- Edge-indexing + `FoldProduced` provenance (the closing principle: every fold-sourced `∀` is
  edge/reachability-indexed or provenance-carried).
- δ-conditional **ideal-membership** `SupportedOn` (uniform on case-1 AND case-2).
- **stepMap = B∘S** (`blockBlowupMap center pivot ∘ edgeShear`, blow-up outermost, per thread-34).
- **Item 7** (edge-level analyticity): `hshear_analytic` field + `analyticOnNhd_edgeShear` /
  `analyticOnNhd_stepMap` / `continuous_stepMap` (unconditional). foldG-analyticity DROPPED (FALSE for
  proof-free `TreePath`); no `ShearsAnalytic` predicate.
- **(A′)**: the δ=1 `foldResid` substitution stands; degree-1-preservation = L3/L4 re-factoring
  content (anchor (v) = case11 (3,3,4)); (A″) representation redesign NOT taken.

## Deferred / next-expedition runway

- The 8 leaf PROOFS (L4 the wall). This thread reifies STATEMENTS only.
- `RLCT.flatDim` (card) ↔ `Aoyagi.flatDim` (sum) coordinate bridge (the FoldProduced divCoord tie is
  a branch-length / `bindingAxes.card = numDiv` tie; the exponent-coordinate bridge is runway).
