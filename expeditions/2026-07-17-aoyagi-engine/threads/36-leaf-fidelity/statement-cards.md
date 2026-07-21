# Statement cards — thread 36 (leaf-fidelity), rung-C monument REIFICATION

Commit SHA: **`27ef12c25`** (branch `expedition/aoyagi-engine-rung-c`, parent `3b03fe375`).
Gate for this thread = **elaboration + cone-shape, NOT sorry-free** (a typed/sorried/wired forecast
ladder). Bump the SHA at controller integration.

---

## ⚠ FIDELITY REVIEW — BROKEN (rev-rungc-fidelity, 2026-07-21; decorrelated Codex + machine-checked)

The MECHANICAL gate passes (build green 8449; `#audit_blueprint` both drivers rest on exactly the 8
leaves; `#print axioms` = `[propext, sorryAx, Classical.choice, Quot.sound]`; cordon OK). The CONTENT
does not: **L3, L4, L6, L7 are FALSE-AS-STATED**; L5, L8 are under-claims. Independently re-derived by
the architect (StepInv divisor `= b·resid`; `TreeEdge.center` is a FREE field; `hsupp` = ideal
membership is monotone in the center) and machine-checked against the real `blockBlowupMap`/
`blockBlowupCoordQuot`.

**Root cause (single).** Structural fields the construction FIXES are left FREE/unpinned in the leaf
hypotheses, and the guarding hypotheses are too weak to exclude the bad instances:
- **L3/L4** — `ed.center` free; `hsupp` = `SupportedOn` (ideal membership: each residual monomial has
  ≥1 center factor) is MONOTONE in the center. Witness `N=2`, `d=![1,2,1]` (`coreGen 0 = u₀u₂+u₁u₃`),
  `center={0,1,2}`, `pivot=0`, `shearφ=0`: `hsupp`+`hcase`+`hinv` all hold, but at `u=(2,1,1,-1)`
  `(F∘foldG)=u₀²u₂+u₀u₁u₃=2` while `foldB·foldResid=u₀(u₂+u₁u₃)=0` — divisor clause unsatisfiable. The
  δ=1 substitution equals the strict transform only under **center-degree-1** (each monomial EXACTLY one
  center factor); ideal membership admits the over-large `{0,1,2}`. **(A′) is falsified: degree-1 is a
  MISSING HYPOTHESIS, not deferrable proof content.**
- **L6** — `GeoAtlasData.jac` free, not tied to `gmap`'s actual Jacobian; L6 takes a bare atlas (no
  `FoldProduced`), so `chart.hjac` (`|jacDet gmap| = jacWeight(jac)·|unit|`) is unsatisfiable for a
  mismatched `jac`. L6 HARD LOCK (`nbhd ≠ univ`) is a render-time check, NOT a statement property.
- **L7** — `FoldProduced` has NO chart-image coverage clause; a single-pivot `blockBlowupMap` atlas
  satisfies every clause yet its charts' images miss a ball about 0 → no compact ball-cover.

**Repair (elder re-statement call — ROUTED, leaves HELD, statements unchanged pending ruling):**
strengthen `hsupp` to center-exact degree-1 (`resid_j = ∑_{i∈center} c_{ji}·u_i`, coeffs
center-independent) OR pin `ed.center` to the construction's layer center; add `FoldProduced` (or the
explicit `jac = ∑ steps.jexp` tie) to L6 and a coverage clause to `FoldProduced` for L7. The coordinate
bridge (thought deferrable) is NOT deferrable for L3/L4/L6/L7. **The composition intent SURVIVES** — L5
only ever supplies layer centers / real charts; the leaves are OVER-GENERAL, not a dead route.

**FAITHFUL (verified):** L1 `principalInv_regionRepresents`; `terminal_bezout`; item-7 edge-analyticity
(`analyticOnNhd_edgeShear`/`_stepMap`/`continuous_stepMap` true + unconditional; dropping foldG-analyticity
leaves no gap). L8 matches `AtlasRealizesExponents` (Type 0, no universe mask) but is a re-read of
`FoldProduced`, not the exponent-realization content itself.

Artefacts: Codex prompt/answer under `…/threads/36-leaf-fidelity/codex/fidelity-{prompt,answer}.md`.
The cards below record the leaves AS RENDERED (pre-repair); the ⚠ status supersedes their "kill"/
"faithful" annotations for L3/L4/L6/L7.

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
