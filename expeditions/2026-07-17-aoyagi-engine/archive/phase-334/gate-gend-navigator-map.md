# Navigator map — the route-P general-`d` gate (position + ladder + #114/#115 reconciliation)

Navigator office (position + planning; propose-never-act; a MAP, not a build). Expedition
2026-07-17-aoyagi-engine. Convened 2026-07-25 for the general-`d` gate the controller opens once the
(3,3,4) route-P instance lands verified.

**Two-channel evidence.** Every claim below is grounded in BOTH the code/git (read in the routeP
worktree) AND the docs (charter / BUILD-STATE / next-build-render / ideal-route-full-render), or is
marked single-source. Charter read FIRST; drift / hard-part-avoidance / contract-fit run against §0–§3.

**What I read (code):** `LearningCoefficient.lean:230-334` (the `:311` seam), `RecursionAdapter.lean`
(the seam + `AtlasRealizesExponents`), `Corank2FaithfulComposite.lean` (the crux + `flat(Pmat)` hideal),
`Corank2CoreGenWrap.lean` (WIP, untracked), `ConjResolution.lean` (banked transport),
`Corank2MaintenanceProto.lean` (general L-B step), `ProductResolution.lean:40-219` (`Chart`/`Resolution`
structs), `Engine.lean` (value roots), import graphs of the Geo*/Monument cluster. **(docs):** charter,
BUILD-STATE, next-build-render, render §L-C/L-D/L-E + SEAM-CHECK (1240-1282).

---

## Position — where the (3,3,4) instance actually is

- **Landed + committed (`af25db69b`):** `Corank2FaithfulComposite` — the faithful (3,3,4) composite chart
  `gFaithful : ℝ²¹→ℝ²¹`, `peeled_comp_gFaithful` (the radial crux, sorry-free), two-sided
  `hideal_faithful_fwd/_bwd` at the **`flat(Pmat)` product-entry level**. `MaintenanceProto`
  (general `n/D` L-B step), `TerminalProto` (L-C), `HidealProto` (L-A block-elim) all present.
- **In-flight, UNTRACKED, INCOMPLETE (#131):** `Corank2CoreGenWrap.lean` — has `eWrap`/`mult_eWrap`,
  `sigmaPiv`/`gWrap`/`mult_gWrap_entry`, `bexpWrap`/`monomialFam_bexpWrap`; but the promised
  `coreGen_comp_gWrap` (`coreGen∘gWrap = c₁₁·Pmat∘gFaithful`) and the **lifted** two-sided
  `⟨coreGen∘gWrap⟩=⟨c₁₁·E⟩` are **not yet written** (sorry-free only because the assembly theorems are
  absent). This is the imminent rung.
- **Pending (#130):** package the (3,3,4) content into a full `Chart`/`Resolution` + `AtlasRealizesExponents`.

**Gate calibration (flag).** The general-`d` gate's own DE-RISK(a) terms (charter §1.B) are "`hideal_fwd`+
`hideal_bwd` dom-wide + **realization at (3,3,4)** + **full-fan cover atom**, green-BOTH." Only the
`hideal` half is landed. The instance-verified bar the general-`d` build waits on therefore includes
**#131 (coreGen-wrap) + #130 (a full (3,3,4) `Resolution` + realization + cover atom)** — and at (3,3,4)
the `jac`/`hjac`, `hg_inj`/`hexcep_null`, `dom`/`hcover`, and `AtlasRealizesExponents` are **un-started**.
Do not convene the general-`d` gate on the `flat(Pmat)` hideal alone.

---

## Deliverable A — the route-P general-`d` ladder

### Verdict on the controller's 5-rung hypothesis

The 5 rungs are a **faithful skeleton of the `hideal` half + transport + value-match**, and each named
rung is real. **But the list UNDER-COUNTS the residual.** It folds the non-`hideal` mandatory
`Chart`/`Resolution` fields — **L6 (`hjac`/`jac`/analyticity/injectivity)** and **L7 (`hcover`)** —
silently into "rung (5) value wiring." The render's own scope-calibration (ideal-route-full-render
1269-1282) is explicit that these are the residual's **true size**, that L6-for-coupled-leaves is
rendered-but-Lean-unbuilt, and that the **coupled `hcover` (L7 fan) is the single highest UN-PROBED
residual risk at corank≥2**. Framing them as "wiring" re-commits the charter §3 newest drift
(RENDER-VERIFIED ≠ LEAN-INHABITED; the coupled hardness MIGRATED to L7's `hcover`). **Make L6/L7
first-class rungs.** Corrected ladder = 9 rungs (0,1,2,3,4,5a,5b,5c,5d).

The seam this all feeds is genuine (verified, see Deliverable B): `Chart` (ProductResolution:62) mandates
`g, hg0, hg_cont, hg_analytic, hFmeas, dom+hdom_compact+hdom_zero, nbhd+hnbhd_open+hdom_sub,
excep+hexcep_meas+hexcep_null+hg_inj, M'+bexp+k₀+hchain+hbind+hunit_mult, jac+unit+hunit_cont+hunit_ne+hjac,
hideal_fwd, hideal_bwd`; `Resolution` adds `numCharts, charts, hne, U, hU, hcover`. Route P has so far
inhabited only `hideal_fwd/_bwd` (at flat-level).

### The corrected ordered ladder

| Rung | Obligation | (3,3,4) status | Class | Depends on |
|---|---|---|---|---|
| **0** | Complete the (3,3,4) instance to a full `Resolution` + `AtlasRealizesExponents` (#131 + #130) | in-flight/pending | prereq gate | — |
| **1** | General mult-flatten: `ℝ^flatDim ≃ₜ Tuple d` with `mult∘e = (∏C)ᵀ` (lift `eWrap`/`mult_eWrap`) | hand-built | detail-at-scale | — |
| **2** | General `hideal` spine over `buildTree`: L-A/L-B/L-C depth recursion (the fold-induction) | flat-level only | **large + risk** | 1 |
| **3** | General coreGen-wrap: pivot block-center blow-up `coreGen∘σ = c₁₁·∏C` + `⟨c₁₁·b₁⟩` scaling | WIP | detail-at-scale | 1,2 |
| **4** | ∀e `conjResolution` transport (eWrap-core → canonical-`e` core) | — | **BANKED (done)** | — |
| **5a** | `AtlasRealizesExponents`: `jac+1 ∈ tree.terminalExponents` (i) + hits `minAdm` (ii) | un-started | detail-at-scale | 2,5b |
| **5b** | **L6:** `hjac` (dom-wide `|det Dg|=jacWeight jac·unit`, unit≡1) + `jac` + analyticity + `hg_inj`/`hexcep_null` | un-started | detail-at-scale, **fidelity-sensitive** | 2 |
| **5c** | **L7:** `hcover` — coupled corank≥2 fan cover (route-a FULL fan) | un-started | **CARRIES RESIDUAL RISK (highest)** | — (encoding-independent) |
| **5d** | Assemble `∃ res, AtlasRealizesExponents` → feed `:308` route-agnostic seam | — | bookkeeping | 2,3,4,5a,5b,5c |

### Rung notes (verify/correct)

- **Rung 1 (VERIFY: detail-at-scale).** `coreReduction` (LearningCoefficient:245) accepts ANY
  measure-preserving origin-fixing `e`, so the value engine tolerates a custom layout flatten — the
  `eWrap` idiom is legitimate. But the (3,3,4) `eWrap`/`mult_eWrap` are `fin_cases`/`rfl` over 21 explicit
  coords; general-`d` needs the abstract transpose-flatten `A_ℓ = C_ℓᵀ`. Moderate.
- **Rung 2 (CORRECT the controller's label + FLAG the idiom-lift).** The controller calls this "the
  general buildTree COVER"; it is NOT the cover — the parenthetical (L-A/L-B/L-C over buildTree) is the
  **`hideal` spine / fold-induction** (render B1 + L-A/L-B/L-C). The cover is rung 5c. This is the
  substantial genuine build: the depth recursion (per-node Case 1/2, block/layer rollover, terminal) +
  the exponent ledger, composing the per-step mechanisms. **The per-step mechanisms are general and
  proven** (`MaintenanceProto.maintenance_step_two_sided` general `n/D`; `TerminalProto` via
  `terminal_bezout`); render-verified sound (rev-render + Codex), carrying render §8-R2's four guardrails
  (running-coordinate block; no `b'_p∤b'_i` row-mix; `bExp` from the ~t-formula; compose BOTH
  directions). **KEY RISK:** the (3,3,4) `hideal` proofs are `fin_cases <;> simp <;> ring` over explicit
  21-var matrices — **that idiom does not lift to general `d`.** General-`d` needs abstract symbolic
  composition (the protos' general-`n` form), a different proof technique. Instance-green ≠ built
  (charter GUARD-B). Largest single-rung labour; the long pole.
- **Rung 3 (VERIFY: detail-at-scale).** `blockBlowupMap` is general (`Core.Aoyagi.BlockBlowup`); the
  per-chart `c₁₁`-factor + `⟨c₁₁·b₁⟩` monomial-scaling is a uniform mechanism. (3,3,4) `sigmaPiv`/`gWrap`
  hand-built; general needs the general pivot-block blow-up + the ideal-scaling lemma. Moderate.
- **Rung 4 (VERIFY: DONE, load-bearing).** `ConjResolution` is sorry-free and general: `conjChart`/
  `conjResolution` transport `Resolution G 0` across a CLE `Φ` + reindex `ρ` to `Resolution (G(ρ·)∘Φ) 0`;
  `translateChart`/`translateResolution` move `x₀→0`. This is exactly the bridge from the eWrap-layout
  core (where route P builds the atlas) to `coreGen d e` for the canonical linear `e` that
  `exists_coreResolution` receives (both flattens linear ⟹ `Φ` linear). Ready to consume; off the
  critical path. One wiring check at assembly: the `ρ`/`Φ` between `eWrap` and the canonical flatten is a
  coordinate reindex (it is).
- **Rung 5a (VERIFY + FLAG dependency).** `AtlasRealizesExponents` reads `jac+1` on `bindingAxes (bexp k₀)`
  — the **Jacobian `h_d` exponents, NOT the `hideal`'s `bexp`.** So it depends on 5b supplying `jac`.
  Route P's (3,3,4) work built `bexp` (the b-monomial) but has not touched `jac`. The match itself is
  render L-D — "monotone order-accumulation induction over buildTree" (detail-at-scale), with `min = qipMin`
  the already-banked Object-D bridge.
- **Rung 5b (ADD — not in the controller list).** L6: the dom-wide Jacobian certificate + `jac` + the
  a.e.-injectivity. Rendered exact (unit≡1) but Lean-unbuilt for the coupled leaves general-`d`;
  fidelity-sensitive (the coupled-leaf `|det Dg|` monomial). Analyticity is easy (polynomial charts).
- **Rung 5c (ADD — the named highest risk).** L7 coupled `hcover`. The `LeafCoverTiling` box-inflation
  engine is banked (‑L7cover merged to trunk) and reusable; `GeneralGeoAtlas`'s box-geometry is for a
  **simpler single-term-shear object**. The FAITHFUL multi-term box-containment (OBL-1) was cleared only
  in a **python probe** (render §9), Lean-UNBUILT; and fan-completeness (OBL-2) forces the **FULL fan
  (route-a)**, not the col-pinned atlas (Codex exhibited a col-0-chart escape). Encoding-independent ⟹
  **parallelizable and to be front-loaded** (risk-free: needed under either spine outcome; elder gate ii
  = probe-before-commit).

### Critical path / parallelism / risk

- **Critical path:** Rung 0 → Rung 2 (spine, long pole) → 5a/5b (need spine + `jac`) → 3 → 5d.
- **Parallelize + front-load:** Rung 5c (`hcover`, encoding-independent, the risk pole — start it in
  parallel with rung 2, not after). Rung 1 (flatten infra) independent. Rung 4 done.
- **Detail-at-scale:** 1, 3, 5a, 5d. **Carry residual risk:** 2 (idiom-lift + fidelity), 5b
  (coupled-leaf Jacobian fidelity), **5c (coupled `hcover` — highest, un-probed in Lean).**

---

## Deliverable B — the #114/#115 reconciliation (survives vs superseded)

### The load-bearing survivor — the `:308` seam is ROUTE-AGNOSTIC (VERIFIED, both channels)

`exists_hlb_hattain_of_exists_atlasRealizesExponents` (RecursionAdapter:109) consumes
`hgeo : ∃ res : Resolution F 0, AtlasRealizesExponents d res` for **ANY** `F`/`res`, built however.
`exists_coreResolution:308` does `refine exists_hlb_hattain_of_exists_atlasRealizesExponents … ?_` and the
sole `:311` `sorry` supplies exactly that `∃`. So **route P plugs its ideal-route atlas into the SAME
seam** — this is #115's target interface and it survives route-agnostic. Confirmed by reading the adapter
(no geometric content; `hlb` via `minAdm_le_terminalExponents`, `hattain` via `o5_core_realized`) and
corroborated by the render's SEAM-CHECK (1240-1267).

### Survives route-agnostic (the backbone route P builds ON)

- **Combinatorial backbone:** `buildTree`, `minAdm`/`cCodim`/`qipMin`, `o5_core_realized`,
  `minAdm_le_terminalExponents` (`EngineConstruction` + `O5Realization`; clean-three). All ℕ-valued
  combinatorics over the tree — independent of how the atlas is built. `RecursionAdapter` imports ONLY
  these (via `O5Realization`/`MinAdmCCodim`), never a Geo*/Monument module. `AtlasRealizesExponents` is
  defined over the SAME `buildTree` (render seam-check point 2 — `hrealize` fires on o5's exact leaf).
- **Value engine + Chart vocabulary:** `ProductResolution` (`Chart`/`Resolution` structs;
  `two_mul_rlctAt_eq_divisorMin`, sorry-free) + `Engine` (`divisorMin_eq_cCodim`,
  `two_mul_rlctAt_eq_cCodim`, sorry-free — I confirmed no `sorry` in these files). These consume `Chart`'s
  `hideal_fwd/_bwd`/`hjac` fields — encoding-agnostic. This is the vocabulary route P inhabits.
- **`ConjResolution`** — banked transport (rung 4). Survives.

### #114 (L6+L7 mechanisms) — PARTIALLY survives, with a fidelity gap

The sorry-free Geo* MECHANISM modules — `GeneralGeoAtlas` (427L: box-cover + multi-step Jacobian unit≡1 +
fan), `GeometricAtlasD12`, `LeafCoverTiling` (box-inflation cover engine, banked/merged), `GeoCoverSpec`,
`GeoJacobianSpec`, `GeoInjFold`, `GeoFoldRegroup`, `GeoInvValWalk`, `GeoLeafLedger`, `L5FoldSpec`,
`ChartBridgeFaithful`, `FlatCubeLeaf`, `EngineDefs` — prove L6/L7 mechanisms but are **NECESSARY-
NOT-SUFFICIENT** (charter §3: they do NOT inhabit `hideal`). Under route P they are candidate **REUSE for
rungs 5b/5c** (`hjac`/`hcover`), **BUT for a SIMPLER single-term-shear object** (BUILD-STATE §CAVEAT); the
FAITHFUL multi-term versions are Lean-unbuilt. So #114 status = **partially survives as reusable L6/L7
machinery; the multi-term-fidelity gap IS rungs 5b/5c.** Not a free reuse — flag the gap.

### Superseded / DEAD under route P (cartographer prune at close)

The geometric-fold atlas-CONSTRUCTION: `MonumentAtlas` (1961L, 11 sorry) + `MonumentAssembly` (116L,
1 sorry) — the fold carrying the substitution frontiers (`appendResidDescent`/`foldResid_case11`),
driving the SEPARATE `exists_coreResolution_via_monument`. Plus the Wire cluster consuming them
(`LastLayerWire`, `Case2Wire`, `LeafChartWire`, `LeafGeometryWire`, `CanonShear`, `PivotPreservation`,
`MultiAffineStepWire`, `AoyagiCompLinear`) and `GeoAtlasTransfer` (1030L, 1 sorry; imported by
`GeoInvValMaint` + `ChartBridgeFaithful`).

**CONE CHECK (gate-verification):** ALL of these are **OFF the `via_engine` value cone.**
`LearningCoefficient` imports only `{Core.Aoyagi.Engine, RecursionAdapter, RlctPayoff, GlobalHomog,
ParamsFlat, Meta.Cordon}` — no Monument/Geo module. `exists_coreResolution_via_monument` is referenced
ONLY by `AxCheck` + the Monument modules themselves. So the fold cluster is dead/fossil under route P →
retire per the dead-branch-registry plan (banner + delete after the general-`d` build lands green; a stale
sorry misdirects the gradient, P6).

### #115 — destination survives, construction superseded

#115 ("Geometric-atlas wiring C → discharge :311") wired the geometric-**fold** atlas → `:311`. Route P
wires the **ideal-route** atlas → the SAME `:308` seam → `:311`. So #115's **destination (rung 5d) is
intact**; its geometric-fold construction is superseded.

---

## Hard-part-avoidance / drift / contract-fit / gate

- **Hard-part-avoidance — CLEAR on the seam.** The `:308` seam genuinely survives route-agnostic; I
  checked its hypotheses — it demands a REAL `Resolution` record (all `Chart` fields) + a real
  `AtlasRealizesExponents`; nothing is smuggled. Route P is not assuming a non-surviving seam.
- **DRIFT FLAG (the product).** The 5-rung framing risks re-committing the charter §3 newest drift by
  folding **L6 (coupled-leaf `hjac`) + L7 (coupled `hcover`)** into "value wiring." These are not
  bookkeeping; **the coupled `hcover` is the render's named highest un-probed residual risk** (the
  coupled hardness MIGRATED from the dissolved maintenance wall to L7). Fix = the 9-rung ladder above
  with 5b/5c first-class, and 5c front-loaded/probed early.
- **Contract-fit.** `:311`'s contract is a full `Resolution` + realization, not just the ideal identity.
  Route P (the build) does NOT do less than the contract. But the 5-rung FRAMING does less — that is the
  flag, resolved by making 5b/5c explicit. No lane is currently on `hcover` in the general-`d` plan (the
  §9 probe was corank-2 python) — the named hard part must hold a lane (5c), not be routed around.
- **Gate verification — `:311` is the RIGHT and ONLY residual sorry on the `via_engine` value path.**
  Code channel: `LearningCoefficient` imports exclude Monument/Geo; `coreReduction`,
  `two_mul_rlctAt_eq_cCodim`/`_divisorMin`, and the RecursionAdapter seam are sorry-free. Ledger channel:
  charter/BUILD-STATE/render-seam-check cite AxCheck cone = `{propext, sorryAx, Classical.choice,
  Quot.sound}`, single `sorryAx` = `:311`. **CAVEAT (do this):** re-run
  `#print axioms aoyagi_learning_coefficient_via_engine` on the next green build once `Corank2CoreGenWrap`
  lands (it imports `LearningCoefficient`, downstream of `:311` — will not change the cone, but the
  olean-staleness discipline demands a forced re-print, not the build's exit status).

---

## Numbered disposition (proposed to controller; accept / re-sequence / moot item-by-item)

1. **ACCEPT the ladder, RE-COUNT to 9 rungs** — adopt 5a/5b/5c/5d in place of a single "rung 5"; L6
   (`hjac`) and L7 (`hcover`) are first-class, not wiring. *(the navigator value-add)*
2. **FRONT-LOAD rung 5c (`hcover`, route-a full fan)** in parallel with rung 2 — it is the highest
   residual risk, encoding-independent, and risk-free to start (needed under either spine outcome). Assign
   a lane now; do not let it trail the spine.
3. **RE-SCOPE the general-`d` gate's entry bar** — it convenes on a FULL (3,3,4) `Resolution` +
   realization + cover atom (#131 **and** #130), not the landed `flat(Pmat)` `hideal`. At (3,3,4),
   `jac`/`hjac`/injectivity/cover/realization are un-started.
4. **FLAG rung 2's idiom-lift** — the (3,3,4) `fin_cases…ring` proof technique does not lift; general-`d`
   is abstract symbolic composition (the protos' general-`n` form). Price it as the long pole, not a
   scale-up of the instance.
5. **COMMIT the fold cluster to prune** — `MonumentAtlas`/`MonumentAssembly`/`GeoAtlasTransfer` + the Wire
   cluster are confirmed OFF the `via_engine` cone → cartographer retires (banner + delete) after the
   general-`d` build lands green. #114's Geo* MECHANISM modules are kept as candidate 5b/5c reuse (with
   the multi-term-fidelity gap noted).
6. **RE-PRINT axioms on the next green build** — forced `#print axioms …via_engine`, not exit status.
7. **No change needed** — rung 4 (`ConjResolution`) is banked/general; consume as-is at assembly.

**Next trigger:** re-convene at the general-`d` gate proper (post #131+#130 verified), or when a spine
(rung 2) or `hcover` (rung 5c) lane goes serial.
