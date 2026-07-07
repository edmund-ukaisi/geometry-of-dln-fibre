# R1-LOWER general-L gap-map + build-order (scout scope cert)

**Seat:** scout (reconnaissance, read-mostly). **Date:** 2026-07-07.
**Worktree:** reset to `origin/expedition/aoyagi-full` @952dff73. NO heavy build (read + `rg` + a
few `#print axioms`-target reads only).
**Charge:** map the general-L R1-LOWER leg so the controller can charge a formaliser collision-free.

---

## HEADLINE VERDICT (one line)

**The general-L R1-LOWER `hdiv` (achiever box-divergence) leg is ALREADY CLOSED — sorry-free, ∀L,
AxCheck-verified `[propext, Classical.choice, Quot.sound, monomial_rlct]`.** It is NOT a bounded
formaliser charge and NOT a design-risk build: it is DONE. The mission's framing ("the entire
R1-LOWER content = construct one uniform `NodeAchieverChart M`") is **stale** — it reads the
`RouteMLayerCoverGE.lean:133` docstring, which predates the stratified dispatch that actually closed
the leg. **Do NOT charge a formaliser to build `NodeAchieverChart M`; that work is banked** (and
re-building it would collide with the `RouteMInteriorLiveGen*` / `RouteMSmeared*Gen` /
`RouteMBoundaryCleanChartFull` chains).

The lone R1-LOWER sorry — `routeMCore_box_diverges_achiever` (`RouteMLayerCoverGE.lean:133`) — is an
**ORPHAN**: consumed only by `layerCover_hdiv` (same file), which is consumed nowhere. The R1-LOWER
leg was re-routed around it (see §2).

---

## 1. What actually closes R1-LOWER (the load-bearing chain)

The general-L R1-LOWER lower bound is delivered by `R1ResolutionGeneral.r1_resolution_general`
(sorry-free; AxCheck line 305). Its `hdiv` field is built **inline**, NOT via the line-133 atom:

```
r1_resolution_general (M, hL : 1≤L, hMid : ∀s, 0<M s, hbox)   -- R1-UPPER hbox is the only open input
  └─ hdiv (inline Sub-A + Sub-B)
       └─ routeMCore_box_diverges_achiever_full'   (RouteMAchieverFullHNoFree.lean, hNo-FREE)
            ├─ InteriorDrop M    → interiorLiveGen_hInterior              (unconditional on InteriorDrop)
            └─ ¬InteriorDrop M   → routeMCore_box_diverges_achiever_full  (+ hNo via bridge)
                 └─ routeMCore_box_diverges_achiever_spine  (4-way dispatch, RouteMAchieverDispatch)
```

`routeMCore_box_diverges_achiever_full'` needs `hpos : 1 ≤ minAdm M`, `hMpos : ∀ s, 0 < M s`,
`hne : (deepestCoords).Nonempty`. In `r1_resolution_general` these are threaded from `hMid`
(all-positive widths): `one_le_minAdm_of_pos_general`, `deepestCoords_nonempty_of_pos`. **So the
`hMpos`/`hne` the line-133 atom lacks are supplied by the resolution's nondegeneracy hypothesis.**

The 4-way dispatch spine (`routeMCore_box_diverges_achiever_spine`), for `1 ≤ minAdm M`:
- `L = 0` — vacuous (`minAdm = 0` contradicts `hpos`).
- `L = 1` — always boundary-clean → `routeMCore_box_diverges_clean` (banked).
- `2 ≤ L` trichotomy (`achiever_trichotomy_total`, unconditionally total):
  - **INTERIOR** (`InteriorDrop M`) → `interiorLiveGen_hInterior`, itself cased on `deepRank M`:
    - `0 < deepRank M` → `interiorLiveNodeChartGen` (LIVE-leaf LDU chart)
    - `deepRank M = 0` → `eDeepRank0NodeChartGen` (E-block re-pivot chart)
  - **BOUNDARY-CLEAN** (`deepRank = deepRows`) → `cleanNodeChart` (whole-deepest radial)
  - **BOUNDARY-SMEARED** (`deepRank < deepRows`) → `smearedChartGen : SmearedAchieverChart M`

All four branches are built general-L and sorry-free. AxCheck force-elaborates the whole chain
(`#print axioms` on `routeMCore_box_diverges_interiorLiveGen`, `interiorLiveNodeChartGen`,
`interiorLiveGen_hInterior_of_deepRank_zero`, `interiorLiveGen_hInterior`, `hSmeared_smearedClose`,
`routeMCore_box_diverges_achiever_full`, `r1_resolution_general` — AxCheck.lean:240–305), which
defeats the stale-olean sorryAx-masking trap.

---

## 2. The precise remaining "gap" (the orphan)

`routeMCore_box_diverges_achiever` (line 133) is stated for ALL `M` with only `1 ≤ minAdm M`.
`routeMCore_box_diverges_achiever_full'` additionally needs `hMpos`/`hne`. The gap between them is
**not chart construction** — it is the missing nondegeneracy. Two honest dispositions:

- **(orphan is superseded)** Nothing downstream consumes line-133 or `layerCover_hdiv`; the leg runs
  through `r1_resolution_general`. Mark line-133 SUPERSEDED / delete it + `layerCover_hdiv`. This is
  the honest move (the residual asserts more generality — degenerate-width `M` with `minAdm ≥ 1` —
  than the payoff ever needs, and than the banked route proves).
- **(close it, if a standalone atom is wanted)** Add `hMpos`/`hne` to its signature and wire
  `routeMCore_box_diverges_achiever_full'` — a ~3-line proof. It CANNOT be closed at its current
  weaker hypotheses (the degenerate-width strata are not covered by the banked route, and are not the
  content anyone needs). Do not launder in `hMpos`/`hne` silently — restate them next to the claim.

Either way this is a **cosmetic tidy, not a build**. Recommend disposition 1 unless the controller
wants a caller-facing unconditional-in-`M` atom (it has no consumer).

---

## 3. Field-by-field gap-map of `NodeAchieverChart M` (structure at `NodeAchieverChart.lean:64`)

THREE of the four strata build a full `NodeAchieverChart M` (general-L, sorry-free); the fourth
(smeared) uses a SEPARATE structure. Status per field, per stratum:

### 3a. Interior LIVE-leaf (`InteriorDrop ∧ 0 < deepRank`) — `interiorLiveNodeChartGen`
`RouteMInteriorLiveGenAtom.lean:94`. Consumes `ha := structAdm_tach M` (unconditional),
`h0c := InteriorDrop.1`, `h0r := 0 < deepRank`, `hpos`, `hInt`. **ALL FIELDS BUILT-GENERAL, sorry-free:**

| field | source (all general-L, sorry-free) | module |
|---|---|---|
| `phi` | `interiorLivePhiGen` | RouteMInteriorLiveGenChart |
| `p` | `leafPivot` | RouteMInteriorLiveGenChart |
| `leafH` / `leafH_pivot` | `interiorLive_leafHGen` / `_pivot` | RouteMInteriorLiveGenChart |
| `Ufun` | `interiorLiveUnitGen` (+ `_nonneg`) | RouteMInteriorLiveGenChart |
| `Ubound` | `ldu_UboundGen` ∘ `interiorLiveUnit_ae_posGen` | RouteMInteriorLiveGenAnalytic |
| `Umeas` | `ldu_UmeasGen` | RouteMInteriorLiveGenAnalytic |
| `leaf_integrand` | `leaf_integrand_of_rate` (det-FREE, ∀M) | RouteMGenLeafIntegrand |
| `cov` | `interiorLive_covGen` = `ldu_cov_of_differentiable_injOn` (E=univ) | RouteMInteriorLiveGenAtom / RouteMNullSliceCov |
| `image_subset` | `ldu_imageGen` | RouteMInteriorLiveGenAnalytic |

The `cov` inputs (the design doc's "heaviest piece"): the composed determinant `DtotGen_abs_det`
(`∏_s |det(readK y₀ s)|^{r_s+c_s}`, staggered staircase-conjugated, `stairMap_abs_det_twoConj`,
landed sorry-free 2026-07-01, `RouteMInteriorLiveGenDet`), decoded to `interiorLive_abs_det'Gen`
(`RouteMInteriorLiveGenDetDecode`); injectivity `interiorLive_injOnGen`
(`RouteMInteriorLiveGenInj` ← `BchartLeafGen_injOn_recover`, `RouteMInteriorLiveGenInjRec`);
differentiability `interiorLive_diffGen` (`RouteMInteriorLiveGenHmap`).

### 3b. Interior `deepRank = 0` (`InteriorDrop ∧ deepRank = 0`) — `eDeepRank0NodeChartGen`
`RouteMInteriorDeepRank0GenAtom.lean:723`, atom `routeMCore_box_diverges_eDeepRank0Gen:758`, wired
via `interiorLiveGen_hInterior_of_deepRank_zero:820`. Full `NodeAchieverChart M`, general-L,
sorry-free (E-block re-pivot chart, boundary `k` aligned to the InteriorDrop pivot `p* = k+1`).

### 3c. Boundary-clean (`deepRank = deepRows`) — `cleanNodeChart`
`RouteMBoundaryCleanChartFull.lean:194`, atom `routeMCore_box_diverges_clean:217`. Full
`NodeAchieverChart M`, general-L, sorry-free (whole-deepest radial; Jacobian `|u_p|^{minAdm−1}`).

### 3d. Boundary-smeared (`deepRank < deepRows`) — `smearedChartGen : SmearedAchieverChart M`
`RouteMSmearedAssembleGen.lean:377`; structure `SmearedAchieverChart` at
`RouteMSmearedAchieverGeneral.lean:129`; `hSmeared_smearedClose` (`RouteMSmearedClose`) derives ALL
structural data from `BoundarySmeared ∧ NoInteriorBothDrop ∧ 1 ≤ minAdm`. General-L, sorry-free,
S2-free (single-axis after the front shear). **NOT a `NodeAchieverChart`** — see §4.

---

## 4. Satisfiability: a UNIFORM `NodeAchieverChart M` for all M does NOT exist (the obstruction)

The mission asks whether a uniform pure-monomial chart (`|det Dφ| = ∏|u_j|^{leafH j}`, polynomial
rate `F∘φ = u_p²·U` holding ∀u) exists for all M, or whether a stratum obstructs it. **A stratum
genuinely obstructs it — the build stratified for a reason, not for convenience.** Two obstructions:

- **Boundary-smeared stratum obstructs the pure-monomial `cov`.** The smeared chart is
  `φ = ψ ∘ R` with `ψ` a **rational** shear (measure-preserving, but rational) and only the radial
  `R` carrying the single-axis Jacobian `|u_p|^h`; the quadratic rate `F∘φ = z²·U` holds **only off
  the null pole** on a conditioned box, not ∀u. This cannot be a `NodeAchieverChart` (whose `cov`
  demands a pure-monomial multi-axis Jacobian and whose `leaf_integrand`/rate a polynomial chart
  supplies ∀u). Hence the dedicated `SmearedAchieverChart` structure. (Corroborated by the
  `RouteMInteriorContract` docstring: the free-K frame Jacobian carries a polynomial `∏|det K_s|^{…}`
  of degree ≥ 2, so a pure-monomial `cov` is unsatisfiable there.)
- **Interior stratum needs the LDU lens to make the Jacobian monomial.** The interior polynomial
  `det K_s` is straightened to the diagonal-pivot monomial `∏_i q_i` only after the kLDU coordinate
  lens; the raw free-K chart's `cov` is likewise unsatisfiable (this is exactly why the free-K
  `RouteMInteriorContract` is SUPERSEDED — see §5).

So the correct picture is a **stratified family** (3 `NodeAchieverChart` strata + 1
`SmearedAchieverChart` stratum), each built ∀L. This directly answers the mission's
"(a)-bounded vs (b)-design-risk": **neither — (c) DONE.** The design/satisfiability risk the
mission worried about (does a uniform chart exist?) is real (answer: no uniform chart), and the codebase
already resolved it by stratifying and building each branch.

---

## 5. Excluded / dead / non-load-bearing (collision hazards to avoid)

- **`RouteMInteriorLDUContract` / `…LDUCov` / `…LDULeafH`** — DEAD free-K→LDU skeleton, 9 live
  sorries, **NOT in the aggregator** (orphaned). The interior leg runs through the LIVE
  `RouteMInteriorLiveGen*` chain instead. Do NOT build on the LDU contract.
- **`RouteMInteriorContract`** — SUPERSEDED free-K interior contract (docstring self-flags: free-K
  `cov` unsatisfiable). Kept as a rate-side reference; not the live route.
- **`RouteM221` / `RouteM4422` / `RouteM3333` / `RouteM3333Atom` / `RouteM3333Det`** — per-INSTANCE
  chart validations (the design doc's "build (3,3,3,3) first" stress-test — now sorry-free). They
  validate the bundle shape at fixed M; they are NOT the general-L route and re-charging them would
  duplicate banked work.
- **`RouteMAchieverGeneralDet`, `RouteMCardBridge`, `RouteMPhiFlatDet`, `RouteMFlatLDU`** — fragments
  of the abandoned single-uniform-`φ_M` det programme (the design doc's approach). Superseded by the
  stratified route; do not extend.

---

## 6. Build order (what a formaliser should / should NOT do)

**For R1-LOWER general-L `hdiv`: NOTHING TO BUILD.** It is closed. The only actions available:
1. (optional, cosmetic) Dispose of the orphan `routeMCore_box_diverges_achiever` (line 133) +
   `layerCover_hdiv` per §2 — delete/supersede, or restate with `hMpos`/`hne` and wire
   `routeMCore_box_diverges_achiever_full'` (~3 lines). No new math.

**The genuine ∀L open walls are NOT R1-LOWER** (for the controller's onward planning):
- **R1-UPPER / box-finiteness** — `hbox : RouteMBoxThresholdFinite M` (the `hfin` leg), the one
  genuine open input of `r1_resolution_general`. Discharged only for depth-2 families
  (`routeMBoxThresholdFinite_mnp` / `_rrp`); general/deep `M` open (`RouteMBoxReduction` docstring:
  "no literal ∀M wiring — a category error"). Root sorries: `RouteMSchur.lean:429`
  (`routeMCore_threshold_lt_top`), `RouteMSJResolution.lean:803` (SJ finiteness assembly).
- **D1 leg** — `Skeleton.lean` (4), `DeepestGaugeChart.lean:357`, `DeepestL2Wiring.lean:1060`
  (the D1 wall; separate from R1).
- **Value recursion general branch** — `RouteMRecursion.lean:257` (the VALUE leg's general branch,
  distinct from the divergence).
- `RouteMSchurGeneral.lean:144` — a deliberately-marked `schurRecStep4_stub`, quarantined.

---

## 7. Design-doc-still-valid check (`threads/32-r1-general-hdiv-design/`, 2026-06-26)

**SUPERSEDED, but its technical predictions were borne out.** The doc adjudicated the lone gate as
"NEEDS-DESIGN-then-build" for a **single uniform `φ_M`**, naming the variable-length composed
determinant as the heaviest piece and flagging the smeared/corank sensitivity as "separate". What
actually happened (2026-07-01+):
- The uniform-`φ_M` route was NOT taken; the build **stratified** (4 branches) — which the doc's own
  "corank-sensitive, separate" caveat foreshadowed. The pure-monomial `NodeAchieverChart` cannot be
  uniform (§4), so the smeared stratum forked to `SmearedAchieverChart`.
- The doc's design pass ("descent-path-indexed `φ_M` + a general composed-determinant lemma +
  a finite-family null-slice cov") LANDED — for the interior stratum: `interiorLivePhiGen` +
  `DtotGen_abs_det` (via `stairMap_abs_det_twoConj`) + `ldu_cov_of_differentiable_injOn`. The doc's
  feared "variable-length `det_comp` could be a multi-week fight" was resolved by the staggered-pack
  route.
- The doc's "ship (3,3,3,3) first as the stress-test" happened (`RouteM3333*`, now sorry-free).

Net: the design doc is a correct historical record of a decision point; its verdict has been
executed and closed. It is not a live guide — do not re-open the "uniform `φ_M`" line it explored.

---

## Reflection (scout close)

- **Most likely to advance the expedition:** the finding itself — R1-LOWER general-L is DONE, so the
  controller's next R1-side charge should target **R1-UPPER `hbox`** (box-finiteness for deep `M`),
  the true open input of `r1_resolution_general`, not the R1-LOWER charts.
- **Most likely to break:** my claim that the line-133 atom is fully orphaned rests on `rg` reachability
  (no consumer of `layerCover_hdiv` or the exact atom name outside docstrings) — sound, but a full
  `lake build DLNFibre` (deferred per charge) would be the definitive confirmation that deleting them
  breaks nothing. The AxCheck `#print axioms` on `r1_resolution_general` (not on line-133) is strong
  independent evidence the live leg bypasses it.
- **Next computation that would clarify:** none needed for R1-LOWER. For the controller's onward plan,
  the sharp next question is R1-UPPER: does `RouteMBoxThresholdFinite M` admit a general-L / deep-`M`
  route, or is it genuinely per-family (the `RouteMBoxReduction` "category error")? That is the R1
  gate's actual remaining content.
