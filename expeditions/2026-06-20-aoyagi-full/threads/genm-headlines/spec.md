# genm-headlines — build spec: the UNCONDITIONAL general-L headline bounds (#82 (b)+(c))

**Mandate (controller, executing the operator CLOSE plan point 3).** The λ-path is now S2-free
(Stage A landed) and the general-L headline `aoyagi_learning_coefficient_gen` is conditional on
`(□) = RouteMBoxThresholdFinite (H−r)` alone (#81 landed, clean-three). Now build the two
**UNCONDITIONAL** general-L headline results the operator asked for — the parts that need NO gate at
all because the ≤-half (achiever divergence) is proven ∀L.

## Discipline (read first)
- `lean/scripts/lb` ONLY; force-recompile the files you touch; forced `#print axioms` on each new
  public result (expect `[propext, Classical.choice, Quot.sound]` — clean-three, NO `sorryAx`, NO
  `monomial_rlct`, NO `cited_aoyagi_dln`). Report the exact axiom lines.
- **NO sorry-scaffold.** If a rung hits a genuine ceiling, STOP and report the shrunk ladder (what
  landed clean, what the wall is) — do not paper it with `sorry`.
- **File ownership:** you OWN `Validate/HeadlineGenAssembly.lean` (add the new theorems here, or a
  new sibling `Validate/HeadlineGenBounds.lean` importing it — your call). You MAY add helper lemmas
  to `Validate/DeepestFrontGaugeGen.lean`. **Do NOT touch** `RouteMState.lean`,
  `NodeAchieverChart.lean`, `RouteMLayerCoverHfin.lean`, `AxCheck.lean`, `DLNFibre.lean`, or any
  `Skeleton.lean` sorried lemma (the controller wires AxCheck/aggregator + does the doc sweep).
- Checkpoint (commit + push branch `genm-headlines`) at: (c) green, (b) green, strand-complete.
  Report to team-lead at each checkpoint. SendMessage summaries ≤180 chars.

## Banked pieces (verified present — use these; do NOT rebuild)
- `r1_resolution_general` (`R1ResolutionGeneral.lean:119`): `(hbox : RouteMBoxThresholdFinite M) →
  rlctAtOn (dlnLoss M 0) 0 = ofReal (lambdaCore M)`. Its INTERNALS separate the two halves: `hdiv`
  (the achiever box-divergence via `routeMCore_box_diverges_achiever_full'`, **no hbox**) gives the
  `≤` direction; `hfin` (via `hbox`) gives the `≥`. The cover bridge `routeM_rlctAtOn_eq_iInf`
  packages both. Read this proof — the `≤`-half you need is the `hdiv`-only direction.
- `deepest_regular_core_reduces_frontPivot_front` (`DeepestFrontGaugeGen.lean:130`): the **front**
  deepest normal form `rlctAt (deepestPoint) = (nRegGen H r)/2 + rlctAtOn (dlnLoss (H−r) 0) 0` (needs
  the front-pivot hyps `htop`/`hcolfront`; `hGne` from `hpos`). **⚠ USE THIS FRONT VERSION.** The
  general (non-front) `deepest_regular_core_normal_form` (Skeleton:1124) is **SORRIED** — off-limits.
- `reg_shift_add_core_eq_aoyagiLambda` (`Skeleton.lean:1088`): `((r*(H 0 + H (last L) − r) : ℕ):ℝ≥0∞)/2
  + ofReal (lambdaCore (H−r)) = ofReal (aoyagiLambda H r)` (the closed-form recombination; `nRegGen H
  r = r*(H 0 + H (last L) − r)`).
- WLOG: `headline_frontRowColPivot_exists H r B hB hL` → front-pivot `B'` + `htop`/`hcolfront` +
  ⨅-invariance `hinv`. `aoyagiLambda H r` is `B`-free. (See the STEP-A block of
  `aoyagi_learning_coefficient_gen` for the exact transport idiom.)
- The D1 `≥`-leg (`d1ge_deepestPoint_via_explicit_core_genL_wired` fed `d1ge_hAtV_explicit_close_gen`)
  + `le_antisymm` gives the **unconditional** `hD1 : ⨅ w ∈ optimalSet H B', rlctAt … w =
  rlctAt (deepestPoint …)` — copy STEP-A/LEAF/STEP-B of the current gen headline verbatim (they need
  NO hbox/hRValue).

## (c) — the UNCONDITIONAL deepest reduction (∀ L ≥ 2, all r, nondeg widths)
Named theorem, e.g. `aoyagi_deepest_reduction_gen`:
```
theorem … (H) (r) (B) (hB : B.rank = r) (hr : ∀ s, r ≤ H s) (hL : 1 ≤ L) (hL2 : 2 ≤ L)
    (hpos : ∀ s, r < H s) :
    (⨅ w ∈ optimalSet H B, rlctAt H (dlnLoss H B) w)
      = (nRegGen H r : ℝ≥0∞)/2 + rlctAtOn (dlnLoss (fun s => H s - r) 0) (fun _ => 0)
```
Fold: WLOG → `B'` (⨅-invariance); `hD1` (⨅ = rlctAt(deepest), unconditional); then the FRONT normal
form `deepest_regular_core_reduces_frontPivot_front` rewrites `rlctAt(deepest)` to `nRegGen/2 +
rlctAtOn(core)@0`. Check the `nRegGen` spelling matches what the front lemma emits (it may be
`(r*(H 0 + H (last) − r):ℕ)`; align via `nRegGen`'s def or a `show`). Unconditional — no hbox.

## (b) — the UNCONDITIONAL general-L UPPER bound (∀ L ≥ 2, all r, nondeg widths)
Named theorem `aoyagi_learning_coefficient_gen_le` (NAME IT AS THE BOUND, not the equality):
```
theorem … (same hyps, NO hbox) :
    (⨅ w ∈ optimalSet H B, rlctAt H (dlnLoss H B) w) ≤ ENNReal.ofReal (aoyagiLambda H r)
```
Fold: (c) gives `⨅ = nRegGen/2 + rlctAtOn(core)@0`. Then
`rlctAtOn(core)@0 ≤ ofReal(lambdaCore(H−r))` (the **≤-half, UNCONDITIONAL** — this is the piece you
must EXTRACT: the `hdiv`-only direction of `r1_resolution_general`. Either factor a
`routeM_rlctAtOn_le_iInf` (from `hdiv` alone, no `hfin`) out of `routeM_rlctAtOn_eq_iInf`'s proof, or
prove `rlctAtOn ≤ ⨅threshold` directly from the box-divergence via the RLCT def. `⨅threshold =
lambdaCore` via `routeLayerAtlas_value_eq_lambdaCore`/`routeMCore` transport, both banked).
Then `add_le_add_left` + `reg_shift_add_core_eq_aoyagiLambda` closes `nRegGen/2 + rlctAtOn(core) ≤
nRegGen/2 + ofReal(lambdaCore) = ofReal(aoyagiLambda)`.

**The one genuinely-new brick is the unconditional ≤-half.** Build it FIRST (checkpoint), then (c),
then (b) is a short combine. If the ≤-half extraction hits a real wall (e.g. the RLCT `≤`-from-
divergence isn't cleanly available and needs new analysis), STOP and report — do not sorry it.

## (a) — CONFIRM (no build)
Forced `#print axioms aoyagi_learning_coefficient_L2` — confirm it is the full RRR equality,
clean-three (unconditional). Report the axiom line. (Controller cards it.)

## Fidelity guards
- (b)/(c) must carry the SAME nondegeneracy scope as the gen headline (`hpos : r < H s`, `hL2`).
- The ≤-half must NOT secretly assume `hbox` (that would make (b) conditional — defeating the point).
  Verify by forced `#print axioms` (no hbox is a hypothesis ⟹ it won't show, but confirm the theorem
  signature has NO `RouteMBoxThresholdFinite` argument).
- Fire a decorrelated `local-codex-consult` on the ≤-half extraction soundness if it feels subtle.
