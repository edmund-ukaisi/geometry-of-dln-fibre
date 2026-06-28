# Statement card — `RouteMSchurDepth2` (the corank-2 N2b→Morse weld; inner-S CLOSED)

> **UPDATE (2026-06-28, the weld leg).** The INNER-S half of the weld is now built end-to-end:
> `schurInner_S_le` chains N2b (`j=1`, cell hyps discharged) → END 1 (`schurSplit_lintegral_le`) → the
> row-0 shear-peel (`schurSplitD_lintegral_lt_top`) → the abstract-`Z` Morse terminal
> (`radial_morse_dominates_absZ_lt_top`), proving `∫_{S∈matBox 2 4 T} frobSq(R·S)^{−c'} < ⊤` for `c'<2`
> on a fixed radial-blow-up angular chart (`R 0 0 = 1`, `|R i k| ≤ 1`). This is the GENERIC-N2b version of
> the bespoke `(3,3,4)` `step3a`/`ratioResidual` chain. All new lemmas axiom-clean
> `[propext, Classical.choice, Quot.sound]` (forced `#print axioms`), S2-FREE. The REMAINING gap is only
> the OUTER radial-R blow-up cover (the `recStep` 4-chart fold + radial Jacobian `|a|³`), mirroring
> `matBox334_chart_lt_top`. See the "Inner-S weld (PROVED)" section below.

> **Naming note (post-review, 2026-06-28).** An earlier draft called the abstract ends a "depth-2
> composition validator" / "composition CLOSED"; a fidelity review (reviewer + decorrelated Codex) flagged
> this as OVERCLAIMING (the abstract ends are not chained). Corrected to "reduction ends". With
> `schurInner_S_le` the INNER-S integral IS now genuinely chained end-to-end (N2b ⟶ Morse); the OUTER
> radial-R cover remains the deferred weld — stated next to the headline.

> **Module.** `DLNFibre.DLN.RLCT.Validate.RouteMSchurDepth2`
> (`lean/DLNFibre/DLN/RLCT/Validate/RouteMSchurDepth2.lean` @ `<uncommitted — controller pins SHA>`;
> base `origin/expedition/aoyagi-full`). Imports `RouteMSchur` (for N1/N2/N3) which pulls in the Morse
> terminal `S1RadialMorse` via `MatMulFibre`. NOT wired into `DLNFibre.lean` (single-writer aggregator —
> controller adds the import `RouteMSchurDepth2` after `RouteMSchur`).
>
> **Scope.** The two ENDS of the corank-2 N2b→Morse reduction (cert §4 N4, `L32a-cover-cert.md`): the
> smallest binding case (`r = 2`, ONE nested minor-pivot level). (i) the N2b-shaped inverse-power
> reduction (core `F` two-sided-comparable to a split form `D` ⟹ `F^{−c'} ≤ c₀^{−c'}·D^{−c'}`), and (ii)
> the finiteness of the `Fin 4` Morse terminal for `c' < 2 = λ_{2,4}`. These three ABSTRACT-end lemmas
> (`schurSplit_integrand_le`/`_lintegral_le`/`schurSplit_depth2_lt_top`) are **NOT chained to each other**.
> The inner-S weld leg (below) THEN chains N2b ⟶ the Morse terminal end-to-end for the inner `S`-integral
> via `schurInner_S_le` (reaching the terminal by the `schurSplitD_lintegral_lt_top` route, not by
> composing the abstract ends). The remaining deferred weld is the OUTER radial-blow-up cover that turns
> the joint corank-2 core over the `Δ`-box INTO the per-chart form `schurInner_S_le` closes
> (`routeMCore_threshold_lt_top`, skeleton in `RouteMSchur`).

## Context — why a separate validator (not re-proving `core334_lt_top`)

The `(3,3,4)` corank-2 JOINT integral `∫_Δ ∫_S frobSq(Δ·S)^{−c'} < ⊤` (`c' < 2 = λ_{2,4}`) is ALREADY
proven sorry-free, two ways: `core334_lt_top` (the S-first transpose-fibre route, `RouteM334Hfin`) and
`routeMCore_M334_threshold_lt_top` (the bespoke 9-chart A0-entry radial cover, `RouteM334Ratiofin`).
`RouteM334Hfin`'s design note (lines ~165–185) records that the transpose route closes `(3,3,4)`
WITHOUT the radial Δ-blow-up / nested minor-pivot recursion — the inner threshold `5/2 > 2` never binds.

So the **Schur minor-pivot recursion** (N1–N4) is the GENERIC path that lifts to ∀M, not the shortest
route for `(3,3,4)` itself. Codex (xhigh, 2026-06-27, decorrelated) confirmed the value of a small lemma
that explicitly chains `N2b → Morse leaf` for the corank-2 case as the "depth-2 regression test for
future layers," and confirmed the certified design has no hole at `r = 2` (the `recStep` entry-chart
cover coincides with the max-modulus `1×1`-minor cover; N2b is the right tool for the first drop, N2a the
terminal rank-1 leaf).

## Proved (axiom-clean `[propext, Classical.choice, Quot.sound]`, no `monomial_rlct`, no new axiom)

Forced-elaboration `#print axioms` (olean force-deleted first) on all three confirms `sorryAx`-free,
`monomial_rlct`-free → **S2-FREE**.

- **`schurSplit_integrand_le`** — the pointwise inverse-power flip (reduction END 1). For
  `c₀, c₁, D, F : ℝ` (abstract reals, NO matrix) with `0 < c₀`, `0 ≤ D`, the two-sided N2b-shaped bounds
  `c₀·D ≤ F` and `F ≤ c₁·D`, and `0 < c'`:
  `ENNReal.ofReal (F^{−c'}) ≤ ENNReal.ofReal (c₀^{−c'}·D^{−c'})`.
  The inverse-power antitone flip of the LOWER bound `c₀·D ≤ F` (`Real.rpow_le_rpow_of_nonpos`),
  zero-guarded by the UPPER bound (`c₀·D = 0 ⟹ D = 0 ⟹ F ≤ c₁·D = 0 ⟹ F = 0`; `0 ≤ F` itself follows
  from `c₀·D ≤ F`). **Both sides of the comparison are load-bearing**: the lower for the bound, the upper
  for the zero-guard. Takes the comparison as a HYPOTHESIS — it does not invoke N2b
  (`schur_minorPivot_split`) to produce it. S2-FREE. (Intended application: `F = frobSq(R·S)`,
  `D = frobSq (R·S)_top + frobSq (Sc·S_bot)`.)
- **`schurSplit_lintegral_le`** — its integral form (reduction END 1, integrated; abstract over a measure
  space `(Ω, μ)`). On a set `Z` where the N2b-shaped comparison holds pointwise (uniform `c₀, c₁ > 0`):
  `∫_Z F^{−c'} ≤ ofReal(c₀^{−c'}) · ∫_Z D^{−c'}`.
  `lintegral_mono` of the pointwise bound + `lintegral_const_mul'` pulls the `Z`-independent `c₀^{−c'}`
  out. The core → split-form reduction, GIVEN the comparison. S2-FREE.
- **`schurSplit_depth2_lt_top`** — the Morse-terminal END (reduction END 2). For `0 ≤ c' < 2`, `0 < T`,
  and a nonneg measurable residual `W : (Fin k → ℝ) → ℝ`:
  `∫_z ∫_P (∑ⱼ (P j)² + W z)^{−c'} < ⊤` over `morseBox k T × morseBox 4 T`.
  `P : Fin 4` is a FREE Morse block (modelling the `j·p = 1·4 = 4` entries of `(R·S)_top`), `W z` an
  arbitrary residual (standing for the corank-1 Schur core `frobSq(Sc·S_bot) ≥ 0`). This is
  `radial_morse_dominates_lt_top` at `m+1 = 4`, bounded by `Kbound 4 c' T · vol(morseBox k T) < ⊤`,
  threshold `4/2 = 2 = λ_{2,4}`. **It takes the split form as its STARTING point** — it does NOT start
  from the corank-2 core and does NOT consume the two reduction lemmas above. S2-FREE.

## English gloss (fidelity — what is and is NOT proven)

**The ABSTRACT ends (not chained to each other).** END 1 (`schurSplit_integrand_le`/`_lintegral_le`):
GIVEN the N2b comparison `c₀·D ≤ F ≤ c₁·D`, the core integral `∫ F^{−c'}` is dominated by the split-form
integral `c₀^{−c'}·∫ D^{−c'}`. END 2 (`schurSplit_depth2_lt_top`): the split-form integral over a FREE
Morse block `P : Fin 4` plus a nonneg residual `W` is finite for `c' < 2 = λ_{2,4}`. **These two abstract
ends are NOT chained to each other**: END 1 takes the comparison as a hypothesis (never invokes N2b to
produce it); END 2 takes the split form as its starting point (never consumes END 1).

**The inner-S weld (`schurInner_S_le`) IS chained end-to-end** (this leg): it invokes N2b to PRODUCE the
comparison for a fixed angular chart, feeds it through END 1, and reaches the Morse terminal via the
`schurSplitD_lintegral_lt_top` shear-peel route (NOT by composing END 2). Reviewer-verified at the
proof-term level. The remaining WELD — the OUTER radial-blow-up CoV turning the joint `∫_Δ frobSq(Δ·S)^{−c'}`
over the `Δ`-box into the per-chart `∫_a ∫_{R-ang} ∫_S` form `schurInner_S_le` closes, summed over the
`r²` charts by `recStep` — is the deferred N4 long pole. What IS proven: the abstract ends + the inner-S
weld, each sorry-free, S2-free, and at the
binding threshold (cross-checked against `core334_lt_top`'s independent `c'' < 2`).

## Inner-S weld (PROVED end-to-end, 2026-06-28 — the weld leg)

The abstract ends are now WELDED for the inner `S`-integral. New lemmas (all axiom-clean
`[propext, Classical.choice, Quot.sound]`, S2-FREE; forced `#print axioms`):

- **`radial_morse_dominates_absZ_lt_top`** — two-radius Morse dominance over an abstract `z`-domain:
  `∫_{z∈Z} ∫_{P∈morseBox (m+1) Tp} (∑ⱼ (P j)² + W z)^{−c'} ∂μ ≤ Kbound (m+1) c' Tp · μ Z < ⊤` for
  `c' < (m+1)/2`, `W ≥ 0`, `μ Z < ⊤`. Generalises `radial_morse_dominates_lt_top` to (i) independent
  `P`/`z` radii and (ii) an arbitrary finite-volume `z`-domain (so the residual `S`-row over `matBox 1 4 T`
  feeds it with NO `Fin 1 → Fin 4 ≃ Fin 4` flatten). Tonelli pulls the `z`-independent inner `P`-bound out.
- **`schurSplitD R Sc S`** — the N2b `r=2,j=1` split form `frobSq (R·S)_row0 + frobSq (Sc · S_row1)`,
  abbreviated; `schurSplitD_nonneg`, and **`schurSplitD_eq`** (with `R 0 0 = 1`):
  `schurSplitD R Sc S = (∑ⱼ (S 0 j + R₀₁·S 1 j)²) + Sc₀₀²·(∑ⱼ (S 1 j)²)` — the top-block shear + scaled
  residual, the shear-peel form. Proof: `frobSq`/`rmatMul` unfold + `Fin.sum_univ_one/two` + `ring`.
- **`lintegral_translate_le_local`** / **`matBox_volume_lt_top`** — small local atoms (the translate
  box-enlarge bound, a local copy avoiding the heavy `RouteM334Ratiofin` import; the matrix-box compactness).
- **`schurSplitD_lintegral_lt_top`** — `∫_{S∈matBox 2 4 T} (schurSplitD R Sc S)^{−c'} < ⊤` for `0<c'<2`.
  Via `schurSplitD_eq` + row-split `S = (S_row0, S_row1)` (`piFinSuccAbove 0`, MP) + Tonelli (`S_row1`
  outermost); per fixed `S_row1` the top block is a shear of `S_row0`, peeled by `lintegral_translate_le_local`
  (box-enlarge `T → 2T` since `|R₀₁·S_row1 j| ≤ T`); `radial_morse_dominates_absZ_lt_top` (`m+1=4`,
  `Tp=2T`, `Z=matBox 1 4 T`) closes it.
- **`schurInner_S_le`** — the inner-S weld CHAINED: on a fixed radial-blow-up angular chart (`R 0 0 = 1`,
  `|R i k| ≤ 1` — the bounded pivot-`(0,0)` cell), `∫_{S∈matBox 2 4 T} frobSq (R·S)^{−c'} < ⊤` for
  `0 < c' < 2 = λ_{2,4}`. Via N2b (`j=1`; cell hyps discharged: the `1×1` minor `R₀₀ = 1` is max-modulus,
  `det = R₀₀ = 1 ≠ 0`) → END 1 (`schurSplit_lintegral_le`) → `schurSplitD_lintegral_lt_top`. The Schur
  complement `Sc` is `R`-determined (extracted once via N2b's uniqueness), so the per-`S` bounds use the
  same `Sc`. **This is the genuinely-new generic-N2b weld heart** — what the bespoke `(3,3,4)` route does
  by hand for `angularR`, here via the generic Schur split; it lifts to ∀M. Codex-confirmed: one N2b level
  closes `∫_S` UNIFORMLY over the chart (the `Sc→0` rank-1 edge does not break it).

## Hypotheses (the load-bearing ones)

- `schurSplit_integrand_le` / `schurSplit_lintegral_le`: the N2b-shaped two-sided comparison
  `c₀·D ≤ F ≤ c₁·D` with uniform `c₀, c₁ > 0` — the SHAPE of `schur_minorPivot_split`'s (N2b) conclusion,
  taken as a hypothesis (not invoked). Both directions needed (lower = bound, upper = zero-guard). `c' > 0`
  (the `c' = 0` constant case is the trivial volume bound, handled separately in the existing anchors).
  (`hF : 0 ≤ F` dropped post-review — it follows from `c₀·D ≤ F`.)
- `schurSplit_depth2_lt_top`: `c' < 2` (= `λ_{2,4}`, the binding corank-2 threshold = `(m+1)/2` with the
  `j·p = 4`-entry Morse block); `W` nonneg + measurable (the corank-1 Schur residual, automatically
  nonneg as a `frobSq`).

## Outer radial-Δ cover — SCAFFOLDING + support lemmas BUILT (2026-06-28, the weld outer leg)

The outer half is substantially built (all sorry-free, axiom-clean `[propext, Classical.choice,
Quot.sound]`):
- **Flatten + cover-to-sum**: `matToFlat2`/`measurePreserving_matToFlat2` (local `Fin 2×2 ≃ Fin 4`),
  `flatBox2`/`matBox2_flatBox_preimage`/`gFlat2`/`matBox2_outer_flat`, `gFlat2_cover_sum` (`recStep`
  4-chart cover-to-sum).
- **Radial pull-out**: `Rmat2`, `gFlat2_blowup_radial` (N1 homogeneity).
- **Pivot atoms**: `frobSq_rmatMul_perm2`/`matBox24_rowperm_lintegral`, `schurInner_S_le_pivot` (inner-S
  finiteness at an ARBITRARY pivot via `Equiv.swap` → (0,0)).
- **Per-chart support**: `e2`/`Rmat2_entry`/`_pivot`/`_entry_le`, `innerS2`/`innerS2_offpivot`/
  `measurable_innerS2`, `flatBox2_blowup_mem_iff`.

### THE PRECISE REMAINING WALL (the exact sub-goal + what was tried)

The assembling `matBox2_chart_lt_top` + `core_schur2_lt_top` need a **UNIFORM (R-independent) bound** from
`schurInner_S_le`. The per-chart finiteness's ratio-residual sub-goal is
`∫_{z∈[−1,1]³} innerS2(e.symm(0,z)) dz < ⊤` — the integral OVER the ratios `z`. `schurInner_S_le_pivot`
gives `innerS2(…) < ⊤` per fixed `z`, but the INTEGRAL over the compact ratio-box needs `innerS2(…) ≤ K`
UNIFORMLY (then `∫_z K = K·vol < ⊤`). The bound IS R-uniform (Codex-confirmed; visible in the proof):
`c₀ = 1/(2+2·1·1) = 1/4` (R-independent) and `∫_S schurSplitD^{−c'} ≤ Kbound 4 c' (2T)·vol(matBox 1 4 T)`
(R-independent), so `K := ofReal((1/4)^{−c'})·Kbound 4 c' (2T)·vol(matBox 1 4 T)`. The refactor: a `≤`-form
`radial_morse_dominates_absZ_le` (the `_lt_top` proves `≤ Kbound·μZ` internally — extract), a
`schurSplitD_lintegral_le` (`≤ Kbound·vol`; needs `hbd : |R 0 1| ≤ 1` re-added — dropping it walled the
box-enlarge in the first attempt), `schurInner_S_le_pivot_bound` (`≤ K`), then `hratiofin = ∫_z K`. Shape
fully determined; ~60 lines of `≤`-threading + the chart-finiteness assembly. Not landed in this leg
(the `_le` refactor + build-cycle cost under shared-semaphore contention).

## Deferred — the remaining N4 outer assembly (the radial CoV chaining)

After the uniform-bound piece above, the remaining N4 gap is the OUTER assembly chaining the per-chart
finiteness into the joint `∫_Δ ∫_S frobSq(Δ·S)^{−c'}`:
- cover `matBox 2 2 T` (the `Δ`-box) by the `r² = 4` max-modulus-entry charts (`recStep`/`g5_pivotNode`);
- per chart, N1 (`radialDelta_loss_factor`) pulls the radial scale `a` (Jacobian `|a|³`,
  `pivotBlowupOnDeriv_det`), N3a/N3b the a-axis divisor; Tonelli separates `a` from the inner `∫_{R-ang}∫_S`;
- per chart, the angular `R'` (pivot entry `= 1`, others `≤ 1`) → permute the pivot to `(0,0)` (Jacobian
  `1`) → `schurInner_S_le` closes the inner `∫_S` (the per-chart constant is `a`-independent and
  `R-ang`-uniform).

This is the cert §4 N4 HIGH-risk assembly (`routeMCore_threshold_lt_top`, skeleton in `RouteMSchur`),
mirroring `matBox334_chart_lt_top`'s radial-CoV plumbing. The note in N4's docstring points at the
reduction ends; this leg added the inner-S weld.

## Build / audit

- `lake build DLNFibre.DLN.RLCT.Validate.RouteMSchurDepth2` green; full `lake build DLNFibre` green
  (RouteMSchur docstring edits only — N2b/N3b "SKELETON" → "PROVED"; N4 docstring points at the ends).
- `scripts/sorries`: ZERO in `RouteMSchurDepth2`. (`RouteMSchur` retains the ONE honest N4 sorry, the
  multi-tide endpoint.)
- `#print axioms` (forced): all load-bearing lemmas `[propext, Classical.choice, Quot.sound]` (S2-FREE).

## Status

`sorry-free` (the abstract reduction ends + the inner-S weld `schurInner_S_le` + the radial-Morse infra).
The abstract ends were `reviewed` (fidelity audit 2026-06-28: math sound, S2-free, threshold-correct; the
earlier "composition CLOSED/validator" framing was corrected to "reduction ends", and `hF` dropped). With
this leg the inner-S integral IS now welded end-to-end (N2b ⟶ Morse) via `schurInner_S_le`; the OUTER
radial-R cover remains the deferred N4 step. The inner-S weld is `reviewed` (fidelity audit 2026-06-28:
SURVIVED — genuinely chained at the proof-term level, N2b cell-hyp discharge + shear-peel box-enlarge
sound, threshold-correct; two PROSE defects fixed — the `3T`→`2T` docstring typo and the stale "not
chained" prose now scoped to the abstract ends with a cross-reference to `schurInner_S_le`). Pending
controller wire-in of the `RouteMSchurDepth2` import into `DLNFibre.lean`.
