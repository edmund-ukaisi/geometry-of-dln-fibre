# Statement card — `RouteMSchurDepth2` (the corank-2 N2b→Morse reduction END-PIECES)

> **Naming note (post-review, 2026-06-28).** An earlier draft called this the "depth-2 composition
> validator" and `schurSplit_depth2_lt_top` "the composition CLOSED". A fidelity review (reviewer +
> decorrelated Codex) flagged this as OVERCLAIMING: the three lemmas are NOT chained end-to-end (lemma 3
> takes the split form as its starting point and does not consume lemmas 1-2 or invoke N2b). Renamed to
> "END-PIECES" / "the two ends of the reduction"; the missing weld (core → split form) is the deferred
> N4 radial-blow-up CoV, now stated next to each headline. The Lean math was sound throughout — only the
> framing was corrected.

> **Module.** `DLNFibre.DLN.RLCT.Validate.RouteMSchurDepth2`
> (`lean/DLNFibre/DLN/RLCT/Validate/RouteMSchurDepth2.lean` @ `<uncommitted — controller pins SHA>`;
> base `origin/expedition/aoyagi-full`). Imports `RouteMSchur` (for N1/N2/N3) which pulls in the Morse
> terminal `S1RadialMorse` via `MatMulFibre`. NOT wired into `DLNFibre.lean` (single-writer aggregator —
> controller adds the import `RouteMSchurDepth2` after `RouteMSchur`).
>
> **Scope.** The two ENDS of the corank-2 N2b→Morse reduction (cert §4 N4, `L32a-cover-cert.md`): the
> smallest binding case (`r = 2`, ONE nested minor-pivot level). (i) the N2b-shaped inverse-power
> reduction (core `F` two-sided-comparable to a split form `D` ⟹ `F^{−c'} ≤ c₀^{−c'}·D^{−c'}`), and (ii)
> the finiteness of the `Fin 4` Morse terminal for `c' < 2 = λ_{2,4}`. These are the INGREDIENTS the
> depth-2 recursion needs — **three separate lemmas, NOT chained end-to-end**. The missing weld is the
> radial-blow-up change-of-variables that turns the corank-2 core `∫_R frobSq (R·S)^{−c'}` over the matrix
> box INTO the split form; that stays the deferred N4 long pole (`routeMCore_threshold_lt_top`, skeleton
> in `RouteMSchur`). This is the leg's FIRST milestone per the dispatch brief — the reduction ends, not
> the end-to-end recursion.

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

The two ENDS of the corank-2 recursion's N2b→Morse step. END 1 (`schurSplit_integrand_le`/`_lintegral_le`):
GIVEN the N2b comparison `c₀·D ≤ F ≤ c₁·D`, the core integral `∫ F^{−c'}` is dominated by the split-form
integral `c₀^{−c'}·∫ D^{−c'}`. END 2 (`schurSplit_depth2_lt_top`): the split-form integral over a FREE
Morse block `P : Fin 4` plus a nonneg residual `W` is finite for `c' < 2 = λ_{2,4}`. **These are NOT
chained end-to-end**: END 1 takes the comparison as a hypothesis (never invokes N2b to produce it from
`frobSq(R·S)`); END 2 takes the split form as its starting point (never starts from the core, never
consumes END 1). The missing WELD — the radial-blow-up change-of-variables turning `∫_R frobSq(R·S)^{−c'}`
over the matrix box into the split form `(P, z)`, summed over the `r²` charts by `recStep` — is the
deferred N4 long pole. What IS proven: the two reduction ingredients, each sorry-free, S2-free, and at the
binding threshold (cross-checked against `core334_lt_top`'s independent `c'' < 2`).

## Hypotheses (the load-bearing ones)

- `schurSplit_integrand_le` / `schurSplit_lintegral_le`: the N2b-shaped two-sided comparison
  `c₀·D ≤ F ≤ c₁·D` with uniform `c₀, c₁ > 0` — the SHAPE of `schur_minorPivot_split`'s (N2b) conclusion,
  taken as a hypothesis (not invoked). Both directions needed (lower = bound, upper = zero-guard). `c' > 0`
  (the `c' = 0` constant case is the trivial volume bound, handled separately in the existing anchors).
  (`hF : 0 ≤ F` dropped post-review — it follows from `c₀·D ≤ F`.)
- `schurSplit_depth2_lt_top`: `c' < 2` (= `λ_{2,4}`, the binding corank-2 threshold = `(m+1)/2` with the
  `j·p = 4`-entry Morse block); `W` nonneg + measurable (the corank-1 Schur residual, automatically
  nonneg as a `frobSq`).

## Deferred — the WELD between the two ends (the heavy N4 long pole, NOT this leg)

END 2 (`schurSplit_depth2_lt_top`) takes the split-form integral over `(P, z)` as its starting point; END
1 takes the comparison as a hypothesis. The remaining N4 gap that would CHAIN them is the
**radial-blow-up change-of-variables** that turns the corank-2 core `∫_R frobSq(R·S)^{−c'}` over the
matrix box `matBox 2 2 T` INTO that split-form `(P, z)` integral (and, at the same step, produces the N2b
comparison END 1 consumes):
- cover `matBox 2 2 T` by the `r² = 4` max-modulus-entry charts (`recStep`/`argmaxCellOn`);
- per chart, N1 (`radialDelta_loss_factor`) pulls the radial scale `a`, N3a/N3b the a-axis divisor;
- per chart, the angular `R'` (pivot entry `= 1`, others `≤ 1`) → permute the pivot to `(0,0)` (Jacobian
  `1`), apply N2b with `j = 1` → the split form `D = frobSq (R'·S)_top + frobSq (Sc·S_bot)`;
- the radial CoV identifies `(R'·S)_top` with a free `Fin 4` Morse block (the genuinely-remaining work).

This is the cert §4 N4 HIGH-risk assembly (`routeMCore_threshold_lt_top`, skeleton in `RouteMSchur`).
The note in N4's docstring now points at these two reduction ends + names the remaining weld precisely.

## Build / audit

- `lake build DLNFibre.DLN.RLCT.Validate.RouteMSchurDepth2` green; full `lake build DLNFibre` green
  (RouteMSchur docstring edits only — N2b/N3b "SKELETON" → "PROVED"; N4 docstring points at this
  validator).
- `scripts/sorries`: ZERO in `RouteMSchurDepth2`. (`RouteMSchur` retains the ONE honest N4 sorry, the
  multi-tide endpoint.)
- `#print axioms` (forced): all three `[propext, Classical.choice, Quot.sound]`.

## Status

`sorry-free` (the three reduction-end lemmas), `reviewed` (fidelity audit 2026-06-28: math sound,
sorry-free, S2-free, threshold-correct; the earlier "composition CLOSED/validator" framing was flagged as
overclaiming and has been corrected to "END-PIECES" — the lemmas are not chained, the core→split weld is
the deferred N4 step; the redundant `hF` hypothesis was dropped). Pending controller wire-in of the
`RouteMSchurDepth2` import into `DLNFibre.lean`.
