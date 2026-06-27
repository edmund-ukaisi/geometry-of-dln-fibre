# Statement card — `RouteMSchurDepth2` (the depth-2 recStep composition validator)

> **Module.** `DLNFibre.DLN.RLCT.Validate.RouteMSchurDepth2`
> (`lean/DLNFibre/DLN/RLCT/Validate/RouteMSchurDepth2.lean` @ `<uncommitted — controller pins SHA>`;
> base `origin/expedition/aoyagi-full`). Imports `RouteMSchur` (for N1/N2/N3) which pulls in the Morse
> terminal `S1RadialMorse` via `MatMulFibre`. NOT wired into `DLNFibre.lean` (single-writer aggregator —
> controller adds the import `RouteMSchurDepth2` after `RouteMSchur`).
>
> **Scope.** The **depth-2 regression test** for the rank-stratified radial-Schur recursion (cert §4 N4,
> `L32a-cover-cert.md`): the smallest binding corank-2 case (`r = 2`, ONE nested minor-pivot level). It
> validates that the certified pieces — N2b `schur_minorPivot_split` (the corank-2→corank-1 Schur drop),
> the radial-blow-up homogeneity N1, and the Morse terminal `radial_morse_dominates_lt_top` — **compose**
> into a finiteness proof, the way the ∀M N4 assembly needs. This is NOT the ∀M N4 endpoint
> (`routeMCore_threshold_lt_top`, still a skeleton in `RouteMSchur`); it is the composition-validation
> milestone, the leg's FIRST milestone per the dispatch brief.

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

- **`schurSplit_integrand_le`** — the pointwise integrand domination the recursion produces. For
  `c₀, c₁, D, F : ℝ` with `0 < c₀`, `0 ≤ D`, `0 ≤ F`, the two-sided N2b bounds `c₀·D ≤ F` and `F ≤ c₁·D`,
  and `0 < c'`:
  `ENNReal.ofReal (F^{−c'}) ≤ ENNReal.ofReal (c₀^{−c'}·D^{−c'})`.
  The inverse-power antitone flip of N2b's LOWER bound `c₀·D ≤ F` (`Real.rpow_le_rpow_of_nonpos`),
  zero-guarded by the UPPER bound (`c₀·D = 0 ⟹ D = 0 ⟹ F ≤ c₁·D = 0 ⟹ F = 0`). **Both sides of the
  two-sided N2b comparison are load-bearing**: the lower for the bound, the upper for the zero-guard.
  S2-FREE. (`F = frobSq(R·S)`, `D = frobSq (R·S)_top + frobSq (Sc·S_bot)` — the corank-2 → split-form
  recursion step.)
- **`schurSplit_lintegral_le`** — its integral form (abstract over a measure space `(Ω, μ)`). On a set
  `Z` where the N2b comparison holds pointwise (uniform `c₀, c₁ > 0`):
  `∫_Z F^{−c'} ≤ ofReal(c₀^{−c'}) · ∫_Z D^{−c'}`.
  `lintegral_mono` of the pointwise bound + `lintegral_const_mul'` pulls the `Z`-independent `c₀^{−c'}`
  out. The recursion's reduction of the corank-2 leaf to the split form `D`. S2-FREE.
- **`schurSplit_depth2_lt_top`** — the depth-2 composition CLOSED. For `0 ≤ c' < 2`, `0 < T`, and a
  nonneg measurable corank-1 residual `W : (Fin k → ℝ) → ℝ`:
  `∫_z ∫_P (∑ⱼ (P j)² + W z)^{−c'} < ⊤` over `morseBox k T × morseBox 4 T`.
  `P : Fin 4` is the top Morse block (`j·p = 1·4 = 4` entries of `(R·S)_top`), `W z` the corank-1 Schur
  residual `frobSq(Sc·S_bot) ≥ 0`. The Morse terminal `radial_morse_dominates_lt_top` (`m+1 = 4`,
  threshold `4/2 = 2 = λ_{2,4}`) bounds it by `Kbound 4 c' T · vol(morseBox k T) < ⊤`. **Validates the
  N2b-split ⟶ Morse-leaf composition at exactly the binding threshold** `2`. S2-FREE.

## English gloss (fidelity)

The certified recursion at corank 2: after the radial-blow-up change-of-variables (the heavy N4 cover
step) the corank-2 core integral becomes a split-form integral over `(P, z)`, where `P` is the disjoint
Morse block (the `j·p = 4` entries of the pivoted top row `(R·S)_top`) and `W z ≥ 0` is the corank-1
Schur residual `frobSq(Sc·S_bot)`. N2b's two-sided comparison reduces the core integral to this split
form (`schurSplit_lintegral_le`); the Morse terminal closes it at `c' < 4/2 = 2 = λ_{2,4}`
(`schurSplit_depth2_lt_top`). The three lemmas together demonstrate the corank-2 → corank-1 → corank-0
chain composes into finiteness at the right threshold.

## Hypotheses (the load-bearing ones)

- `schurSplit_integrand_le` / `schurSplit_lintegral_le`: the N2b two-sided comparison `c₀·D ≤ F ≤ c₁·D`
  with uniform `c₀, c₁ > 0` — exactly the conclusion of `schur_minorPivot_split` (N2b). Both directions
  needed (lower = bound, upper = zero-guard). `c' > 0` (the `c' = 0` constant case is the trivial
  volume bound, handled separately in the existing anchors).
- `schurSplit_depth2_lt_top`: `c' < 2` (= `λ_{2,4}`, the binding corank-2 threshold = `(m+1)/2` with the
  `j·p = 4`-entry Morse block); `W` nonneg + measurable (the corank-1 Schur residual, automatically
  nonneg as a `frobSq`).

## Deferred (the heavy N4 long pole — NOT this leg, the multi-tide endpoint)

The composition above takes the split-form integral over `(P, z)` as its starting point. The remaining
N4 gap is the **radial-blow-up change-of-variables** that turns the corank-2 core `∫_R frobSq(R·S)^{−c'}`
over the matrix box `matBox 2 2 T` INTO that split-form `(P, z)` integral:
- cover `matBox 2 2 T` by the `r² = 4` max-modulus-entry charts (`recStep`/`argmaxCellOn`);
- per chart, N1 (`radialDelta_loss_factor`) pulls the radial scale `a`, N3a/N3b the a-axis divisor;
- per chart, the angular `R'` (pivot entry `= 1`, others `≤ 1`) → permute the pivot to `(0,0)` (Jacobian
  `1`), apply N2b with `j = 1` → the split form `D = frobSq (R'·S)_top + frobSq (Sc·S_bot)`;
- the radial CoV identifies `(R'·S)_top` with a free `Fin 4` Morse block (the genuinely-remaining work).

This is the cert §4 N4 HIGH-risk assembly (`routeMCore_threshold_lt_top`, skeleton in `RouteMSchur`).
The note in N4's docstring now points at this validator + names the remaining gap precisely.

## Build / audit

- `lake build DLNFibre.DLN.RLCT.Validate.RouteMSchurDepth2` green; full `lake build DLNFibre` green
  (RouteMSchur docstring edits only — N2b/N3b "SKELETON" → "PROVED"; N4 docstring points at this
  validator).
- `scripts/sorries`: ZERO in `RouteMSchurDepth2`. (`RouteMSchur` retains the ONE honest N4 sorry, the
  multi-tide endpoint.)
- `#print axioms` (forced): all three `[propext, Classical.choice, Quot.sound]`.

## Status

`sorry-free` (the three composition lemmas). Pending controller wire-in of the `RouteMSchurDepth2`
import + a reviewer fidelity check (does the depth-2 split-form statement faithfully model the cert §4
N2b → Morse-leaf composition?).
