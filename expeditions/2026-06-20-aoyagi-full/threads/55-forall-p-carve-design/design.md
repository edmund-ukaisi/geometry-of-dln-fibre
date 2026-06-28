# ∀p generalization of the carve — design doc (Item-55)

**Status:** DESIGN-ONLY (no Lean, no build). Structure diff-gate APPROVED by controller (2026-06-28);
threshold CORRECTED (see §3 — `λ = ½·minAdm(r,r,p)`, quadratic; my earlier `(r−1)p/2` was wrong for p≠4).
Build gated on (i) STEP 0 pen-and-paper (does the blow-up achieve `½·minAdm`?), (ii) the binding-p=4 family
landing (#143 + genm-n4 front-peel-bridge), (iii) controller clearance.

**Scope (sharpened by controller + genm-n4/Codex, 2026-06-28).** This design is the **DEPTH-2
output-width** generalization ONLY: extend the `(r,r,4)` carve (`SchurCore 4 r`, depth-2, SQUARE left
factor, output width 4) to `(r,r,p)` = `SchurCore p r` for arbitrary `p = M(last)`. genm-n4 owns the
`(r,r,4)` build; this design EXTENDS it to general `p` — coordinate so they compose. The carve
(`schurRatioResidGen_mid` → `schurRecStep_four`, closed sorry-free + axiom-clean `[propext,
Classical.choice, Quot.sound]`) is hardcoded at `p = 4`; this doc maps the `p = 4 → ∀p` lift.

**OUT OF SCOPE — the depth-≥3 (L ≥ 3) generalization is a SEPARATE RESEARCH WALL (do NOT design here).**
genm-n4 + Codex established: the iterated-fibre (layer-by-layer) resolution caps the codimension at
`min_s M_s / 2` (the bottleneck single layer), but the target `½·minAdm` is a **SUM over the binding
rank path** (across layers). So for `L ≥ 3` the iterated/sequential carve is provably INSUFFICIENT —
reaching `½·minAdm` needs an **L-layer JOINT resolution = new geometry**, not an extension of this carve.
This is the named research wall (owned by genm-n4 + Codex / a future expedition); this design deliberately
does NOT address it. The depth-2 carve (`SchurCore p r`) is exact precisely because two factors with a
square left block admit the single-step Schur carve — that structure does not iterate to `L ≥ 3`.

The author's standpoint: I wrote the p=4 carve. This is a structural audit of *what `4` is doing* at each
step — distinguishing the places where `4` is **merely instantiated** (mechanical lift) from where the
**`p=4` structure is load-bearing** (a genuine wall) — strictly within the depth-2 `SchurCore p r` object.

---

## 0. The object, with `p` exposed

For corank `r` and output width `p`, the firing target is `SchurCore p r c' T`:

    ∫_{Δ ∈ matBox r r T} ∫_{S ∈ matBox r p T} ‖Δ·S‖_F^{−c'}  < ⊤   for 0 < c' < schurLambda(p) r.

The ABSTRACT recursion framework is **already `∀p`-parametric** — `SchurCore (p r)`, `SchurLowerIH (p lam r)`,
`SchurRecStep (p lam)` all take `p` as the first explicit argument (`RouteMSchurGeneral`). So the firing's
*contract* is already general; only the *p=4 instance* (`schurRecStep_four : SchurRecStep 4 schurLambda`)
and the threshold function `schurLambda : ℕ → ℝ` are specialized.

---

## 1. What becomes `p`-dependent (the lift surface)

### 1a. Box dimensions — MECHANICAL (merely instantiated)
- `matBox r 4 T` → `matBox r p T` (the `S`-box: `r × p`).
- `morseBox 4 (…)` → `morseBox p (…)` (the peeled spectator block is the top ROW of `S`, width `p`).
- `frobSq (… : Fin _ → Fin 4 → ℝ)` → `Fin p`.
- In my support lemmas: `GinnerGA` (`matBox (r-1) 4` / `morseBox 4`), `stepShearG` (`matBox (m+1) 4` /
  `morseBox 4`), `topRow_*A` (`∑ q : Fin 4`), `measurable_GinnerGA_carve`, the `Fin 4` row indices.
  Every `4` here is a **free width**; replacing with `p` is a verbatim re-parametrization. NONE of these
  proofs read `4` numerically — they sum/integrate over `Fin 4` opaquely.

### 1b. The threshold function `schurLambda` — THE genuine `p`-dependence
`schurLambda r = 2r − 2` (r≥2) is the **p=4** threshold. The general threshold is a function of BOTH `(r,p)`.
The radial blow-up at chart `q` contributes a Jacobian `|y q|^{N}` with `N = r·p − 1` (the flat ratio
count: `r·p` cells minus the pivot). The a-axis divisor is finite for `c' < (r·p)/2` (the
`chart_integrand_factorG` / `schur_matBoxG_chart_lt_top` divisor exponent). The recursion peels a width-`p`
Morse block (threshold `p/2`) and recurses at corank `r−1`. So:

    λ(p, r) = the sup of c' for which SchurCore p r is finite.

**Claim (to verify numerically before build):** `λ(p, r) = (r−1)·p / 2 + something`? Let me derive from the
recursion rather than guess. The peel: `c' ↦ c'' = c' − p/2` (Morse threshold `p/2` for the `Fin p` block),
then recurse at corank `r−1`. The recursion bottoms at `r = 1` (the Morse leaf: `Δ` is `1×1`, `S` is
`1×p`, the integrand is `(Δ₀₀·S)`-radial — finite for `c' < p/2`, mirroring `schurCore4_one`'s `c' < 1/2`
at p=1... NO: `schurCore4_one` is `c' < 1/2` for the p=4, r=1 leaf). **Flag: the leaf threshold is the
first place to re-derive carefully — for p=4 it is `1/2`, NOT `p/2 = 2`.**

So the p=4 ladder is `λ(4,1) = 1/2`, `λ(4,2) = 2`, `λ(4,3) = 4`, `λ(4,r) = 2r−2`. The increment from
`r−1` to `r` is exactly `2` = `p/2`. This strongly suggests:

    λ(p, r) = (r − 1)·(p/2) + λ(p, 1),   with λ(p, 1) = ?  (the r=1 leaf, the OTHER input).

For p=4: `(r−1)·2 + 1/2`? That gives `λ(4,2) = 2.5`, NOT `2`. So the naive `(r−1)·p/2 + leaf` is WRONG —
the recursion is NOT a clean arithmetic ladder. **This is the single most important thing to nail before any
build:** re-run `Vzero_lambda_recursion.py` (the script `schurLambda`'s docstring cites) at general `p` to
get the closed form `λ(p, r)`, and re-derive the leaf `λ(p, 1)`. The p=4 closed form `2r−2` is a coincidence
of `p=4`; the general form is the deliverable's crux.

### 1c. The N2b split — ALREADY `∀p`
`schur_minorPivot_split {r p} (j) (hj : j ≤ r)` is **already general in `p`** (`RouteMSchur`). The two-sided
comparison `c₀·(frobSq(R·S top j rows) + frobSq(Sc·S_bot)) ≤ frobSq(R·S) ≤ c₁·(…)` holds for any output
width `p`. At `j=1` the readback `Sc = M22 − M21·M11⁻¹·M12 = M22 − g·bᵀ` is `p`-independent (it's about the
`r×r` matrix `R`, not `S`). **Zero lift work here** — my `schur_minorPivot_split` call already passes
`(p := 4)`; just pass `(p := p)`.

### 1d. The cell enumeration `cellR` / `zσG` / `zEG` carve — `p`-INVARIANT
The carve is over the `r²−1` ANGULAR RATIOS `z` of the `r×r` matrix `R` (NOT of `S`). `cellR` enumerates the
off-(0,0) cells of `Fin r × Fin r`; `zσG : Fin (r²−1) ≃ (M22 ⊕ g ⊕ b)`; `zEG` reshapes. **None of this
touches `p`** — `p` only enters `S`, which the carve does not reshape. So `cellR`, `zσG`, `zEG`,
`RmatGnorm_eq_slot`, `zσG_slot`, `RmatGnorm_carve_*`, `schurSc_carve_eqA` all lift VERBATIM (the `N = r²−1`
is `p`-free). **This is the biggest reuse win: the hardest sub-step (the carve) is already ∀p.**

### 1e. The IH structure — `∀p` framework, `p`-threaded
`SchurLowerIH p schurLambda r` and `coreSchurGenVal_lt_top` already take `p`. The IH-invoking core
`schurResidG_translate_lt_top` / `resolvedShiftRG_le` integrate `S` over `matBox (r−1) 4` — these need
`4 → p`. The translate-enlarge (`matBoxSq_translate_le`) is `p`-free (it's the `Δ` matrix-space shift).

---

## 2. What is `p`-invariant (reusable as-is)

| Component | `p`-status |
|---|---|
| pivot-WLOG (`frobSq_rmatMul_permG`, `matBox_rowperm_lintegralG`, `innerSGen_eq_norm`) | invariant (permutes `R` rows/cols + `S` rows; `p` = `S` columns, untouched) |
| the carve `cellR`/`zσG`/`zEG`/`measurePreserving_zEG`/`zEG_symm_apply`/`zσG_slot` | invariant (`N = r²−1`, `p`-free) |
| the Sc readback `RmatGnorm_carve_M22/_g/_b`, `schurSc_carve_eqA` | invariant |
| N2b split `schur_minorPivot_split` | already ∀p |
| the `Δ`-translate `matBoxSq_translate_le`, `matOfGEquivA` (curry the `r−1` × `r−1` M22 block) | invariant |
| the outer `(g,b)`-box finite volume | invariant (`vbox` over `Fin (r-1) ⊕ Fin (r-1)`, `p`-free) |
| `ofReal_rpow_le_const_mul` (antitone rpow), `bgShiftG`/`bgShiftG_entry_le` | invariant |

The Tonelli peel `core_T_peel_le_aeG (m)` is `∀m` — instantiate `m = p − 1` (the `Fin p` block is
`morseBox p`, peeled via `radial_morse_residual_power_le (p−1)` at threshold `((p−1)+1)/2 = p/2`).

---

## 3. The threshold arithmetic (the load-bearing check)

The p=4 chain closes because:
- N2b peels a `Fin 4` Morse block at threshold `4/2 = 2`, leaving `c'' = c' − 2`.
- The recursion needs `c'' < schurLambda(r−1)`, i.e. `c' − 2 < 2(r−1) − 2 = 2r − 4`, i.e. `c' < 2r − 2 =
  schurLambda r`. ✓ (exactly the firing window).

### CORRECTED THRESHOLD (controller diff-gate, 2026-06-28 — my earlier `(r−1)p/2` was WRONG for p≠4)

**The true threshold is `½·minAdm(r,r,p)`, QUADRATIC in `p`.** My earlier conjecture `λ(p,r) = (r−1)·p/2`
(from a naive "each peel adds `p/2`" ladder) is WRONG for `p ≠ 4` — it matches `½·minAdm` only at `p=4`
(a coincidence). The kill-condition I flagged FIRED. Definitions and the corrected form:

    minAdm(r,r,p) := min_{t = 0..r} [ (r − t)² + p·t ]        (type-A codim of the rank-(r−t) stratum)
    λ_true(p, r)  := ½ · minAdm(r,r,p).

Numerically verified (controller + my recheck):
- `½·minAdm` matches `(r−1)p/2` ONLY at `p=4`: e.g. (2,4)→2, (3,4)→4, (4,4)→6, (5,4)→8 all agree;
  but (3,6): `½·minAdm = 4.5` vs `(r−1)p/2 = 6` → my formula OVERSHOOTS = claims finiteness PAST the
  divergence point = IMPOSSIBLE. Likewise (4,8): 8 vs 12, (4,6): 7.5 vs 9, (3,5): 4.5 vs 5.
- The continuous closed form `(pr − p²/4)/2` (controller's) = the min of the RELAXED `(r−t)² + pt` over
  REAL `t` (minimizer `t* = r − p/2`), valid for `p ≤ 2r` (else the min is at `t=0`, value `r²/2`). It
  EQUALS `½·minAdm` (integer-`t` min) exactly when `r − p/2 ∈ ℤ` (p even); for ODD `p` they differ slightly
  (e.g. (3,3): integer `½·minAdm = 3.5` at t=1, continuous `3.375` at t*=1.5). **So the Lean threshold must
  be the INTEGER min `½·min_t[(r−t)²+pt]`, NOT the continuous `(pr−p²/4)/2`** — the latter under-states by
  up to `p²/8 −` floor effects at odd `p`, which would WRONGLY claim divergence inside the finite window.
  (`p=4` is even, so the corank-3/4 instances never saw this — another p=4 coincidence.)

The binding stratum is `t* = argmin` (the rank-drop that minimizes the codim): `t* = max(0, round(r − p/2))`
roughly — for `p` small (`p ≤ 2`) `t*` is large (drop almost to 0), for `p` large (`p ≥ 2r`) `t* = 0` (no
drop, codim `r²`). This `t*`-dependence is why the threshold is NOT a clean per-corank ladder: the binding
stratum MOVES with `p`, so the recursion's IH threshold is itself the quadratic `½·minAdm(r−1,r−1,p)`, and
the per-step increment `λ_true(p,r) − λ_true(p,r−1)` is NOT constant `p/2` (it varies with where `t*` sits).
That is exactly the structural reason the naive ladder failed.

### THE GENUINE OPEN SUB-PROBLEM (the real ∀p content — pen-and-paper, BEFORE any build)

Does the SchurCore-`p` radial blow-up + N2b-peel recursion ACHIEVE the threshold `½·minAdm(r,r,p)`? I.e.:

    Is  SchurCore p r c' T < ⊤  for ALL c' < ½·minAdm(r,r,p),  and DIVERGENT at c' = ½·minAdm?

This is NOT mechanical — at `p=4` the blow-up achieved `2r−2 = ½·minAdm(r,r,4)` because the binding stratum
`t*` and the Morse-peel exponent lined up; for general `p` the **per-step peel exponent and the binding
stratum `t*` must be re-derived together**, and the recursion must be re-cast so its IH threshold is the
quadratic `½·minAdm(r−1,r−1,p)` (NOT `λ(p,r−1) = (r−1−1)p/2`). Concretely the pen-and-paper deliverable:
1. derive the SchurCore-`p` Morse/peel threshold as a function of `(r,p)` (the a-axis divisor `c' < (r·p)/2`
   from `chart_integrand_factorG`, intersected with the recursive residual window);
2. show the recursion closes EXACTLY up to `½·min_t[(r−t)²+pt]` (the integer min) — the threshold function
   `schurLambdaP p r := ½·minAdm(r,r,p)` is the right Lean def, and the firing window is `c' < schurLambdaP`;
3. identify which stratum `t*` is binding per `(r,p)` and confirm the blow-up resolves it (the divergence
   side — kill-condition: if the blow-up only reaches some `λ' < ½·minAdm`, the ∀p firing is INCOMPLETE
   and needs a different chart, not just a re-parametrization).

Until (1)-(3) are settled pen-and-paper, the ∀p build is NOT mechanical — the threshold is the crux, and the
firing's recursive window must be re-derived against the quadratic `½·minAdm`, not the linear ladder.

---

## 4. Load-bearing `p=4` structure (genuine walls vs instantiation)

After the audit, the `4`s split as:

**MERELY INSTANTIATED (mechanical lift, ~no risk):** all box dims (§1a), the Tonelli peel width (§2),
the N2b split (§1c, already ∀p), the carve (§1d, `p`-free).

**LOAD-BEARING (genuine design content):**
1. **The threshold function `schurLambdaP p r := ½·minAdm(r,r,p)`** (§3, CORRECTED) — QUADRATIC in `p`,
   binding stratum `t*` moves with `p`. This is the ONE genuine wall: the pen-and-paper sub-problem (does
   the blow-up ACHIEVE `½·minAdm`?) must be settled before the build. Everything else is plumbing GIVEN the
   threshold. The recursion must be re-cast against the quadratic IH `½·minAdm(r−1,r−1,p)`, not a linear
   ladder. **Lean def must use the INTEGER min `½·min_t[(r−t)²+pt]`, not the continuous `(pr−p²/4)/2`**
   (they differ at odd `p`; the continuous form under-states the window).
2. **The base finiteness lemmas** (`schurCore4_one`/`_two` analogs) at the strata the recursion bottoms on —
   their thresholds are the `½·minAdm` values at the binding `t*`. For general `p` the bottom may NOT be
   `r=1` (if `t* < r` the binding stratum is a higher-rank drop), so the leaf/base structure itself is
   `p`-dependent — re-derive per the §3 sub-problem.
3. **`p` parity + the binding-family restriction** — the integer-vs-continuous threshold gap is an ODD-`p`
   effect (p=4 even hid it). The *binding* family (genm-n4) restricts `p` to admissible last-layer widths
   (`p = M(last)`); the ∀p design sits ABOVE it — do NOT re-derive genm-n4's binding-p=4 hfin; consume its
   front-peel-bridge spec for the `p = M(last)` instantiation.

---

## 5. Build plan (AFTER controller clearance + binding family lands)

**STEP 0 (pen-and-paper, GATING — the corrected crux): settle the §3 sub-problem** — derive the SchurCore-`p`
peel threshold as a function of `(r,p)` and prove the recursion achieves EXACTLY `½·minAdm(r,r,p)` (integer
min); identify the binding stratum `t*(r,p)` and confirm the blow-up resolves it (divergence side). This
REPLACES the old "numerical check of `(r−1)p/2`" — that conjecture is dead. No Lean until STEP 0 lands.

Then, in dependency order (each a separate, gated tide):
1. **`schurLambdaP p r := ½·minAdm(r,r,p)`** (`minAdm` = the integer min) + `schurLambdaP_pos` + the
   binding-stratum lemma (`t*`). Per STEP 0.
2. **Base finiteness** at the binding strata (the `p`-dependent bottom of the recursion — NOT necessarily r=1).
3. **Lift the firing file `4 → p`**: re-parametrize `GinnerGA`/`stepShearG`/`topRow_*A`/`resolvedShiftRG_le`/
   `coreSchurGenVal` (all `Fin 4 → Fin p`); the carve lifts verbatim. Mechanical given §1a/§1d — BUT the
   recursive window must be threaded against the quadratic `½·minAdm`, not the linear ladder.
4. **`schurRecStepP : SchurRecStep p schurLambdaP`** (the ∀p firing) + wire to `RouteMBoxThresholdFinite ∀p`.

**Estimate (line counts, not wall-clock):** STEP 0 is pen-and-paper (the real risk, unknown until done);
§1 ~60 lines (minAdm def + pos + t*); §2 ~150+ (base finiteness, `p`-dependent count); §3 the carve ~700
lines lift verbatim + ~150 lines box-dim/window-rethread friction; §4 ~50 (dispatch). Risk is ENTIRELY in
STEP 0 + the window-rethread in §3 (the recursion against the quadratic threshold) — NOT a pure token-swap
as I first scoped.


### Coordination + template (genm-n4, 2026-06-28)
- **`minAdmRec` tactic idiom (genm-n4, build-time)**: `minAdmRec_rr4_ge2` (`origin/genm-n4 RouteMBoxThresholdRR4.lean:63-83`, + `four_mul_le_sq_add_four`, `rr4_term_ge`) dodges the inf'-dependent-nonempty-motive trap by reducing `(![r,r,4]) 0/1 = r` in the LEAF goals (NEVER rewriting `min` under `inf'`). Transfers verbatim to ∀p (the `(![r,r,p]) 0/1` reductions) — use this exact tactic shape for the `minAdm(r,r,p)`-recursion lower-bound lemma.
- **Box-reduction infra is genm-n4's** (landed, reviewer-survived on `origin/genm-n4`): `RouteMBoxThresholdFinite`,
  `routeMCore_le_matBox`, `routeMCore_threshold_lt_top_of_box`. The ∀p build CONSUMES these — does NOT redefine.
- **The `minAdm` integer-min lower-bound template**: genm-n4's `minAdmRec_rr4_ge2`
  (`RouteMBoxThresholdRR4.lean`) is the inf'-over-`Finset.range` route with explicit witness `t = r−2` and the
  `(s−2)² ≥ 0` core — the EXACT shape `schurLambdaP p r := ½·minAdm(r,r,p)`'s lower bound needs. Generalize the
  witness `t = r−2 → t*(r,p) = argmin_t [(r−t)²+pt]` (and track its parity-dependent closed value); the inf'-witness
  structure carries verbatim. Build the ∀p threshold-bound ON this, don't re-derive.
- **Boundary check at p=4**: genm-n4's `minAdm_rr4_eq` (`½·minAdm(![r,r,4]) = schurLambda r`, un-halved `4r−4`) is
  EXACTLY `schurLambdaP 4 r` — the ∀p firing window specializes to the binding-p=4 window, so they compose at p=4.


## STEP-0 RESOLUTION (the ∀p gate) — derivation + decorrelated Codex verdict (2026-06-28)

**Verdict: the depth-2 ∀p firing is REACHABLE — `½·minAdm(r,r,p)` IS achievable — but needs ONE new chart
(the `{Δ=0}` divisor) beyond the lifted p=4 carve.** My derivation and a decorrelated Codex (gpt-5-codex,
xhigh) CONVERGED; Codex added a sharper mechanism for why p=4 hid the new chart.

### The exact recursion identity (mine; Codex independently re-derived it algebraically)
    ½·minAdm(r,r,p) = min( ½·minAdm(r−1,r−1,p) + p/2 ,  r²/2 ),    base ½·minAdm(1,1,p) = ½.
Codex's algebra: split `minAdm = min_{t≥0}[(r−t)²+pt]` at t=0 vs t≥1; for t≥1 put `t=1+u` ⟹
`p + [(r−1−u)²+pu] = p + minAdm(r−1,r−1,p)`. So the min of the two caps is exact (verified numerically r≤9,p≤11).

### The two caps = two divergence strata of the rank-drop locus of `Δ·S` (`Δ:r×r`, `S:r×p`)
- **Cap A — PEEL-RECURSE `½·minAdm(r−1,r−1,p) + p/2`** (the rank-drop cascade, `t* ≥ 1`): the EXISTING carve.
  Peel a width-`p` Morse block at threshold `p/2`, recurse at corank `r−1`. The carve is p-INVARIANT (reshapes
  only the `r×r` ratio block, `N=r²−1` p-free) — lifts verbatim.
- **Cap B — NO-RANK-DROP `r²/2`** (the stratum `{Δ = 0}`, `t* = 0`): `{Δ=0}` has codim `r²` in `ℝ^{r×r}×ℝ^{r×p}`;
  the `r×p` entries of `Δ·S` have linear parts spanning an `r²`-dim space (rank `r²` once `S` is full rank), so the
  ideal is a NORMAL CROSSING of `r²` independent linear forms → RLCT `= codim/2 = r²/2`; `‖Δ·S‖^{−c'}` diverges
  there exactly for `c' ≥ r²/2`. (Codex Q2, confirmed.)

### The binding stratum `t*(r,p)` MOVES (crossover at `p = 2r`)
`t* = argmin_t[(r−t)²+pt]`; continuous minimizer `t* = r − p/2`. So cap A (`t*≥1`) binds for `p < 2r`, cap B
(`t*=0`, `r²/2`) binds for `p ≥ 2r`. **Why p=4 hid cap B (Codex's sharper mechanism):** the p=4 radial chart
FIXES a nonzero PIVOT entry of `Δ` before introducing ratio coordinates — this structurally EXCLUDES a
neighborhood of `{Δ=0}`, so the p=4 proof never exposes the `Δ=0` divisor. For p=4, cap A dominates for all
r≥3 (and r=2 is the corank-2 base, where `r²/2=2` is handled directly), so the omission went unnoticed. For
`p ≥ 2r` cap B BINDS and the pivot-fixing chart MISSES it — the naive a-axis divisor `(r·p)/2` overshoots
`r²/2` (e.g. (3,6): `(rp)/2=9` vs true `4.5`), wrongly claiming finiteness past the `Δ=0` divergence.

### The genuine NEW content (the only non-mechanical piece)
A **`{Δ=0}` chart / divisor**: an additional chart that keeps `Δ` itself radial (does NOT pivot-fix away from
`Δ=0`), delivering the `r²/2` valuation. This is the normal-crossing estimate on the `r²` independent linear
forms — standard RLCT-of-normal-crossing, NOT a research wall. NO deeper obstruction (Codex Q5): the r→r−1
induction only feeds cap A, so switching to cap B at higher rank does not invalidate lower-r IH.

### Integer-min (Codex Q4, confirmed)
The singular set is stratified by INTEGER rank drops; the Lean threshold is `½·min_{t∈{0..r}}[(r−t)²+pt]`,
NOT the continuous `(pr−p²/4)/2` (which under-states at odd p, e.g. (3,3) 3.375 vs 3.5).

### Updated build plan delta (STEP-0 → build)
The §5 build now has, BEFORE the firing: a `minAdm`-recursion lemma (`½minAdm = min(peel+p/2, r²/2)`, Codex's
t=1+u algebra, ~25 lines on genm-n4's `minAdmRec` inf'-witness template) + a **`{Δ=0}` normal-crossing chart**
(the new cap-B chart, ~the only genuinely new analytic lemma — a normal-crossing RLCT bound on `r²` linear
forms; medium, NOT a wall). The lifted p=4 carve supplies cap A. Dispatch picks `min(A,B)` by `t*` vs `p=2r`.

**STEP-0 PASSES: ∀p depth-2 firing is reachable. Gate cleared (pending controller diff-gate of this section +
the binding-p=4 family). Build remains next-layer (no rush).**


## CAP-B {Δ=0} CHART DESIGN (controller-gated, surface BEFORE deep-build) — cert-grounded

The controller cleared the ∀p build with ONE gate: surface the cap-B {Δ=0} chart design first. After Codex
(2nd decorrelated consult on the capA>capB overclaim) I found this is ALREADY worked pen-and-paper in-repo:
**`expeditions/2026-06-20-aoyagi-full/threads/27-r1-hfin-completeness/Vzero-termination-cert.md`** (pen-and-paper
seat, Codex-red-teamed, VERDICT: S2-only feasible, depth ≤ r). My STEP-0 independently reproduced its recursion.
This design CONSUMES that cert as the authoritative resolution; below is the chart structure + the Lean shape.

### The architecture correction (important): cap B is NOT a bolt-on chart — it's the RADIAL AXIS of the
### `Δ = a·R` blow-up; cap A is the ANGULAR part of the SAME blow-up.
The honest resolution of `SchurCore p r` is the **`Δ = a·R` radial blow-up** (cert §1,§3):
- `Δ = a·R`, `a ∈ [0,T]` the scale, `R` on the bounded `r²`-chart atlas (chart-`(i,j)`: `|Δ_{ij}|` maximal ⟹
  `R_{ij}=1`, `|R_{kl}| ≤ 1` — unit polydisc, angular coords BOUNDED). Jacobian `|a|^{r²−1}` (≠ 0 off `a=0`,
  a genuine c-o-v; the `r²` charts cover `{Δ≠0}`, `{Δ=0}` is the `a=0` null divisor).
- `‖Δ·S‖² = a²·‖R·S‖²`. So `(frobSq(Δ·S))^{−c'} = a^{−2c'}·(frobSq(R·S))^{−c'}`.
- **`a`-axis = CAP B**: `∫₀^T a^{(r²−1) − 2c'} da < ⊤ ⟺ (r²−1) − 2c' > −1 ⟺ c' < r²/2`. (Cert line 53:
  corank-2 `∫a^{3−2c'} ⟺ c'<2 = r²/2`. The `r²−1` is the Jacobian dim; the `−2c'` is the SQUARED-Frobenius.)
- **angular `R`-integral = CAP A**: `∫_{R atlas} (frobSq(R·S))^{−c'}` is the EXISTING carve (`R` pivot-normalized,
  the rank-stratified Morse-block ⊕ lower-core recursion) — threshold capA = `½minAdm(r−1,r−1,p)+p/2` (in fact
  the full `min_{1≤j≤r}(jp/2 + λ_{r−j,p})`, cert line 107). p-INVARIANT (the carve reshapes only R's r² ratios).
- **JOINT (Δ,S) σ_min→0 worry, RESOLVED** (Codex Q3 + cert §4c-2): after `Δ=a·R` and pivot-normalizing R on
  each bounded chart, the inner `‖R·S‖²` is a UNIFORMLY-elliptic Morse form in S (the bounded unit-polydisc R
  gives uniform lower bounds); Tonelli + the radial disjoint-sum lemma keep it uniform despite σ_min(SSᵀ)→0.
  So the fixed-S non-uniform bound is NOT the route — the bounded-angular-chart localization is.

### Why this is the CORRECT fix for the capA>capB overclaim (p ≥ 2r)
The window is `c' < min(capA, capB)` = the INTERSECTION (both the `a`-axis AND the angular integral must be
subcritical): the product `a^{−2c'}·(frobSq(R·S))^{−c'}` is integrable iff BOTH factors are (Tonelli, disjoint
var groups `a` vs `(R,S)`). The p=4 carve omitted the `a`-axis factor (its chart fixed a nonzero pivot of Δ,
EXCLUDING `a→0`), so it only ever saw capA — fine for p=4 (capA ≤ capB for r≥3) but OVERCLAIMS for p≥2r. The
`Δ=a·R` blow-up restores the `a`-axis factor → the min binds correctly.

### The genuinely-new Lean lemma (cap B, the only new analytic content)
`schurCore_radialAxis_lt_top` (shape): `∫₀^T a^{(r²−1)−2c'} da < ⊤` for `c' < r²/2` — a 1-D radial-divisor
integral, S2-free (Mathlib `integrableOn` of `a^k` on `[0,T]`, or the existing `radial_aAxis_divisor_lt_top`
generalized from the p=4 `a`-axis to exponent `r²−1`). Then the JOINT finiteness:
`schurCore_p_lt_top (c' < ½minAdm) = a-divisor (capB) ⊗ angular-carve (capA)` via Tonelli + `lintegral_const_mul`.
The angular carve is the lifted existing carve (cap A); the disjoint-sum glue `rlct(‖P‖²+H)=½dimP+rlct(H)`
(cert line 104, S2-free radial integration) is the rank-stratified recursion's step — ALREADY the carve's
`stepShearG`+`resolvedShiftRG_le` shape, generalized.

### Build plan (cap B), gated:
1. `radial_aAxis_divisor_lt_top` at exponent `r²−1` (generalize the p=4 `a`-axis lemma; ~15L, S2-free).
2. The `Δ = a·R` blow-up c-o-v (Jacobian `|a|^{r²−1}`) — generalize the p=4 `pivotBlowup`/`chart_integrand_factorG`
   to expose the `a`-axis (the p=4 version folds it into the chart; need the `a` factor explicit). ~MEDIUM.
3. Joint Tonelli: `SchurCore p r < ⊤ ⟺ c' < min(capB [a-axis], capA [angular carve])`. ~30L given 1,2 + the carve.
The cert's corank-2 worked identity (`G∘π = a²·[(1+v²)‖P'‖² + (e²/(1+v²))‖Q‖²]`) is the validate-small anchor.

**Surfacing for diff-gate.** The cap-B chart = the `a`-axis of the `Δ=a·R` blow-up at threshold r²/2 (cert-grounded,
S2-free). The architecture correction (cap A = angular part of the SAME blow-up, NOT a parallel chart; window =
INTERSECTION via the product factorization) is the load-bearing design point — please diff-gate that framing
before I deep-build. No new geometry beyond the cert; bounded-medium confirmed (2 Codex consults + the cert).


## BUILD-TIME FINDING (2026-06-28, during deep-build setup): CAP-B IS ALREADY BUILT; the real gap is N4

Setting up the deep-build, I found the cap-B `{Δ=0}` chart machinery **ALREADY EXISTS, sorry-free, and
`{r p}`-GENERAL** in `lean/DLNFibre/DLN/RLCT/Validate/RouteMSchur.lean`:
- `radialDelta_loss_factor {r p}` — the `|a|^{r²−1}·(a²·F)^{−c'} = |a|^{(r²−1)−2c'}·F^{−c'}` factorization (N1).
- `radial_aAxis_divisor_lt_top (r)` — the `a`-axis `∫|a|^{(r²−1)−2c'} < ⊤ ⟺ c' < r²/2` (cap B, exactly).
- `radial_loss_chart_lt_top {r p}` — the FULL `Δ=a·R` per-chart blow-up: `∫_a∫_R |a|^{r²−1}·frobSq((a·R)·S)^{−c'}
  < ⊤` for `c' < r²/2` GIVEN the inner angular finiteness `hSfin`. This IS cap-B ⊗ cap-A (the `hSfin`), the
  window-intersection — precisely the architecture this design specified. p-general already.

So the cap-B chart is NOT new content to build — it is DONE. **The actual remaining gap for the ∀p (and the
whole-`M`) hfin is N4**: `routeMCore_threshold_lt_top {L} (M : Fin (L+1)→ℕ) (c' < minAdm M / 2)` (RouteMSchur.lean
line ~429, `sorry`) — the depth-`r` WellFounded-on-corank cover assembly (cert §4 N4, "the HIGH-risk long pole"):
cover `routeMBaseNbhd M` by `recStep` over the `r²` radial-`Δ` charts, apply N3 (`radial_loss_chart_lt_top`),
stratify by the N2 minor-pivot Schur split, peel the Morse block, RECURSE on the corank-`(r−j)` core. This N4
is stated ∀M (hence ∀p) ALREADY — it is NOT output-width-specific.

**RE-SCOPE (surfaced to controller):** the ∀p firing does NOT need a new cap-B chart (built) nor a separate
∀p firing file (the carve is the angular `hSfin`, already closed). It needs the N4 recursion assembly — which
is the SHARED whole-`M` hfin long pole, HIGH-risk, NOT the bounded-medium cap-B task. The two corank-2 ENDS of
N4 are built in `RouteMSchurDepth2` (`schurSplit_integrand_le`/`schurSplit_lintegral_le` + the Morse terminal
`schurSplit_depth2_lt_top`); the unbuilt weld is the radial-blow-up c-o-v turning the core-over-the-box into
the split form, summed over `r²` charts by `recStep`. That is the genuine remaining work, and it is the same
N4 the immediate-path hfin needs — not a separable ∀p-only deliverable.

## 6. Open questions for the controller / pen-and-paper (UPDATED)

- Q-A (RESOLVED): `λ(p,r) = (r−1)p/2` is WRONG for p≠4; the true threshold is `½·minAdm(r,r,p)` (quadratic).
  The Lean def uses the INTEGER min `½·min_t[(r−t)²+pt]` (the continuous `(pr−p²/4)/2` under-states at odd p).
- Q-B (THE CRUX, STEP 0): does the SchurCore-`p` radial blow-up ACHIEVE `½·minAdm(r,r,p)` (both finiteness
  for `c' < ½·minAdm` AND divergence at the boundary)? Pen-and-paper, gating the build. The binding stratum
  `t*(r,p)` and the per-step peel exponent must be re-derived together against the quadratic IH.
- Q-C: does the binding family (genm-n4) restrict `p`, and does its front-peel-bridge spec fix the
  `p = M(last)` instantiation? (The ∀p design sits above the binding family.)
- Q-D (parity): handle the odd-`p` integer-vs-continuous threshold gap — confirm the Lean `minAdm` integer
  min is the divergence point at odd `p` (the geometric codim is over integer strata, so yes — but the
  blow-up must match it, not the continuous relaxation).

## 7. The depth-≥3 boundary (explicit out-of-scope marker)

This design covers EXACTLY the depth-2 object `SchurCore p r` = `∫∫ ‖Δ·S‖^{−c'}` (one square left factor
`Δ`, one output-width-`p` factor `S`). It is the `(r,r,p)` family. The boundary where this design STOPS:

- **Depth ≥ 3 is NOT an extension of this carve — it is a research wall (genm-n4 + Codex finding).** The
  per-layer iterated resolution caps codim at `min_s M_s/2`; the target `½·minAdm` is a SUM over the binding
  rank path; closing the gap at `L ≥ 3` needs an L-layer JOINT resolution (new geometry). The single-step
  Schur carve (this design's engine) does not iterate to that. Owned by genm-n4 + Codex / a future
  expedition. Do not build the depth-≥3 case off this design.
- Concretely: the depth-2 threshold is `½·minAdm(r,r,p) = ½·min_t[(r−t)²+pt]` (single `Δ·S`, binding
  rank-drop `t*`). The depth-≥3 codim is a different object — `½·minAdm` over the FULL chain `M` is a SUM
  over the binding rank PATH (min over per-edge drops), not this single-factor min. So the depth-2
  `½·minAdm(r,r,p)` does NOT transfer to L≥3; that's the research wall.

So: this design + the depth-2 `(r,r,p)` build it scopes = the FULL output-width generalization; the depth
generalization is a clearly-separated, named research wall, not part of this thread.

## 8. DEPTH-2 N4 WELD ASSESSMENT (2026-06-28, controller-commissioned, design-only)

**Question (controller):** is the DEPTH-2 part of N4 — the `(r,r,p)` cover weld (the done radial charts +
genm-n4's `(r,r,4)` recStep template, extended to `(r,r,p)`, NO L-layer joint) — separably BOUNDED (→ a real
bounded `(r,r,p)` ∀p-hfin deliverable), or does it bleed into the depth-≥3 N4 long pole?

**Verdict: the depth-2 `(r,r,p)` hfin is SEPARABLY BOUNDED — it does NOT touch the depth-≥3 long pole.** It is
a genuine bounded `(r,r,p)` ∀p-hfin deliverable. Evidence, from reading the landed depth-stratified infra:

**(i) The two-matrix-box reduction is the depth-2 essence, and it is ALREADY GENERIC in `r` (genm-n4).** The
N4 statement `routeMCore_threshold_lt_top {L} M` quantifies over all `M`, but its proof at depth-2 does NOT go
through the depth-`r` WellFounded-on-corank `recStep` Schur-ATLAS (the abandoned `RouteMSchur` route). It goes
through the **two-matrix-box reduction**: dominate the open box by the closed cube → transport via
`paramsEquivFlat` (MP) → reshape via a depth-2 MP equiv `eParams` splitting `Params (![r,r,p])` into EXACTLY
two factors `(A0 : matBox r r, A1 : matBox r p)` → Tonelli to `∫_{A0}∫_{A1} frobSq(A0·A1)^{−c'}`. This is the
`(3,3,4)` route (`routeMCore_M334_le_matBox` + `matBox334_blowup_lt_top`, both sorry-free, S2-free, axiom-clean
at RouteM334{Hfin,Ratiofin}). genm-n4 has ALREADY built this reshape generic in `r`: `eParamsRR4 (r)`,
`measurePreserving_eParamsRR4 (r)`, `eParamsRR4_preimage_box (r)`, `frobSq_prod_eq_eParamsRR4 (r)`,
`routeMLayerBoxIntegral_rr4_eq (r)`, `routeMBoxThresholdFinite_rr4_of_schurRecStep (r)` (RouteMBoxThresholdRR4,
sorry-free ∀r, gated only on `schurRecStep_four`). The ONLY thing fixing `p=4` in genm-n4's build is the
threshold-arithmetic (`rr4_term_ge`, `minAdmRec_rr4_ge2`, `minAdm_rr4_eq`) and the box-integral gate
`schurRecStep_four`. The MP reshape itself is `prod (![r,r,p]) A = A0·A1` — a SINGLE matrix product — for any
`p`, generic.

**(ii) Why this is the wall against L≥3, structurally.** `prod M A = A⁽¹⁾·…·A⁽ᴸ⁾` is a product of `L` matrices
(`Foundations/Loss.lean:48`). At depth-2 (`M : Fin 3 → ℕ`, `L=2`, two layers) the product is `A0·A1` — one
`frobSq(A0·A1)`, reducible to a two-box integral, then the SINGLE radial-`Δ` blow-up of the done charts. At
depth-3 (`M4422`, `L=3`) the reshape is into THREE boxes `(A2,A1,A0)` and the integrand is
`frobSq(rmatMul (rmatMul A0 A1) A2)` — a product of three matrices, bounded by a depth-3-SPECIFIC argument
(`triple_fibre_lt_top`), NOT the two-matrix blow-up. So "the L-layer joint" the depth-≥3 wall needs is exactly
the structure that depth-2 LACKS: the depth-2 reduction is a clean Tonelli split into two independent factors,
and the cap-A/cap-B radial blow-up acts on the single product `Δ·S`. No iterated/joint resolution. The depth-2
`(r,r,p)` build therefore lives ENTIRELY inside the two-matrix-box world — it cannot bleed into the L≥3 long
pole because it never forms a ≥3-factor product.

**(iii) The remaining bounded pieces (the `(r,r,p)` deliverable), all reusing landed infra:**
1. **Reshape ∀p:** generalize genm-n4's `eParamsRR4 (r)` from `p=4` to `eParamsRRP (r) (p)` (same MP plumbing —
   `piFinSuccAbove` + `prodUnique`; only the `Fin 4 → Fin p` width changes). LOW risk, mechanical.
2. **`routeMCore_le_matBox` ∀p:** the open→cube→`paramsEquivFlat`→`eParamsRRP`→Tonelli chain, byte-for-byte the
   `(3,3,4)` / genm-n4 `(r,r,4)` proof with `4 ⟶ p`. LOW risk.
3. **The inner box-integral finiteness `∫_{A0∈matBox r r}∫_{A1∈matBox r p} frobSq(A0·A1)^{−c'} < ⊤` for
   `c' < ½·minAdm(r,r,p)`:** the `r²`-chart radial-`Δ` cover (`recStep` over the `r²` max-modulus charts) +
   per-chart `radial_loss_chart_lt_top {r p}` (DONE, p-general) + the angular `hSfin` from the corank-`(r−1)`
   recursion. The corank recursion here is the genuine MEDIUM piece — but it is the depth-2 Schur recursion
   (`SchurCore p r`, the recStep this design's STEP-0 validated reaches `½·minAdm(r,r,p)`), NOT the depth-`r`
   atlas. This is the `schurRecStep_four` gate, generalized to `schurRecStep_p` / the `½·minAdm(r,r,p)` IH.
4. **Threshold arithmetic ∀p:** generalize genm-n4's `minAdmRec_rr4_ge2`/`minAdm_rr4_eq` (the `inf'`-witness
   `minAdm(r,r,p)/2 = schurLambda_p r` recursion) to the `½·minAdm(r,r,p) = min(½·minAdm(r−1,r−1,p)+p/2, r²/2)`
   identity (cert-verified 10/10, the recursion this design banks). MEDIUM (integer-min arithmetic, parity).

**(iv) Boundary with the depth-≥3 long pole — clean.** Piece 3's corank recursion is `SchurCore p r` recursing
on corank (the depth-2 single-product Schur split), terminating at the `r=1` Morse leaf — depth ≤ r in the
RANK measure, NOT in the LAYER count `L`. The N4 statement is `∀M`, but the depth-2 instantiation
`M = ![r,r,p]` is discharged by this two-box route with ZERO reference to `recStep`-over-layers or the L-layer
joint resolution. So instantiating N4 at `(r,r,p)` is a SELF-CONTAINED corollary lane that does not unblock,
and is not blocked by, the `∀M` (L≥3) proof. The shared `routeMCore_threshold_lt_top {L} M` sorry is discharged
for `L≥3` by a DIFFERENT argument (the triple/general-`L` fibre bound + the L-layer resolution — the genm-n4
research wall); the `(r,r,p)` lane is a parallel, independent instantiation.

**CONCLUSION for commissioning.** There IS a bounded `(r,r,p)` ∀p-hfin deliverable, separable from the L≥3 N4
long pole: pieces (iii).1–4, all reusing the landed depth-2 / genm-n4 infra, gated on the `½·minAdm(r,r,p)`
Schur recursion (the natural ∀p generalization of `schurRecStep_four`, STEP-0-validated as reachable). Risk
profile: 1–2 LOW (mechanical p-generalization of MP reshapes), 3 MEDIUM (the corank Schur recursion ∀p —
bounded, the depth-2 single-product split, NOT the atlas), 4 MEDIUM (integer-min threshold arithmetic ∀p). It
is NOT a single bounded-medium chip (it is the corank recursion + reshape + arithmetic bundle), but it is
bounded-and-standard end-to-end — no research wall. The one genuine dependency is `schurRecStep_p` (the ∀p
recStep), which subsumes/generalizes genm-n4's `schurRecStep_four` gate; if the controller wants ONE commission
that lands the `(r,r,p)` family, it is "the ∀p Schur recStep + the four reshape/arithmetic generalizations,
instantiating `routeMCore_threshold_lt_top` at `M = ![r,r,p]`." This does not require, and is not required by,
the L≥3 N4 weld.
