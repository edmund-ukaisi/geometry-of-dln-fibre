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

## 9. `schurRecStep_p` DESIGN/PLAN (2026-06-28, controller-commissioned, for diff-gate BEFORE build)

The controller commissioned the `(r,r,p)` ∀p-hfin bundle (§8) and gated the SUBSTANTIAL piece —
`schurRecStep_p` (the ∀p Schur recStep, generalizing `schurRecStep_four`) — on a design diff-gate. This is
that design. It is grounded in the ACTUAL landed proof (`RouteMSchurFiring.lean`, `RouteMSchurGeneral.lean`),
not a recalled picture; every claim below cites the file/line it audits.

### 9.0 What `schurRecStep_four` actually IS (audited)

`schurRecStep_four : SchurRecStep 4 schurLambda` (`RouteMSchurFiring:2076`) is a 4-way DISPATCH on `r`:
- `r = 0`: vacuous (`schurLambda 0 = 0`, no `c' > 0` below it);
- `r = 1`: the Morse leaf `schurCore4_one` (`:141`), threshold `c' < 1/2`;
- `r = 2`: the base `schurCore4_two` (`:132` in General), threshold `c' < schurLambda 2 = 2`;
- `r ≥ 3`: the firing `schurCoreGen_firing` (`:2063`), threshold `c' < schurLambda r`.

The ABSTRACT framework `SchurCore p r`, `SchurThreshold p lam`, `SchurLowerIH p lam r`, `SchurRecStep p lam`,
and the WellFounded wrapper `core_schurGen_lt_top (p lam …)` (`RouteMSchurGeneral:59–120`) are ALREADY
`∀p`-PARAMETRIC — `p` is the first explicit argument of each. `core_schurGen_lt_top` is axiom-clean and
`p`-generic AS-IS (the strong-induction-on-corank wrapper has no analytic content; the per-corank work is the
`hstep` hypothesis). So `schurRecStep_p` is ONLY the `hstep`-supplier; the wrapper consumes it unchanged.

The engine under `r ≥ 3` is (`schurCoreGen_firing`, `:2067`):
1. `matBoxG_outer_flat r` — flatten the `r²` Δ-cells to `Fin (r²) → ℝ` (MP);
2. `gFlatG_cover_sum r` — the `r²`-chart radial-Δ cover, `recStep` over `univ : Finset (Fin (r²))`;
3. `ENNReal.sum_lt_top` over the `r²` charts, each finite by `schur_matBoxG_chart_lt_top` (`:1913`).

The per-chart engine `schur_matBoxG_chart_lt_top` consumes: the cap-B divisor exponent `r²−1` (from
`pivotBlowupOnDeriv_det = |y p|^{r²−1}`, `:1929`), the cap-B threshold `schurLambda r ≤ r²/2`
(`schurLambda_le_sq`, `:1924`), the `piRatioG` reshape (radial axis `a` × angular ratios `Fin (r²−1)`), and the
angular finiteness from the IH `SchurLowerIH 4 schurLambda r` (the carve `schurRatioResidGen_mid` consumes it).

### 9.1 Threshold structure — NUMERICALLY VALIDATED (the load-bearing check, §1b superseded)

`½·minAdm(r,r,p) = min(r²/2, min_{1≤j≤r}(jp/2 + λ_{r−j,p}))` is EXACTLY the greatest solution of the existing
`SchurThreshold p lam` contract (`lambda0` / `radial_le` = cap B / `peel_le` = cap A). Validated p=1..8, r=0..7
(`/tmp/minadm_check.py`, ALL MATCH); p=4 reproduces `schurLambda = [0, ½, 2, 4, 6, 8, 10]` exactly. So:

- **The `SchurThreshold p` contract is ALREADY the right ∀p contract** — `radial_le : lam r ≤ r²/2` (cap B,
  `p`-FREE) and `peel_le : lam r ≤ jp/2 + lam(r−j)` (cap A, `p`-linear). NO change to the contract `structure`.
- **The leaf is `λ(p,1) = ½` for ALL p≥1** (cap B at r=1: `r²/2 = ½`), NOT `p/2`. This RESOLVES §1b's flagged
  worry: `schurCore4_one`'s `1/2` is the single Δ₀₀ scalar's radial axis (`schurOne_delta_divisor_lt_top`,
  `c' < 1/2`), `p`-INDEPENDENT; the `Fin p` S-block is the pure-Morse factor (`schurOne_morse_lt_top`, finite
  ∀c'>0). So `schurLambdaP p 1 = 1/2` for every p — the leaf does NOT move with p.
- **The binding cap SHIFTS with (r,p)** (numerics §): cap B (`r²/2`) binds while `p ≥ 2r` (small r / wide
  output); cap A (the peel) binds for larger r. `t* = argmin_t[(r−t)²+pt]` = the binding rank-drop. This is
  why §1b's naive `(r−1)p/2+leaf` ladder was WRONG: there is no single arithmetic ladder; it is a genuine
  `min`. The Lean `schurLambdaP` must be the piecewise-`min` solution, NOT a closed linear form. (The p=4
  `2r−2` closed form is the coincidence that cap A always binds for r≥2 at p=4.)

### 9.2 The `schurLambdaP p` witness + its three contract lemmas (piece iv of §8)

Replace the p=4 `schurLambda` (`RouteMSchurGeneral:157`) + `schurLambda_satisfies_threshold` (`:201`) with a
`p`-indexed witness. TWO design options:

- **Option A (closed recursive def):** `schurLambdaP (p) : ℕ → ℝ` by strong recursion
  `schurLambdaP p r = if r = 0 then 0 else min (r²/2) (min_{1≤j≤r} (jp/2 + schurLambdaP p (r−j)))`. Direct, but
  the `min over Finset.range` def is friction-heavy to prove the three contract lemmas against.
- **Option B (RECOMMENDED — reuse genm-n4's `minAdm`):** define `schurLambdaP p r := (minAdm (![r,r,p]) : ℝ)/2`
  and prove `SchurThreshold p (schurLambdaP p)` directly from `minAdm`'s `minAdmRec` recursion. This REUSES
  genm-n4's landed arithmetic (`minAdmRec_succ_succ`, `minAdmRec_leaf`, the `inf'` idiom) and makes piece (iv)
  = piece (the threshold-match) the SAME object — `minAdm_rrp_eq` is then `rfl`-adjacent, no separate ladder.
  The three contract lemmas become:
  - `lambda0`: `minAdm(![0,0,p])/2 = 0` — `decide`/`minAdmRec_leaf` (genm-n4 pattern, `:96-99`).
  - `radial_le`: `minAdm(![r,r,p])/2 ≤ r²/2`, i.e. `minAdm ≤ r²` — the `t=0` witness `(r−0)²+p·0 = r²` in the
    `inf'` (one `Finset.inf'_le_of_le`, the genm-n4 `:79-82` pattern with witness `t=0` not `t=r−2`).
  - `peel_le`: `minAdm(![r,r,p])/2 ≤ jp/2 + minAdm(![r−j,r−j,p])/2`. THE one non-mechanical lemma: it says
    `minAdm(r,r,p) ≤ jp + minAdm(r−j,r−j,p)`, the SUB-ADDITIVITY of the codim along a rank-drop path. Provable
    from the `inf'` recursion: a binding stratum `t'` for `(r−j)` lifts to a stratum `t'+j` for `r` with
    `(r−(t'+j))² + p(t'+j) = (r−j−t')² + p t' + pj`. [The generalization of genm-n4's `rr4_term_ge`; MEDIUM.]
- Drop-in helpers from genm-n4 to generalize: `four_mul_le_sq_add_four (s)` → the per-leaf bound is now the
  sub-additivity above (no single scalar inequality); `minAdmRec_rr4_ge2` → NOT needed in Option B (we never
  need the closed VALUE `4r−4`, only the three inequalities — a strict simplification over the p=4 path).

### 9.3 The recStep proof — `p`-lift map (pieces i–iii of §8, the engine)

`schurRecStep_p : ∀ p, SchurRecStep p (schurLambdaP p)` — same 4-way dispatch as `schurRecStep_four`:
- `r = 0`: vacuous (`schurLambdaP p 0 = 0`), VERBATIM.
- `r = 1`: the Morse leaf, threshold `c' < 1/2` (`p`-INDEPENDENT, §9.1). `schurCore4_one` (`:141`) generalizes
  to `schurCoreP_one (p)` by `4 → p`: `frobSq_one_eq` sums over `Fin p` (opaque), `schurOne_morse_lt_top` is
  the `Fin p` block (any width, finite ∀c'>0), `schurOne_delta_divisor_lt_top` is `p`-FREE (the Δ₀₀ scalar).
  LOW — the only `4` is the `Fin 4` S-width, summed opaquely.
- `r = 2`: the base `schurCore4_two` repackages `core_schur2_lt_top`. Needs the `core_schur2` weld at width `p`
  — this is INSIDE the recStep engine (the r=2 instance of the same firing), so it is NOT a separate hand-built
  base; with the engine `p`-lifted, `schurCoreP_two` IS `schurCoreGen_firing p 2` (or the explicit r=2 weld
  lifted). [Audit which: at p=4 r=2 is a hand base `core_schur2_lt_top`, not the firing. If the firing's
  `hr : 3 ≤ r` is essential, r=2 stays a separate `p`-lift of `core_schur2_lt_top`; MEDIUM.]
- `r ≥ 3`: `schurCoreGen_firing` (`:2063`) `p`-lifted = `schurCoreGenP_firing (p)`. The engine
  (`matBoxG_outer_flat`/`gFlatG_cover_sum`/`schur_matBoxG_chart_lt_top`) `p`-lift surface:
  - `matBoxG_outer_flat r`, `gFlatG_cover_sum r`, the `r²`-chart cover, `pivotBlowupOnDeriv_det = |y p|^{r²−1}`:
    ALL `p`-FREE (they reshape the `r×r` Δ-block; `p` lives only in `S`). VERBATIM. [§1d confirmed: the carve is
    over the `r²−1` angular ratios of `R`, `p`-invariant — `cellR`/`zσG`/`zEG`/`RmatGnorm_eq_slot`/
    `schurSc_carve_eqA` all lift with `N = r²−1` `p`-free.]
  - `schur_matBoxG_chart_lt_top` (`:1913`): the cap-B threshold `schurLambda r ≤ r²/2` becomes
    `schurLambdaP p r ≤ r²/2` (= `radial_le`, §9.2). The angular finiteness consumes
    `hIH : SchurLowerIH p (schurLambdaP p) r` (the carve `schurRatioResidGen_mid` — `RouteMSchurFiring:1677`,
    closed) which is `∀p` MODULO the `4 → p` width swap in its S-box (`matBox (r−1) 4 → matBox (r−1) p`),
    `morseBox 4 → morseBox p`, `Fin 4 → Fin p` row indices. §1a/§2: NONE read `4` numerically. LOW-MEDIUM (the
    carve is large but the lift is a mechanical width-parametrization — the hardest sub-step is ALREADY ∀p in
    structure). The Tonelli Morse peel `core_T_peel_le_aeG (m)` is `∀m`: instantiate `m = p−1` (threshold
    `((p−1)+1)/2 = p/2`, the cap-A peel exponent).

### 9.4 Diff-gate confirmations the controller asked for

1. **carve `cellR`/`zEG`/Sc-readback `p`-invariant + lift verbatim:** CONFIRMED (§1d/§2, audited
   `RouteMSchurFiring`). The carve is over `R`'s `r²−1` angular ratios; `N = r²−1` is `p`-free; `p` enters only
   `S`, untouched by the reshape. The S-width `4 → p` swaps are mechanical (`Fin 4` summed opaquely everywhere).
2. **`½·minAdm(r,r,p) = min(capA, capB)` recursion:** CONFIRMED numerically (§9.1, ALL MATCH p=1..8). It IS the
   existing `SchurThreshold p` contract's greatest solution; cap B = `r²/2`, cap A = `min_j(jp/2+lam(r−j))`.
3. **cap B = the done radial axis:** CONFIRMED. cap B `r²/2` is the `pivotBlowupOnDeriv_det = |y p|^{r²−1}`
   radial divisor (`schur_matBoxG_chart_lt_top:1929`), `p`-FREE, = the `radial_aAxis_divisor_lt_top (r)` /
   `radial_loss_chart_lt_top {r p}` in `RouteMSchur` (§8 finding, already `{r p}`-general, sorry-free).

### 9.5 Build order + risk (line-count estimate, NO wall-clock)

Recommended order (each rebuilds GREEN before the next; reuse — do NOT re-derive carve/STEP-0/radial chart):
1. `schurLambdaP p := minAdm(![r,r,p])/2` + `lambda0`/`radial_le` (Option B). ~40 LoC, LOW.
2. `peel_le` (the codim sub-additivity, the one non-mechanical arithmetic). ~50–80 LoC, MEDIUM.
3. `schurCoreP_one` (leaf, `4→p`). ~30 LoC, LOW.
4. The carve `p`-lift: `schurRatioResidGen_mid` + its A-suffixed support lemmas, `4→p` in the S-box/morseBox/
   `Fin 4` indices. The LARGE piece by LoC (the carve is ~600 LoC), but mechanical width-parametrization.
   MEDIUM (volume, not difficulty — STEP-0-validated reachable).
5. `schurCoreGenP_firing` + `schur_matBoxG_chartP_lt_top` (`4→p` in the IH type + S-box). ~80 LoC, LOW-MEDIUM.
6. `schurRecStep_p` dispatch + `minAdm_rrp_eq` (Option B: near-`rfl`). ~40 LoC, LOW.
7. Instantiate `routeMBoxThresholdFinite_rrp_of_schurRecStep_p` (generalize genm-n4's `eParamsRR4 r` →
   `eParamsRRP r p`, `routeMLayerBoxIntegral_rrp_eq`) → `routeMCore_threshold_lt_top` at `M=![r,r,p]`. ~120 LoC
   reusing genm-n4 pattern, LOW-MEDIUM.

NO research wall on any step. The one genuine MEDIUM is `peel_le` (codim sub-additivity); the LARGE-by-volume is
the carve `4→p` lift (mechanical). Total ~360 LoC new + the carve width-swap. Reuses: the carve, STEP-0, the
done radial charts (`RouteMSchur`), genm-n4's `minAdm`/`eParamsRR4` arithmetic+reshape. Build gated on
controller diff-gate of THIS plan + (per §8) the binding-family landing (#143 / genm-n4) for the integration
base.

## 10. CODEX RED-TEAM (2026-06-28, xhigh, decorrelated) — the [HIGH] exponent-routing confound

Fired a decorrelated Codex consult (`codex/schurRecStep-p-design-{prompt,answer}.md`) on the §9 plan BEFORE
the diff-gate. Codex confirmed Option B (`schurLambdaP p := minAdm(![r,r,p])/2`) and the `peel_le` lift as
sound, and the r=2-separate-base call as correct — but found a [HIGH] CONFOUND I had mis-filed as "mechanical
4→p". I VERIFIED it against the landed proof (it is real) and re-validated numerically. The correction:

### 10.1 The confound (VERIFIED): the firing engine has a HARDCODED exponent split at `2 = p/2`

The carve `schurRatioResidGen_mid` (`RouteMSchurFiring:1678`) has hypothesis **`(hc2 : 2 < c')`** — it
hardcodes the Morse-peel threshold `2 = p/2|_{p=4}`. The chart radial axis routes `(r²−1) − 2c'` separately
(`:1973`, the cap-B divisor, p-free). So the p=4 firing genuinely SPLITS on `c'` vs `p/2`:
- **peel branch `p/2 < c'`:** the carve fires — peel the `Fin p` Morse block (threshold `p/2`), recurse on
  the corank-lower core via the IH. Window `p/2 < c' < lam r`.
- **direct-Morse branch `c' ≤ p/2`:** when `lam r ≤ p/2`, the WHOLE window `0 < c' < lam r ≤ p/2` closes by the
  uniform radial/Morse bound, NO recursion (the carve's `2 < c'` is unavailable and unneeded).

I had folded this into "mechanical width-swap" in §9.3. It is NOT mechanical — it is a p-dependent CASE SPLIT.

### 10.2 Why the p=4 fixed corank dispatch does NOT generalize (numerically pinned)

`branch_check.py` (verified): the peel range `(p/2, lam r)` is EMPTY exactly when `lam r ≤ p/2` (cap-B
binding, p ≥ 2r-ish), nonempty (carve fires) when `lam r > p/2` (cap-A binding). The boundary is `r ≈ p/2`:
- p=4: peel-EMPTY for r∈{1,2} (`lam 1=½≤2`, `lam 2=2≤2`), nonempty r≥3. So the LANDED dispatch's
  "r=1,r=2 direct; r≥3 firing" is EXACTLY this branch boundary AT p=4 — a p=4 COINCIDENCE, not a general cutoff.
- p=8: peel-EMPTY for r∈{1,2} still (`lam 2=2≤4`), but the band shape differs; for larger p the direct-Morse
  corank band GROWS (general boundary `lam r ≤ p/2`). The fixed "r<3 ⟹ base" rule is p=4-specific.

So `schurRecStep_p`'s dispatch must branch on **`lam r ≤ p/2` vs `lam r > p/2`** (a p-dependent predicate),
NOT on a fixed corank `r < 3`. The r=1 leaf and r=2 base are the p=4 INSTANCES of the direct-Morse branch.

### 10.3 Corrected design — the p-dependent exponent-routing API (the REQUIRED pre-build piece)

REVISES §9.3. Before the large carve `4→p` width-swap, build the p-dependent split API:
1. **`schurCoreP_directMorse (p r)`** — the direct-Morse branch: `SchurCore p r c' T` for `0 < c' < lam r`
   GIVEN `lam r ≤ p/2` (equivalently the cap-B regime). Closes by the radial axis (`c' < r²/2`, since
   `lam r ≤ r²/2` always) × the uniform `Fin p` Morse bound — NO carve, NO IH recursion. Generalizes
   `schurCore4_one` (r=1) AND `schurCore4_two` (r=2) into ONE branch. [MED — new uniform-Morse-over-the-whole-
   window argument, but no carve; the radial divisor is the done `radial_aAxis_divisor_lt_top`.]
2. **`schurCoreP_peel (p r)`** — the peel branch: `SchurCore p r c' T` for `p/2 < c' < lam r` (cap-A regime),
   via the carve (`schurRatioResidGenP_mid` with `hc2 : p/2 < c'`) + the IH. This IS the `4→p` carve lift,
   now with the threshold `2 → p/2` made explicit. [the LARGE-by-LoC carve swap; the `2 < c'` → `p/2 < c'`.]
   NOTE the equality/boundary `c' = p/2`: Codex flags choosing a flexible `c★` with `max c' (p/2) < c★ < lam r`
   when `p/2 < lam r` — i.e. the peel exponent need not be `c'` itself; peel at a `c★` strictly above `p/2`.
   The p=4 proof's "subcritical fallback exponent 3" (`2 < 3 < schurLambda r` for r≥3) is this `c★` device;
   at general p it becomes `c★ ∈ (p/2, lam r)`, NOT a fixed `3`. [MED — the c★ existence + routing.]
3. **`schurRecStep_p` dispatch:** `rcases le_or_lt (lam r) (p/2)` (or `le_or_lt c' (p/2)`) → directMorse vs
   peel. Plus r=0 vacuous, and p=0 guard (Codex §4: `∀p:ℕ` invokes `Fin p`/`Fin 0` lemmas — either restrict to
   `1 ≤ p` (the DLN output width is ≥1, so a `hp : 1 ≤ p` hypothesis is honest) or handle `p=0` vacuously).

### 10.4 Net effect on the §8 bundle estimate

- The "carve 4→p is mechanical" claim (§9.3/§9.5 step 4) STANDS for the peel branch's width-swap, but the
  carve's `2 < c'` must become a threaded `p/2 < c'` AND the firing dispatch must gain the directMorse branch.
- NEW required piece BEFORE the carve swap: `schurCoreP_directMorse` (the uniform-Morse whole-window bound for
  the cap-B regime) — this is genuinely new (p=4 only ever needed it at r=1,2 as two hand bases; at general p it
  is a ∀r-in-the-cap-B-band lemma). [MED, ~80–120 LoC.]
- Option B / `peel_le` / `schurLambdaP` (§9.2) UNCHANGED — Codex corroborated. r=2 stays a (now subsumed-by-
  directMorse) base, NOT a loosened `hr`.
- Revised risk: the bundle is still bounded-and-standard, NO research wall, but the genuine MED pieces are now
  THREE: `peel_le` sub-additivity (LOW-MED, the lift identity is exact), `schurCoreP_directMorse` (MED, new),
  the `c★`-routing in the peel branch (MED). Total ~+120 LoC over §9.5's estimate.

### 10.5 Diff-gate recommendation (revised)

GO to diff-gate, with Codex's ONE required change folded in (§10.3): the design now carries the p-dependent
exponent-routing (directMorse `c'≤p/2` / peel `p/2<c'` with a `c★` device) as a FIRST-CLASS piece, not a
mechanical swap. The `1 ≤ p` honesty hypothesis (DLN output width ≥ 1) is added. Everything else (Option B
witness, `peel_le` lift, r=2 base, carve angular p-invariance, cap-B = done radial axis) stands and is
Codex-corroborated. Build still gated on controller diff-gate of THIS (corrected) plan.

## 11. BUILD KICKOFF — refinements folded + BASE-SELECTION blocker (2026-06-28)

Controller DIFF-GATE = GO. The 5 refinements (all verified before folding):
1. **Dispatch PURELY predicate-driven** `le_or_lt (lam r) (p/2)` — NEVER a fixed corank cutoff. VERIFIED
   (`refine_check.py`): r=2 routes PEEL at p≤3, directMorse at p≥4 — my §10.4 "r=2 base" WAS a p=4-ism.
   Corrected: r=2 is not special; it routes by the predicate like every r.
2. **c★ = (p/2 + lam r)/2** when `lam r > p/2`. VERIFIED strict-interior, gap ≥ 1/2 ∀(r,p) (both endpoints
   half-integers since minAdm ∈ ℤ). Generalizes p=4's fallback "3" cleanly.
3. **`1 ≤ p` honesty hyp** — thread it (DLN output width ≥ 1). FOLD IN.
4. Base discipline (Item-58) — see BLOCKER below.
5. Incremental build per §9.5/§10.3; green per step; REPORT at the first MED piece (peel_le or
   schurCoreP_directMorse), do not go dark for ~1000 LoC. KILL-CONDITION: a 2nd hidden p=4-ism ⟹ STOP+report.

### 11.1 BASE-SELECTION BLOCKER (surfaced to controller — NOT solo-decidable)

Refinement 4 suggested base = `origin/genm-n4 @6ff61035`. AUDIT (Item-58 prereq check) — **genm-n4 does NOT
have all 3 prerequisites**:
| branch | prereq-1 closed carve (schurRatioResidGen_mid) | prereq-2 RR4 (minAdm/eParamsRR4) | prereq-3 radial chart |
|---|---|---|---|
| origin/genm-n4 @6ff61035 | **OPEN** (sorry at RouteMSchurFiring:1425) | YES (sorry-free) | YES |
| origin/genm-capstone @c2777384 | **CLOSED** (header COMPLETE, clean-three) | NO | YES |
| genm-assemble @dd162c10 (mine) | **CLOSED** | NO | YES |

NO single existing branch has the union {closed carve + RR4 + radial}. genm-n4's carve is OPEN (it's based on
e2941aa1, pre-carve-close); capstone/mine have the closed carve but lack genm-n4's `RouteMBoxThresholdRR4`.

GOOD NEWS: `RouteMBoxThresholdRR4` imports ONLY `RouteMBoxReduction` + `RouteMSchurGeneral` (both on
capstone's lineage; merge-base of capstone & genm-n4 is e2941aa1). So it GRAFTS cleanly onto capstone.

**RECOMMENDED base: `origin/genm-capstone @c2777384` (closed carve + radial, controller's canonical) +
cherry-pick genm-n4's `RouteMBoxThresholdRR4.lean` (one self-contained file).** This is the union, minimal.

BUT: assembling a cross-lineage base (capstone ⊎ genm-n4's RR4 file) is an INTEGRATION act that overlaps #143
(the canonical integration the controller gates). I will NOT unilaterally merge cross-lineage — surfacing for
the controller to either (a) bless capstone+RR4-cherry-pick as my build base, or (b) point me at an existing
integration branch that already has the union, or (c) have #143's owner produce the union base first. Pending
that, I CANNOT green-confirm a base, so the build is HELD at the base gate (correctly — Item-58 says confirm
the 3 prereqs GREEN before extending, and no base currently provides them).

## 12. directMorse DESIGN — Codex-corrected (2026-06-28, decorrelated xhigh, repo-verified)

After the base landed, I studied the p=4 cap-B bases to build `schurCoreP_directMorse` and found my §10.3
"uniform Morse over the whole window" sketch was WRONG — the p=4 cap-B bases (schurCore4_one r=1,
core_schur2_lt_top r=2) use the SAME r²-chart RADIAL COVER as the firing, with the angular integral bounded
WITHOUT recursion. Fired a decorrelated Codex xhigh pass (`codex/directMorse-design-{prompt,answer}.md`) to
nail the exact angular bound. Corrected design:

### 12.1 The cap-B angular bound (Codex-corrected; the §10.3 sketch was naive)

- WRONG (my §10.3): `frobSq(R·S) ≥ c₀·frobSq(S)` (a uniform norm bound). Codex: **FALSE** — `R` can annihilate
  `S` (e.g. `R = diag(1,0,…)`, `S` with zero top row). VERIFIED counterexample. The pivot controls only the
  SHEARED TOP ROW, not all of `S`.
- RIGHT: the SAME N2b one-pivot Schur/Morse lower bound the carve uses (`schur_minorPivot_split` j=1,
  already p-parametric), THEN DROP the residual `frobSq(Sc·Sbot)` term (cap-B doesn't need it) and bound the
  surviving sheared-top-row Morse factor by the generic Morse leaf:
      frobSq(R·S)^{−c'} ≤ c₀^{−c'} · (∑_q (S₀q + ∑_a b_a·Sbot_aq)²)^{−c'}
  shear `S₀ ↦ Τ = S₀ + b·Sbot` (shifted box ⊆ `morseBox p (max 1 (r·T))`), then
      ∫_{S₀} (…) ≤ ∫_{Τ∈morseBox p K} (∑_q Τq²)^{−c'} < ⊤   for c' < p/2  (generic `sumSqND_box_lt_top`).
  So directMorse proves **`c' < min(p, r²)/2`** (angular `c'<p/2` × radial `c'<r²/2`). This covers cap-B
  exactly (binding stratum t=0 ⟹ `lam = r²/2 ≤ p/2`, so the window `c'<lam r ≤ min(p,r²)/2` is inside). Above
  `p/2` (cap-A) directMorse is NOT enough — that's the peel branch. The dispatch `lam r vs p/2` (refinement 1)
  is exactly this boundary. CONSISTENT.

### 12.2 Codex's "fixed-S route fails" (rules OUT a tempting shortcut)

Do NOT supply `radial_loss_chart_lt_top`'s `hSfin` via a fixed-`S` lemma `∫_R frobSq(R·S)^{−c'}<⊤`: it FAILS
at `S=0` / low-rank `S`, and even a.e.-fixed-`S` loses the codimension in `S` needed for JOINT integrability.
directMorse must be the joint (R-angular, S) integral via the shear+Morse-leaf, NOT radial_loss_chart with a
per-S hSfin. (radial_loss_chart stays useful for the cap-A peel where the IH supplies a genuine joint hSfin.)

### 12.3 REPO FIND that shrinks the plumbing (Codex's "bite" is smaller than it inferred)

Codex's top risk was "p-generalize the Fin 4 chart plumbing." I VERIFIED the repo: `RouteMSchurGenCover.lean`
(on the genm-pbuild base, sorry-free) ALREADY has the `(r,p)`-PARAMETRIC outer cover — `gFlatGen (r p)`,
`matBoxGen_outer_flat (r p)`, `gFlatGen_cover_sum (r p)`. So the r²-chart cover is DONE p-general; I do NOT
rebuild it. The remaining `Fin 4 → Fin p` work is the narrower PER-CHART angular layer:
`innerSGen`/`stepShearG_r`/`frobSqTopRow_eq_shear` (all `Fin 4` at RouteMSchurFiring:275/1405/1462), which
BOTH directMorse and the peel branch share. `schur_minorPivot_split` + `sumSqND_box_lt_top` are already
p-parametric (verified). So the shared `Fin p` plumbing = {top-row identity, stepShear, innerSGen} p-versions.

### 12.4 Corrected lemma decomposition + build order (revises §9.5/§10.3)

SHARED `Fin p` chart plumbing FIRST (both branches need it), then the two branches:
1. `frobSqTopRowP_eq_shearP` [LOW] — p-general top-row identity (`Fin 4 → Fin p` in frobSqTopRow_eq_shear).
2. `stepShearP_r` [MED] — p-general `stepShearG_r` over `morseBox p`.
3. `innerSGenP` + its measurability — p-general `innerSGen`.
Then the cap-B branch:
4. `innerSGenP_directMorse_le_const` [MED] — N2b j=1 lower bound + shear + DROP residual; uniform in angular z.
5. `schurRatioResidP_capB_lt_top` [LOW] — integrate the uniform inner bound over the bounded ratio box.
6. `schurCoreP_directMorse` [MED] — `gFlatGen` cover (DONE) + radial axis (DONE) + (5).
Then the cap-A branch (the carve 4→p) reuses 1–3 + the IH + the residual (NOT dropped) + the recursion.

REVISED RISK: the shared plumbing (1–3) is the real bulk (the carve's `Fin 4` machinery, ~mechanical but
large); directMorse (4–6) is then ~120 LoC of genuinely-new cap-B content. NO research wall. The build order
flips: shared `Fin p` plumbing BEFORE either branch (directMorse and peel both consume it). This is the one
real structural correction over §10.3 (which treated directMorse as standalone-trivial).

KILL-CONDITION status: this is the "2nd mechanical-looking that's structural" the controller flagged — caught
it by studying the p=4 bases + Codex, BEFORE building. Not a wall (the math is the carve's own N2b bound,
residual-dropped); a build-order + decomposition correction. Proceeding to build the shared `Fin p` plumbing.
