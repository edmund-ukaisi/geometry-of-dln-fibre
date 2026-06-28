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
