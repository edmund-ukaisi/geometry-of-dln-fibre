# ∀p generalization of the carve — design doc (Item-55)

**Status:** DESIGN-ONLY (no Lean, no build). Diff-gate to controller before any build. Build gated on
(i) the binding-p=4 family landing (#143 + genm-n4 front-peel-bridge) and (ii) controller clearance.

**Scope.** The carve (`schurRatioResidGen_mid` → `schurRecStep_four`, closed sorry-free + axiom-clean
`[propext, Classical.choice, Quot.sound]` on `genm-assemble`) is hardcoded at **output-width `p = 4`**.
This doc maps precisely how it generalizes to **arbitrary `p = M(last)`** (the last layer width of the
DLN), which is the largest remaining piece for the fully-general ∀M headline.

The author's standpoint: I wrote the p=4 carve. This is a structural audit of *what `4` is doing* at each
step — distinguishing the places where `4` is **merely instantiated** (mechanical lift) from where the
**`p=4` structure is load-bearing** (a genuine wall).

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

**For general `p`:** peel threshold `p/2`, shift `c'' = c' − p/2`, recursion needs `c'' < λ(p, r−1)`:

    c' < λ(p, r−1) + p/2.

For this to define a CONSISTENT `λ(p, r) := λ(p, r−1) + p/2` ladder, the base `λ(p, 1)` must be the true
r=1 leaf threshold. **The p=4 leaf is `1/2` (schurCore4_one), which does NOT fit `λ(4,1) = λ(4,0) + 2`.**
So the recursion `λ(p,r) = λ(p,r−1) + p/2` holds only for `r ≥ 2`, with `λ(p,1)` a separate leaf input —
EXACTLY as `schurLambda` is defined piecewise (`0 ↦ 0`, `1 ↦ 1/2`, `n+2 ↦ 2n+2`). The general analog:

    schurLambdaP p : ℕ → ℝ
      | 0 => 0
      | 1 => (leaf, to re-derive — p=4 gives 1/2; conjecture (p−2)/2 or similar)
      | (n+2) => schurLambdaP p (n+1) + p/2     -- equivalently λ(p,1) + (n+1)·p/2

with `λ(4, n+2) = 1/2 + (n+1)·2`? = `2n + 2.5` — but `schurLambda(n+2) = 2n+2`. **MISMATCH again.** So the
r≥2 branch is NOT `leaf + (r−1)·p/2`; it detaches from the leaf. The p=4 r≥2 formula `2r−2` corresponds to
`λ(4, r) = (r−1)·2 = (r−1)·p/2` for r≥2 (a clean `(r−1)·p/2`), with the r=1 leaf `1/2` an OUTLIER below it.

So the **conjectured general threshold**:

    λ(p, r) = (r − 1) · (p / 2)      for r ≥ 2;     λ(p, 1) = leaf(p);   λ(p, 0) = 0.

Check p=4: `(r−1)·2 = 2r−2` ✓. The r≥2 closed form is `(r−1)·p/2`. **The leaf `λ(p,1) = leaf(p)` is the one
genuinely new threshold input** (p=4: `1/2`). The recursion `λ(p,r) = λ(p,r−1) + p/2` holds for r ≥ 3
(stepping within the r≥2 branch: `(r−1)p/2 = (r−2)p/2 + p/2` ✓), and the r=2-from-r=1 step is special
(`(2−1)p/2 = p/2` vs `leaf(p) + p/2`) — so the **r=2 base case uses the corank-2 base finiteness directly**
(`schurCore4_two` analog), NOT the leaf-plus-peel. This matches the p=4 dispatch table (r=1 leaf, r=2 banked
base, r≥3 firing).

### Does this equal the ½·minAdm-flavored exponent?
The RLCT payoff wants `λ` to be `½·codim` (the geometric codimension of the rank-drop locus). For the
deepest stratum the codim is `(r) · (output width contributions)`; the `(r−1)·p/2` form is `½ · (r−1)·p` =
`½ · codim` of the relevant `Δ·S` rank-`(r−1)` locus in the `r×p` `S`-block (codim `(r−1)·p`?). **TO VERIFY:
confirm `(r−1)·p` is the geometric codim the radial blow-up matches** — this is the bedrock check that the
named `schurLambdaP` is the RIGHT threshold, not just a number that closes the recursion. If it is `½·codim`,
the ∀p firing directly feeds the ∀M RLCT headline.

---

## 4. Load-bearing `p=4` structure (genuine walls vs instantiation)

After the audit, the `4`s split as:

**MERELY INSTANTIATED (mechanical lift, ~no risk):** all box dims (§1a), the Tonelli peel width (§2),
the N2b split (§1c, already ∀p), the carve (§1d, `p`-free).

**LOAD-BEARING (genuine design content):**
1. **The threshold function `schurLambdaP p r`** (§3) — the leaf `leaf(p)` and the r=2 base must be
   re-derived per `p` (the closed form `(r−1)p/2` for r≥2 is conjectured, needs the numerical recursion
   check + the ½·codim identification). This is the ONE genuine wall — everything else is plumbing.
2. **The r=1 leaf and r=2 base finiteness** (`schurCore4_one`, `schurCore4_two` analogs) — these are
   concrete `∫` finiteness lemmas at the bottom of the recursion; their thresholds (`1/2`, `2` for p=4)
   are the `leaf(p)` / base inputs. They are NOT covered by the carve (which is the r≥3 firing) — they
   need their own p-general proofs (the leaf is a 1×1·1×p radial integral; the base is the corank-2
   rank-1 case, the `RouteMSchurCorank2` analog at width p).
3. **`(p)` even vs odd / `p ≥ ?` hypotheses** — the Morse peel threshold `p/2` and the divisor `c' <
   (r·p)/2` assume nothing about parity, but the *binding* family (genm-n4) may restrict `p` to the
   admissible last-layer widths (`p = M(last) ≥ minAdm`). Flag: the ∀p design sits ABOVE the binding
   family — do NOT re-derive genm-n4's binding-p=4 hfin; consume its front-peel-bridge spec for the
   `p = M(last)` instantiation.

---

## 5. Build plan (AFTER controller clearance + binding family lands)

In dependency order (each a separate, gated tide):
1. **`schurLambdaP p : ℕ → ℝ`** + `schurLambdaP_eq` (closed form r≥2) + the ½·codim identification
   (numerical recursion check FIRST — kill-condition: if `(r−1)p/2 ≠ ½·codim`, the threshold is wrong).
2. **Leaf + base**: `schurCorePLeaf` (r=1, `c' < leaf(p)`) + `schurCorePTwo` (r=2 base, `c' < λ(p,2)`).
3. **Lift the firing file `4 → p`**: re-parametrize `GinnerGA`/`stepShearG`/`topRow_*A`/`resolvedShiftRG_le`/
   `coreSchurGenVal` (all `Fin 4 → Fin p`); the carve lifts verbatim. ~Mechanical given §1a/§1d.
4. **`schurRecStepP : SchurRecStep p schurLambdaP`** (the ∀p firing) + wire to `RouteMBoxThresholdFinite ∀p`.

**Estimate (line counts, not wall-clock):** §1 ~80 lines (def + closed form + codim lemma); §2 ~150 lines
(two base finiteness lemmas); §3 ~the firing file re-parametrized (the carve ~700 lines lift verbatim, only
the `4→p` token-swap + box-dim proofs ~100 new lines of friction); §4 ~50 lines (dispatch). The risk is
ENTIRELY in §1 (the threshold closed form + codim identification); §3/§4 are plumbing once §1/§2 land.

## 6. Open questions for the controller / pen-and-paper

- Q-A: confirm `λ(p, r) = (r−1)·p/2` (r≥2) numerically at p ∈ {3,5,6} and identify `leaf(p)`.
- Q-B: is `(r−1)·p` the geometric codim of the rank-`(r−1)` locus in the `r×p` block (the ½·codim check)?
- Q-C: does the binding family restrict `p` (parity / `p ≥ minAdm`), and does the front-peel-bridge spec
  fix the `p = M(last)` instantiation shape I should target?
