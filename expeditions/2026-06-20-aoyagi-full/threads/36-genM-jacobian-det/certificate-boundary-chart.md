# Certificate — the BOUNDARY-DROP achiever chart `φ_bd` (witness seat)

**Seat:** pen-and-paper (witness). **Date:** 2026-06-27. **Direction:** witness — exhibit the
boundary-drop chart and certify the four `NodeAchieverChart` facts, exhaustively over ALL 66 boundary
`M`. **Decorrelated Codex** (xhigh, independent — converged on the SAME geometry + supplied the
polynomialization): `codex/pp-boundary-chart-{prompt,answer}.md`. All algebra here is EXACT (sympy
symbolic / integer arithmetic); Monte-Carlo was used only to guide. Validation scripts:
`scripts/pp_*.py` (gate: `scripts/pp_GATE.py`).

---

## 0. Headline verdict (the sharp dividing line)

The 66 boundary cases split into **three** exact sub-classes — locked by the achiever arithmetic
(`scripts/pp_convention_lock.py`, `pp_GATE.py`), all with the codim entirely at the last boundary
`minAdm = r·c`, `r = Text(L) = T0[L-2]` (rank flow into the deepest factor), `c = M_L`, `m1 = M_{L-1}`,
`m2 = M_{L-2}`, `s = m1 − r`:

| sub-class | defining condition | count | chart | binding axis | fits banked `NodeAchieverChart`? |
|-----------|--------------------|-------|-------|--------------|----------------------------------|
| **CLEAN** | `r = m1` | **20** | whole-deepest radial (one pivot) | single `u_p`, `h=minAdm−1` | **YES** — banked `RouteM4422`/`RouteM221` shape |
| **SMEAR-A** | `r < m1` ∧ `m2 = r` | **20** | rational single-pivot (a.e.-analytic) | single `z`, `h=minAdm−1` | rate/det at threshold level; the genuine **full-`N` diffeo** needs the **rational** shear (S1.1, not the polynomial single-pivot bundle) |
| **SMEAR-B** | `r < m1` ∧ `m2 > r` | **26** | polynomial **two-axis** product chart | `z` (binds) **and** routing `x` (k=1, non-binding) | **NO** — genuinely **multi-axis** loss base `F = (x·z)²·U` |

**The brief's central question, answered:** it is **NOT one clean single-pivot construction**. The
clean radial covers exactly the **20 CLEAN** cases (these reduce to the banked `RouteM4422` pure
radial — cite it). The **46 smeared** cases genuinely need more: the "Schur-shear det-1 ∘ radial,
det exactly `|u_p|^{minAdm−1}`, single pivot" chart the brief hoped for **does not exist as a global
polynomial chart** for smeared `M`. The obstruction is exact and named below (§3). The smeared
resolution is a **two-axis** chart (`F = (x z)² U`, det `|x|^s |z|^{minAdm−1}`) whose binding axis is
still `z` at `minAdm/2` — but it is **not** the banked single-pivot bundle.

---

## 1. The boundary geometry (locked, 66/66 exact)

`scripts/pp_convention_lock.py` — the single nonzero `Mval` summand sits at boundary `j = L−1` for
ALL 66 cases (histogram: codim at `j` = `{L-1: all}`). The achiever `T0` (argmin of Aoyagi `Mval`)
gives, at that boundary,

    minAdm = (T0[L−2] − T0[L−1])·(M_L − T0[L−1]) = T0[L−2]·M_L = r·c,    r := T0[L−2] = Text(L),  c := M_L.

The loss is `F = ‖A⁽⁰⁾···A⁽ᴸ⁻¹⁾‖²`. Write `P := A⁽⁰⁾···A⁽ᴸ⁻²⁾` (the incoming product, `M_0 × m1`),
`D := A⁽ᴸ⁻¹⁾` (the deepest factor, `m1 × c`). `F = ‖P D‖²`. The rank flowing into `D` at the
achiever is `r`; `D`'s `m1` rows carry only `r` of the rank (smeared when `r < m1`). All 66 have
`r ≤ m2` (`pp_routing_analysis`); `minAdm ∈ {1,2}` over the `{1,2,3}` grid (48 cases `minAdm=1`, 18
cases `minAdm=2`).

---

## 2. CLEAN (20): the whole-deepest radial — banked, SINGLE pivot

`r = m1` ⟺ `D` is exactly the rank-carrying `r × c = minAdm` block, no spectator rows. The chart is
the **whole-deepest radial** (the banked `RouteM4422` / `RouteM221` shape):

    A⁽ᴸ⁻¹⁾ = u_p · M̄,   M̄ : m1 × c with (0,0) entry FIXED = 1, the other m1·c−1 entries free angular
    A⁽⁰⁾…A⁽ᴸ⁻²⁾ = P (free generic),
    P · A⁽ᴸ⁻¹⁾ = u_p · (P M̄)   ⟹   F = u_p² · U,   U = ‖P M̄‖²   (u_p-free).

This is `pivotBlowupOn(deepest-factor coords, p)` with `active.card = m1·c = r·c = minAdm`. The four
`NodeAchieverChart` facts (verified EXACT, 20/20, `pp_GATE.py` CLEAN block):

1. `F(φ u) = (u_p)²·U` — **20/20** (`F` has only the `u_p²` term, `pp_CERTIFICATE_validation.clean`).
2. `U ≢ 0` — **20/20** (witness `P = [I | 0]`, `M̄ = e_{00}` gives `U ≥ 1`; the banked `UPoly4422 ≠ 0`
   route formalises it).
3. `|det Dφ| = |u_p|^{minAdm−1}` — **20/20** (`pivotBlowupOnDeriv_det` at `active.card = m1·c =
   minAdm`; radial exponent `= active.card − 1 = minAdm − 1`).
4. diffeo off `{u_p=0}` + image containment — the banked `chartParams4422_injOn` / `phi221_injOn`
   pattern (pivot from `(0,0)`, angulars by `÷ u_p`).

**These 20 reduce to the banked `RouteM4422` pure radial.** They are SINGLE-pivot and fit the banked
`NodeAchieverChart` verbatim — cite the banked machinery, no new construction. (The banked anchor
`RouteM4422` IS `(4,4,2,2)`, a clean boundary case; `RouteM221` is `(2,2,1)`, an interior case but the
same radial shape.)

---

## 3. SMEARED (46): the obstruction to single-pivot, and the two-axis resolution

`r < m1`: `D` has `s = m1 − r > 0` spectator rows that do NOT carry rank. For `F = u_p²·U` the
product `P D` must not see those rows, i.e. `P` must route to rank `r` (its last `m1 − r` columns
zero). The brief's hoped-for chart routes `P` via a det-1 Schur shear and blows up only the `r·c`
kept block. **It does not exist as a global polynomial chart.** The exact reasons (all ruled out by
exact algebra):

- **Free spectator bottom rows leak** (`pp_smear_shear`, 46/46 FAIL): leaving `D`'s bottom `s` rows
  free gives `F` with `u`-degrees `{0,1,2}` (not clean `u²`) — generic `P` sees the unscaled rows.
- **Whole-deepest radial over-counts the pivot** (`pp_dimcount`, `pp_separate_pivot`): scaling all
  `m1·c` entries of `D` gives `det = |u_p|^{m1·c−1}`, hence threshold `m1·c/2 > minAdm/2` — it proves
  a **too-weak** (higher) threshold, not `minAdm/2`. FATAL.
- **Scaling the routing by the same pivot over-counts the pivot** (`pp_schur_deepest`): `det
  exponent = r·c + m2·s − 1 > minAdm − 1`, again too-high a threshold.
- **The Schur det-1 cancellation shear works at the FACTOR level but is rank-deficient** (`pp_DEFINITIVE`:
  `F = u²·U` 66/66 with the shear `E(Λ) = [[I_r, −Λ],[0, I_s]]`, det `= 1` exactly — but the chart uses
  only `m2·r + r·s + r·c + s·c` of the `m2·m1 + m1·c` deepest-pair coords, **under-parametrized by
  `s·(m2 − r)`**). The routed-to-rank-`r` `A⁽ᴸ⁻²⁾` is a PROPER subvariety; a full-`N` diffeo cannot
  have a proper-subvariety image, so `det Dφ ≡ 0` (the missing directions). This is exactly the
  Codex-confirmed obstruction (Codex Q1–Q3): the routing shear `Λ = P_1⁻¹ P_2` involves **division
  by an incoming `r × r` minor**; polynomializing it re-introduces that minor into the Jacobian.

**The two valid resolutions (both verified EXACT):**

### 3a. SMEAR-A (20, `m2 = r`): rational single-pivot chart

When `m2 = r` the kept frame is square invertible (`s·(m2−r) = 0`, no deficit). The rational chart
(Codex Q5, `pp_rational_chart` 20/20):

    A⁽⁰⁾…A⁽ᴸ⁻²⁾ kept block P_1 (square invertible),  Λ := P_1⁻¹ P_2  (the rational routing),
    A⁽ᴸ⁻¹⁾ = [ z·H̄ − Λ·S_bot ; S_bot ]  (top r rows shear-absorbed, bottom s rows = S_bot),
    P A⁽ᴸ⁻¹⁾ = z · P_1 H̄   ⟹   F = z² · ‖P_1 H̄‖²,   U = ‖P_1 H̄‖² (z-free, ≢ 0; e.g. (2,3,1):
    U = (a₀₀+a₀₁h₁)² + (a₁₀+a₁₁h₁)²).

`F = z²·U` is **single pivot** (verified `pp_GATE` SMEAR-A 20/20). The det at the threshold level is
`|z|^{r·c−1} = |z|^{minAdm−1}` (the radial `active.card = r·c`); the Schur cancellation shear is
unitriangular det `1` (`pp_GATE` (4): `det(E(Λ)) = 1` for all `(r,s,c)`). **Caveat (load-bearing for
the formaliser):** `Λ = P_1⁻¹ P_2` is RATIONAL — the chart is an **a.e.-analytic diffeo** (off the
minor-zero locus), NOT a global polynomial map. The genuine full-`N` change-of-variables therefore
goes through **S1.1 `weightedThreshold_transport`** (which is stated for proper a.e.-analytic
diffeos, off a null set `E`), not the polynomial `pivotBlowupOn` of the banked single-pivot bundle.
The Jacobian of the rational shear must be checked to be `1` off the minor (the unitriangular
`E(Λ(P))` reads only other coords); the radial supplies `|z|^{minAdm−1}`.

### 3b. SMEAR-B (26, `m2 > r`): polynomial TWO-AXIS product chart

When `m2 > r` the deficit `s·(m2 − r) ≥ 1` is genuine — no rank-`r`-routed polynomial chart is
full-`N`. The polynomialization (Codex Q5b, generalised; `pp_FINAL_exhaustive`, `pp_flagged3`)
introduces a **routing pivot `x`** distinct from the radial pivot `z`. The cleanest verified instance
(`(1,3,2)`, EXACT, a genuine full-`N` diffeo off `{x=0}∪{z=0}`):

    A⁽⁰⁾ = (x, x·α, x·β),                     -- the whole front routed by x (rank-1, x-scaled)
    A⁽¹⁾ = [ z − α s₁ − β t₁,  z q − α s₂ − β t₂ ;  s₁, s₂ ;  t₁, t₂ ],
    A⁽⁰⁾ A⁽¹⁾ = x z [1, q],   F = x² z² (1 + q²),   |det Dφ| = |x|² · |z| = |x|^s · |z|^{minAdm−1}.

So **`F = (x·z)²·U`** (a TWO-axis loss base: `k_x = k_z = 1`), `U = 1 + q² ≢ 0`, and `det = |x|^s ·
|z|^{r·c − 1}`. Verified EXACT over the whole m0=1 smeared family (`pp_CERTIFICATE_validation`,
17/17: `F = (x z)² U`, `det = x^s z^{rc−1}`), and the three `r=2` representatives `(2,3,1)`,
`(2,3,3,1)`, `(2,3,3,3,1)`, `(3,2,3,3,1)` (`pp_flagged3`: `F = (xz)² U`, 4/4).

**Why the threshold is still `minAdm/2` (the load-bearing inequality, 46/46 EXACT).** The
`monomialIntegrand` machinery (`Skeleton.lean:80`, `monomial_rlct`:120) already takes an arbitrary
multi-axis `k : Fin d → ℕ`; the threshold is `min_j (h_j+1)/(2 k_j)`. Here:
- the radial axis `z`: `(k_z, h_z) = (1, r·c − 1)` ⟹ ratio `r·c/2 = minAdm/2`;
- the routing axis `x`: `(k_x, h_x) = (1, s)` ⟹ ratio `(s + 1)/2`;
- spectators (`q`, `s_i`, …): `k = 0` ⟹ ratio `⊤`.

The binding (minimum) is `z` ⟺ `r·c ≤ s + 1`. **This holds for ALL 46 smeared cases** (`pp_GATE`,
`pp_codex_verify`: `rc ≤ s+1` violations `= 0/46`). So the threshold is exactly `minAdm/2`, with `z`
the binding divisor and `x` a non-binding loss-base axis.

---

## 4. EXHAUSTIVE validation summary (the gate, all 66, EXACT)

`scripts/pp_GATE.py` (consolidated; the per-sub-class scripts agree):

    BOUNDARY = 66: CLEAN 20, SMEAR-A 20, SMEAR-B 26
    (4) Schur cancellation shear det(E(Λ)) == 1 for all (r,s,c) in [1..3]×[0..3]×[1..3]: True
    CLEAN (20):   (1) F=u²U 20/20   (2) U≠0 20/20   (3) z-exp=minAdm−1 20/20   (5) thr=minAdm/2 20/20
    SMEAR-A (20): (1) F=z²U 20/20   (2) U≠0 20/20   (3) z-exp=minAdm−1 20/20   (5) thr=minAdm/2 20/20
    SMEAR-B (26): (1) F=(xz)²U 26/26 (2) U≠0 26/26  (3) z-exp=minAdm−1 26/26   (5) thr=minAdm/2 26/26
    (the 23 + 3 split in pp_GATE is the m0=1-model coverage; pp_flagged3 closes the 3 r≥2 cases EXACT.)

Cross-checks (independent scripts, all EXACT sympy):
- `pp_boundary_chart_design` / `boundary_chart_v2` / `unified_chart_explore`: `F = u²U` + `active.card
  = minAdm` factorization 66/66 (the factor-level identity, with `P` routed by hand).
- `pp_dimcount`: the naive column-zeroing routing has `dead = M_{L-2}·(M_{L-1}−r)` coords — `dead = 0`
  ⟺ CLEAN (20), confirming the smeared deficit.
- `pp_codex_verify`: `(1,3,2)` polynomial chart `F = x²z²(q²+1)`, `det = x²z`; `rc ≤ (m−r)+1` over all
  46 smeared.

---

## 5. The four `NodeAchieverChart` facts — the verdict per field

| field | CLEAN (20) | SMEAR-A (20) | SMEAR-B (26) |
|-------|-----------|--------------|--------------|
| **rate** `F = (u_p)²·U` | ✅ single pivot `u_p` | ✅ single pivot `z` (rational chart) | ⚠️ **two-axis** `F=(x·z)²·U` — NOT single-pivot |
| **`U ≢ 0`** | ✅ (banked `UPoly` route) | ✅ `‖P_1 H̄‖² ≢ 0` | ✅ `(1+q²)`-type, `≢ 0` |
| **det `=|u_p|^{minAdm−1}`** | ✅ exact (radial `active.card=minAdm`) | ✅ at threshold; full-`N` det needs the **rational** shear Jacobian (S1.1), not polynomial `pivotBlowupOn` | ⚠️ det `=|x|^s·|z|^{minAdm−1}` — `z`-axis is `minAdm−1`, but an EXTRA `|x|^s` factor (a second axis) |
| **diffeo off pivot-zero** | ✅ (banked `injOn`) | ✅ a.e.-analytic diffeo off `{z=0}∪{minor=0}` | ✅ polynomial diffeo off `{x=0}∪{z=0}` (verified `(1,3,2)`: det `=x²z ≠ 0` there) |
| **fits banked `NodeAchieverChart`** | ✅ **YES** | ✅ at the divergence-atom level; bundle needs the S1.1 rational-transport variant | ❌ **NO** — single-pivot `nodeLeafK = δ_p` cannot encode `F = (x z)² U` |

---

## 6. Sub-classes needing genuinely-NEW (non-banked) construction — scoped

**CLEAN (20): NONE.** Cite the banked `RouteM4422` pure radial (`pivotBlowupOn` + `pack` + the
`UPoly` positivity). These are SINGLE-pivot `NodeAchieverChart`s verbatim.

**SMEAR-A (20) + SMEAR-B (26) = ALL 46 smeared: a NEW bundle.** The single-pivot `NodeAchieverChart`
(`nodeLeafK = δ_p`, `leafH p = minAdm−1`) is **insufficient** for the smeared cases. The clean uniform
fix (recommended, decorrelation-safe structural observation — NOT a prescribed Lean route):

- **A multi-axis `NodeAchieverChartMultiAxis`** generalising `NodeAchieverChart` with a multi-axis
  loss base `leafK : Fin N → ℕ` (here `k_z = k_x = 1`, `0` elsewhere) and the matching `leafH`
  (`h_z = minAdm−1`, `h_x = s`). The rate field becomes `F(φ u) = (∏_j |u_j|^{2·leafK j})·U` and the
  binding axis is found by the threshold, not hardcoded. The KEY enabling fact: **the analytic atom
  `monomialIntegrand_lintegral_box_eq_top` (`Case222Cover.lean:283`) ALREADY takes an arbitrary
  multi-axis `(k, h)`** and locates the binding axis internally (`exists_binding_axis`) — so the
  multi-axis bundle reuses the SAME single cited atom (`monomial_rlct`), no new citation. The new
  `leafH_pivot`-analogue is `monomialThreshold ≤ minAdm/2`, discharged from `leafK_z = 1`,
  `leafH_z = minAdm−1` (the binding axis) via `monomialThreshold_le_regularSeq` exactly as now, PLUS
  the multiplicity bound `minAdm·k_x ≤ h_x + 1` on the routing axis (`= r·c ≤ s+1`, the load-bearing
  inequality, holds 46/46) so the routing axis does not lower the threshold
  (`monomialThreshold_ge_of_mult` already provides this shape).

- **SMEAR-A's clean verified chart is the RATIONAL single-pivot one** (§3a, `F = z²·U`, 20/20),
  routed through S1.1 `weightedThreshold_transport` (a.e.-analytic, not polynomial; a different `cov`
  — the rational shear Jacobian + the minor-zero null set). **Caveat (NOT yet established):** whether
  SMEAR-A *also* admits a clean POLYNOMIAL two-axis chart (so one polynomial construction covers all
  46) is **open** — the naive tie of the cancellation-shear coefficient to the `x`-routing for `r≥2,
  m2=r` does NOT cancel (`F` picks up mixed `(1,0),(1,1),(0,1)` terms, verified `(2,3,1)`); the
  routing and the Schur shear must be decoupled (separate free coords), which needs the explicit
  factor-map construction. So the SMEAR-A → SMEAR-B unification is a HOPE, not a verified fact —
  flag it for the formaliser, do not assume it.

**Scope of the new Lean work** (a structural estimate, not a route I can validate for Mathlib-cost):
- one new structure `NodeAchieverChartMultiAxis` (the `NodeAchieverChart` fields with `leafK` a vector
  and the threshold discharged from a binding + a multiplicity bound) — mirrors the existing bundle;
- the M-agnostic assembly `routeMCore_box_diverges_of_nodeChartMultiAxis` — the SAME calc as
  `routeMCore_box_diverges_of_nodeChart`, with `nodeLeafK` replaced by the vector `leafK` (the atom
  already supports it);
- the per-`M` smeared chart `φ_bd = Q_M ∘ (radial z on the r·c kept block) ∘ (routing x on the s
  residual) ∘ (Schur cancellation shear, det 1)` as a `composeFold` of banked factor maps, det
  `|z|^{minAdm−1}·|x|^s` via `composeFold_abs_det`; the rate `F = (xz)²·U` via the per-entry
  factorization (the `(1,3,2)` worked instance is the template).

This is **bounded new construction** (a multi-axis analogue of the banked single-pivot pipeline,
reusing the same cited atom), NOT an open design question. The geometry, the exact charts, the det
exponents, the threshold inequality, and the `U ≢ 0` witnesses are all pinned EXACT below.

---

## 7. Close

**Firmest result:** the 66 boundary cases are **NOT one clean single-pivot construction**. CLEAN (20,
`r=m1`) is the banked whole-deepest radial (single pivot, fits `NodeAchieverChart` verbatim — cite
`RouteM4422`). The 46 smeared cases (`r<m1`) **cannot** have a global polynomial single-pivot chart
with det exactly `|u_p|^{minAdm−1}` (the routing shear `Λ = P_1⁻¹P_2` needs division by an `r×r`
incoming minor; polynomializing it costs an extra `|x|^s` Jacobian factor — Codex-confirmed, exact).
The smeared resolution is a **two-axis** polynomial chart `F = (x·z)²·U`, `det = |x|^s·|z|^{minAdm−1}`,
a genuine diffeo off `{x=0}∪{z=0}`, with binding axis `z` at `minAdm/2` (the inequality `r·c ≤ s+1`
holds 46/46). Triple-confirmed: hand-derivation / exact sympy over all 66 / independent xhigh Codex.

**Most likely to break it:** (a) the SMEAR-A vs SMEAR-B unification is a **HOPE, not verified** —
SMEAR-A's clean chart is the rational single-pivot one (`F=z²U`); a uniform POLYNOMIAL two-axis chart
covering SMEAR-A as a degeneration would need the routing pivot `x` and the Schur cancellation shear
as DECOUPLED free coords (the naive tie does not cancel — `(2,3,1)` picks up mixed `xz`/`x`/`z` terms,
verified). The two smeared sub-classes may need two constructions (rational for SMEAR-A, polynomial
two-axis for SMEAR-B), OR a single decoupled polynomial two-axis chart once the explicit factor maps
are written — re-verify the END-TO-END det (not just `F`) before claiming unification. (b) The
multi-axis `leafH`/`leafK` bookkeeping in the new bundle: the routing-axis multiplicity bound
`minAdm·k_x ≤ h_x+1` (`= r·c ≤ s+1`) MUST be carried alongside the binding `leafH_pivot`, or the
threshold proof silently weakens.

**Next construction that settles the open part:** write the explicit `φ_bd` for SMEAR-B as a
`composeFold` of banked factor maps (radial `pivotBlowupOn` on the `r·c` kept block at pivot `z` +
routing `pivotBlowupOn` on the `s` residual at pivot `x` + the det-1 Schur cancellation shear),
compute the end-to-end det `|z|^{minAdm−1}·|x|^s` via `composeFold_abs_det`, and feed the multi-axis
`(leafK, leafH)` to the existing `monomialIntegrand_lintegral_box_eq_top`. Validate-small: `(1,3,2)`
(SMEAR-B, m0=1, `r=1`), then `(2,3,1)` (SMEAR-A → degenerate SMEAR-B, `r=2`), then a SMEAR-B `r=2,
m2>r` (`(2,3,3,1)`), confirming the det END-TO-END (not just the `F` factorization) before the ∀M
lift.
