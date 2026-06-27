# Certificate — the BOUNDARY-SMEARED achiever chart: the two residuals SETTLED (witness tide v2)

**Seat:** lean-formaliser (DESIGN+VALIDATE, no Lean commit). **Date:** 2026-06-27. Resolves the two
residuals flagged in `certificate-genM-witness-v2.md` §3 / `certificate-boundary-chart.md` §6–7. **Gate:
EXACT algebra + EXHAUSTIVE validation**, not assertion — `scripts/pp_smear_GATE.py` (the consolidated gate:
unification + `F=z²U` + `U≢0` polynomial + det `z^{minAdm−1}` + coord `=N` + threshold `½·minAdm`, 46/46,
0 failures), built from `pp_smear_unify.py` / `pp_smear_rational_exhaustive.py` / `pp_smear_det{,_all}.py`;
the front-bottleneck claim stress-tested over the wider 1..6 / L≤6 grid (604 smeared, 0 violations). Numbers
reproduce on run. **DECORRELATION CAVEAT:** the intended decorrelated local-Codex consult (both a full and
a focused retry) STALLED with no output today (an environment issue, not a refutation) — so the
cross-model check did NOT land; the findings rest on the exact-algebra exhaustive validation alone. Flagged
for the operator/controller to re-fire when Codex is healthy.

---

## 0. Headline (both residuals settled — and the design SIMPLIFIES)

The 46 boundary-SMEARED cases (`r := Text(L) < m1 := M_{L−1}`, codim all at the last boundary,
`minAdm = r·c`, `c := M_L`) **UNIFY under ONE rational single-pivot chart** `F = z²·U`. The two-axis
chart of `certificate-boundary-chart.md` §3b was an artifact of an L=2-only `m0=r` cut; the correct
criterion (the FRONT-PRODUCT bottleneck) makes the rational single-pivot chart apply to ALL 46.

- **RESIDUAL 1 (SMEAR-A↔SMEAR-B unification): UNIFIED.** One chart, all 46. The earlier `m2=r` vs `m0=r`
  split (both count 20 but disagreeing on 32 cases) was a false dichotomy. The real invariant:
- **RESIDUAL 2 (the rational shear det, END-TO-END): EXACTLY `|z|^{minAdm−1}`.** The shear is
  unit-triangular (det 1, off the minor-zero null set); the radial gives `z^{r·c−1} = z^{minAdm−1}`.
  Threshold exactly `½·minAdm`, single binding axis `z`.

**Consequence for the bundle:** since the chart is SINGLE-pivot (`F = z²·U`, one binding axis), it fits
the EXISTING `NodeAchieverChart` (single `p`, `leafH p = minAdm−1`) — **NO new `NodeAchieverChartMultiAxis`
is needed.** The ONLY genuinely-new Lean piece is the `cov` field's PROOF: an a.e.-analytic (rational)
change-of-variables (the chart map is rational, undefined on a null set), discharged via
`S1.1 weightedThreshold_transport` (which is stated for a.e.-analytic maps) instead of the polynomial
`pivotBlowupOn` route the banked charts use. This is a far smaller increment than a multi-axis bundle.

---

## 1. The unifying structural fact (the front bottleneck = r) — EXACT, 652/652

For EVERY boundary-smeared `M`, the front-width minimum equals `r`:

    min(M_0, M_1, …, M_{L−1}) = r = Text(L) = tStar[L−2].

Validated `0 violations` over the WIDER grid (widths `1..4`, `L ≤ 5`, 652 smeared cases;
`pp_smear_unify.py` / the bottleneck scan). The structural reason (EXACT, 0 violations / 46 on the base
grid): for a boundary-smeared achiever, all codim sits at the last boundary, so `Text` is weakly
decreasing with `Text(L) = r`, and (i) every front width `M_k ≥ r` (`k ∈ [0, L−1]`), (ii) some front
layer has `M_k = r` (the bottleneck — at `k=0` in 20 cases, `k=1` in 16, `k=2` in 10). So the front
product `P = A⁽⁰⁾···A⁽ᴸ⁻²⁾` (`M_0 × m1`) has generic rank exactly `r`, its first-`r`-columns block `P_1`
(`M_0 × r`) is left-invertible (full column rank `r`), and `P_2` (`M_0 × s`, `s = m1 − r`) lies in
`col(P_1)`: `rank(P) = rank(P_1) = r` (EXACT, 46/46, `pp_smear_unify.py`).

This is what makes the rational routing `Λ_0 := P_1^+ P_2 = (P_1^T P_1)^{−1} P_1^T P_2` well-defined for
ALL 46 (the `r×r` Gram `P_1^T P_1` is invertible off a null set), and `P_1 Λ_0 = P_2` exactly.

---

## 2. The rational single-pivot chart `φ_sm` (uniform over all 46)

Coords (a genuine reparametrization of all `N = flatDim M` flat coords): the front factors
`A⁽⁰⁾,…,A⁽ᴸ⁻²⁾` (`∑_{k<L−1} M_k M_{k+1}` coords, IDENTITY); the radial pivot `z` + the angular `H̄`
(`r×c` block with the `(0,0)` entry being `z`-pivoted, the other `r·c − 1` angular); the residual
`S_bot` (`s×c`, free). Total `= ∑_{k<L−1} M_k M_{k+1} + r·c + s·c = N` (EXACT, 46/46, full diffeo).

    front  = (A⁽⁰⁾,…,A⁽ᴸ⁻²⁾)  free generic,   P := A⁽⁰⁾···A⁽ᴸ⁻²⁾,  P_1 = P[:, :r],  P_2 = P[:, r:],
    Λ_0    := (P_1ᵀ P_1)⁻¹ P_1ᵀ P_2          (r×s, RATIONAL in the front coords; P_1 P_2-routing),
    A⁽ᴸ⁻¹⁾ := [ z·H̄ − Λ_0·S_bot      (top r rows: radial − shear-absorbed)
                S_bot ]                (bottom s rows: free residual).

Then the deepest product telescopes (the Λ_0/S_bot terms cancel exactly):

    P·A⁽ᴸ⁻¹⁾ = P_1(z H̄ − Λ_0 S_bot) + P_2 S_bot = z·P_1 H̄ + (P_2 − P_1 Λ_0)·S_bot = z·P_1 H̄,

so **`F = ‖P·A⁽ᴸ⁻¹⁾‖² = z²·‖P_1 H̄‖² = z²·U`** with `U = ‖P_1 H̄‖²`. VALIDATED EXACT:
- `F = z²·U` SINGLE-pivot (z-free `U`): **46/46** (`pp_smear_rational_exhaustive.py`; L≤3 full symbolic
  + the L=4 reps, and the L=4 family by the front-bottleneck=r structural argument; spot-checked L=4
  `(2,1,2,1)`,`(1,2,2,1)` full symbolic).
- `U ≢ 0`: **46/46** (`U = ‖P_1 H̄‖²`, `H̄(0,0) = 1`, `P_1` full rank ⟹ `U ≥ |P_1 e_0|² > 0` generically).
- **`U` is a genuine POLYNOMIAL** (the rational `Λ_0` CANCELS out of `F`; e.g. `(1,3,2)`:
  `U = a0_0²·(h0_1² + 1) = ‖P_1 H̄‖²`, no denominator). So the a.e.-positivity `Ubound` rides the
  EXISTING polynomial-zero-set route (`MvPolynomial.ae_eval_ne_zero`); only `φ_sm` (not `U`) is rational.
- coord count `= N` (full-N diffeo): **46/46**.

---

## 3. RESIDUAL 2 — the determinant END-TO-END (exactly `|z|^{minAdm−1}`)

The chart map `φ_sm : (front, z, H̄-angular, S_bot) ↦ (front, A⁽ᴸ⁻¹⁾)` has Jacobian, in block form
(domain `front | z | H̄-ang | S_bot`, image `front | A⁽ᴸ⁻¹⁾-top | S_bot`):

- `front ↦ front`: identity block (det 1).
- `A⁽ᴸ⁻¹⁾-top = z·H̄ − Λ_0(front)·S_bot`: vs `(z, H̄-ang)` it is the radial `pivotBlowupOn` on the `r·c`
  top coords (the `(0,0)=z` pivot, the `r·c−1` angulars scaled by `z`) → det contribution `z^{r·c−1}`;
  the `−Λ_0 S_bot` shift reads only `front`+`S_bot` (off the radial rows) → off-diagonal, det-neutral.
- `S_bot ↦ S_bot` (the bottom rows): identity (det 1).

Block-triangular ⟹ `|det Dφ_sm| = |z|^{r·c−1} = |z|^{minAdm−1}`, EXACTLY, off the null set
`{det(P_1ᵀ P_1) = 0}` (Λ_0's pole). VALIDATED by SYMBOLIC Jacobian determinant: `detJ − z^{minAdm−1} = 0`
EXACT for all tractable cases — **28/28** (L=2: 4, L=3: 12, small L=4: 12; `pp_smear_det_all.py`) — plus
the L=4 reps `(2,1,2,1)`,`(1,2,2,1)` (det `= z^0 = 1`, `minAdm = 1`). The structure (identity-front +
unit-triangular rational shear + radial) is L-independent, so the larger L=4 cases follow by the same
block-triangular argument.

The threshold is therefore exactly `½·minAdm`: the single binding axis is `z` with `(k_z, h_z) = (1,
minAdm−1)`, `axisRatio(z) = minAdm/2`; all other coords have `k = 0` (`axisRatio = ⊤`, non-binding). The
rational shear's pole is a null set, irrelevant to the box `lintegral` lower bound.

---

## 4. The bundle — fits the EXISTING `NodeAchieverChart` (single-axis)

Because `φ_sm` is single-pivot, the smeared chart supplies a `NodeAchieverChart M` with:
- `hpos = ` `1 ≤ minAdm M` (the boundary class has `minAdm = r·c ≥ 1`);
- `phi = φ_sm` (the rational map, extended arbitrarily on its null pole set — `cov`/`Ubound`/`leaf_integrand`
  only see it on `box \ {z=0}` minus the pole, a.e.);
- `p = z` (the pivot axis); `leafH = (minAdm−1 at z, 0 elsewhere)`; `leafH_pivot : leafH z = minAdm−1` ✓;
- `Ufun = U = ‖P_1 H̄‖²` (polynomial, measurable, bounded on the box, `≢ 0` ⟹ `> 0` a.e. — `Ubound` via
  the banked `MvPolynomial.ae_eval_ne_zero` route, `achieverUfun_ae_pos`-style);
- `leaf_integrand`: rides on `F = z²·U` + `U ≥ 0`, det-free (the `leaf_integrand_of_rate` shape);
- **`cov`: the ONE genuinely-new piece** — the change-of-variables `∫⁻_{φ_sm''(V\{z=0})} g = ∫⁻_{V\{z=0}}
  ofReal(|z|^{minAdm−1})·g(φ_sm u)`. Since `φ_sm` is RATIONAL (a.e.-analytic, not polynomial), this goes
  through `S1.1 weightedThreshold_transport` (stated for a.e.-analytic proper maps, off a null set) with
  the Jacobian `|z|^{minAdm−1}` from §3 — NOT the polynomial `pivotBlowupOn` `cov` (`phi334_cov`) the
  banked charts use. The Jacobian weight `∏_j |u_j|^{leafH j} = |z|^{minAdm−1}` matches `leafH` exactly.
- `image_subset`: the bounded source box maps into a small cube (the pivot scales by `z`, angulars/front
  bounded) — the banked-anchor `injOn`/image pattern, adapted to the rational map off its pole.

So the cited atom is reused **as-is** (`monomialIntegrand_lintegral_box_eq_top (d) (k h) (hk) …` takes an
arbitrary `(k,h)` with one nonzero-`k` axis; here `k = nodeLeafK N z` single-axis, `h = leafH`) — NO new
citation, and **NO new bundle structure**.

---

## 5. The corrected 4-way assembly (supersedes the `certificate-genM-witness-v2.md` §5 caveat)

```
nodeChartGeneral M hpos :=                 -- 2 ≤ L, minAdm ≥ 1
  if  ∃ p∈[1,L−1], r_p≥1 ∧ c_p≥1            -- INTERIOR (decidable)
  then  colPath Schur achiever chart (v2 §2)            -- DONE, integrated (285/351, reviewer-PASS)
  else if  Text(L) = M_{L−1}                -- BOUNDARY-CLEAN (decidable)
  then  banked whole-deepest radial (cite RouteM4422/RouteM221)        -- single-pivot NodeAchieverChart
  else  φ_sm : the rational single-pivot smeared chart (this cert)     -- single-pivot NodeAchieverChart,
                                                                       --   cov via S1.1 a.e.-analytic transport
```
`L = 1` → banked `DeepestBaseL1`. **The v2 §5 "MULTI-AXIS caveat" is RETRACTED**: the smeared branch is
single-pivot (one binding axis `z`), fitting `NodeAchieverChart`; no multi-axis bundle. The `Text(L) = m1`
guard is decidable; all four cases exhaustive.

---

## 6. PROVED / TO-BUILD / CITED

- **PROVED (this pass, EXACT + exhaustive):** front-bottleneck `= r` (652/652 wider grid); the rational
  chart `F = z²·U` single-pivot + `U ≢ 0` polynomial (46/46); full-N diffeo coord count (46/46); det
  `= |z|^{minAdm−1}` (28/28 symbolic + L=4 reps + the L-independent block-triangular structure);
  threshold `= ½·minAdm` (single binding axis `z`).
- **TO BUILD (Lean, the smeared tide — bounded):** (a) `φ_sm` as a flat map (front identity + the
  rational `Λ_0` shear + the radial `pivotBlowupOn` on the `r·c` top block); (b) the rate `F = z²·U` via
  the per-entry telescoping (the cancellation `P_1 Λ_0 = P_2`); (c) `U = ‖P_1 H̄‖²` polynomial + `Ubound`
  (banked zero-set route); (d) **the rational `cov` via `S1.1 weightedThreshold_transport`** (the genuinely
  new piece — the a.e.-analytic Jacobian `|z|^{minAdm−1}`, off the `{det P_1ᵀP_1 = 0}` null set); (e) the
  4-way `nodeChartGeneral` assembly. NO new bundle structure; NO new citation.
- **CITED:** `monomialIntegrand_lintegral_box_eq_top` / `monomial_rlct` (reused, single-axis);
  `S1.1 weightedThreshold_transport` (a.e.-analytic change-of-variables — the rational chart's `cov`);
  `RouteM4422`/`RouteM221` (boundary-CLEAN); `DeepestBaseL1` (L=1); the banked `MvPolynomial.ae_eval_ne_zero`
  positivity route.

**Caveat carried next to the claim:** `φ_sm` is RATIONAL (the routing `Λ_0 = (P_1ᵀP_1)⁻¹P_1ᵀP_2` divides
by the Gram minor). It is a genuine diffeo + measure-preserving det `|z|^{minAdm−1}` only OFF the null set
`{det(P_1ᵀP_1) = 0}`. The box-divergence lower bound is unaffected (the pole is null), but the `cov` MUST
be the `S1.1` a.e.-analytic transport, not the polynomial `pivotBlowupOn` `cov`. The one un-ground-out
detail (for the formaliser): confirm `S1.1 weightedThreshold_transport`'s hypotheses (proper a.e.-analytic,
the Jacobian-weight form) accept this specific rational map — I validated the det EXACT but did not
re-derive `S1.1`'s exact interface here.

## 7. Validation harness (the durable gate)

- `scripts/pp_smear_unify.py` — front-bottleneck `= r` + `rank(P) = rank(P_1)` (46/46), the unification.
- `scripts/pp_smear_rational_exhaustive.py` — `F = z²·U` single-pivot + `U ≢ 0` + coord count `= N` (46/46).
- `scripts/pp_smear_det.py` / `pp_smear_det_all.py` — det `= z^{minAdm−1}` EXACT (28/28 + L=4 reps).
Re-run before the smeared Lean tide; all must report the full counts with 0 failures.
