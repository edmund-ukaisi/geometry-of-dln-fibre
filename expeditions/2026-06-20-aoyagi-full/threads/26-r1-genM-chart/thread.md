# R1 #135 — the GENERAL-M achiever chart design (witness seat)

**Seat:** `pen-and-paper` (witness; obstruction fallback). **Date:** 2026-06-24.
**Gate:** R1 lower-bound atom `routeMCore_box_diverges_achiever` (`RouteMLayerCoverGE.lean:117`) —
does the now-PROVEN (3,3,4) coupled-`diag(b)` achiever chart **generalize** to a general-`M` chart
proving the box-divergence lower bound `rlctAtOn(routeMCore M) 0 ≤ ½·minAdm M`?
**Method:** exact symbolic (sympy) flat-coordinate factorizations + exact Jacobian determinants +
exact-rational monomial-threshold arithmetic; one decorrelated `local-codex-consult` (gpt-5.x, xhigh,
conclusion withheld). Scripts: `scripts/*.py`; Codex prompt/answer: `codex/genM-chart-{prompt,answer}.md`.

---

## VERDICT: **GENERALIZES** (mechanism), via a single common radial blow-up; build-ready as a
## PER-NODE chart SPEC. The closed-form general-`M` chart needs case-specific frame chaining.

> The (3,3,4) chart's mechanism **does generalize to all positive `M`** at the level of the
> *mechanism* + the *Jacobian arithmetic*: the achiever loss, after the Aoyagi Schur gauge, is a
> **sum-of-squares** `F ∼ Σ_{i=1}^{d} g_i²` of `d = minAdm M` binding generators (NOT a product —
> this corrects thread 22's "product axis" framing), radialized by **one common pivot** `g_i = u·w_i`.
> This gives `F∘φ = u²·V`, `V` bounded above and below on a positive-measure box, and
> `|det Dφ| = |u|^{minAdm−1}·(spectator monomial on k=0 axes)`. The single binding axis `(k,h)=
> (1, minAdm−1)` feeds the existing Lean atom `monomialIntegrand_lintegral_box_eq_top` at threshold
> exactly `½·minAdm` (the spectator monomial sits on `k=0` axes, `axisRatio = ⊤`, so it does not
> lower the threshold — exactly the `leafK334`/`leafH334` pattern).
>
> **Verified EXACTLY (rate + bound + nonzero Jacobian `= u^{minAdm−1}`) on three structurally-distinct
> witnesses:** `(3,3,4)` [`L=2`, single pivot — the banked Lean chart], `(4,4,2,2)` [`L=3`, leaf-only
> codims `0,0,4`], and **`(3,3,3,3)` [`L=3`, NONZERO intermediate codims `1,2,3` — the "shared deep
> factor" regime the (3,3,4) cert §6 flagged untested]**. The last is the decisive new evidence: the
> single-radial chart works for genuine multi-pivot nested descents.
>
> The **honest residual** is not the mathematics but the **closed-form chart construction**: a single
> uniform formula for `φ_M` that is simultaneously (a) the right achiever RATE (`F = u²·V`, no `u⁰`
> term) and (b) a genuine **diffeo** (`det ≠ 0` off the divisor). Naive uniform recipes break one or
> the other (the degenerate-chart trap). The verified charts need a **case-specific Schur frame** with
> a **free spectator pivot** (the `det = 0` failures all trace to a kept-pivot pinned to a constant,
> i.e. an unreachable flat coordinate). Strictly-decreasing kept-rank paths chain cleanly (`(3,3,3,3)`);
> a codim-0 rank-STAY at an intermediate boundary (`(2,3,4,2)`) needs more frame care — the boundary of
> what a verbatim recipe covers, NOT a math obstruction (the codim-`minAdm` center still gives `u^{minAdm−1}`).

---

## The load-bearing mechanism (depth-independent, exact)

The Lean atom diverges via a single binding axis `j₀` with `e_{j₀} = h_{j₀} − 2k_{j₀}c' ≤ −1`
(`exists_binding_axis`); `monomialThreshold d k h = inf_{k_j≠0} (h_j+1)/(2k_j)`. The chart must deliver,
on a positive-measure box mapping into `cubeBox`:

    F∘φ(u) = u²·V(u),   0 < c₀ ≤ V ≤ B  on the box,   |det Dφ(u)| = |u|^{minAdm−1}·(spectator),

then `∫ |det|·|F∘φ|^{−c'} ≥ B^{−c'} ∫ u^{minAdm−1−2c'} = ⊤` at `c' = ½·minAdm` (exponent exactly `−1`).

**Exact threshold arithmetic (all minAdm):** binding axis `(k,h)=(1,minAdm−1)`; at `c'=½·minAdm`,
`e = (minAdm−1) − 2·1·(minAdm/2) = −1` (sharp `∫₀^ε u⁻¹ = ⊤`). Spectator `k=0` axes carry `h≥0`,
`∫₀^ε u^h` finite → harmless. Threshold `= (minAdm−1+1)/(2·1) = ½·minAdm`. [`scripts/genM_chart_monomial.py`,
final block of summary run — exact `Fraction`, all of `{3,4,6,8,11}`.]

**The unradicalized form is a SUM, not a product** (decorrelated Codex + my `genM_transcribe.py`):
the nested Schur peel yields `F ∼ r₁²+…+r_d²` (smooth-normal), `d=minAdm`; the product-normal-crossing
`∏ rᵢ²` form is FALSE for genuine multi-pivot cases. The single product-monomial Lean atom becomes
valid only AFTER the common radial blow-up `r₁=u, rᵢ=u·wᵢ` (Jacobian `u^{d−1}`).

## Witness certificates (EXACT, sympy)

| `M` | `minAdm` | descent `T*` | block sizes `d_j` | `F=u²·V` rate | `V` bounded ∈(c₀,B) | `|det Dφ|` | binding axis | threshold |
|---|---|---|---|---|---|---|---|---|
| `(3,3,4)` | 8 | `(1,0)` | `[4,4]` | ✓ (pure `u²`) | ✓ (`U≥a²`) | `u₀⁷·u₁²` (Lean, exact) | `(1,7)` | `4 = ½·8` ✓ |
| `(4,4,2,2)` | 4 | `(4,2,0)` | `[0,0,4]` | ✓ (pure `u²`) | ✓ (`U=2`@slice) | `u₀³` (exact) | `(1,3)` | `2 = ½·4` ✓ |
| `(3,3,3,3)` | 6 | `(2,1,0)` | `[1,2,3]` | ✓ (`u²·V`, `V` poly) | ✓ (`U=1`@sector) | `u⁵·a⁴·δ²·b³` (exact) | `(1,5)` | `3 = ½·6` ✓ |

- `(3,3,4)`: the banked Lean chart `phi334`; `det = −u₀⁷·u₁²` re-derived exactly (`verify_334_jacobian.py`).
- `(4,4,2,2)`: leaf-only codims; pure radial blow-up of the deepest `2×2` factor, `det = u₀³`
  (`genM_genuine_4422.py`). The radial coord exponent `= codim(center) − 1 = minAdm − 1`.
- `(3,3,3,3)`: Codex's explicit nested-frame chart, **independently re-verified** (never paste-trusted):
  `(I₂|m)B=D`, `wC=uζ`, `ABC=uH` ⟹ `F=u²·V` (`V` polynomial, `V|_{u=0}=U`, `U(sector)=1>0`),
  `|det Dφ| = u⁵·a⁴·δ²·b³` (exact 27×27 det) — the spectator monomial `a⁴δ²b³` on `k=0` axes
  (`verify_codex_3333.py` + `verify_codex_3333_bound.py`). The DECISIVE multi-pivot-with-residual case.

`(2,2,2)` is ALREADY banked in Lean (`Case222Resolution.phiUnit`, a two-step composite — even the
depth-2 single pivot is NOT a one-line radial scaling). `(2,3,4,2)` [codim-0 intermediate stay]: rate
`F=u²·V` achievable but the naive frame gives `det=0` (a flat coord unreachable) — needs a free spectator
pivot; recorded as the construction-effort boundary.

## The codim-`minAdm` backbone (why the Jacobian is `u^{minAdm−1}`, depth-independent)

The achiever center is the locus where the `d=minAdm` binding generators `g_i` vanish — codim `minAdm`
(Codex's block sizes `d_j = (t_{j−1}−t_j)(M_j−t_j)`, `t_0=M_0`, `Σd_j = minAdm` — verified `=Mval(M,T*)`
exactly for all test `M`, `scripts/genM_structure.py` cross-checked). A single radial blow-up of a
codim-`d` linear center has radial-coordinate Jacobian exponent `d−1` (standard;
`scripts/genM_genuine_3333_correct.py` confirms `d(g_aff)/d(u,w) det = u^{d−1}`). Hence `u^{minAdm−1}`
regardless of `L`. The `minAdm = ½·codim` value is **already PROVEN** at the combinatorial level
(`routeLayerAtlas_value`: `⨅ monomialThreshold = ½·minAdm`); this thread supplies the GEOMETRIC chart
realizing that center with `F=u²·V`, `V` bounded.

## Build-ready SPEC for the formaliser (the `L2AchieverChart`-style bundle, general `M`)

The existing `(3,3,4)` Lean assembly (`RouteMLayerCoverGEL2.lean`: `L2AchieverChart` structure +
`leaf334_box_div` + `routeM334_box_diverges_of_chart`) is the **template**. The general-`M` per-node
chart is a `NodeAchieverChart M` bundle with fields (the `(3,3,4)` field shapes, generalized):

1. **`phi : (Fin N → ℝ) → (Fin N → ℝ)`** (`N = routeMAmbient M`), the iterated Schur-frame ∘ single
   radial blow-up; `phi 0 = 0`, continuous, `phi '' [0,δ]^N ⊆ cubeBox N ε` (the image-containment field).
2. **`routeMCore_phi : routeMCore M (phi u) = (u p)² · Vfun u`** (the EXACT factorization; the
   soundness-critical identity, proven by `ring` from the chart matrices, NOT asserted), `p` the radial
   pivot axis. For multi-pivot `M` this is `(u p)²·V` with `V = Vfun` a polynomial (not necessarily a
   pure unit) — the `(3,3,3,3)` shape.
3. **`Vbound : ∀ δ, ∃ B>0, (∀ u∈[0,δ]^N, Vfun u ≤ B) ∧ ∀ᵐ u, 0 < Vfun u`** — `V` polynomial ⟹
   continuous ⟹ bounded on the compact box; `V|_{up=0}=U` not identically 0 (the sector point witness)
   ⟹ `c₀ ≤ V` on a positive-measure neighborhood. (The `(3,3,4)` `Ubound` field, lifted: `V` need only
   be bounded — the divergence uses `V^{−c'} ≥ B^{−c'}`, the UPPER bound on `V`.)
4. **`leaf_integrand`**: `(∏_j |u_j|^{h_j})·|F∘phi|^{−c} = monomialIntegrand N leafK leafH c u · (Vfun u)^{−c}`,
   with `leafK = δ_{p}` (1 on the radial axis, 0 else) and `leafH` the genuine Jacobian exponents
   (`minAdm−1` on `p`, the spectator monomial on `k=0` axes). The `(3,3,4)` `monomialIntegrand_leaf334_eq`
   analog.
5. **`cov`**: the composite change-of-variables off `{u_p=0}` (the `lintegral_image_…_abs_det_fderiv`
   + null-slice), `|det Dφ| = ∏_j |u_j|^{leafH j}`. Reuses the BANKED `Foundations/ParamsReshapeMP.lean`
   (`measurePreserving_paramsPack_of_flatIdxEquiv` + `continuousLinearMap_abs_det_eq_one_of_measurePreserving`)
   for the outer reshape, and the `(3,3,4)` c-o-v TEMPLATE (Schur-shear det-1 BlockTriangular + chain-rule
   composite det + outer-reshape `|det|=1` pull-out).

Then `routeMCore_box_diverges_achiever M hpos c' hc' ε hε` follows from `NodeAchieverChart M` by the
`(3,3,4)` assembly verbatim (the `leaf334_box_div`/`routeM334_box_diverges_of_chart` chain is
M-agnostic given the bundle — `monomialThreshold N leafK leafH = ½·minAdm` is the only M-specific input,
discharged by `monomialThreshold_le_regularSeq` with `m₀ = minAdm`, exactly as `leafMonomialThreshold334_le`).

**Recommended formalisation order** (decreasing cleanliness of the chart construction):
- (a) **`(4,4,2,2)`** next — leaf-only codims, the chart is a CLEAN pure radial blow-up of the deepest
  factor (no Schur shear, `F = u²·U` PURE), the simplest `L≥3` instance; banks the `NodeAchieverChart`
  structure + the radial-blow-up `det = u^{minAdm−1}` lemma.
- (b) **`(3,3,3,3)`** — the decisive multi-pivot-with-residual; Codex's explicit frame, the `F=u²·V`
  (V poly, not pure unit) shape, exercises the full `Vbound` field. Build on (a)'s structure.
- (c) The general strictly-decreasing-kept-rank class (the `(3,3,3,3)` recipe lifted); roadmap the
  codim-0-stay frames (`(2,3,4,2)`-type) as the residual construction work.

## Scope / levels kept separate / what would break this

- **Levels separate.** This adjudicates the **`rlctAtOn ≤ ½·minAdm` (box-divergence / lower) mechanism**
  — the cover's `cover_ge_div`. The VALUE `⨅ monomialThreshold = ½·minAdm` is already PROVEN
  (`routeLayerAtlas_value`); the `rlct = ½·codim` reading still rides the cited S2 (Aoyagi/Watanabe) bound.
  The matching **upper bound `cover_le` (global convergence below `½·minAdm`) is NOT addressed here**
  (it is corank-SENSITIVE — thread 22 §hfin — and needs the full coupled cover or the cited bound).
- **Proved (exact symbolic):** the three witness charts' rate + bound + Jacobian; the block-size identity
  `Σd_j = minAdm = Mval(M,T*)`; the codim-`d` radial-blow-up exponent `d−1`; the leaf-threshold `−1`
  arithmetic at `c'=½·minAdm`; the sum-not-product unradicalized form.
- **Decorrelated-corroborated:** Codex (xhigh, conclusion withheld) independently reached "sum form,
  not product," "single common radial blow-up ⟹ `(1,minAdm−1)`," gave the explicit `(4,4,2,2)`+`(3,3,3,3)`
  charts (the `(3,3,3,3)` re-verified exactly here), and the block-size formula. It also independently
  flagged that the lower bound does NOT give global convergence below threshold (the upper-bound cover).
- **Structural / NOT a closed certificate:** that a UNIFORM general-`M` `φ_M` formula exists that is
  simultaneously the right rate AND a diffeo. Verified for three cases; the codim-0-stay frame
  (`(2,3,4,2)`) is unverified (the naive frame is degenerate). The honest claim: the MECHANISM
  generalizes; the per-node CHART is build-ready as a SPEC, instantiated case-by-case (the formaliser's
  construction, mirroring `(3,3,4)`).
- **The one thing most likely to break the BUILD (not the math):** the case-specific Schur frame for
  asymmetric / codim-0-stay descents — getting `det ≠ 0` (a genuine diffeo) while keeping the rate.
  The degenerate-chart trap (a `det=0` chart has the rate but is NOT a valid c-o-v) is the recurring
  hazard; mitigated by ALWAYS verifying `det ≠ 0` off the divisor (which all three banked witnesses do).
  **Mitigation:** ship `(4,4,2,2)` (cleanest `L≥3`) then `(3,3,3,3)`; roadmap the general frame.
- **Next construction:** the general strictly-decreasing-kept-rank `φ_M` (the `(3,3,3,3)` frame lifted to
  arbitrary `L` with `t_{s}−t_{s+1}=1`), and a clean frame for the codim-0-stay boundary (`(2,3,4,2)`).
