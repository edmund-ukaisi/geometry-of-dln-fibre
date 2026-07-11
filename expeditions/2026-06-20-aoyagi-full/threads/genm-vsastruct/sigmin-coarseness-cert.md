# genm-vsastruct — the σ_min-coarseness crux (gates mountain gaps (3)+(4))

**Seat:** pen-and-paper (crux adjudication). **Date:** 2026-07-11. **NO Lean.** **Charge:** does the CRUDE
coercivity bound `∫_tail σ_min(L_θ)^{−2c'}` close the native one-peel at `c'<7/2`, or undershoot (needing the
SHARPER anisotropic estimate)? Gates gaps (3)+(4) of the mountain formaliser. **Exact algebra:**
`/tmp/sigmin_coarse.py` (MC guide + the exact Beta reduction). **Decorrelated:** `codex/sigmin-{prompt,answer}.md`
(gpt-5.6, xhigh; my lean withheld — it CONFIRMED `β=2c'−6` with the exact Gamma constant + the deeper-rung
`β=2c'−5`). Reads: `genm-mountain-recon/recon-map.md`, `onepeel-altroute-cert`, `corank2-cert`.

---

## ONE-LINE VERDICT — the CRUDE bound UNDERSHOOTS (to `c'<½`); the SHARPER anisotropic estimate is REQUIRED

**The crude `corner_block_lintegral_le` bound (inner `≤ σ_min(L_θ)^{−2c'}`, the sphere-min/worst-direction)
DOES NOT close at 7/2 — it charges the FULL `2c'` to the single smallest direction, treating all 6 stable
directions as if they also collapsed, and undershoots MASSIVELY (feeds `α=2c'` to the ProductTube, `α<1 ⟹
c'<½`). The SHARP inner value as one direction collapses is `σ_min^{−(2c'−6)}` (EXACT: `I_c(σ) ≍ σ^{6−2c'}`
for `3<c'<7/2`; only the collapsing direction charges, the 6 stable ones integrate to a bounded factor —
codims-add), which feeds `α=2c'−6<1 ⟹ c'<7/2` to the ProductTube and CLOSES. So the required sharp estimate
is EXACTLY the front-first / two-block-radial majorant (`twoBlock_radial`, the "off-path" vsa module) — it
is REUSABLE and NEEDED for gap (3), NOT off the critical path. The deeper (front-rank-drop) stratum is a
corank recursion (`β=2c'−5<2 ⟺ c'<7/2`, non-worsening). This is the native, det-inverse-free re-expression
of the codims-add / abscissa-0.88 finding: the cover charges must ADD (only the collapse charges), not MIN
(all directions charge → 3/2 caricature).**

## 1. (Q1) The crude bound does not close — the sharp inner exponent is `2c'−6`, not `2c'`

The banked fixed-θ inner slice (`sjGoodMap_loss_matBox_lt_top`) is finite at `c'<7/2` (full 7-dim
positive-definite corner) — SHARP for fixed θ. The COARSENESS is in bounding the inner VALUE for the outer
θ-integration. Two bounds:
- **CRUDE** (`corner_block_lintegral_le`, RouteMSJCornerBound:55): inner `≤ a(θ)^{−c'} = σ_min(L_θ)^{−2c'}`,
  `a =` sphere-min of `g_cc = σ_min(L_θ)²` (the worst-direction / `g_cc ≥ σ_min²‖x‖²`).
- **SHARP** (exact, one direction collapsing): `I_c(σ) = ∫_{[-1,1]^7}(‖y‖² + σ²z²)^{−c'}, y∈ℝ⁶, z∈ℝ`. Scale
  `y=σu`: `I_c(σ) ≍ C_c·σ^{6−2c'}`, `C_c = 2π³Γ(c'−3)/((7−2c')Γ(c'))` (for `3<c'<7/2`). So

> **inner `≍ σ_min(L_θ)^{−(2c'−6)}`** (codims-add: only the collapse charges, the 6 stable directions give a
> bounded `∫_{ℝ⁶}(‖u‖²+z²)^{−c'}du = π³Γ(c'−3)/Γ(c')·|z|^{6−2c'}` factor).

[FACT — exact Beta reduction; Codex-confirmed with the Gamma constant. Piecewise: `c'<3` bounded, `c'=3`
log, `3<c'<7/2` → `σ^{−(2c'−6)}`; at `c'=7/2` the fixed-θ slice itself diverges.] The crude over-charges by
`σ_min^{−2c'}/σ_min^{−(2c'−6)} = σ_min^{−6}` — it charges the 6 stable directions as if collapsing. [FACT.]

## 2. (Q2) Crude vs sharp threshold over the tail — `c'<½` vs `c'<7/2`

`σ_min(L_θ) ≠ sigMin(rmatMul (A 0)(A 1))` (the 7-dim `g_cc` operator vs the product's σ_min), but relates:
`L_θ = L_env ∘ (·A₂)`, `σ_min(L_θ) ≥ σ_min(L_env)·σ_min(tail)`, `σ_min(L_env)` bounded below on the good chart
— so `σ_min(L_θ)^{−α} ≤ C·σ_min(tail)^{−α}`, integrable by the ProductTube (`sjProductTube_params_lintegral_lt_top`,
`α<1`). Then:

| bound | weight fed to ProductTube | closes iff |
|---|---|---|
| CRUDE (`corner_block_lintegral_le`) | `σ_min^{−2c'}` (`α=2c'`) | `2c'<1 ⟹` **`c'<½`** (undershoot) |
| SHARP (two-block-radial) | `σ_min^{−(2c'−6)}` (`α=2c'−6`) | `2c'−6<1 ⟹` **`c'<7/2`** (closes) |

[FACT — Codex Q2, exact.] So the build must NOT feed the crude `σ_min^{−2c'}` to the ProductTube (closes
only at `c'<½`); it must produce the SHARP `σ_min^{−(2c'−6)}` weight (integrate the stable block first) and
feed THAT. The deeper rung is the sharp estimate, not the crude corner-block. **⟹ the recon-map's staging of
`corner_block_lintegral_le` for gap (3) is INSUFFICIENT.**

## 3. (Q3 SOUNDNESS) The cover must ADD the codim — the sharp estimate IS the codims-add

The sharp estimate charges ONLY the collapsing direction (`σ_min^{−(2c'−6)}`), the 6 stable directions
bounded below on the `{s_1..s_6 ≥ κ}` SECTOR — this IS "the codims ADD" (the collapse codim `+` the stable-block
codim reconstitute `minAdm`). The crude charges all 7 as if collapsing (`σ_min^{−2c'}`), which is the
independent-scalar-split → MIN → the `z²(x²+y²)` / abscissa-0.88 caricature (undershoot to `3/2`/`½`). The
EXACT charge-addition making it 7/2:
- **Good branch** `{s_6(L_θ) ≥ κ}` (the SECOND-smallest bounded below — the vsa F2 sector, NOT just
  `{σ_min≥κ}`): the stable 6-block integrates to a bounded factor, only `s_7 = σ_min` charges `2c'−6`; the
  ProductTube integrates `σ_min^{−(2c'−6)}`, `α'<1 ⟹ c'<7/2`.
- **Deeper branch** `{s_6 < κ}` (two directions collapse, `s_6≈s_7≈σ`): `β = 2c'−5`, integrated against the
  codim-2 tube; `2c'−5 < 2 ⟺ c'<7/2` — a corank recursion, NON-worsening (the higher-corank strata reproduce
  the same strict `7/2` under matching tube codim, per `corank2-cert` `D_prod=(8,4,1)`). [FACT+INFERENCE —
  Codex Q3.]

## 4. VERDICT — SHARPER anisotropic estimate needed; the "off-path" `twoBlock_radial` is the reusable core

The crude `corner_block_lintegral_le` (`σ_min^{−2c'}`) undershoots to `c'<½`. **The required sharp estimate
is the front-first / two-block-radial majorant** `∫_{[-1,1]^7}(Σ s_j² u_j²)^{−c'} ≲ (∏_{j<7} s_j^{−1})
s_7^{6−2c'}`, i.e. on the sector `{s_1..s_6 ≥ κ}`: `≲ σ_min^{−(2c'−6)}`. This is EXACTLY the banked vsa
`twoBlock_radial` (`RouteMSJTwoBlockRadial`, the `α'=2c'−m₀(r−1)=2c'−6` majorant) — the module the recon-map
listed as "PARALLEL / off critical path" is REUSABLE and NEEDED here. The det-inverse is still gone (the sharp
estimate is a σ_min-power, not a det-Jacobian); the sharp estimate is the native re-expression of the
codims-add. **Feeds the mountain gaps:**
- **Gap (3) [good-branch integration]:** REPLACE the crude `corner_block_lintegral_le` with the sharp
  `twoBlock_radial` — integrate the stable 6-block first (bounded on `{s_6≥κ}`), leaving `σ_min^{−(2c'−6)}`,
  then the ProductTube (`α'<1`). Banked pieces: `twoBlock_radial` (vsa), `sjProductTube_params_lintegral_lt_top`
  (α<1), the spectral bedrock `minStretch`/`gram_rayleigh_lb`/`FrontSpectral`.
- **Gap (4) [deeper front-rank-drop descent]:** the corank recursion (`β=2c'−5<2` at 7/2, non-worsening) —
  the `corank2-cert` `β_k`/`D_prod` structure, integrated per stratum; the good∪deeper cover splits on the
  SECOND-smallest sector `{s_6(L_θ)≥κ}` (not `{σ_min≥κ}`), and the deeper stratum recurses (a further peel).

### Firmest / most-likely-to-break / next
- **Firmest.** Crude `σ_min^{−2c'}` undershoots to `c'<½` (`α=2c'` vs ProductTube `α<1`); sharp
  `σ_min^{−(2c'−6)}` closes at `7/2` (`α'=2c'−6<1`). Exact Beta reduction, Codex-confirmed. The crude
  over-charges by `σ_min^{−6}` (the 6 stable directions).
- **Most likely to break.** The good∪deeper cover must split on the SECOND-smallest singular value
  `{s_6(L_θ)≥κ}` (the vsa F2 sector), NOT `{σ_min≥κ}` — the sharp estimate needs the STABLE block bounded
  below. A build that covers on `{σ_min≥κ}` alone (as "good∪deeper" naively reads) still hits the crude
  coarseness on the near-second-smallest locus. The dichotomy is on `σ_{r−1}`, not `σ_r` (secinfra's F2,
  now the native gate).
- **Next.** Spec gap (3) on the sharp `twoBlock_radial` (not `corner_block_lintegral_le`): the sector
  `{s_6(L_θ)≥κ}` → stable-block-first → `σ_min^{−(2c'−6)}` → ProductTube. Spec gap (4) as the corank
  recursion on `{s_6<κ}` (the `corank2-cert` strata). Re-list `RouteMSJTwoBlockRadial` + the corank2/vsa
  spectral bedrock as ON the critical path (the recon-map's "off-path" call was for the crude route; the
  sharp route needs them). The det-inverse remains eliminated — this is a σ_min-power sharpening, not a
  det-Jacobian.
