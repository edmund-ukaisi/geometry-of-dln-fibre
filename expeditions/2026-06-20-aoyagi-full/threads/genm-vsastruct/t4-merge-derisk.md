# genm-vsastruct — the T4 coupled-corner MERGE de-risk (TERMINAL design pass)

**Seat:** pen-and-paper (design + carrier-fit adjudication). **Date:** 2026-07-11. **NO Lean.** **Charge:**
realise ONE coupled-corner merge on (3,3,3,4) t=1 through the `sharedDivisorExp` accounting → the
CARRIER-FIT VERDICT that gates the T4 formaliser. **Decorrelated:** `codex/merge-{prompt,answer}.md`
(gpt-5.6, xhigh; my lean withheld — it reached FITS and located the banked endpoints I then verified).
Reads: live code (`RouteMSJSlice334.lean`, `RouteMSJRadialPolar.lean`, `RouteMSJLedger.lean`,
`RouteMSJDecorated*.lean`); prior certs (t4-design, dps-instance, corank2).

---

## ONE-LINE VERDICT — **FITS. No new carrier constructor.**

**The additive coupled-corner at `½·minAdm` is ALREADY BANKED — `sjSlice_corner_two_block_lt_top`
(`RouteMSJSlice334.lean:77`) proves `∫(u₀²U₀+u₁²U₁)^{−c'}|u₀|^{h₀}|u₁|^{h₁} < ⊤` for
`c' < (h₀+h₁+2)/2`, given `U₀,U₁ ≥ a > 0`, by weighted AM-GM at the min-cut weights (the "codimensions
ADD" mechanism), with the (3,2)→7/2 instance already in-file. The block-additive support is built by the
banked `prependColumn` with INDICATOR columns (`a_k(i)=𝟙[block(i)=k]`), NOT `radialAttach` (which is
`prependColumn(≡1)` = the multiplicative product → the 3/2 min). The general-`m` corner is the banked
`corner_block_cube_lintegral_lt_top` (P-dim flat isotropic corner, threshold `P/2 = ½·Σp_k`) via blockwise
polar coordinates. So route (A) FITS: the carrier + banked endpoints express the `7/2`. The genuinely-new
content is NOT a constructor but the ASSEMBLY + the ADMISSIBLE class + the explicit A₂-rank-drop
stratification (the units-bounded-below sector is a REQUIRED hypothesis; the complement routes to a deeper
stratum). → Commission the T4 formaliser on the assembly below.**

---

## 1. The merge on (3,3,3,4) t=1, through `sharedDivisorExp` (both routings → 7/2)

**Setup.** Two blocks at the binding cut: the Γ corank block (dim `p₀ = ab = (3−1)(3−1) = 4`, radial `u₀`,
Jacobian `h₀ = p₀−1 = 3`) and the boundary-1 row (dim `p₁ = 3`, radial `u₁`, Jacobian `h₁ = p₁−1 = 2`).
The loss is ADDITIVE (separate blocks): `G = u₀²·U₀ + u₁²·U₁`, `U₀ = ‖w₁A₂‖²+δ²‖w₂A₂‖²`, `U₁ = a_piv²‖v̄A₂‖²`,
measure `|u₀|³|u₁|² du₀ du₁`. Block-additive support (built by indicator `prependColumn`):

| generator | `u₀` | `u₁` |  | sharedDivisorExp |
|---|---|---|---|---|
| U₀-gens | 1 | 0 | | `min = (0,0)` |
| U₁-gens | 0 | 1 | | (NOT dehomogenised) |

**Routing 1 (direct banked endpoint — the one to build).** The block-additive corner is closed DIRECTLY by
`sjSlice_corner_two_block_lt_top 3 2` (no coordinate merge needed): `c' < (h₀+h₁+2)/2 = (3+2+2)/2 = 7/2`,
given `U₀,U₁ ≥ a > 0`. Its proof IS the "codims add" (weighted AM-GM at min-cut weights `w =
((h₀+1)/s,(h₁+1)/s)`, `s = h₀+h₁+2`, the unique direction where both axis constraints coincide at `s/2`).
[FACT — banked, verified in-file; instance at (3,2) is `RouteMSJSlice334:204–212`.]

**Routing 2 (the toric-CoV merge — the `sharedDivisorExp` picture, for intuition).** Blow up the corner
`u₁ = u·τ`, `u₀ = u` (Jacobian `|u|`): support and jac transform to

| generator | `u` | `τ` |  |
|---|---|---|---|
| U₀-gens | 1 | 0 | | sharedDivisorExp `= (1,0)`; U₀-gen achieves both minima ⟹ **dehomogenised** |
| U₁-gens | 1 | 1 | | `G = u²(U₀+τ²U₁)`, residual `U₀+τ²U₁` a unit (≥ `U₀ ≥ a`) |

`(h_u, h_τ) = (h₀+h₁+1, h₁) = (6, 2)` (the `+1` = CoV Jacobian). `monomialThreshold = min_{k>0}(h_k+1)/(2k_k)
= (6+1)/(2·1) = 7/2` (only `u` has `k>0`; `τ` has `k_τ=0`, needs `h_τ>−1` ✓). General `m`: pivot chart
`u_r=ρ`, `u_k=ρτ_k`, `sharedDivisorExp=(1,0,…,0)`, `H_ρ = Σh_k+(m−1) = Σp_k−1`, threshold `(H_ρ+1)/2 =
½·Σp_k = ½·minAdm`. Both routings give the SAME `7/2`; Routing 1 is the banked one-shot, Routing 2 is why
the `sharedDivisorExp` accounting yields the sum. [FACT — exact; Codex-confirmed term-for-term.]

**Contrast — `radialAttach` gives the 3/2 UNDERSHOOT.** `radialAttach = prependColumn(≡1)`: every generator
gets exponent 1 on the fresh coord ⟹ `G = (∏_k u_k²)·U` (MULTIPLICATIVE), integrand `≍ ∏|u_k|^{h_k−2c'}`,
threshold `½·min_k(h_k+1) = ½·min_k p_k = 3/2`. So the recursion must use INDICATOR `prependColumn` (block-
additive), NOT `radialAttach`. [FACT — Codex Q2, exact; matches t4-design-cert.]

## 2. The A₂-rank-drop → explicit generic-minor sector (soundness (d))

The banked endpoint REQUIRES `U₀,U₁ ≥ a > 0` (`hU0`/`hU1`) — the units bounded below on the sphere. This
IS the generic-minor sector: `U₀ = ‖w₁A₂‖²+δ²‖w₂A₂‖²`, `U₁ = a_piv²‖v̄A₂‖²` are bounded below iff `A₂` has
full row rank (`w₁A₂, v̄A₂ ≠ 0`). So:

- **Sector `{U_k ≥ a > 0}`** (A₂ generic, full row rank): `sjSlice_corner_two_block_lt_top` closes it at
  `7/2`. This is the good branch.
- **Complement `{A₂ rank-drop}`** (units collapse): NOT covered by the endpoint (both corner charts need a
  unit > 0). Must route to a DEEPER / higher-`Mval` stratum — NOT an a.e.-drop (the weight is unbounded near
  it; `|u|^{−1}` model). The banked docstring already names the analogous pivot-degeneration direction as a
  *separate non-binding rank-profile stratum* (§4a, threshold `≥ 9/2 > 7/2`); the A₂-rank-drop is the same
  species (a strictly-deeper corank profile, higher `Mval`, so `≥ ½·minAdm`). [FACT — the endpoint's
  hypotheses; INFERENCE — the complement is a higher-`Mval` stratum, corank2-cert §1 + vslice §4a.]

**The RLCT-collapse trap avoided:** the endpoint's AM-GM is the COUPLED addition (codims add → 7/2); an
independent scalar split would take the min (→ 3/2, the `z²(x²+y²)` caricature). The units-bounded-below
hypothesis is exactly what pins the coupled branch; the complement (where it fails) is stratified off.

## 3. CARRIER-FIT VERDICT: **FITS** — the banked assembly (formaliser-ready)

No new carrier constructor. The (A) peel assembles from banked pieces, in order:

1. **Peel + block-additive support:** pivot-chart + Schur-split (`frobSq_schur_block_split`) + shear
   (`measurePreserving_shearSub`) expose the corank block; the loss becomes `∑_k (block-k generators)²`.
   Record it via `prependColumn` with the INDICATOR column `a_k(i)=𝟙[block(i)=k]` (banked `prependColumn`,
   NOT `radialAttach`) — building the block-additive support `[[1,0],[0,1]]`. [banked machinery]
2. **Units-bounded-below comparison (the sector):** on `{U_k ≥ a > 0}` (A₂ generic), the residual units are
   bounded below — the `hU0`/`hU1` the endpoint consumes. This is the T2 rowMix casting the generators + the
   sector restriction. [T2 carrier + sector hypothesis]
3. **The corner endpoint:** `sjSlice_corner_two_block_lt_top (h₀ h₁) c' hc' U₀ U₁ a ha hU0 hU1` for `m=2`
   (the (3,3,3,4) binding path), threshold `(h₀+h₁+2)/2 = 7/2`. For general `m>2`:
   `corner_block_cube_lintegral_lt_top` (P-dim flat isotropic corner, `g` degree-2 homogeneous + bounded
   below on the sphere, threshold `P/2 = ½·Σp_k`) via a blockwise-polar CoV — packaged as a multi-block
   wrapper (existing semantics, not a new op). [banked endpoints]
4. **Stratification:** cover = sector `{U_k ≥ a}` (step 3) ⊔ complement `{A₂ rank-drop}` → deeper `Mval`
   stratum (the recursion / a higher-corank peel), each `≥ ½·minAdm`. [NEW glue — the soundness split]

**Genuinely-new content (all buildable-as-labour, NO new constructor):**
- The **ADMISSIBLE decoration class** (∀-decoration is FALSE — `(trivial (1,2)).radialAttach 0` diverges at
  `c'=3/4`; t4-design §2): pin `jac` = true valuation, block-additive support from indicator `prependColumn`,
  units bounded below on the sector, rank-drop → deeper, binding-budget. + the decorated arity driver over it.
- The **explicit A₂-rank-drop stratification** (step 4) — the soundness-critical split.
- The **wiring**: indicator `prependColumn` (not `radialAttach`) → the additive-corner endpoint (not the
  `monomialIntegrand` min-terminal); the `exists_binding_cut` guard (dps-cert Q3: else `c'=ab/2` coincides
  with the threshold, e.g. `(4,4,2,2)` t=2).
- The **multi-block (`m>2`) wrapper** packaging `corner_block_cube` via blockwise polar (existing semantics).

---

## VERDICT / firmest / most-likely-to-break / next

- **VERDICT: (A) FITS and is FULLY SPECIFIED — buildable-as-labour → commission the T4 formaliser on the
  §3 assembly.** No new carrier constructor: the additive-corner endpoint (`sjSlice_corner_two_block_lt_top`
  / `corner_block_cube`) that delivers the SUM-threshold `½·minAdm` is banked and proven (weighted AM-GM,
  codims add). The design phase closes. The formaliser builds: indicator-`prependColumn` block-additive
  support → units-bounded-below sector → banked corner endpoint → stratified cover with the A₂-rank-drop
  complement → deeper.
- **Firmest.** `sjSlice_corner_two_block_lt_top` closes `(u₀²U₀+u₁²U₁)^{−c'}|u₀|^{h₀}|u₁|^{h₁}` at
  `(h₀+h₁+2)/2 = 7/2` (banked, in-file (3,2) instance). `radialAttach` = multiplicative → 3/2 (must use
  indicator `prependColumn`). Both merge routings → 7/2 via `sharedDivisorExp`. All decorrelated-confirmed.
- **Most likely to break.** (i) The A₂-rank-drop complement (step 4): it MUST be an explicit deeper stratum
  with `≥ ½·minAdm`, not an a.e.-drop — the one spot a subtle RLCT-collapse hides; the endpoint's
  `U_k ≥ a > 0` is the exact gate, so the build must PRODUCE the sector cover + route the complement, not
  assume units positive. (ii) The `m>2` blockwise-polar wrapper (recording the joint loss as degree-2
  homogeneous + bounded below on the sphere) — routine but the homogeneity/lower-bound casting must be
  faithful. (iii) The ADMISSIBLE class must be closed under the peel (units-bounded-below propagates), else
  the decorated IH is unprovable.
- **Next.** Commission the T4 formaliser on the §3 assembly (m=2 first, on the (3,3,3,4) binding path, using
  the banked `sjSlice_corner_two_block_lt_top`), with the A₂-rank-drop complement routed to the deeper
  stratum. The `m>2` wrapper and the admissible-class closure are the follow-on labour. No 6th design pass
  needed — the carrier fits.
