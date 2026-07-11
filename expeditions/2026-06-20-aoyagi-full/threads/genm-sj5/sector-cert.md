# CRUX cert — the sector-from-region bridge (3iii + 3ii): the single sector does NOT cover; the rank-stratified coupled cover does

**Seat:** pen-and-paper (obstruction — adjudicate the load-bearing core: does a region→sector map close
`g(Q) ≤ C·σ_min^{−α}` over the box?). **Date:** 2026-07-11. **NO Lean.** **Charge (team-lead):** produce
the Lean-buildable sector-from-region construction for `RouteMSJFrontSpectral` (3iii sector-from-region +
3ii measurability), DODGING secinfra's F2 (`sector ⇍ dominance`) — OR surface the wall loudly with the
witness. CONSUME vsastruct (verdict + corank2-cert), don't re-derive.

**Exact algebra (mine):** `/tmp/prodD/sector.py` (codim-k front scaling; single-sector failure on
codim-2; coupled-vs-independent 7/2 vs 3/2; Cauchy–Binet minor-band sandwich). **Consumed:**
`genm-vsastruct/{verdict,corank2-cert}.md`, `RouteMSJFrontSpectral.lean` (`sjSector`,
`frobSq_ge_twoBlock_of_sector`), the banked product-tube codim `D_prod=(8,4,1)` (#116/#127). **Decorrelated:**
own `local-codex-consult` (xhigh, conclusion withheld — told it to HUNT the obstruction):
`codex/sector-{prompt,answer}.md`. Codex reached the same verdict term-for-term (I converged first; it
confirmed) + two caveats, both adopted.

---

## VERDICT (headline): the single two-block `sjSector` does NOT cover the box — F2 is a GENUINE obstruction. It is NOT a hard wall: the RANK-STRATIFIED cover + a corank-q COUPLED majorant closes it. The fill's single-`sjSector` conditional drops its hypothesis ONLY on the top stratum.

`sjSector κ P` (`frobSq_ge_twoBlock_of_sector`) is "one collapsing direction + `(r−1)` directions `≥ κ²`".
It gives `g(Q) ≤ C·σ_min^{−α}`, `α = max{0, 2c'−m(r−1)}`, **on the codim-1 (top) stratum ONLY**. Two exact
facts kill any single-sector cover of the box:

1. **Fixed `κ` misses a positive-measure tube.** Any finite cover by sectors with constants `κ_i > 0`
   (`κ_* = min_i κ_i`) lies in `{σ_{r−1} ≥ κ_*}`, so it misses the OPEN tube `{0 < σ_{r−1} < κ_*}` — a
   positive-measure corank-2 neighbourhood, NOT the null rank-`(r−1)` locus. (F2 made rigorous: the codim-2
   stratum is generic in its tube, not negligible.)
2. **Varying `κ = σ_{r−1}(P)` destroys the estimate.** The predicate holds, but the u-block weight
   `κ² = σ_{r−1}² → 0`, so the bound degrades to `σ_{r−1}^{−6}·σ_min^{−(2c'−6)}` (`m=r=3`) — the true
   corank-2 scaling is `σ_{r−1}^{−3}·σ_min^{−(2c'−6)}` (`corank2-cert`), so the varying-`κ` bound loses
   `σ_{r−1}^{−3}`; on the diagonal it gives `σ^{−2c'}` (threshold `c'<2`) vs the true `σ^{−(2c'−3)}`
   (threshold `7/2`). Far short.

So **the codim-2 stratum forces a genuinely DIFFERENT estimate** — a corank-2 COUPLED majorant (two
collapsing directions in the v-block, coupled at the corner), NOT the single two-block sjSector. This is
vsastruct's "no single global majorant" made precise for the sector construction.

**But it is buildable, not a wall.** The correct construction is a finite RANK-STRATIFIED cover
`{cell_q}_{q=1}^{r}` (corank exactly `q`), measurable via minor cells (3ii, below), with a corank-`q`
coupled majorant on `cell_q`. The single sjSector = the `q=1` rung (closes the top stratum). The
`q≥2` rungs need the coupled corner majorant (the genuine new content).

---

## 1. The codim-k front scaling — the single-sector bound is FALSE on codim-2 (exact)

`g(Q) = ∫_{A₀ box} frobSq(A₀·P)^{−c'} dA₀`, `frobSq(A₀·P) = Σ_j λ_j‖(A₀U)_{·j}‖²` (banked Frobenius–Gram,
`RouteMSJFrontSpectral`). On the codim-`k` stratum (`k` smallest `σ_j ≍ σ`, rest `≍ 1`):
> `g(Q) ≍ σ^{−β_k}`, `β_k = max{0, 2c'−m(r−k)}` (log at `2c'=m(r−k)`).

For `m=r=3`: `β_1 = max(0, 2c'−6)`, `β_2 = max(0, 2c'−3) = β_1 + 3`. Verified `sector.py`: measured
`−dlog g/dlog σ` → `β_2 ≈ 3.44–4.14` (predicted 3.5), `β_3 = 6.5` (exact), `β_1 ≈ 0.24–0.83` (predicted
0.5, log-slow). The single-sector majorant `σ_min^{−β_1}` is EXCEEDED on codim-2 by `σ^{−3}`: the ratio
`g/σ_min^{−β_1}` BLOWS UP (`14.9 → 114 → 1031 → 12900` as `σ = 0.2 → 0.025`) — **no uniform constant `C`
makes `g ≤ C·σ_min^{−β_1}` on codim-2.** Codex Q1 confirms, exact, with the explicit witness
`P_σ = [diag(1,σ,σ) | 0]`.

---

## 2. THE CRUX — no single-sector region→cover closes (F2 genuine); a coupled q-block estimate is forced

Codex Q2, **PROVEN, decorrelated**: "A finite cover by the stated one-small-direction sectors cannot cover
even almost all of the box near corank two. Letting `κ` vary makes the sector constant singular and
produces a non-integrable overestimate. A joint multi-collapse estimate, or an analytically equivalent
rank-stratified resolution, is required." This matches §VERDICT (1)+(2) exactly.

The secinfra F2 counterexample (`P=diag(1,2)`, `A₀=(0 1)`, `κ=3 → 9≤4`) is the pointwise seed: the sector
needs `κ ≤ σ_{r−1}`, and `σ_{r−1}` varies (→0 on the corank-2 tube), so no fixed `κ`, and no varying `κ`,
closes. **The obstruction is that the single sjSector puts only ONE direction in the collapsing v-block;
the corank-2 corner has TWO collapsing directions that must BOTH be in the (coupled) v-block.**

---

## 3. The correct construction (3iii) — rank-stratified cover + corank-q coupled majorant

**The cover.** `cell_q = {σ_{r−q} ≥ κ} ∩ {σ_{r−q+1} < κ}` for `q = 1,…,r` (corank exactly `q`: the
`q` smallest singular values collapse, the top `r−q` are `≥ κ`). `{σ_r < κ}` alone is the whole
degenerate region; the cells partition it by how many directions collapse. Finite (`q ≤ r`), and an a.e.
partition of the box.

**The per-cell majorant.** On `cell_q`, Gram-diagonalise and split the `r` eigen-columns into the top
`r−q` (weight `≥ κ²`, the bounded u-block, `d_u = m(r−q)`) and the bottom `q` (the COUPLED collapsing
v-block, weights `σ_{r−q+1}²,…,σ_r²`):
> `frobSq(A₀·P) ≥ κ²·Σ_{j∈top r−q}‖(A₀U)_{·j}‖² + Σ_{j∈bottom q} σ_j²‖(A₀U)_{·j}‖²`.

- `q=1`: this IS `frobSq_ge_twoBlock_of_sector` (the banked single sjSector), giving `g ≤ C·σ_min^{−β_1}`,
  closed by LAYER 2 (`sjProductTube_params_lintegral_lt_top`, banked). ✓ TOP STRATUM.
- `q≥2`: the `q` collapsing directions COUPLE at the corner. The corank-2 rung (`corank2-cert`, exact):
  `g̃ ≍ σ_{r−1}^{−3}·σ_min^{−(2c'−6)}` (asymmetric), and the coupled corner `u₀²U₀+u₁²U₁`
  (measure `|u₀|³|u₁|²`) gives threshold `7/2 = ½(D₂+d₂) = ½(4+3)`, NOT the independent-divisor
  undershoot `3/2`. This is the genuine new content — a `q`-block generalisation of the banked two-block
  radial (`RouteMSJTwoBlockRadial` one collapsing dimension up per `q`), coupled.

**The assembly.** `∫_box g = Σ_q ∫_{cell_q} g < ∞` for `c' < 7/2`, since each `cell_q` binds at
`½(D_q + d_q)` and `min_q ½(D_q + d_q) = ½·minAdm = 7/2` (the linchpin `minAdm = min_q[D_prod(q)+m(q−1)]`,
banked #117; indexed by COLLAPSE-COUNT `q`: `(D_q,d_q) = (1,6),(4,3),(8,0)` for `q=1,2,3` → thresholds
`½(D_q+d_q) = (7/2, 7/2, 4)`; `q=1,2` bind, `q=3` slack). Both codim-1 AND codim-2 bind at exactly `7/2` —
the deep cell is NOT a negligible correction. *(Correction 2026-07-11: `D_q` here is `codim{rank Q ≤ r−q} =
minAdm(reduced by r−q) = (1,4,8)`, indexed by collapse-count `q`; the `D_prod = (8,4,1)` of #116/#127 is the
SAME list indexed by corank-CUT — the two reverse. An earlier draft mispaired them as `(8,6),(4,3),(1,0)`,
`½(8+6)=7≠7/2`; the thresholds and binding structure are unchanged.)*

---

## 4. Measurability (3ii) — YES, no obstruction (minor cells, Cauchy–Binet)

Codex Q4, **PROVEN**. `M_ℓ(P) = max_{|I|=|J|=ℓ}|det P_{I,J}|` is a finite max of `|`polynomials`|`, hence
continuous/Borel. Cauchy–Binet: `Σ (det P_{I,J})² = e_ℓ(PPᵀ) = Σ_{i₁<…<i_ℓ} s_{i₁}²⋯s_{i_ℓ}²`, giving the
sandwich `s_1⋯s_ℓ/√N ≤ M_ℓ ≤ s_1⋯s_ℓ` (`N = C(r,ℓ)C(n,ℓ)`; verified `sector.py`: `M_2/s_1s_2 ∈
[0.33,0.98]`, `M_1/s_1 ∈ [0.42,0.99]`). On the bounded box (`s_1 ≤ R`), minor-bands and `s_ℓ`-bands
sandwich (`{s_ℓ≥κ} ⊆ {M_ℓ ≥ κ^ℓ/√N}`, `{M_ℓ≥κ'} ⊆ {s_ℓ ≥ κ'/R^{ℓ−1}}`). So:
> `cell_q = {M_{r−q} ≥ κ'} ∩ {M_{r−q+1} < κ''}` (`ℓ = r−q`) — polynomial, Borel, singular-value-band
> equivalent; exact rank cells `{rank=ℓ} = {M_ℓ>0}∩{M_{ℓ+1}=0}` are semialgebraic.

**No eigenvalue-sorting / continuity infra needed** (avoids the `IsHermitian.eigenvalues₀` measurability
gap). This reuses the banked cover-assembly's `Continuous.matrix_det` keys (`RouteMSJDominantCover`). But —
Codex, verbatim — "Measurable minor cells do NOT rescue the single-sector proof": measurability is clean;
the obstruction is ANALYTIC (the `q≥2` cells need the coupled estimate).

---

## 5. The corank-q coupled majorant — the genuine new brick (two caveats)

The `q≥2` coupled front-first majorant is the load-bearing new content (`corank2-cert §1`, exact iterated
Beta). Codex Q3 confirms `7/2` (coupled) vs `3/2` (independent), and adds **two caveats I adopt**:

- **Units-bounded-below is a sub-hypothesis.** The `7/2` needs `U_0, U_1 > 0` (the resolved cores bounded
  below on the generic-`A₂` chart — the vslice §8 "named brick" / shared-support closure). Where `U_i`
  vanishes, that degeneration is assigned to a DEEPER rank cell (`cell_{q+1}`) — the recursion. So the
  cover is genuinely rank-stratified with a per-cell units-bounded-below hypothesis discharged by
  descending to the next cell.
- **The `7/2` presupposes the PRODUCT pushforward measure.** The corank-2 tube codim `D_2 = 4`
  (`= D_prod`, #116/#127), NOT the free-matrix `(3−1)(4−1) = 6`. On free Lebesgue `dP` the corner would be
  `6+3 → 9/2`; the `7/2` is correct because `P = A₁·A₂` is a product/pushforward. This is exactly my #127
  result (`D = minAdm(reduced)`, strictly below the free determinantal codim) — the tube side is banked.

The corank-2 tube itself is NOT reachable by the symmetric `∧²`-compound `σ_min(∧²P)=s₂s₃` route
(`corank2-cert §4`: pointwise forces `b ≥ c'−3/2 > 3/2`, integrability forces `b < 1`, no overlap — the
asymmetry `s₂^{−3}` vs `s₃^{−(2c'−6)}` is fatal). Two routes for the tube, neither fully banked: (J) a
joint-pushforward-density module (`dμ ≍ s₂²ℓ(s₂)`), or (S) the native (S,J) corner (vslice §5), whose Lean
endpoint is the (□) sorry itself. **corank2-cert recommends route S** (the corner monomial
`u₀²U₀+u₁²U₁ → monomialIntegrand_integrable_of_lt`, reusing the banked charge bookkeeping).

---

## 6. What the fill (genm-sj5-schur) should build

- **Keep** the single-`sjSector` conditional (`frobSq_ge_twoBlock_of_sector` + LAYER 2) — it closes
  `cell_1` (the top stratum). Its region→sector map: `cell_1 = {M_{r−1} ≥ κ'}` (the `(r−1)`-minor sector),
  on which the unique collapse gives `sjSector κ` (F2 dodged by using the `(r−1)`-minor, which controls
  `σ_{r−1}`, NOT the dominant/smallest minor).
- **Build** the corank-`q` coupled majorant (`q≥2`) — the `q`-collapse generalisation of the banked
  two-block radial (`RouteMSJTwoBlockRadial` + one radial layer per extra collapsing direction), with the
  coupled corner (route S / vslice §5), the units-bounded-below sub-hypothesis (recurse to `cell_{q+1}`),
  and the product-tube codim `D_prod` (#127, banked).
- **Cover + sum:** `cell_q = {M_{r−q}≥κ'}∩{M_{r−q+1}<κ''}` (Borel, §4), `∫_box = Σ_q ∫_{cell_q}`, finite
  for `c'<7/2` by the linchpin `min_q ½(D_q+d_q) = 7/2` (#117).

**Do NOT:** try to cover the box with the single two-block `sjSector` at any fixed or varying `κ` (fails,
§2); use the `∧²`-compound `σ_min` tube for `q≥2` (asymmetry-fatal, `corank2-cert §4`); assume free
Lebesgue codim `6` for the corank-2 tube (it's the product `4`, #127).

---

## 7. Close

- **Firmest.** The single two-block `sjSector` does NOT cover the box: any fixed-`κ` cover misses the
  positive-measure corank-2 tube `{0<σ_{r−1}<κ_*}`, and varying `κ` destroys the estimate
  (`σ_{r−1}^{−6}` vs true `σ_{r−1}^{−3}`, threshold collapses to `c'<2`). F2 is a GENUINE obstruction to
  the single-sector proof, surfaced loudly with the witness `P_σ=[diag(1,σ,σ)|0]`. Confirmed by my exact
  algebra (codim-2 exponent `2c'−3`; ratio blow-up `→10⁴`) + vsastruct + decorrelated Codex (I converged
  first, Codex confirmed term-for-term).
- **NOT a hard wall.** The rank-stratified cover `{cell_q}` (Borel via minor cells, §4) + a corank-`q`
  coupled majorant (7/2 via the coupled corner + the product-tube codim `D_prod`, #127) closes `∫_box g`
  for `c'<7/2 = ½·minAdm`. The single sjSector is the `q=1` rung; the `q≥2` rungs are the genuine new
  content.
- **Most likely to break / watch.** The corank-`q` coupled majorant + its tube (route S = the (S,J) corner,
  or route J = joint-density) is the one un-banked analytic brick — the same endpoint the whole (S,J)
  descent needs (`sjJointResolution`). Its two sub-hypotheses: units-bounded-below (recurse to `cell_{q+1}`)
  and the product-tube codim (`D_prod`, banked #127). The `∧²`-compound shortcut is a dead route (asymmetry).
- **Next.** Build the corank-2 coupled corner monomial `u₀²U₀+u₁²U₁` (measure `|u₀|³|u₁|²`) →
  `monomialIntegrand_integrable_of_lt` (route S), reusing `Mval_decompose`/`sjChargeBudget_le`; this settles
  `cell_2` (equally binding at 7/2) and is the same endpoint the descent needs. `q=3` (`d_3=0, D_3=8`,
  threshold 4) is slack, deferred.
