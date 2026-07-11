# corank-q coupled majorant (route S) — the buildable recipe + the AIRTIGHT units→transverse-charge soundness

**Seat:** pen-and-paper (witness + obstruction — the RLCT-collapse hunt). **Date:** 2026-07-11. **NO Lean.**
**Charge (team-lead):** design the corank-q coupled majorant (`q≥2`), the genuine remaining new brick
(route S, the (S,J) corner) genm-sj5-schur builds from — (1) the corank-q coupled corner monomial + its
threshold; (2) ★ the airtight units-bounded-below → transverse-charge soundness (no RLCT-collapse to the
min); (3) the product-tube codim per cell + linchpin.

**Exact algebra (mine):** `/tmp/prodD/corankq.py` (k-block corner threshold; additive-vs-multiplicative
7/2-vs-3/2; weighted-AM-GM min-cut weights). **Consumed (banked):** `corner334`
(`sjCorner334_sector_slice_lt_top`, `sjLoss_indicator_two_block`, the SHARP boundary
`cornerSlice334_eq_top_of_unit{0,1}_zero`), `onePeel334` (the JOINT integral, codim rescue via weighted
AM-GM), `RouteMSJSlice334` (`sjSlice_corner_two_block_lt_top`, `sjSlice334_symmetric_undershoot`),
`RouteMSJTwoBlockRadial`, `monomialIntegrand_integrable_of_lt`, `Mval_decompose`/`sjChargeBudget_le`, the
product-tube codim `D_prod` (#116/#127), the front-peel linchpin (#117). **Decorrelated:** own
`local-codex-consult` (xhigh, conclusion withheld — told it to HUNT the collapse):
`codex/corankq-{prompt,answer}.md`. Codex EXHIBITED the collapse and pinned the exact condition that
avoids it — adopted, and it sharpens the soundness beyond "the units are generically positive."

---

## VERDICT (headline): the corank-q corner ADDS on a uniformly-coercive cell (→ ½(D_q+d_q)); a vanishing unit WITHOUT transverse charge GENUINELY COLLAPSES the RLCT; the DLN recursion avoids the collapse ONLY via the PROVED product-rank tube charge D_q (#127). The soundness is real, not free.

The min→sum coupling gives `½(D_q+d_q)` per cell **conditional on** the units being bounded below. The
★ soundness is NOT "the units are generically positive so it's fine" — a vanishing unit is a genuine
RLCT-collapse (Codex-exhibited), rescued **exactly** by the proved transverse product-rank charge `D_q`
(my #127). This makes #127 load-bearing for the soundness, and the recursion `q→q+1` well-founded (`q≤r`)
**and sound iff each `D_q` is proved**.

Index convention (corrected): by **collapse-count `q`** (number of collapsing singular directions),
`(D_q,d_q) = (1,6),(4,3),(8,0)` for `q=1,2,3`, thresholds `½(D_q+d_q) = (7/2,7/2,4)`, `min = 7/2 = ½·minAdm`
(`q=1,2` bind). `D_q = codim{rank Q ≤ r−q} = minAdm(reduced by r−q)`; `d_q = m(r−q)`. (The `D_prod=(8,4,1)`
of #116/#127 is the SAME list by corank-CUT — the two reverse; do not mispair `D` with `d`.)

---

## 1. The corank-q coupled corner monomial (PROVEN threshold ½·Σ charges)

**Cell.** `cell_q = {σ_{r−q}(Q) ≥ κ, σ_{r−q+1}(Q) < κ}` — the tail product `Q` has exactly `q` collapsing
singular directions, `r−q` stable (`≥κ`). After Gram-diagonalising and rotating the front factor, the loss
is the **block-additive** sum (`RouteMSJCorner334.sjLoss_indicator_two_block`, generalised to `q+1` blocks):
> `frobSq(A₀·Q) ≥ κ²·(stable u-block, `d_u=m(r−q)`) + Σ_{i=0}^{q−1} u_i²·U_i` (`q` COUPLED collapsing blocks,
> each `U_i>0` a unit; `u_i` the per-block radial, Jacobian power `a_i = block_dim_i − 1`).

**Threshold (iterated corner blow-up, PROVEN — mine + Codex Q1 exact).** On the chart where `u_0` is
maximal, `u_i = u_0 τ_i` (`i≥1`): `∏du_i = u_0^{q−1}du_0 dτ`, `∏u_i^{a_i} = u_0^{Σa_i}∏τ_i^{a_i}`,
`Σu_i²U_i = u_0²(U_0+Στ_i²U_i)`. So the exceptional exponent is `u_0^{Σa_i+(q−1)−2c'}`, and
> `∫_0^ε u_0^{Σa_i+q−1−2c'} du_0 < ∞ ⟺ c' < ½·Σ_i(a_i+1) = ½·Σ_i block_dim_i`.

The charges **ADD** (`Σ(a_i+1)`), NOT min. For `(3,3,3,4)` corank-2: `a=(3,2)`, `Σ(a_i+1)=4+3=7`,
threshold `7/2 = D_2+d_2` — matches. (Exact Beta endpoint, Codex:
`I ≍ 2^{−q}B((a_0+1)/2,…,(a_{q−1}+1)/2)·∫s^{½Σ(a_i+1)−c'−1}ds`.) The identity `Σ(a_i+1) = D_q+d_q` is a
separate charge identity (`Mval_decompose`/`sjChargeBudget_le` + #127), **not** automatic from the corner
lemma — it must be supplied (banked ℕ).

**Banked pieces:** `sjLoss_indicator_two_block` (additive block loss — the min→sum crux at the carrier
level), `RouteMSJTwoBlockRadial` (one radial layer per collapsing block; the `q`-block corner is `q−1`
iterated applications), `monomialIntegrand_integrable_of_lt` (the terminal `∫u_0^{h−2c'}<∞`),
`Mval_decompose`/`sjChargeBudget_le` (charges sum to `minAdm`).

**The min→sum discipline (NOT cosmetic).** The ADDITIVE (indicator) loss `Σu_i²U_i` → `½·Σ(a_i+1)`; the
MULTIPLICATIVE (`radialAttach`, ONE shared divisor `u_0²·everything`) → the MIN
`min_i (a_i+1)/2 = 3/2` undershoot (banked `sjSlice334_symmetric_undershoot`). **Build the indicator
(block-diagonal) form, not `radialAttach`** — this is the `RouteMSJDecorated.radialAttach` note in the
BUILT-INDEX made concrete per rung.

---

## 2. ★ THE AIRTIGHT SOUNDNESS — the collapse is REAL; the transverse charge D_q avoids it

The controller's long-standing watch-point. **Codex (told to hunt the collapse) EXHIBITED it**, and this
sharpens the soundness decisively:

### The collapse is genuine (units vanishing WITHOUT transverse charge)

On a FIXED slice with a vanishing unit, only the surviving blocks charge:
`λ_slice = ½·Σ_{i:U_i>0}(a_i+1)` — a COLLAPSE. For `a=(3,2)`: `U_0=0<U_1 → λ=3/2`; `U_1=0<U_0 → λ=2`
(banked `cornerSlice334_eq_top_of_unit{0,1}_zero` — the fixed slice genuinely DIVERGES below 7/2). Sharper
(Codex): `F = u_0²|z|² + u_1²`, `z∈ℝ^D` ⟹ `λ = 3/2 + min(2, D/2)`; **`D=1` gives `λ=2 < 7/2`**. And
`U_0=U_1=|z|²` ⟹ `λ = min(D/2, 7/2)`; `D=1` gives the crude `λ=1/2` (the `z²(x²+y²)` collapse exactly).

**⟹ "Allowing `U_i→0` without transverse charge DOES collapse the RLCT."** The naive "recurse to
`cell_{q+1}`" / "the units are generically positive so it's fine" / an a.e. deletion of `{U_i=0}` is
INSUFFICIENT — it does not control the surrounding tube, and the RLCT genuinely drops.

### Why the DLN integral avoids it — the PROVED transverse charge

The vanishing-unit locus `{U_i=0}` = `{the deep factor rank-drops}` is a positive-codim locus carrying a
**transverse product-rank charge `D_q`**. Integrating the units over the deep data (the JOINT integral,
`onePeel334`, NOT fixed-slice), with the units cast as squared norms of disjoint deep-data blocks
`U_i = ‖X_i‖²` (`X_i ⊥ X_j`), the weighted AM-GM at the **min-cut weights** `w_i = (a_i+1)/Σ(a_j+1)`
decouples:
> `(Σ u_i²U_i)^{−c'} ≤ ∏_i (u_i²‖X_i‖²)^{−w_i c'}`, then `∫u_i^{a_i−2w_ic'}du_i` (finite ⟺ `w_ic'<(a_i+1)/2`)
> × `∫‖X_i‖^{−2w_ic'}dX_i` (finite ⟺ `w_ic' < ½·dim(X_i-block) = ½·(transverse codim)`).

Both factors bind at the SAME `c' < ½·Σ(a_j+1) = ½(D_q+d_q)` — the u-charge and the deep-block codim are
balanced by the min-cut weights. The SVD pushforward supplies exactly the tube charge (Codex Q4: for a
matrix, `q` singular values scaling by `ρ` give radial exponent `q|M−N|+q(q−1)+(q−1) = D_q−1`), so
`∫ρ^{D_q+d_q−1−2c'}dρ` has threshold `½(D_q+d_q)`. **The `7/2` is recovered iff the transverse charge
`D_q ≥ 4` — exactly the proved product-rank tube codim (#127).** For `D<4` the collapse is real
(Codex's `D=1 → λ=2`); for `(3,3,3,4)`, `D_2=4` is exactly the transverse charge needed.

### Well-foundedness + the exact soundness condition

- The recursion `q→q+1` (cell partition by collapse-count) is finite (`q ≤ r`).
- It is **sound iff each transverse charge `D_q` is PROVED** (the product-rank tube exponent, #127 — the
  load-bearing input; for a matrix product, algebraic codim alone is insufficient, the stratified
  tubular/resolution statement is #127's content). An a.e. deletion of `{U_i=0}` does NOT suffice.
- No cell undershoots `7/2`: `½(D_q+d_q) = (7/2,7/2,4)`, `min=7/2` (`q=1,2` bind). The deeper stratum is
  non-WORSE but not always strictly better (`q=1,2` both bind at `7/2`) — so the seam-matching is by the
  `ρ^{D_q+d_q−1−2c'}` tube calc, NOT by the deeper threshold being strictly larger.
- Seam continuity (Codex Q3b, corrected): at `σ_{r−q}=κ>0` the coefficient is `≥κ²`, so the estimates
  overlap at the positive cutoff; "continuously matches" does NOT mean equal adjacent thresholds (they are
  `7/2,7/2,4`) — it means overlap at the cutoff + the deeper threshold no smaller.

**The no-collapse, precisely:** (i) build the ADDITIVE (indicator) loss, not `radialAttach` (else `→3/2`);
(ii) the vanishing-unit locus is NOT deleted a.e. — it is integrated JOINTLY with its PROVED transverse
product-rank charge `D_q` (#127), which is exactly `≥` the charge needed to hold `7/2`. Both are
load-bearing; dropping either collapses the RLCT.

---

## 3. The product-tube codim per cell + linchpin (banked)

`D_q = codim{rank(A₁···A_{L−1}) ≤ r−q} = minAdm(reduced by r−q)` — the product-rank tube codim, **banked**
(#127: `= cCodim(reduced)`, leading power = codim, no sub-codim multiplicity; #116 for `(3,3,3,4)`:
`D_prod=(8,4,1)` by corank-cut = `(1,4,8)` by collapse-count). The linchpin `minAdm = min_q[m·q + minAdm(reduced by q)]`
(front-peel, banked #117) gives `min_q ½(D_q+d_q) = ½·minAdm = 7/2`. The assembly
`∫_box g = Σ_q ∫_{cell_q} g < ∞` for `c' < 7/2` (Codex Q3c). The `q=3` cell (`d_3=0`, `D_3=8`, threshold 4)
is slack; `q=1,2` bind.

---

## 4. The buildable recipe (what genm-sj5-schur builds)

```
g(Q) = ∫_{A₀ box} frobSq(A₀·Q)^{−c'},   box = ⊔_q cell_q  (Borel, minor cells — sector-cert §4)
  cell_1 (top): single sjSector (frobSq_ge_twoBlock_of_sector) + LAYER 2      [banked; genm-sj5-schur #125]
  cell_q (q≥2): the corank-q COUPLED majorant (route S) —
    (i)  ADDITIVE block loss  κ²·u-block + Σ_i u_i²U_i   [sjLoss_indicator_two_block, generalised]
    (ii) iterated corner blow-up (q−1 layers)            [RouteMSJTwoBlockRadial ×(q−1)]
         → u_0^{Σa_i+q−1}·(unit), threshold ½·Σ(a_i+1)=½(D_q+d_q)   [monomialIntegrand_integrable_of_lt]
    (iii) the units U_i integrated JOINTLY over the deep data (onePeel334), the {U_i=0} rank-drop
          RESCUED by the transverse product-rank charge D_q   [weighted AM-GM + #127 tube codim]
  Σ_q ∫_{cell_q} < ∞ for c' < min_q ½(D_q+d_q) = 7/2 = ½·minAdm   [#117 linchpin]
```

The corank-2 rung is BANKED end-to-end: `corner334` (fixed-slice, coercive units) + `onePeel334` (joint,
codim rescue). The `q≥2` GENERAL rung is the `(q−1)`-fold iteration of the two-block radial + the joint
codim rescue — the genuine remaining new content, but banked-adjacent (`RouteMSJTwoBlockRadial`,
`onePeel334`'s weighted-AM-GM template, #127's `D_q`).

**Do NOT:** (i) build `radialAttach` (multiplicative → `3/2` collapse); (ii) delete `{U_i=0}` a.e. (the
collapse is real — must integrate with the transverse charge `D_q`); (iii) use the `∧²`-compound `σ_min`
tube (asymmetry-fatal, `corank2-cert §4`); (iv) mispair `D` (collapse-count) with `d` — `(D_q,d_q)=(1,6),(4,3),(8,0)`.

---

## 5. Codex (decorrelated, told to HUNT the collapse) — adopted

`codex/corankq-answer.md`, verbatim adjudication: "**ADD on each uniformly coercive cell; genuine COLLAPSE
on a vanishing-unit slice; the full DLN avoids it only through the proved transverse `D_{q+1}` charge.**"
Q1: the `q`-corner is additive, `λ = ½Σ(a_i+1)` (exact Beta). Q2: the collapse is REAL (`U_0=U_1=|z|²`,
`D=1 → 1/2`; `u_0²|z|²+u_1²`, `D=1 → 2 < 7/2`); recovered only when the vanishing locus supplies `D≥4`. Q3:
coercive cell → `½(D_q+d_q)`; seam overlaps at the cutoff (thresholds not equal: `7/2,7/2,4`). Q4: no
concrete `q` fails (`D_q+d_q=(7,7,8)`), but `Σ(a_i+1)=D_q+d_q` is a separate charge identity and `D_q` (the
product pushforward exponent) must be PROVED (stratified resolution, #127) — algebraic codim alone
insufficient. **Two adopted corrections:** (a) the `(D_q,d_q)` pairing `(1,6),(4,3),(8,0)` (I fixed the
sector-cert's mispaired parenthetical); (b) "seam continuity" ≠ equal adjacent thresholds.

---

## 6. Close

- **Firmest.** The corank-q coupled corner ADDS the charges → `½·Σ(a_i+1) = ½(D_q+d_q)` on a
  uniformly-coercive cell (exact, mine + Codex Beta); the ADDITIVE (indicator) form is load-bearing
  (`radialAttach` → `3/2` collapse, banked). The corank-2 rung is banked (`corner334`/`onePeel334`); the
  general rung is `(q−1)`-fold iterated two-block radial + joint codim rescue.
- **★ The soundness (airtight, sharper than the naive version).** A vanishing unit is a GENUINE
  RLCT-collapse (Codex-exhibited: `D=1 → λ=1/2` or `2 < 7/2`); it is avoided ONLY by integrating the
  `{U_i=0}` locus JOINTLY with its PROVED transverse product-rank charge `D_q` (#127) — NOT by a.e.
  deletion, NOT by relabeling. So #127 is load-bearing for the (□) soundness; the recursion `q→q+1` is
  well-founded (`q≤r`) and sound iff each `D_q` is proved. The min→sum (add-not-min) and the transverse
  charge are BOTH required; dropping either collapses the RLCT.
- **Most likely to break / watch.** The build must (i) use the indicator/block-additive loss (not
  `radialAttach`), (ii) route the `{U_i=0}` locus through the joint integral with `D_q` (the `onePeel334`
  weighted-AM-GM template), NOT delete it a.e. — the RLCT-collapse hides exactly in an a.e.-deletion
  shortcut. GATE the route-S close on confirming both. The `Σ(a_i+1)=D_q+d_q` charge identity + the
  product-pushforward `D_q` are the ℕ/#127 inputs (banked).
- **Next.** Build the general `q`-block corner as `(q−1)` iterations of `RouteMSJTwoBlockRadial` on the
  indicator loss (threshold `½Σ(a_i+1)`), and the joint codim rescue as the `onePeel334` weighted-AM-GM
  with the `D_q` tube (#127). The corank-2 rung (`corner334`+`onePeel334`) is the worked template; `q=3`
  (slack at 4) is a coarse-bound coda.
