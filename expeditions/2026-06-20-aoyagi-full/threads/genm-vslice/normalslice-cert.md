# `normalSlice_transfer` witness — the width-general product normal-slice iso (CoV + additive charge)

**Seat:** pen-and-paper (witness). **Charge:** #109 (front-peel W1 crux). **Date:** 2026-07-10. **NO Lean.**
**Scope (from the spec):** FINITENESS is BANKED (`radial_morse_residual_power_le` `RadialResidualPower:157`,
`lintegral_eq_polar` `RouteMSJSphereBlowup:82`); the OPEN part is ONLY the CoV / singularity-type **IDENTITY**
`{rank P ≤ q} ≅ shifted Σ⁰(M₁−q,…,M_L−q)` with additive charge composition. This cert witnesses that identity
for general `M` / corank `q`, Lean-friendly. **Decorrelated:** `local-codex-consult` (xhigh), my construction
withheld — it produced the explicit threaded normal form and corrected a codim error of mine (§5).
**Exact-algebra:** `normalslice_verify.py`, `normalslice_threaded.py` (+ `normalslice_schur.py`).

> **⚠ CORRECTION (2026-07-10, `genm-covdesign` cert + decorrelated Codex, exact-confirmed).** §3–4's claim
> that the loss splits as `‖R‖² + ‖Z‖²` under a **unit** Jacobian is **WRONG for the loss/RLCT layer**. The
> exact split is `frobSq(A₀·P) = ‖R̃·α‖² + ‖R̃·B + S̃·Z‖²` (α = the pivot block); cleaning to `‖R‖²` needs
> `R = R̃·α`, Jacobian `|det α|^{−m₀}` — a **determinant INVERSE**. The unit-Jacobian claim is correct ONLY
> for the **RANK identity** `rank P = q + rank Z` (§2 — what the landed `blockShear_step` /
> `rank_eq_q_add_of_normalForm` proved, unaffected). The loss-split carries a real **codim-1 PIVOT CHARGE**
> (threshold ½) that the front-peel `frontCharge q` omits; the per-chart finiteness needs it spent via
> disjoint dyadic `|det α|`-shells (or Anderson). See `threads/genm-covdesign/cert.md`. This does NOT change
> the RANK / additive-charge accounting result (§2, §4's `min_q = ½·minAdm`) — only the **mechanism** of the
> per-chart loss finiteness, which was never formalised (it lived in the open `frontChartIntegral_lt_top`).

---

## VERDICT

The identity **HOLDS**, with an **explicit unit-Jacobian change of variables** (a threaded chain of
unit-triangular shears), verified exactly:

> `{rank(A₁···A_{L-1}) ≤ q}` (`P` = tail product, widths `(M₁,…,M_L)`) `⟺` `{Y₁·Y₂···Y_{L-1} = 0}`,
> the deepest locus `Σ⁰` of the **reduced chain** `(M₁−q, M₂−q, …, M_L−q)` — ALL tail widths reduced by `q`.
> The CoV Jacobian is `±1` (no determinant inverse survives — the compass holds), and the front-peel Morse
> block `‖R‖²` (dim `M₀·q`) is a **disjoint** variable block from the reduced normal equations `‖Z‖²`
> (`Z = Y₁···Y_{L-1}`), so the RLCTs **ADD**: `½·M₀q + ½·minAdm(reduced) = ½·frontCharge(q)`, `min_q = ½·minAdm(M)`.

No new obstruction; the one honest caveat is that the CoV is **local** (a finite pivot chart cover, §6). This
is the "sum-not-min" of the `(3,3,3,4)` vslice, now at general width/corank, framing-independent.

---

## 1. The statement to witness (Lean-friendly shape)

After the banked front-split (`routeMLayerBoxIntegral_front_split`), the object is
`∫_{A'∈box(tail)} ∫_{A₀∈box} frobSq(A₀·P)^{−c'}`, `P = prod(tailChain M) A' = A₁···A_{L-1}` (`M₁×M_L`).
The front-peel (`FrontPeelStep`, r1substratum §C, banked-brick-fed) charges the A₀-integral by `M₀·q/2` on
the stratum `{rank P = q}` and leaves a residual over `{rank P ≤ q}` at exponent `c'−M₀q/2`. **`normalSlice_transfer`**
is the recursion step:

    (residual over {rank P ≤ q} at exponent s)   =CoV=   (box integral of the reduced chain (M₁−q,…,M_L−q) at exponent s)

so the whole recursion is `RouteMBoxThresholdFinite` of a chain with **one fewer layer** (arity `L → L−1`),
closing by the banked strong-induction wrapper. The **finiteness** of the reduced-chain box is the induction
hypothesis (banked endpoint machinery); the **CoV/identity** is what this cert supplies.

---

## 2. THE EXPLICIT CoV — the threaded normal form (verified exact, `normalslice_threaded.py`)

Block each factor `X_i` (`= A_i`, `m_i × m_{i+1}`) by the `q + (m_i−q)` row / `q + (m_{i+1}−q)` column split:
`X_i = [[A_i, B_i],[C_i, D_i]]` (`A_i` is `q×q`). Thread right-to-left with `K_L = 0`:

    α_i = A_i + B_i K_{i+1}        (q×q)
    γ_i = C_i + D_i K_{i+1}        ((m_i−q)×q)
    K_i = γ_i · α_i⁻¹              ((m_i−q)×q)          -- the shear coefficient
    Y_i = D_i − γ_i · α_i⁻¹ · B_i  ((m_i−q)×(m_{i+1}−q)) -- the reduced factor (Schur complement)

With the unit-triangular shear `M_i = [[I, 0],[−K_i, I]]` (`det = 1`), the key per-factor identity is

    M_i · X_i · M_{i+1}⁻¹  =  [[α_i, B_i],[0, Y_i]]        (block upper-triangular)   [VERIFIED, 0 fails]

Telescoping (`M_{i+1}⁻¹` cancels against the next factor's `M_{i+1}`):

    M_1 · P  =  [[ α_1···α_{L-1},  * ],[ 0,  Y_1···Y_{L-1} ]].

On the chart where every `α_i` is invertible, `α_1···α_{L-1}` is an invertible `q×q` block and `M_1` is unit, so

    **rank P  =  q + rank(Y_1 Y_2 ··· Y_{L-1})**,   hence   **{rank P ≤ q} ⟺ {Y_1···Y_{L-1} = 0}.**

`Y_1···Y_{L-1}` is the product of the **reduced chain** `(M₁−q,…,M_L−q)` (widths `Y_i : (m_i−q)×(m_{i+1}−q)`),
so `{rank P ≤ q} = Σ⁰(M₁−q,…,M_L−q)` in the CoV coordinates. **Verified `0/…` fails** on exact-rational
instances for tails `(2,2,2),(3,3,3),(3,3,4),(4,4,4)@q2,(3,3,3)@q2` and a genuine `L=4` chain `(2,3,4,3)@q1`
(reduced `(1,2,3,2)`), with the reduced widths and `rank P = q + rank(reduced product)` matching exactly.

*(The naive "Schur(P) = Y₁Y₂ with independent Schur complements" is FALSE — the middle width must thread:
the `K_{i+1}` correction `α_i = A_i + B_i K_{i+1}` is load-bearing. This is Codex's correction, adopted.)*

---

## 3. THE COMPASS — unit Jacobian, no determinant inverse

The CoV is a composition of:
- `X_i ↦ X_i·M_{i+1}⁻¹` (right unit-triangular shear), Jacobian `det(M_{i+1}⁻¹)^{m_i} = 1`;
- the Schur shear `D_i ↦ Y_i = D_i − γ_i α_i⁻¹ B_i` (`α_i,B_i,γ_i` held), Jacobian `det = 1`;
- (chart selection: row/column permutations, Jacobian `±1`).

**Total Jacobian `±1`** (verified `det M_i = 1` on every instance). The pivot inverses `α_i⁻¹` appear **only
as analytic unit coefficients inside shears** — never as a Jacobian determinant factor. A genuine
determinant-inverse would appear only if one wrongly normalised a pivot to `I` (scaling by `α_i⁻¹`) instead of
using unit-triangular elimination — exactly the det-inverse compass the charter names, and the native
re-expression (threaded unit shears) exists here as everywhere.

---

## 4. THE ADDITIVE CHARGE (the "sum-not-min", general width)

Write the front matrix in the matched coordinates `X₀·M_1⁻¹ = [R | S]`, `R : M₀×q`. On the normal slice the
squared loss is, up to analytic units and smooth (free) variables,

    ‖A₀·P‖²  ≃  ‖R‖²  +  ‖Z‖²,      Z = Y_1···Y_{L-1}   (the reduced product).

`R` (dim `M₀·q`, the condition that `A₀` kills the rank-`q` image of `P`) and `Z` (the reduced normal
equations) are **disjoint variable blocks**, so their RLCTs ADD (Watanabe product rule for disjoint
sum-of-squares):

    rlct  =  ½·M₀q  +  ½·minAdm(M₁−q,…,M_L−q)  =  ½·frontCharge(q),      min_q  =  ½·minAdm(M).

It is a **SUM, not a min**, precisely because both normal blocks vanish **simultaneously on the same local
stratum** (the corner) — a min would be an alternative-component (product) model. This is the general form of
the `(3,3,3,4)` corner blow-up (cert.md §5): there `M₀q` and `minAdm(reduced)` were the `[4,3,0]` charges; here
it is one A₀-Morse block plus the recursive reduced budget.

**Accounting verified (`normalslice_verify.py` (A)):** `minAdm(M) = min_q [M₀q + minAdm(M₁−q,…,M_L−q)]`,
`0` violations (widths ≤ 5, `L≤4`); `(3,3,3,4)`: frontCharge over `q=0..3` = `[8,7,7,9]`, min `7`. (This
half is the banked `minAdm_eq_frontPeel` `RouteMFrontPeelCharge:158`; re-confirmed here.)

---

## 5. CODIM RECONCILIATION (a correction I adopted from the decorrelated pass)

A first pass (via `prodrank_codim.py`) reported `codim{rank(X₁X₂)≤1} = 4` for tail `(3,3,3)`, seemingly `≠
minAdm(2,2,2)=3`, suggesting the iso was RLCT-only (not codim). **That was wrong**: the script forced the
sample onto the **special component `{rank X₁ ≤ q}`** (codim `(M₁−q)(M₂−q)=4`), not the generic stratum.

By the normal form (§2), `{rank P ≤ q} ≅ {reduced product = 0} × (free pivot/off-diagonal directions)` under a
unit-Jacobian CoV, so **`codim{rank P ≤ q} = codim Σ⁰(reduced) = minAdm(M₁−q,…,M_L−q) = 3`** for `(3,3,3)@q=1`
— the free directions add zero codim. The dense stratum is `rank Y₁ = rank Y₂ = 1`, `im Y₂ ⊆ ker Y₁`
(dim `5` in the `8`-dim reduced space, codim `3`). The `{rank X₁≤q}` component (codim `4`) is a *higher-codim*
sub-locus, not the generic one. So codim and RLCT are **both** `= minAdm(reduced)` — consistent, no RLCT-vs-codim
gap. (The `(3,3,4)@q=1` reduced chain is `(2,2,3)`, `minAdm=4` — the last width `4→3` also reduces, confirming
ALL tail widths drop by `q`.)

---

## 6. SCOPE, GAPS, LEAN-FRIENDLINESS

- **Local chart / finite cover.** The CoV needs every `α_i` invertible (`≈92%` of random instances hit the
  chart; the rest are lower-strata handled by other pivot selections). The honest Lean statement is a **finite
  pivot-chart cover**: `{rank P ≥ q}` (or the `q`-stratum) `= ⋃_{pivot selections} chart`, reusing the banked
  `pivotLocus_eq_iUnion` (`RouteMSJPivotChart:307`) + `pivotChartCover_matBox_le_sum` — the SAME cover the
  A₀-peel already uses. Each chart carries the threaded CoV above; subadditivity over the finite cover assembles
  it. **This is plumbing (banked-shaped), not new analysis.**
- **What the sorry sits on (per the spec's scope split).** State `normalSlice_transfer` so the (banked)
  finiteness leg is CONSUMED — the reduced-chain box integral's finiteness is the induction hypothesis
  (`RouteMBoxThresholdFinite` at arity `L−1`), and the corner/endpoint uses `radial_morse_residual_power_le`
  (residual at the accumulated block dim) + `lintegral_eq_polar`. The **sorry is the CoV/identity alone**:
  the measure-preserving threaded shear `(X₁,…,X_{L-1}) ↦ (α_i, B_i, γ_i, Y_i)` and the loss transfer
  `frobSq(A₀P) ≃ ‖R‖² + ‖Z‖²`. This cert is that sorry's proof-content.
- **Lean bricks to reuse for the CoV:** the shear MP `measurePreserving_shearSub` (`RouteMSJPivotChart:337`)
  generalised to the block shear `M_i`; `⅟`→`⁻¹` via `invOf_eq_nonsing_inv` for integrand use; ASCII binders
  (`al_i`, `Yt`); dependent-width reassociation via `mul_three_reassoc` (lean/CLAUDE.md). The reduced product
  `Y₁···Y_{L-1}` is `prod` of the reduced chain — the SAME `prod`/`prodAux` API, at reduced widths.
- **Named residual (bounded, not a wall).** The block shear `M_i X_i M_{i+1}⁻¹ = [[α_i,B_i],[0,Y_i]]` at
  **opaque widths** (the `q + (m_i−q)` block algebra + the `α_i = A_i + B_i K_{i+1}` threading) is the one new
  brick; it is bounded block-matrix algebra (the `L=2` single-matrix Schur case is banked
  `frobSq_schur_block_split`), verified exact here for `L≤4`. The loss transfer `‖A₀P‖² ≃ ‖R‖²+‖Z‖²` on the
  slice needs the disjointness of `R` and `Z` — structural (R from `X₀`, Z from the tail), shown by the block
  form.

---

## 7. Codex (decorrelated, xhigh; my construction withheld) — CONCUR + supplied the threaded form

`normalslice-codex-{prompt,answer}.md`. Codex independently produced the **exact threaded normal form** of §2
(the `K_{i+1}` recursion, `M_i X_i M_{i+1}⁻¹` block-upper-tri, `rank P = q + rank(Y₁···Y_{L-1})`), the **unit
Jacobian** argument of §3 (`det = ±1`, `α_i⁻¹` as unit coefficients only), the **additive** `‖R‖²+‖Z‖²`
disjoint-block RLCT of §4 ("a SUM because both normal blocks vanish simultaneously… a minimum would correspond
to a product/alternative-component model"), and — the correction I adopted — the **codim `= 3` not `4`** for
`(3,3,3)@q=1` (§5: "the `4` is the determinantal codim of rank `≤1` inside a free product matrix, or of the
special component where one factor already has rank `≤1`"). Two independent derivations agree term-for-term;
the one correction (naive independent-Schur is insufficient; threading needed) strengthened the result.

---

## 8. Closing

- **Firmest.** The width-general product normal-slice iso `{rank(A₁···A_{L-1}) ≤ q} ⟺ {Y₁···Y_{L-1} = 0} =
  Σ⁰(M₁−q,…,M_L−q)` holds via an explicit **unit-Jacobian threaded shear** (verified exact, `L≤4` incl. a
  genuine `L=4` chain; `det M_i = 1`; `rank P = q + rank(reduced product)`, 0 fails). Charges compose
  ADDITIVELY (`‖R‖²+‖Z‖²` disjoint, RLCTs add) to `½·frontCharge(q)`, `min_q = ½minAdm(M)`. Codim `= RLCT`
  budget `= minAdm(reduced)` (the `4` was a special sub-component). Compass held. Codex decorrelated-concurs.
- **Most likely to break / watch.** The opaque-width block-shear identity `M_i X_i M_{i+1}⁻¹ = [[α_i,B_i],[0,Y_i]]`
  in Lean (bounded block algebra, `L=2` banked) and the finite pivot-chart cover assembly (banked-shaped). No
  research wall — the analysis is standard rank-normal-form linear algebra (cite natively, NOT the L&R quiver
  `addlongest`, per `addlongscope` independence).
- **Next.** Hand the threaded CoV to the formaliser as `normalSlice_transfer`'s proof-content: (i) the block
  shear identity (state at general widths, prove `L=2` from banked, lift), (ii) the MP of the threaded shear,
  (iii) the `‖R‖²+‖Z‖²` disjoint split feeding the banked additive endpoint. `normalslice_threaded.py` is the
  exact target (the `α_i,K_i,Y_i` recursion + `rank P = q + rank(Y₁···Y_{L-1})`).
