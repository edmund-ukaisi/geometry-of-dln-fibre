# genm-vsastruct — the (a) chart-reduction STRUCTURE + measurability (task, gates secinfra 3iii)

**Seat:** pen-and-paper (obstruction-adversarial + native-re-expression hunt). **Date:** 2026-07-11.
**NO Lean.** **Charge:** nail the structure of step (a) of the (3,3,3,4) vslice — the front-first coupled
majorant `∫_{x,Γ box} sjGoodChartLoss^{−c'} ≤ C·σ_r(Ã₁·A₂)^{−α'}` — and adjudicate whether it is
BOUNDED-BUILDABLE or a WALL, plus the two secinfra red flags (F1 measurability, F2 the sector dichotomy).
**Exact algebra:** `/tmp/vsastruct_scaling.py` (stratum exponents, MC-guided), `/tmp/vsastruct_minor_sector.py`
(Cauchy–Binet sector bracket). **Decorrelated:** `codex/struct-{prompt,answer}.md` (gpt-5.6, xhigh; my
conclusion withheld — it CONCURRED term-for-term + refined Q4). Cross-check: the prior `genm-vsdeep`
compass consult (independent) reached the same rank-stratification necessity.

---

## ONE-LINE VERDICT

**The (a) dichotomy is GENUINE and the complement is LOAD-BEARING (binding at exactly 7/2, equal to the
top stratum). Step (a) → `σ_min^{−α'}` → LAYER 2 closes ONLY the codim-1 (top) stratum; the binding
codim-2 stratum is a *genuinely separate* integrability obligation that LAYER 2 (`σ_min^{−a}`, `a<1`)
CANNOT absorb, and NO single global majorant of the `σ_min^{−a}` / `det(G)^{−a/2}` (`a<1`) form exists.
It is NOT a hard wall — the math is sound (7/2 proven two ways) — but it is BUILDABLE-AS-A-RANK-STRATUM-
RECURSION (multiple new modules), not "labour on 3iii + a one-shot complement descent". The complement is
NOT handled by any already-CLOSED banked piece: the (S,J) descent's analytic endpoint `sjJointResolution`
is itself an unproven named sorry, and the cover-assembly is only a partition tool. Measurability (F1) is
NOT a wall — the cheapest route is the 2×2-minor sector `{max|det 2×2 minor| ≥ κ'}` (polynomial, trivially
measurable, Cauchy–Binet-equivalent to `{σ₂≥κ}`), no eigenvalue continuity needed.**

---

## 1. F2 — the dichotomy is REAL and the complement is BINDING (not negligible)

### The step-(a) bound is SECTORIAL, not global
Reduce (a) to the front-first `g(P) := ∫_{A₀∈[−1,1]^{3×3}} frobSq(A₀·P)^{−c'} dA₀`, `P = Ã₁·A₂` the
`3×4` tail, singular values `s₁≥s₂≥s₃`, `m₀ = r = 3`. After Gram-diagonalising `PPᵀ = Q diag(s²) Qᵀ` and
rotating `A₀↦A₀Q`, `frobSq(A₀P) = Σⱼ sⱼ²‖(A₀Q)_{·j}‖²`. On the codim-`k` locus (`k` smallest `≍ σ`, the
rest `≍1`) the stable block has dim `d_k = m₀(r−k) = 3(3−k)`, and radial scaling gives EXACTLY

> `g(P) ≍ σ^{−β_k}`, `β_k = max(0, 2c'−d_k) = max(0, 2c'−3(3−k))`   (log at `2c'=d_k`).

| stratum | collapse `k` | `d_k = 3(3−k)` | `β_k` (exact) | at `c'=3` (MC guide) |
|---|---|---|---|---|
| codim-1 (`s₃→0, s₂≥κ`) | 1 | 6 | `max(0,2c'−6)` = α' | 0 / log (MC ≈ 0.4–0.6) |
| **codim-2** (`s₂,s₃→0, s₁≥κ`) | 2 | 3 | **`2c'−3` = α'+3** | **3.0** (MC 2.7–3.2) |
| codim-3 (`s₁,s₂,s₃→0`) | 3 | 0 | `2c'` | 6.0 (MC 5.99) |

The proposed majorant is `σ_min^{−α'} = σ^{−(2c'−6)}`. On codim-2 the TRUE `g ≍ σ^{−(2c'−3)}` exceeds it by
`σ^{−3}` → **no uniform constant makes `g ≤ C·σ_min^{−α'}` hold there.** The bound is valid ONLY on the
sector `{s₂ ≥ κ}` (with a `κ`-dependent constant). [FACT — exact radial scaling; MC-guided; Codex-concurred.]

### The complement is BINDING at 7/2 (as binding as the top stratum)
Tube measure of a codim-`D_k` product-rank tube is `σ^{D_k−1}dσ`, so `∫_{tube-k} g` converges iff
`β_k < D_k`, i.e. `2c' < D_k + d_k`. With the banked product-rank codim `D_prod = (8,4,1)` at
`q=(1,2,3)` (task #116; `d_k` at `k=(3,2,1)` reindexes to the same list):

> `½(D_k + d_k) = (7/2, 7/2, 4)` for `k=(1,2,3)`.

**Both `k=1` (codim-1) AND `k=2` (codim-2) bind at exactly `c' = 7/2`**; only `k=3` is slack (binds at 4).
The linchpin `minAdm = min_q[D_prod(q)+m₀(q−1)] = min(8,7,7) = 7` is the min-over-strata, and it is TIGHT at
BOTH codim-1 and codim-2. **⟹ the deep stratum is NOT a negligible boundary correction — it carries a
contribution tight at the SAME threshold.** [FACT — exact; Codex-concurred: "k=1 is not the sole
obstruction; k=2 is equally binding".]

## 2. NO single global majorant of a LAYER-2-integrable form

For `W(P)` to (i) dominate `g` pointwise on the whole box and (ii) be LAYER-2-integrable
(`σ_min^{−a}` or `det(G)^{−a/2}`, `a<1`):

- `W = σ_min^{−a}`: on codim-2, `σ_min^{−a} ≍ σ^{−a}` must beat `σ^{−(2c'−3)}` ⟹ `a ≥ 2c'−3 ≈ 4` near 7/2.
  **`a≥4 ≫ 1`.**
- `W = det(G)^{−a/2}`: `det G = (s₁s₂s₃)² ≍ σ⁴` on codim-2 ⟹ `σ^{−2a} ≥ σ^{−(2c'−3)}` ⟹ `a ≥ c'−3/2 ≈ 2`.
  **`a≈2 > 1`.** (Same failure I found: `det` wastes exponent on the bounded `s₁`.)

**No single global majorant of either form exists in `3<c'<7/2`.** [FACT — forced exponents `2c'−3`,
`c'−3/2`; Codex-concurred.] The AM–GM route `frobSq(R)^{−c'} ≤ C·det(RRᵀ)^{−c'/r}` on the FULL product
`R=A₀A₁A₂` also fails (gives `c'<3/2`): it loses that `A₀` is free/full-rank. The det-inverse compass does
NOT dissolve this wall — the strata genuinely demand DIFFERENT weights, so a STRATIFIED cover is forced.

## 3. Does the complement descend to an ALREADY-CLOSED banked piece? NO.

The complement `{s₂(tail)<κ}` is the rank-`(tail)≤1` locus (codim-2 stratum). Audit of the banked pieces:

- **LAYER 2** (`sjProductTube_params_lintegral_lt_top`, PROVED): integrates `σ_min^{−a}`, `a<1`. Handles
  codim-1 only (§2: `g ⋠ σ_min^{−a}` on codim-2).
- **Cover-assembly** (`RouteMSJDominantCover`, PROVED, but *not yet consumed by any file*): a PARTITION
  tool — it reduces `∫_box` to `Σ ∫_{cell}` and REQUIRES the per-cell finiteness as a HYPOTHESIS
  (`hcharts`). It does NOT supply the deep-cell bound. It also partitions by *dominant minor*, which
  controls `σ_r` (smallest), NOT `σ_{r−1}` (secinfra's F2 is exactly right).
- **(S,J) descent** (`RouteMSJResolution`): the rank-recursion that WOULD handle deep strata (via the
  vslice-cert §5 corner blow-up) — but its analytic endpoint `sjJointResolution` (pieces 4/5/7) and the
  cover/shear `sjBoundaryPeel` are **UNPROVEN named sorries.**

**⟹ The complement routes into the (S,J) recursion, whose endpoint is not closed — OR needs a new
corank-recursive front-first + LAYER-2-analogue.** It is not absorbed by a closed piece. [FACT +
INFERENCE from the sorry audit.]

## 4. Composition trace — (3,3,3,4), `t=1` (the front-split, then the residual)

`∫_box frobSq(A₀A₁A₂)^{−c'} = ∫_{tail box (A₁,A₂)} g(Q)`, `Q=A₁A₂` (`3×4`), `g(Q)=∫_{A₀ box}frobSq(A₀Q)^{−c'}`.
Split the tail box by the sector:

- **Sector `{σ₂(Q)≥κ}`:** step (a) gives `g(Q) ≤ C·σ₃(Q)^{−α'}`, `α'=2c'−6<1` (log at `c'=3`). LAYER 2
  integrates `σ₃(Q)^{−α'}` over the whole tail box (`α'<1` ⟺ `c'<7/2`). **✓ CLOSES the top stratum.**
- **Complement `{σ₂(Q)<κ}`:** `g(Q) ≍ σ^{−(2c'−3)}`; `∫_{complement} g ≍ ∫σ^{6−2c'}dσ` finite for `c'<7/2`
  **but NOT bounded by LAYER 2's weight.** **OWED.**

So `[sector via LAYER 2] + [complement OWED]`. The composition closes the codim-1 slice; the codim-2 slice
(equally binding) is the residual, and secinfra's "(a) is a wall" is *half right*: (a)-as-a-single-majorant
walls, (a)-as-a-rank-stratum-recursion does not.

## 5. F1 — measurability of the sector: NOT a wall, cheapest route is the 2×2-minor sector

The set `{σ₂ ≥ κ}` via sorted eigenvalues is NOT off-the-shelf (`Matrix.IsHermitian.eigenvalues₀` exists,
antitone-sorted, but its measurability/continuity *as a function of `P`* is absent, and it is
`hA.eigenvalues₀` — dependent on the Hermitian proof). Three routes, cheapest first:

1. **2×2-minor sector (CHEAPEST for measurability).** `S := {max over 2×2 submatrices B of |det B| ≥ κ'}`
   — a finite max of polynomials, **trivially Borel** (no eigenvalue continuity, no operator norm). By
   Cauchy–Binet `s₁s₂/√18 ≤ maxminor₂ ≤ s₁s₂` (verified numerically, ratio ∈ [0.31, 0.98] ⊂ [1/√18,1]),
   and `s₁ ≤ R` on the box, `S` **sandwiches** `{σ₂ ≥ κ}` up to box constants (both directions). Fits the
   banked cover-assembly's `|det minor|` keys directly.
2. **Adjugate (CHEAPEST for an EXACT characterization — Codex).** `{‖G‖_op ≥ κ²} ∩ {‖adj G‖_op ≥ κ²‖G‖_op}`,
   `adj(G) = G² − e₁(G)·G + e₂(G)·I` (polynomial in `G`; eigenvalues `λ₂λ₃,λ₁λ₃,λ₁λ₂`, so `‖adj G‖=λ₁λ₂`).
   Both conditions closed; needs `‖·‖_op` (top eigenvalue) continuity but NO sorted-eigenvalue infra.
3. **char-poly sign `q(κ²), q'(κ²)` — FALSE.** Codex counterexample: spectra `(5,2,1)` and `(7,6,5)` both
   give `q(4)<0, q'(4)>0` but only the second has ≥2 eigenvalues `>4`. A full Sturm chain would work but is
   heavier. **Do not use.**

[FACT — Cauchy–Binet bracket verified; adjugate spectrum exact; route-3 counterexample Codex-supplied.]

---

## 6. VERDICT: BUILDABLE (rank-stratum recursion), NOT a hard wall — but NOT bounded plumbing

The 7/2 threshold is SOUND (proven twice: vslice-cert §5 corner blow-up + pivchg direct `∫g`). The
obstruction is architectural: **the (a)-step is intrinsically a rank-stratum recursion, and LAYER 2 is only
its top (`q=1`) rung.** Ordered plan for the (3iii) + complement:

1. **[cheap] Sector measurability (F1):** the 2×2-minor sector `S = {maxminor₂ ≥ κ'}` (Cauchy–Binet
   sandwich). Discharges the F1 flag; reuses the cover-assembly's `Continuous.matrix_det` key machinery.
2. **[the 3iii sector piece] Sector step-(a):** the banked two-block radial crux (`twoBlock_radial_le`,
   `genm-vsa` card) + the chart-reduction wiring (card items 1,2,5: v-exposure CoV, Frobenius–Gram spectral
   identity, chart algebra), **RESTRICTED to `S`**, producing `g ≤ C·σ₃^{−α'}` on `S`; then LAYER 2. Closes
   the top stratum. *(This is the "buildable" part secinfra can proceed on.)*
3. **[the genuine new content] The complement / deep strata (`q=2,3`):** a RANK-stratum cover (corank
   `q=1,2,3` via `(q)`- and `(q+1)`-minor conditions — measurable, cover-assembly-style), and on each
   corank-`q` cell a *corank-`q`* front-first majorant + a *corank-`q`* tube integral:
   - `q=1`: LAYER 2 (banked).
   - `q=2,3`: **NEW** — a coupled `(1 stable + q collapsing)`-block radial estimate (the 2-collapsing-block
     generalisation of the card's crux) + a `q`-compound tube integral (`∫` of the `q`-th compound det
     weight, `∧^q` functorial ⟹ `det_product_gram` on the compound factors), **restricted to the cell** so
     the other strata's divergence is excised.
   - **Assemble** `∫ = Σ_q ∫_{cell_q} < ∞` for `c'<7/2` via the linchpin `minAdm = min_q[D_prod(q)+m₀(q−1)]=7`.
   Alternative (conceptually cleaner, bigger): a single new analytic module integrating `g(Q)` directly
   (pivchg's Beta-reduction + tube codim). Either way this is a **multi-module build**, not 3iii labour.

### Firmest / most-likely-to-break / next
- **Firmest.** The dichotomy is genuine, the complement is binding at 7/2, and no global `σ_min^{−a}`/`det^{−a/2}`
  (`a<1`) majorant exists (exact algebra + two independent Codex consults agree; codim-2 exponent `2c'−3`).
- **Most likely to break the clean plan.** The corank-2 front-first must **COUPLE** the two collapsing
  directions: the vslice-cert §5 warning bites here — treating them as independent divisors UNDERSHOOTS to
  `min(2,3/2)=3/2`; only the coupled corner (sum-form `u₀²U₀+u₁²U₁`, measure `|u₀|³|u₁|²`) recovers 7/2. So
  the corank-2 radial estimate is genuinely new coupled content, not a copy of LAYER 2. Secondary: the
  product-rank tube codim `D_prod(q)` under the pushforward measure carries a `log`/tie at the codim-4
  double component (task #116) — harmless to the strict threshold (`C_ε t^{D−ε}`), but the tube estimate
  must not assume a clean `t^D`.
- **Next construction (smallest test).** Build the corank-2 coupled front-first majorant
  (`1-stable-2-collapsing` radial) + its corank-2 tube integral on `{σ₂<κ}∩{σ₁≥κ}`, and verify it composes
  to the codim-2 binding at 7/2. That single piece settles whether the recursion closes as designed.
