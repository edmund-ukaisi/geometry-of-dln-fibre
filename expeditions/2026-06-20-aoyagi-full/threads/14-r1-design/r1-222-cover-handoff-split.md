# (2,2,2) cover — execution-ready SPLIT hand-off (fm assembly / fm-2 measure) + G5 validate-small

- **Seat:** `pp` (design). For `fm` (assembly) + `fm-2` (per-chart measure). The first TRUE cover rung
  AND G5-abstract's validate-small in one. Sequenced after the (1,1,1) gate (closed) + G5-step (#52).
- **Companion:** `r1-general-atlas-design.md` §(2,2,2) EXECUTION-READY COVER (the tree + bounds);
  `g5-abstract-statement.md` (the G5-step this instantiates). This card = the EXPLICIT charts + the
  fm/fm-2 split.

## The COMPLETE 24-leaf list (all 4 A-charts) — the set is EXACTLY 24, STABLE

Route (b) [step-3 sub-blowup of the δ-branch deeper points] keeps the set at EXACTLY 24 — the deeper-point
pieces ARE the step-3 block sub-leaves, already counted (the δ-pivot was never a leaf; it always
subdivides). The pin CONFIRMS the 24-set, doesn't grow it. fm-2 builds against this stable set.

| leaf type | count | d | k | h | RHS | φ (composite) |
|---|---|---|---|---|---|---|
| E-pivot (unit) | 4 | 2 | `![1,1]` | `![3,2]` | 3/2 | step1(P=x,Jac x³)∘Lemma2∘[E=s,F0=sv,δ=sw,Jac s²] → x²s²·unit |
| F0-pivot (unit) | 4 | 2 | `![1,1]` | `![3,2]` | 3/2 | …∘[F0=s,E=sv,δ=sw,Jac s²] → x²s²·unit |
| δ→step3 block | 16 | 3 | `![1,1,1]` | `![3,2,3]` | 3/2 | …∘[δ=s,E=sv,F0=sw,Jac s²]∘[Y=u, others u·zᵢ, Jac u³] → x²s²u²·(1+Σ³z²) |
| **TOTAL** | **24** | | | | `⨅`=3/2 | |

The 4 A-charts differ ONLY in the step-1 pivot choice `P ∈ {a00,a01,a10,a11}` (P=x, other 3 a-entries =
x·tᵢ; Jac x³); the Lemma-2 + step-2 + step-3 subtree is IDENTICAL per A-chart (a00↔a_ij symmetry).
`⨅` over all 24 = 3/2 = ½·Mval(deepest rank-1 stratum) = lambdaCore(2,2,2). θ=1.

## EXECUTABLE φ maps + Jacobians (all 4 nodes, sympy-verified — fm-2 build-grade, 2026-06-21)

The chart tree has 4 NODES per branch (the Lemma-2 node is a homeomorph, made explicit here):
`step1 φ₁ (blow-up |det|=x³) → Lemma-2 φ_L2 (HOMEOMORPH det ±1) → step2 φ₂ (blow-up |det|=s²) →
[δ-branch: step3 φ₃ |det|=u³]`. All φ explicit polynomial maps; all `|det Dφ|` sympy-verified
(`/tmp/r222_executable_leaves.py`, `/tmp/r222_lemma2_explicit.py`).

- **STEP 1** (4 A-charts, `(x,t1,t2,t3,b00,b01,b10,b11) → originals`; B passes through): pivot `a_pq=x`,
  others `= x·tᵢ`. `|det Dφ₁| = x³` (all 4). e.g. a00: `a00=x, a01=x·t1, a10=x·t2, a11=x·t3`.
- **LEMMA-2 φ_L2** (HOMEOMORPH, `det = −1`, `rlctAtOn_comp_homeomorph`): `(t1,t2,t3,b00,b01,b10,b11) →
  (E,F0,δ,q,G,H)` [t1 carried, SPECTATOR]: `E = b00 + t1·b10`, `F0 = b01 + t1·b11`, `δ = t3 − t1·t2`,
  `q = t2`, `G = b10`, `H = b11`. Inverse: `b10=G, b11=H, b00=E−t1·G, b01=F0−t1·H, t2=q, t3=δ+t1·q`.
  After it: `F = x²·(E²+F0²+(qE+δG)²+(qF0+δH)²)`, center `{E=F0=δ=0}`.
- **STEP 2** (3 charts, `(s,v,w)→(E,F0,δ)`; q,G,H spectators): `|det Dφ₂| = s²`. E/F0-pivot → UNIT;
  δ-pivot `δ=s,E=s·v,F0=s·w` → smooth-4-block → step 3.
- **STEP 3** (δ-branch, 4 charts, `(u,z1,z2,z3)→y0..y3`): pivot `yₖ=u`, others `=u·zᵢ`. `|det Dφ₃| = u³`.

**Composite `|det Dφ|`:** 8 UNIT leaves `= x³s²`; 16 BLOCK leaves `= x³s²u³` (Lemma-2 contributes ±1).
**Per-leaf target** (the g5_step output): unit `weightedThreshold (F∘φ) |x³s²| {0}`; block `… |x³s²u³| {0}`.
**THE SPLIT (confirmed w/ fm-2):** Option A ⟹ fm-2's #54-measure = ONLY the `∫⁻=Σ∫⁻` (discharge
H-C¹/inj/null/cover/disj from φ); fm owns the per-leaf VALUE (monomialThreshold 3/2). The weighted target
is the g5_step OUTPUT (fm-2 produces, fm evaluates).

## The explicit leaf chart maps (representative branch: A-pivot a00)

`F = ‖AB‖²`, `A=[[a00,a01],[a10,a11]]`, `B=[[b00,b01],[b10,b11]]` (8 coords). The other 3 A-charts are
the obvious symmetry `a00 ↔ a_ij`; 6 leaves each, 24 total.

- **Step 1 — φ₁** (A-pivot a00): `a00=x, a01=x·t1, a10=x·t2, a11=x·t3`, `B` unchanged. `Jac φ₁ = x³`.
  ⟹ `F = x²·Q`. [x-exceptional: k=1, h=3, ratio 2]
- **Lemma-2** (unit-Jacobian regular change → coords `E,F0,δ,q,G,H`): `Q ~ E²+F0²+(qE+δG)²+(qF0+δH)²`,
  center `{E=F0=δ=0}` (codim 3). [verified, `r1_222_verify_codex.py`; does NOT shift exponents]
- **Step 2 — φ₂** (blow up `{E=F0=δ=0}`, 3 charts, `Jac = s²`): [s-exceptional: k=1, h=2, ratio 3/2]
  - **E-pivot** `E=s, F0=s·v, δ=s·w`: `Q = s²·U`, `U(0)=1` ⟹ **UNIT LEAF** `x²s²·unit`.
  - **F0-pivot** `F0=s, E=s·v, δ=s·w`: `Q = s²·U`, `U(0)=1` ⟹ **UNIT LEAF**.
  - **δ-pivot** `δ=s, E=s·v, F0=s·w`: `Q = s²·U`, `U(0)=0` ⟹ smooth-block `v²+w²+G'²+H'²` (after
    unit-Jac `G'=qv+G, H'=qw+H`) ⟹ needs **Step 3**.
- **Step 3 — φ₃** (δ-branch only; blow up the block vertex `{v=w=G'=H'=0}`, 4 charts, `Jac = u³`):
  e.g. **y0-pivot** `v=u, w=u·z1, G'=u·z2, H'=u·z3`: `Σy² = u²·(1+Σz²)`. ⟹ **BLOCK LEAF**
  `x²·s²·u²·(1+z1²+z2²+z3²)`, total `Jac = x³·s²·u³`. [u-exceptional: k=1, h=3, ratio 2]

## FM gets — the ASSEMBLY (the leaf-sum ⟹ headline)

24 leaves; per-leaf `monomialThreshold` (k=1 everywhere, pos-def-real initial forms):
- **8 UNIT leaves** (4 A × {E,F0}): divisors `x(k1,h3), s(k1,h2)` ⟹ `min(2, 3/2) = 3/2`.
- **16 BLOCK leaves** (4 A × 4 step-3): divisors `x(k1,h3), s(k1,h2), u(k1,h3)` ⟹ `min(2,3/2,2) = 3/2`.
- `⨅` over 24 = `3/2 = ½·Mval(deepest) = lambdaCore(2,2,2)` ✓.

fm assembles: `rlctAt F = ⨅_leaves monomialThreshold` (from G5-step `∫⁻=Σ∫⁻` + per-leaf monomial rlct
via S2/Case111-style) `= 3/2`; θ=1 (the s-exceptional binds in every branch, one component). UPPER = any
one leaf (3/2); LOWER = all 24 + the cover.

## FM-2 gets — the PER-CHART MEASURE pieces (the G5-step instance)

**Per-leaf value = the WEIGHTED threshold, NOT bare `rlctAtOn` (load-bearing — the Jacobian trap):**
the per-leaf contribution is `weightedThreshold (F∘φ) |Jac φ| {0}` — weight ρ = the Jacobian, NOT
`rlctAtOn (F∘φ)` (which has trivial weight ρ=1, `rlctAtOn = weightedThreshold F 1 {w*}` per
`Rlct.lean:168`). Bare `rlctAtOn(x²s²u²·unit) = min(½,½,2,…) = ½` — the WRONG value; the Jacobian
`x³s²u³` shifts the exponents to give `min(2,3/2,2) = 3/2`. The G5-step c-o-v
(`lintegral_image_eq_lintegral_abs_det_fderiv_mul`) PRODUCES the `|det fderiv|·g∘φ` integrand, so the
Jacobian lands in the `weightedThreshold` ρ slot AUTOMATICALLY via the G5 composition. State per-chart
targets as weighted-threshold-with-Jac, never bare rlctAtOn.

The `∫⁻=Σ∫⁻` is a G5-step instance with the 24-leaf chart family. Per-chart obligations (discharge from
the EXPLICIT φ above; all mechanical given the polynomial maps):
- **(H-C¹/Jac)** each φ (step1/2/3) is polynomial ⟹ C¹; `|det fderiv| = |x|³`, `|s|²`, `|u|³` resp.
  (composite leaf Jac = product). Compute via the explicit substitution Jacobian.
- **(H-inj)** each φ is InjOn off its exceptional `Z` (x=0 / s=0 / u=0) — the standard
  blow-up-chart injectivity (a point with the pivot ≠ 0 has a unique preimage).
- **(H-null)** each `Z` (`{x=0}` etc.) is a coordinate hyperplane ⟹ Lebesgue-null;
  `addHaar_image_eq_zero_of_det_fderivWithin_eq_zero` for the image.
- **(H-cover)** the leaves cover a nbhd of `{F=0}` up to null — VERIFIED (12063/12063 leaf-reachable,
  only `{A=0}` uncovered = null; `r1_222_full_cover.py`). At each step it's the standard affine cover of
  the coordinate-subspace blow-up (the pivots exhaust the projective directions).
- **(H-disj)** the charts within a blow-up step are a.e.-disjoint (distinct pivot-max regions) — the
  standard affine-chart a.e.-disjointness.
Then `G5-step` (×3 nested: step1 4-way ∘ step2 3-way ∘ step3 4-way) gives the 24-leaf `∫⁻=Σ∫⁻`.

### THE δ-CHART DEEPER-POINT PIN (fm SPECIFY finding, 2026-06-21 — load-bearing for the δ-branch build)
fm verified the δ-pivot chart `F∘φ = α²ρ²·(ξ²+η²+(bξ+r)²+(bη+s)²)` (Jac ρ², ratio 3/2), and found the
"unit" `U = ξ²+η²+(bξ+r)²+(bη+s)²` vanishes EXACTLY at `{ξ=η=r=s=0}` = the deeper stratum `B=0` (codim-4
origin). So the δ-chart is monomial×SMOOTH-4-BLOCK, NOT monomial×unit (`U` is a nondegenerate 4-block,
Hessian det 16; `= ξ²+η²+r'²+s'²` after the unit-Jac `r'=bξ+r, s'=bη+s`). This IS the δ-pivot smooth-block
catch, chart-exact.
- **ROUTE (the δ-branch handling): FURTHER BLOW UP (step 3)** — blow up the block vertex `{ξ=η=r=s=0}`
  (the cone `Σ⁴y² → w²·unit`, 4 sub-charts). The δ-chart SUBDIVIDES into 4 step-3 BLOCK leaves; it is
  NOT itself a leaf. Each step-3 leaf = `ρ²w²·(1+Σ³z²)` = monomial×UNIT (now genuinely `≥1`) ⟹ S1.4
  unit-strip + S2 per step-3 leaf. (NOT "S1.4 on a unit-positive nbhd of the δ-chart" — the unit is NOT
  positive at the deeper point; you must blow up first. NOT "exclude the bad locus" — that drops the
  deeper stratum from the cover, breaking the lower bound.)
- **SOUNDNESS (deeper-point ratio ≥ 3/2, the chart-exact lower-bound crux):** the deeper point `B=0`
  sits in the 16 step-3 block leaves. Jac carries `ρ²·w³` (step-3 codim-4 vertex blowup ⟹ `w^{4−1}=w³`);
  `∫(ρ²w²)^{-c}·ρ²w³` ⟹ ρ-divisor `c<3/2` (ratio 3/2, BINDING), w-divisor `c<2` (ratio 2). Block-leaf
  ratio `= min(3/2, 2) = 3/2 ≥ 3/2`. ✓ The w-divisor ratio is 2 = `4/2 = ½·Mval(B=0 stratum)` (block dim
  4 = the B=0 codim in the δ-chart), and `Mval(B=0)=4 > minMval=3` ⟹ `2 > 3/2` ⟹ the deeper stratum's
  exceptional NEVER binds. The admissible-strata-codim-ordering (`min over Adm = 3` at the rank-1 stratum,
  not 4 at B=0) IS the soundness. `/tmp/r222_delta_soundness.py`.

### THE δ-BRANCH BUILD-ROUTE FORK (step-3 blow-up vs skip-via-weighted-split) — 2026-06-21
fm-2's instinct: SKIP step-3, handle the δ-leaf `α²ρ²·U` directly by a product-split (U via shear+#38).
Adjudicated (pp + decorrelated Codex xhigh, INDEPENDENT, IDENTICAL on all 4 points):
- **SOUND** — the skip gives 3/2: split `α`-piece (weighted-monomial `α²`, weight `α³` → 2) | `ρ`-piece
  (`ρ²`, weight `ρ²` → 3/2 BINDING) | `U`-piece (`rlctAtOn(U)=2` via S1.1-shear + #38). `min(2,3/2,2)=3/2`.
  The shear with `b` a free coord is SOUND (det 1, `U` independent of `b`). (Correction: the FULL δ-chart
  Jacobian is `α³·ρ²` — the `α³` is the step-1 A-blowup, not just the `ρ²` second blowup.)
- **BUT NOT `product_min` (#56)** — #56 is for `rlctAtOn` = TRIVIAL weight; the δ-value is the WEIGHTED
  threshold (the `α³ρ²` Jacobian rides along). The skip needs a NEW lemma:
  `weightedThreshold (fun (x,y) => f x · g y) (fun (x,y) => w x · v y) (0,0) = min (weightedThreshold f w 0) (weightedThreshold g v 0)`
  (disjoint blocks, `f,g ≥ 0` a.e.-nonzero) — a WEIGHTED generalization of product_min, NOT YET BUILT.
- **VERDICT (Q4, pp + Codex BLOWUP-LIGHTER for (2,2,2) alone):** step-3 = 16 uniform monomial×unit leaves,
  ALL via the existing 1-D weighted-monomial fact (no shear, no #38, no new lemma). skip = 1 leaf, but the
  new weighted-split lemma + shear + #38 wiring. Step-3 is lighter NOW.
- **NUANCE (the down-payment):** the weighted-product-split lemma, IF built, is REUSABLE for GENERAL-M
  (every general-M leaf is monomial×block with a Jacobian weight) and simplifies the (2,1,2) δ-leaf — like
  G5-abstract was. So skip is worth it IF building toward general-M; step-3 if (2,2,2) is the goal.
- **RECOMMENDATION:** step-3 for (2,2,2) (the 24-leaf list above assumes it, no new lemma) UNLESS fm-2
  takes the weighted-split as a general-M down-payment. Both SOUND (3/2). fm-2's call (owns the measure
  build). `/tmp/codex-skip3-answer.md`, `/tmp/r222_skip_step3*.py`.

## The split, crisply

- **fm-2 (measure):** build `G5-step` (#52) → instantiate it on the 24-leaf family (discharge
  H-C¹/inj/null/cover/disj from the explicit φ) → the `∫⁻=Σ∫⁻`.
- **fm (assembly):** per-leaf `monomialThreshold = 3/2` (8 unit + 16 block) → `⨅ = 3/2` → wire to the
  headline `rlctAt(2,2,2) = 3/2 = lambdaCore`, θ=1.
- The δ-branch smooth-block layer (step 3) is Option A (ratio-preserving monomialization) — keeps every
  leaf monomial×unit, RHS `⨅ monomialThreshold` literally true. (Option B would skip step 3 and use
  smoothBlockND on the block directly; A chosen for fixed-M uniformity per the controller.)
- **If Option B is ever used here** (the δ-leaf `x²s²·Σ⁴y²` directly): it's the SAME `product_min_rlct`
  lemma as (2,1,2), MONOMIAL×BLOCK instance — `rlct = min(axisRatios of x²s², rlct Σ⁴y²) = min(2,3/2,2)
  = 3/2`. This needs the product-MIN lemma stated with the POSITIVITY GUARD (not "vanishes only at 0",
  which excludes the monomial x²s²) — see the (2,1,2) card's HYPOTHESIS CORRECTION. So the (2,1,2)
  product-MIN lemma, stated right, is REUSABLE for the δ-leaf — no separate tool. (Option A avoids needing
  it here, but the unified lemma is the cleaner general path.)

## Why this doubles as G5-abstract's validate-small

The 24-leaf `∫⁻=Σ∫⁻` IS the first real composition of `G5-step` (nested 3-deep). Building #52 and proving
the (2,2,2) cover are the SAME measure work at this scale — so the (2,2,2) rung validates G5-abstract on
a concrete finite tree before any general-M use. No separate validate-small needed.
