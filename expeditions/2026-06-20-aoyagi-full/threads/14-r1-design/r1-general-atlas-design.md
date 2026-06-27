# R1 general atlas design — R1.1 (pivot atlas) + R1.3 (count, NOT codim) + R1.6 (cover)

- **Seat:** `pp` (leading R1 math/design). Task #48. The general-(M) atlas, in parallel with fm's
  (1,1,1) validate-gate. Route GREENLIT: route-A-CONCRETE (explicit poly blow-up charts + S1.1 +
  non-vacuous multiplicity-control + cover; no abstract blow-up infra).
- **Headline win (Codex R1.3 consult, /tmp/codex-r13-answer.md):** R1.3 is NOT the feared
  determinantal-codim theorem — it reduces to a **ℕ sum identity** (residual-entry count = Mval),
  sidestepping the Mathlib-v4.29 determinantal-codim gap entirely.

## R1.3 — the residual-entry COUNT (a ℕ identity, NOT a codim theorem)

Mathlib v4.29 lacks determinantal-variety codimension. But R1 does NOT need `codim S(t) = Mval` as a
global theorem. It needs the **local pivot-chart construction**: in a valid pivot chart, the blow-up
center is the coordinate subspace `{y₁=…=y_c=0}` cut by the nested Schur residual coordinates, with
`c = Mval(t)` = the **count of residual entries**. Then:
- codim of a coordinate subspace = #coordinates = Mval(t) (TRIVIAL, no codim API);
- Jacobian of the coordinate-subspace blow-up = `u^{c−1} = u^{Mval−1}` ⟹ `h = Mval−1` (standard);
- `k = 1` (F = Σg²·unit, pos-def-real initial form, order 2).

> **R1.3 (Lean form): `∑_j |residual block_j| = Mval(t)`**, where the blocks have sizes
> `(M¹−t₁)(M²−t₁)` and `(t_{j−1}−tⱼ)(M^{j+1}−tⱼ)` (j=2..L). A finite **ℕ sum identity** — VERIFIED
> (/tmp/r13_count_verify.py): the count = Mval, all block sizes ≥0 under admissibility (the validity
> hyps so Nat-sub doesn't truncate). NO determinantal geometry. The Mathlib gap is GONE.

Local chart obligations (Codex, fold in): pivots/minors invertible; the residual entries are part of
a coordinate system (not merely equations); their common zero = the center locally; the
pivot-elimination coordinate changes have UNIT Jacobian (don't shift the exponent). Caveat:
`Mval(t) > 0` for an actual blow-up center (`Mval=0` ⟹ no center, the smooth/regular case).

## R1.1 — the general pivot atlas (recursion on L, explicit poly charts)

The resolution is the iterated pivot blow-up (Aoyagi pp.15-21 as CONCRETE charts, NOT his exponent
bookkeeping). Recursion on L:
- **Base L=1:** core `‖C‖²` (one matrix M¹×M²) — already a SMOOTH block `Σ entries²`; `rlct = ½·M¹M²`
  via `smoothBlockND_rlct` (fm-2, #38). NO blow-up. (Mval(L=1) = M¹·M².)
- **Step L≥2:** blow up the locus where the current partial product's residual block vanishes (the
  pivot-vanishing center); the chart map φ is the explicit pivot substitution (pivot = u, other
  residual entries = u·(new vars)); `F = u²·(residual')·…`; recurse on the smaller residual product.
  Each step peels ONE rank-drop, accumulating the Jacobian exponent.
- **Branch terminus:** along the branch reaching stratum `S(t)`, the binding divisor has `(k,h) =
  (1, Mval(t)−1)`, ratio `½·Mval(t)` (R1.3-count + the Jacobian formula + k=1).

`ι` = the pivot branches (finite — each step has finitely many pivot choices). Per chart `(d_i, k_i,
h_i)`: the exceptional divisors' exponents (k=1 each; h = the codim-count−1 of the center each
resolves), spectator coords k=h=0. Validate-small'd: (1,1,1) [base, φ=id, monomial-NC]; (2,1,2)
[cone blow-up, 4 charts, φ=(x,xy,z,zw)]; (2,2,2) [pivot atlas, 24 charts, binding ratio 3/2]. All
symbolically verified (thread-14).

## R1.6 — the cover / exhaustiveness

The pivot branches' chart images COVER a neighbourhood of `origin ∩ {∏C=0}`: each step's charts cover
the blown-up locus minus the next (lower) center; iterating over all pivot branches exhausts the
nested-rank stratification `{∏C=0} = ⋃_t S(t)` (the strata partition). Off `{∏C=0}` the integrand is
locally bounded (threshold-irrelevant). The cover is the genuine residual real work (ranges over all
branches; an exhaustiveness claim, not a per-chart exponent computation). S1.1's `hsurj`+`hImE` carry
the per-chart blow-up transport (a blow-up chart is non-injective, Jacobian vanishing on the
exceptional locus — exactly hsurj/hImE's design).

## The assembly (R1.1+R1.2+R1.3+R1.6 → resolution_charts-core)

```
rlctAtOn (dlnLoss M 0) (0:Params M)
  = [S1.1 min-over-cover, R1.6 cover]  ⨅ over charts of chart-RLCT
  = [per chart: unit-absorption (rlct_unit_invariant) + S2 (monomial_rlct)]  ⨅⨅ axisRatio(h,k)
  = [R1.2 binding divisor k=1,h=Mval(t)−1 via R1.3-count; multiplicity-control all divisors]  ½·min_t Mval
  = ⨅ monomialThreshold (the resolution_charts-core RHS).
```
UPPER: binding divisor on the min stratum (R1.2a, ratio ½ min Mval). LOWER: every divisor ratio
≥ ½ min Mval (R1.2b multiplicity-control + R1.6 cover). A1 bridges ½ min Mval = lambdaCore.

## NET — the general atlas is MEDIUM, not a determinantal mountain

The feared heavy piece (R1.3 codim) is a ℕ sum identity (count = Mval) — Mathlib gap GONE. The real
remaining work: R1.1 the general pivot recursion (explicit charts, induction on L) + R1.6 the cover
(exhaustiveness over branches). Both route-A-concrete (explicit poly maps + S1.1), no abstract infra.
R1.2 sits on the count + the pos-def-real k=1 + the coordinate-blow-up Jacobian. The (2,2,2) witness
(ord₀=4, binding 3/2) is the key general case; the recursion generalizes it. Hand fm R1.3-as-count
(the ℕ identity) as the next concrete piece after the (1,1,1) gate — it's light and decouples the
codim worry.

---

## HONEST CORRECTION (pressure-testing R1.6, the cover) — do NOT overclaim "R1 medium"

I was drifting toward "R1 is medium" after R1.3 dissolved. Pressure-testing R1.6 corrects that:
**R1.6 (the general-M cover / exhaustiveness) is the genuine residual mountain, NOT dissolved by the
R1.3-count win.** And it's on the CRITICAL PATH:
- The headline is an EQUALITY ⟹ needs BOTH bounds. The UPPER (rlctAt ≤ ½ min Mval) needs only ONE
  chart (binding divisor) — cheap. The LOWER (rlctAt ≥ ½ min Mval) needs the resolution to be
  COMPLETE (no chart/divisor beats the min) ⟹ the cover. There is NO shortcut: the direct codim
  bound `rlct ≥ ½ codim` is FALSE (x^{2k}, (x²+y²)²), so the lower bound genuinely needs the
  resolution + the cover. D1 (inf over fibre) does NOT supply the per-point lower bound.
- So R1.6 (cover) is on the critical path for the headline equality, and it IS the hardest Lean piece
  in R1 — more than R1.1's chart maps (explicit) or R1.3 (a ℕ count).

**Tractability (honest):** the cover is "every point near {∏C=0} lies in some pivot-branch chart" — a
finite case-split (the pivot-pattern exhaustiveness), tractable per fixed M but genuinely intricate
for general M. The validate-small covers are finite + explicit: (1,1,1) needs NO cover (one chart =
whole space; the gate is clean); (2,1,2) 4 charts (the cover in miniature, 4-way case split); (2,2,2)
24 charts (the genuine cover work in miniature). The GENERAL-M cover (exhaustiveness over the iterated
pivot atlas) is the OPEN HARD DESIGN.

**Corrected R1 difficulty map:** R1.3 (count) LIGHT (ℕ identity, gap gone) ✓; R1.1 (explicit charts)
MEDIUM (the pivot recursion, induction on L); **R1.6 (general cover) the genuine LIFT** (the lower
bound depends on it, no shortcut). The (1,1,1) gate is clean (no cover); the small cases exercise the
cover incrementally; the general cover is the remaining mountain. Validate-small-first is the right
discipline precisely because the cover is the hard part — prove it on (2,1,2)/(2,2,2) (finite explicit
covers) before the general lift.

---

## R1.6 DETAILED COVER DESIGN (task #48 — the residual mountain, designed) — 2026-06-21

Pressure-tested the general cover with a decorrelated Codex (`/tmp/codex-r16-answer.md`, xhigh,
hypothesis withheld). The cover factors into THREE obligations; Codex graded them + found the wall.

### The three cover obligations (O1/O2/O3)
- **O1 — per-step affine cover:** the `c` standard charts `chart_i: y_i=u, y_j=u·v_j (j≠i)` cover the
  punctured nbhd of the COORDINATE-SUBSPACE center `{y_1=…=y_c=0}`. Codex: **INCOMPLETE** — for a
  coordinate-subspace center it is near-definitional (point with `y_i≠0` ⟹ chart `i`, explicit preimage
  `u=y_i, v_j=y_j/y_i`), but the blow-up-surjects-onto-punctured-nbhd + Jacobian-well-defined-a.e. is a
  (LIGHT, per-step) obligation, not free. The center IS a coordinate subspace by R1.3's same fact — the
  `c` residual coords both COUNT to `Mval` (R1.3) AND index the cover (R1.6).
- **O2 — termination:** strata finite, codim strictly increases each step ⟹ well-founded recursion.
  Codex: **CORRECT (FACT).** Verified: Mval strictly drops down the stratification (`/tmp/r16_general_design.py`).
- **O3 — partition:** each point has a unique rank vector `t` ⟹ strata partition `{∏C=0}`. Codex:
  **CORRECT (FACT).**

### The wall (Codex's omitted obligations, my re-grade)
Per-STEP everything is LIGHT/STANDARD (O1/surjectivity/measure-zero-boundaries/Jacobian-monomial). The
WALL is the GENERAL-M ITERATION, concentrated in two of Codex's omitted obligations:
- **(G3) strict-transform tracking** — after each pivot substitution the residual product `∏C'` must be
  re-identified as the same shape (a smaller core) so the recursion closes; for general M this is
  bookkeeping over arbitrary rank vectors. HEAVY.
- **(G5) gluing the iterated change-of-variables into ONE global integral identity** — Mathlib has
  SINGLE change-of-variables; an iterated/recursive c-o-v over a TREE of charts assembled into one
  `∫_U = Σ_charts ∫_chart` is infrastructure that does NOT exist. HEAVY (the infra wall). Codex's
  load-bearing INFERENCE.
- Codex Q3 (cover unavoidable for the lower bound): **FACT, YES** — without a covering family whose
  union matches a nbhd up to measure zero, chartwise bounds cannot certify integrability on the whole
  domain. (Reconfirms: the direct codim bound `rlct ≥ ½ codim` is FALSE — `x^{2k}`, `(x²+y²)²`.)

### The precise FIXED-M vs GENERAL-M boundary (the deliverable)
- **FIXED M = INTRICATE-STANDARD (provable now).** The resolution is a FINITE TREE (depth ≤ L−1,
  branching ≤ c per node); unrolled ⟹ a FINITE explicit list of leaf charts `φ_1..φ_n` (each a composite
  of finitely many pivot substitutions). Cover identity = `∫_U |F|^{-c} = Σ_i ∫_{V_i} |F∘φ_i|^{-c}|Jac φ_i|`
  — a FINITE sum, each term ONE application of Mathlib's single change-of-variables. NO recursion-gluing
  infra. [(2,2,2): 24 leaf charts.]
- **GENERAL M = RESEARCH-WALL.** `n`, the tree, the `φ_i` all depend on M — can't be written without the
  recursion; the recursion-gluing-as-a-theorem (G3+G5) is the missing infra. Codex verdict for
  general-M Lean: **RESEARCH-WALL.**

### REFINEMENT — the validate-small ladder's rungs are NOT all cover-exercises
- **(1,1,1):** `F = c₁²c₂²` already normal-crossing; ONE identity chart = whole space. NO cover.
- **(2,1,2):** `F = (a₁²+a₂²)(b₁²+b₂²)` — DISJOINT variables (a-block × b-block). This is a FUBINI
  PRODUCT (`∫[(|a|²)(|b|²)]^{-c} = (∫|a|^{-2c})(∫|b|^{-2c})`, separates), NOT a blow-up cover. rlctAt=1
  = ½·Mval(deepest)=½·2 ✓ (`/tmp/r16_212_finite_cover.py`). My earlier "(2,1,2) 4-chart cover" was the
  smooth-cone route; the product separates by Fubini WITHOUT blowing up. (2,1,2) does NOT exercise the
  iterated-cover.
- **(2,2,2):** `P_ik=Σ_j a_ij b_jk` — variables COUPLED (a,b multiply), no separation (verified 12 terms,
  `a₀₀b₀₀` present). THE FIRST genuine iterated-blow-up cover case (24 leaf charts). The cover-in-miniature.

So the cover-ladder really starts at (2,2,2): (1,1,1) monomial, (2,1,2) Fubini-product, **(2,2,2) the
first true finite cover**, then up the M-ladder as labour allows.

### One-citation-policy TENSION (controller adjudication, surfaced not papered over)
The wall is NOT "a fact to cite" (like S2's bare monomial integral) — it's "a CONSTRUCTION + a
c-o-v-tree-gluing lemma to BUILD." Axiomatising it = axiomatising a whole resolution-of-singularities-
for-this-family (far heavier than S2; against the awkward-middle lesson "prove the construction, R1 real
charts"). Honest options for the controller:
1. **Headline PER FIXED M** (validate-small ladder up the M-ladder), general-M flagged as the genuine
   open obstruction. PRESERVES one-citation. [Recommended near-term.]
2. **Build the recursion-gluing infra** (G3+G5) — the research lift, PRESERVES one-citation.
3. **Axiomatise cover-existence** — BREAKS one-citation + against the awkward-middle lesson. NOT recommended.

---

## (2,2,2) FULL-COVER CLIMB (validate-small, controller-blessed) — 2026-06-21

Climbed the (2,2,2) cover concretely (the controller's "prove the small covers FIRST" directive). The
cover mechanism is VALIDATED, with ONE genuine catch found and closed. All exact-symbolic
(`/tmp/r16_222_full_cover.py`, `/tmp/r16_222_deltachart.py`, `/tmp/r16_222_delta_rlct.py`,
`/tmp/r16_chart_shape.py`).

### The (2,2,2) resolution (two nested blow-ups, faithful to Aoyagi Lemma 2 / Thm 3)
- **Step 1** — blow up `{A=0}` (codim 4 in A-space). 4 affine charts (pivot = `a_ij`). Each:
  `A = x·Ahat` (unit at pivot), `F = x²·‖Ahat·B‖²`, Jacobian `x³` ⟹ x-divisor `(k=1,h=3)` ratio 2.
- **Lemma-2 regular split** (UNIT Jacobian, doesn't shift exponents): clears the pivot row/col of the
  product ⟹ `‖Ahat·B‖² ~ E²+F0²+(qE+δG)²+(qF0+δH)²` with center `{E=F0=δ=0}` (codim 3).
- **Step 2** — blow up `{E=F0=δ=0}` (codim 3). 3 charts (E-/F0-/δ-pivot), each Jacobian `s²` ⟹
  s-divisor `(k=1,h=2)` ratio 3/2. The s-exceptional is the BINDING divisor (= ½·Mval(deepest) = 3/2).

### THE CATCH (a genuine hole, found and closed — NOT skated over)
The three step-2 charts are NOT uniform:
- **E-pivot, F0-pivot:** residual `U` is a POSITIVE UNIT (`U(origin)=1`). Leaf = `x²·s²·unit`, pure
  monomial, rlct = min(2, 3/2) = 3/2. ✓
- **δ-pivot:** residual `U(origin)=0` — **NOT a unit.** `U = (qv+G)²+(qw+H)²+v²+w²` = a SMOOTH 4-block
  (after the unit-Jacobian change `G'=qv+G, H'=qw+H`: `U = v²+w²+G'²+H'²`). So the δ-leaf is
  `F = x²·s²·(smooth-4-block)`, NOT monomial×unit. My earlier "every leaf = monomial×unit, all ratios
  3/2" was PREMATURE — the δ-chart carries an unresolved smooth block.
- **Closure:** rlct of `x²·s²·(Σ⁴yᵢ²)` separates (Fubini): x-divisor c<2, s-divisor c<3/2, smooth-block
  c<4/2=2 ⟹ chart rlct = min(2, 3/2, 2) = **3/2**. The smooth-4-block contributes rlct 2 ≥ 3/2, so the
  s-exceptional STILL binds at exactly 3/2. The δ-chart is NOT a hole — but only because the smooth
  block's rlct (4/2) happens to exceed the binding min. This needed checking, not assuming.

### FIDELITY POINT for the skeleton (load-bearing for fm)
The current `resolution_charts` RHS = `⨅ᵢ monomialThreshold(dᵢ,kᵢ,hᵢ)` is PURE MONOMIAL, but the δ-leaf
is monomial×smooth-block. Two readings:
- **Option A (full monomialization):** blow up the residual smooth block too. The cone `Σⁿyᵢ²` blown up
  at 0 gives an exceptional of ratio EXACTLY `n/2` (chart `yᵢ=u, yⱼ=u·zⱼ` ⟹ `Σy²=u²·unit`, Jac `u^{n-1}`,
  ratio `n/2`) = the smooth block's own rlct. So monomializing is RATIO-PRESERVING ⟹ the pure-monomial
  RHS is LITERALLY TRUE, and no new divisor drops below the min (smooth-block ratio `n/2` ≥ binding min).
  COST: extra blow-up charts per residual smooth block (the δ-branch subdivides further; (2,2,2) is NOT
  4×3=12 simple leaves — the δ-branch spawns a 4-chart Σy² blow-up).
- **Option B (keep smooth blocks):** Aoyagi-faithful (he uses smooth-block n/2 directly), but the
  skeleton RHS must generalize to `⨅ (monomialThreshold ⊓ smoothBlock-rlct)`.

**Recommendation: Option A** — keeps the skeleton RHS (`⨅ monomialThreshold`) literally true, is
ratio-preserving (no soundness risk), and is more uniform for fm (every leaf is monomial×unit). The
atlas design MUST include the residual-smooth-block monomialization layer (an extra blow-up per block,
ratio = block-dim/2, always ≥ the binding min = ½·minMval). This is the concrete general-design
refinement the (2,2,2) climb produced: leaves are NOT all (step1×step2); residual-smooth-block branches
carry a THIRD monomialization layer.

### NET (2,2,2): cover VALIDATED, lower bound 3/2 SOUND
Every divisor across the full atlas (x-exceptional ratio 2; s-exceptional ratio 3/2; residual-block
monomialization ratio 2) has ratio ≥ 3/2, with the s-exceptional binding at exactly 3/2 in every branch.
Cover (every point near `{F=0}` is in some A-chart × residual-chart × block-chart) ⟹ LOWER bound
rlctAt ≥ 3/2; UPPER (one chart) ⟹ ≤ 3/2. EQUALITY 3/2 = ½·Mval(deepest), θ=1 (one exceptional). The
cover-in-miniature is sound. (2,1,2) does NOT exercise this (Fubini-product); (2,2,2) is the genuine
first cover, and it required catching+closing the smooth-block leaf.

---

## LOWER-BOUND CRUX — SETTLED (the centers are exactly the admissible strata) — 2026-06-21

The general lower bound `rlctAt ≥ ½·min_{Adm} Mval` needs: every blow-up center has codim ≥ min_Adm
Mval. I pressure-tested this and found a genuine-looking WORRY, then resolved it (decorrelated-Codex
confirmed, `/tmp/codex-r16b-answer.md`).

### The worry (a real one, not hand-waved)
There exist weakly-decreasing rank vectors that are NOT admissible (`t_L ≠ 0`) with `Mval < min_Adm`.
Concrete: (2,2,2) has the weakly-decreasing `t=(1,1)` (Mval=1) — but `min_Adm Mval = 3` (over
`Adm={(0,0),(1,0),(2,0)}`). IF the resolution blew up the codim-1 `S(1,1)` as an intermediate center,
its exceptional would have ratio ½·1 = 1/2 < 3/2, BREAKING the lower bound. (I had earlier mis-dropped
the `t_L=0` constraint and computed `minPosMval=1` — an ARTIFACT; the encoded `admPred` requires
`T j = 0` for the last coordinate. Re-matched ground truth over the CORRECT Adm: (1,1,1)→1, (2,1,2)→2,
(2,2,2)→3.)

### The resolution (independent reason + Codex confirmation, AGREE)
- **My geometric reason:** on `{∏C=0}` the PRODUCT has rank 0 by definition ⟹ the deepest-layer
  residual rank `t_L = 0` ALWAYS on the zero-locus. The non-admissible `t_L≠0` strata are NOT subsets
  of `{∏C=0}` — they're elsewhere. The resolution resolves `{∏C=0}`, so it only blows up centers IN it
  = `t_L=0` = admissible strata. `admPred`'s `t_L=0` IS exactly "lies in the zero-locus".
- **Codex (Q1/Q2 CORRECT, FACT):** the flag-resolution chooses centers only where the tail product
  already has zero rank — each an admissible `t` with `t_L=0`; non-admissible strata never appear as
  centers (they sit in the smooth locus of the total transform once the flag component is introduced).
- **Codex Q3 (FACT) — the sharp statement:** on the flag-resolution recording `K^(j)⊂ℝ^{M^{j+1}}`,
  `dim K^(j)=M^{j+1}−t_j`, `C^(j)(K^(j))⊂K^(j−1)`, every exceptional divisor is indexed by an
  admissible `t`; along it `k=1`, `h=Mval(t)−1`, ratio `(h+1)/(2k)=½·Mval(t)`. Min over admissible `t`
  ⟹ the lower bound.

⟹ **The lower bound is STRUCTURALLY SOUND.** No blow-up center has codim < min_Adm Mval, because every
center lies in `{∏C=0}` ⟺ admissible ⟹ codim = Mval(t) ≥ min_Adm Mval.

### Codex Q4 (a direct route) — FLAGGED AS A TRAP, not taken
Codex offered (INFERENCE, its own mark): `rlct(F)=½·lct(I)`, `I=(f_j)`, and `lct(I)=min_Adm Mval` via
multiplier-ideal computations for quiver rep spaces — sidestepping intermediate centers. **Do NOT
take it:**
1. **Real vs complex:** `lct` is the COMPLEX threshold; `rlct_ℝ(Σf²)=½·lct_ℂ(I)` is NOT generally true
   (real/complex thresholds differ); needs the coincidence PROVEN for this family — Codex-flagged
   INFERENCE, not a free FACT.
2. **Two constraints broken:** it's a SECOND citation (beyond S2) AND almost certainly the
   Lehalleur–Rimányi / determinantal-multiplier-ideal literature ⟹ against Aoyagi-independence.
3. **It black-boxes the content R1 exists to prove** (`lct(I)=min_Adm Mval` IS the geometric codim
   result). Citing it = giving up the proof.
Q4 is a useful CROSS-CHECK (answer `min_Adm Mval` matches) — keep as confirmation, not a path.

### NET — the general lower bound is sound; the residual work is the construction, not the bound
The lower-bound DIRECTION is settled (centers = admissible strata, Codex-confirmed). What remains for
general M is the CONSTRUCTION (G3 strict-transform tracking + G5 c-o-v gluing) — building the
flag-resolution explicitly and gluing the iterated change-of-variables. That is the RESEARCH-WALL
already mapped; the lower-bound's logical soundness is no longer in question. This sharpens the
fixed-M/general-M boundary: fixed-M is a finite explicit flag-resolution (tractable); general-M is the
recursive flag-construction + gluing (the wall).

---

## G5 SEPARABILITY — IS THE C-O-V-TREE-GLUING A BUILDABLE DOWN-PAYMENT? (controller's scope Q) — 2026-06-21

The controller adjudicated: (1) fixed-M ladder near-term + (2) general infra ROADMAPPED; and asked ONE
thing — is **G5 (the abstract change-of-variables-tree-gluing lemma over an arbitrary finite tree)
separable + buildable NOW**, reducing the wall to G3's geometry?

### Verdict: YES — G5-abstract is SEPARABLE + BUILDABLE NOW (intricate-standard, NOT the wall).
G5 = `∫_U |F|^{-c} = Σ_{leaf charts i} ∫_{V_i} |F∘φ_i|^{-c}|Jac φ_i|`. Unfolded, ONE blow-up step's
identity = [lintegral cover-additivity] ∘ [single change-of-variables per chart] — BOTH are Mathlib
FACTS:
- **Single c-o-v (CHECKED in Mathlib):** `lintegral_image_eq_lintegral_abs_det_fderiv_mul`
  (`Mathlib/MeasureTheory/Function/Jacobian.lean:1189`):
  `(hs : MeasurableSet s)(hf' : ∀ x∈s, HasFDerivWithinAt f (f' x) s x)(hf : InjOn f s)(g : E→ℝ≥0∞) :`
  `∫⁻ x in f''s, g x = ∫⁻ x in s, ENNReal.ofReal |(f' x).det| * g (f x)`. EXACTLY the ℝ≥0∞ form G5
  needs — over `lintegral` ⟹ NO integrability side-conditions (the threshold integrand `|F|^{-c}` is
  ∞ above the rlct; ℝ≥0∞ handles it unconditionally).
- **Cover-additivity:** `lintegral` over an a.e.-disjoint null-cover = Σ (Mathlib set-additivity). FACT.
- **Tree composition:** finite structural recursion on the (depth ≤ L−1) blow-up tree, composing the
  step-identity at each node. Intricate-standard induction, NOT research.

### The ONE real friction (the caveat, now PINNED against Mathlib)
Mathlib's c-o-v wants `InjOn f s` (injective ON the set). Blow-up charts φ are injective only OFF the
exceptional locus (a null set). ADAPTER: apply the lemma to `s = chart-domain minus exceptional` (where
φ IS injective); the exceptional is null ⟹ doesn't affect the `lintegral`. This adapter (restrict to
the injective locus, exceptional null) is itself intricate-standard — Mathlib has measure-zero of
proper subvarieties (`addHaar_image_eq_zero_of_det_fderivWithin_eq_zero` for the Jacobian-vanishing
exceptional). So G5-abstract = Mathlib c-o-v + cover-additivity + the null-exceptional adapter +
finite-tree induction. All intricate-standard.

### What this buys (the down-payment)
G5-abstract is a REUSABLE lemma: "for a finite tree of C¹ charts, each InjOn off a null set, covering U
up to null, `∫⁻_U g = Σ_leaves ∫⁻ (g∘φ)|Jac|`." Its per-node hypotheses (InjOn-off-null, C¹, null-cover)
are DISCHARGED BY THE CALLER (G3's geometry: the explicit blow-up charts ARE polynomial/C¹, injective
off the exceptional, covering). So building G5-abstract NOW **reduces the general wall to G3 alone** (the
quiver strict-transform geometry: "the resolution IS such a finite tree of admissible-strata blow-ups").
RECOMMENDATION: G5-abstract is a worthwhile down-payment — genuinely separable (caller-discharged hyps),
genuinely buildable (Mathlib has the pieces, CHECKED), and it converts the wall from "two heavy pieces
(G3+G5)" to "one (G3 geometry) + a reusable lemma." It also serves the fixed-M ladder (the (2,2,2)
finite cover's `∫=Σ∫` IS a G5-instance with a concrete small tree) — so it is NOT speculative infra; the
ladder exercises it immediately.

### Residual after G5 (honest): G3 is still the wall
G3 (strict-transform tracking: the in-chart residual product re-identified as a smaller core of the
right shape, over arbitrary rank vectors) remains the genuine general-M research piece — it's the
quiver-determinantal geometry Mathlib lacks. G5-abstract does NOT dissolve G3; it ISOLATES it. The
honest general headline = ladder-proven instances + G5-abstract (buildable) + G3 (named open
obstruction).

---

## (2,2,2) EXECUTION-READY COVER — fm hand-off (the first TRUE cover + G5 down-payment) — 2026-06-21

The (2,2,2) cover designed to execution-ready: tree, 24 leaves, per-leaf `(d,k,h)`, G5-instance,
cover-completeness — all exact-symbolic / numerically-confirmed.

### The resolution tree (24 leaves, depth ≤ 3)
```
root (F = ‖AB‖², A,B ∈ 2×2, 8 vars)
 ├─ A-chart a_ij  (4 charts; A = x·Ahat, x-exceptional k=1,h=3, ratio 2; Lemma-2 unit-Jac split)
 │   ├─ E-pivot   [LEAF: x²s²·unit;  divisors x(k1,h3), s(k1,h2);            rlct 3/2]
 │   ├─ F0-pivot  [LEAF: x²s²·unit;  same;                                   rlct 3/2]
 │   └─ δ-pivot   (residual = smooth-4-block; STEP 3: blow up vertex, u-exc k=1,h=3, ratio 2)
 │       ├─ block-y0 [LEAF: x²s²u²·unit; divisors x(k1,h3), s(k1,h2), u(k1,h3); rlct 3/2]
 │       ├─ block-y1 [LEAF: same; 3/2]   ├─ block-y2 [LEAF: same; 3/2]   └─ block-y3 [LEAF: same; 3/2]
 └─ (a01, a10, a11: same 6-leaf subtree by symmetry)
```
LEAF COUNT = 4 A-charts × (2 unit-leaves + 4 block-leaves) = **24**.

### Per-leaf monomialThreshold (k=1 everywhere, pos-def-real initial forms)
- **8 unit-leaves** (4 A × {E,F0}): divisors `{x:(k1,h3), s:(k1,h2)}` ⟹ `min((3+1)/2,(2+1)/2) = 3/2`.
- **16 block-leaves** (4 A × 4 block): `{x:(k1,h3), s:(k1,h2), u:(k1,h3)}` ⟹ `min(2,3/2,2) = 3/2`.
- `⨅` over all 24 leaves = **3/2 = ½·Mval(deepest) = lambdaCore(2,2,2)** ✓.

### The G5-instance (the `∫⁻=Σ∫⁻` fm assembles)
`∫⁻_U |F|^{-c} = Σ_{i=1}^{24} ∫⁻_{V_i} |F∘φ_i|^{-c}·|Jac φ_i|`, U a nbhd of 0 in ℝ⁸. Each `φ_i` = the
composite (step1 ∘ Lemma2-change ∘ step2 [∘ step3 on δ-branch]) — an explicit POLYNOMIAL map ℝ⁸→ℝ⁸,
InjOn off its exceptional (null). This IS a G5-abstract instance (finite tree, 24 leaves, depth ≤ 3) —
so (2,2,2) doubles as G5-abstract's validate-small.

### Cover-completeness (VERIFIED, the lower-bound prerequisite)
`{AB=0} = {A=0} (null, on the exceptional) ∪ ({A≠0}∩{AB=0})`. The A≠0 part: in an A-chart, `AB=0 ⟺
Ahat·B=0 ⟺ residual (E,F0,δ)=0`, resolved by step-2/3. Numerically confirmed: 12063/12063 sampled
points near {AB=0} are leaf-reachable (the only uncovered set = `{A=0}`, null). The G5 `∫⁻=Σ∫⁻` over
the 24 leaves is VALID.

### The ONE non-mechanical part (flag for fm)
The null-exceptional handling (the G5 InjOn-off-null adapter): each `φ_i` is non-injective / Jac-vanishing
on its exceptional (a null set), excised via Mathlib's `addHaar_image_eq_zero_of_det_fderivWithin_eq_zero`.
Everything else (the 24 explicit `φ_i`, the per-leaf 3/2, the unit positivity) is mechanical.

### Bounds
UPPER: any ONE leaf (e.g. an E-pivot leaf, rlct 3/2) ⟹ rlctAt ≤ 3/2. LOWER: all 24 leaves
(every monomialThreshold = 3/2) + the cover (G5 `∫⁻=Σ∫⁻`) ⟹ rlctAt ≥ 3/2. Headline: **rlctAt(2,2,2) =
3/2**, θ=1 (the s-exceptional binds, one component).

---

## (2,1,2) PRODUCT-MIN — fm hand-off (the ladder's middle rung, NO cover) — 2026-06-21

(2,1,2) is NOT a cover-exercise (the variables separate). `F = (a₁²+a₂²)(b₁²+b₂²)`, disjoint blocks
`a=(a₁,a₂)`, `b=(b₁,b₂)`, 4 vars. The tool is the PRODUCT-MIN rule, lighter than (2,2,2).

### The lemma (product-MIN rule)
For `F(x,y) = G(x)·H(y)`, `G,H ≥ 0` continuous on DISJOINT variable blocks, each vanishing only at 0:
`rlctAt_{(0,0)}(G·H) = min(rlctAt_0 G, rlctAt_0 H)`.

### Proof (ℝ≥0∞, fm-tractable)
`∫⁻_{U×V} (G·H)^{-c} = (∫⁻_U G^{-c})·(∫⁻_V H^{-c})` [Tonelli; `(GH)^{-c}=G^{-c}H^{-c}` by `mul_rpow`].
Finite ⟺ both factors finite ⟺ `c < rlctAt G ∧ c < rlctAt H` ⟺ `c < min`. ⟹ `sSup = min`.
Mathlib: `lintegral_prod_mul` (Tonelli) + `ENNReal.mul_rpow` + a min-sSup order argument.

### THE EDGE CAUGHT (the 0·∞ trap — would have been a silent hole)
In ℝ≥0∞, `0·∞ = 0`. So "product finite ⟺ both finite" FAILS if a factor can be 0 while the other is ∞.
It does NOT bite here: `∫⁻_U G^{-c} ≥ μ(U∩{G≤1}) > 0` (positive measure near 0) ⟹ BOTH factors are in
`(0,∞]`, never 0. The lemma's hypothesis must RECORD this (factors strictly positive, automatic from
`G,H ≥ 0` vanishing only at 0). Folded in — caught before fm.

### Value + hand-off
`rlctAt(a₁²+a₂²) = rlctAt(b₁²+b₂²) = 2/2 = 1` (`smoothBlockND_rlct`, fm-2 #38, DONE) ⟹
`rlctAt(F) = min(1,1) = 1 = ½·Mval(2,1,2;deepest) = ½·2` ✓. Hand-off: product-MIN lemma (Tonelli +
mul_rpow + min-sSup + the positivity edge) + `smoothBlockND` ×2 + arithmetic `1=½·Mval`. NO blow-up, NO
cover, NO G5. Self-contained, lighter than (2,2,2).

---

## THE FIXED-M LADDER — fully designed (controller-blessed near-term path) — 2026-06-21

The three rungs are designed end-to-end, each a COMPLETE headline instance AND a distinct machinery
validate-small:
| rung | mechanism | tools | weight |
|------|-----------|-------|--------|
| (1,1,1) | monomial (already normal-crossing) | monomial_rlct / Case111Bridge (DONE) | done |
| (2,1,2) | PRODUCT-separation (disjoint blocks) | product-MIN lemma + smoothBlockND ×2 | light |
| (2,2,2) | iterated-blow-up COVER (first true cover) | G5-instance (24 leaves) + per-leaf monomial | the cover rung |
Each exercises the WHOLE chain (S1 · separation/cover · A1 · assembly) on a concrete M. The ladder is
stackable solid progress; the GENERAL-M lift sits behind G3 (roadmapped), with G5-abstract as the
buildable down-payment that (2,2,2) instantiates.

---

## A-vs-B FOR GENERAL-M + the STRAIGHT TRACTABILITY VERDICT — 2026-06-21

The controller blessed Option A for fixed-M and asked: does the residual-block layer compound the
G3/G5 wall for general M? A (monomialize the block, extra layer) vs B (handle the smooth-block leaf
directly via smoothBlockND + Fubini, no layer). Decorrelated Codex (xhigh, hypothesis withheld,
`/tmp/codex-r16c-answer.md`) + my refinement:

### The entanglement question (Codex Q1: CAN-ENTANGLE, FACT — I REFINED it)
Codex flagged (FACT): later blow-ups can make exceptional coords divide combinations defining the
terminal block ⟹ the clean Fubini split can fail. VERIFIED concretely (`/tmp/r16_entangle_test.py`:
a 2-pivot residual carries `q²` on a sub-block). **MY REFINEMENT (the useful sharpening):** the
entanglement lands at **T1 (UNIT) termini** — where the residual = monomial × (unit with constant
term, e.g. `(1+β²)+q²(…)` whose `1` dominates) — and is **HARMLESS** (it's a clean monomial×unit leaf
either way). At **T2 (SMOOTH-BLOCK) termini — the ONLY place the A-vs-B split MATTERS** — the block
coords are FRESH ratio/residual coords with the exceptional pulled OUT front (the `s²` in (2,2,2)'s
δ-leaf is outside `v²+w²+G'²+H'²`), so they're DISJOINT and the split HOLDS. (Checked on (2,2,2) +
the 2-pivot construction; the all-M version is inside G3.)

### The other three (Codex + me AGREE)
- **Q2: A compounds ONLY G5** — the block blow-up is a standard coordinate-cone (no new G3 geometry);
  it just adds leaves/depth to the gluing.
- **Q3: B-LIGHTER for general M** — B reuses `smoothBlockND_rlct` (done) + product-MIN (the (2,1,2)
  lemma, light), adds NO blow-up layer ⟹ shallower tree, fewer charts.
- **Q4: HYBRID** — default to B (Fubini split), apply the cone blow-up ONLY where entanglement occurs.
  Dominates: needs no global disjointness guarantee (handles entanglement locally).

### The verdict
1. **FIXED-M (2,2,2): Option A stays** (uniform monomial leaves, RHS literally true; already designed,
   24 leaves cheap at small M).
2. **GENERAL-M: Option B / the HYBRID** — lighter, reuses existing machinery, and the entanglement
   risk is (on my refinement) confined to harmless T1 termini; the hybrid is the safe default.
3. **Does the block layer compound the WALL? NO.** No new G3 (block = standard cone in coords); it
   compounds only G5 under A (more leaves), which B/hybrid avoids. The wall stays **G3 alone**.

### STRAIGHT GENERAL-M TRACTABILITY VERDICT (climb-or-roadmap, assessed)
- **Lower bound:** SETTLED (centers = admissible strata; no center beats the min). Not at risk.
- **G5 (c-o-v-tree gluing):** BUILDABLE down-payment (Mathlib-checked; task #52). Not the wall.
- **Block layer:** does NOT compound the wall (B/hybrid keeps it minimal).
- **G3 (explicit flag-resolution / strict-transform tracking for arbitrary M):** the GENUINE
  research-wall — ISOLATED and NAMED, not compounded by anything above. It's the quiver-determinantal
  resolution geometry Mathlib lacks.
⟹ **CLIMB** the fixed-M ladder (designed, execution-ready) **+ BUILD G5-abstract** (down-payment);
**ROADMAP G3** (the one named wall). Honest general headline = ladder instances + G5-abstract + G3 as
the named open obstruction. The general-M reach is gated on G3 alone — a clean, single, well-scoped
obstruction, which is the best possible shape for the roadmap (one wall, not a diffuse difficulty).
