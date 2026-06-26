# L3.2a — the `r²`-chart Δ-blow-up cover up to null, BUILD-READY (spec build-risk #1)

**Seat:** `pen-and-paper` (design, no Lean). **Date:** 2026-06-25. **Thread:** `28-hfin-recStep-spec`.
**Target:** de-risk the ONE HIGH-risk step (spec §"build risks" #1, L3.2a): the **`r²`-chart Δ-blow-up
cover up to null at general `r`** — the measure-theoretic cover + per-chart change-of-variables that the
`(2,2,2)` proof does for its 4 A-pivot cells (`argmaxCellOn`/`recStep`/`univ_ae_cover`/`coordZero_null`),
generalised to the `r×r` entry-pivot atlas of the radial blow-up `Δ = a·R`. Anchored on `(3,3,4)` (the
smallest binding corank-2 case); general-`r` shape stated and verified `r = 2,3`.
**Method:** exact sympy (cover/Jacobian/integrand/Schur identities) + decorrelated Codex (xhigh) red-team.
Scripts `scripts/L32a_*.py`; Codex `codex/L32a-cover-{prompt,answer}.md`.

---

## VERDICT: the `r²`-chart Δ-blow-up cover **CLOSES up to null at general `r`**, and it **IS the existing
## Lean `argmaxCellOn`/`pivotBlowupOn` machinery applied at the `r²` Δ-entry level** — no new cover
## geometry. The build needs a NEW integrand read (the loss `G` in blown-up coords) + the radial Jacobian
## read, NOT a new atlas. ONE refinement vs the #54 spec (decorrelated-Codex, exact-confirmed): the
## **second-level rank recursion is a nested minor-pivot OPEN-NEIGHBOURHOOD cover, not exact rank strata**
## (exact strata are measure-zero, illegal as integration domains).

> **The spine, in one line.** The radial blow-up map `φ_p(a, R-ratios, S) = (a·R, S)` on chart-`p` is,
> coordinate-for-coordinate, the existing `pivotBlowupOn (univ : Finset (Fin r²)) p` applied to the `r²`
> flat `Δ`-entries (identity on `S`). So `argmaxCellOn_cover`/`univ_ae_cover` (the `r²`-entry argmax)
> gives the cover-up-to-null, `pivotBlowupOnDeriv_det` gives `|det| = |a|^{r²−1}`, and `g5_pivotNode`
> gives the per-chart split — verbatim the `(2,2,2)` `recStep` infra at scale `r²`. The genuinely new
> content is (i) `G ∘ φ_p = a²·‖R·S‖²` (a degree-2 homogeneity identity, `ring`), and (ii) the inner
> `‖R·S‖²` recursion = a **nested minor-pivot cover** whose Schur complement `Sc = M22 − M21·M11⁻¹·M12`
> is the exact corank-`(r−j)` residual core (`det R = det M11 · Sc`, the Schur determinant identity).

---

## 0. Where this sits (the frame transport — read first, it is the real scope boundary)

`routeMCore M x = dlnLoss M 0 ((paramsEquivFlat M).symm x)` (`RouteMExtraction.lean:41`): the integration
variable `x` ranges over the **flat matrix-tuple entries** (`Σ_s M_s·M_{s+1}` coords), over the box
`routeMBaseNbhd M = (−1,1)^N`. The residual `Δ` and free block `S` are **NOT raw coordinates** — they
arise from the flat entries after a **frame transport** (the `NodeAchieverChart.phi`'s "Schur-frame ∘
radial blow-up"): a det-1 multiplicative shear that brings the binding node into the normal form
`F = (clean Morse spectator block) ⊕ ‖Δ·S‖²` (thread 27 cert §1; the `(4,4,2,2)` `RouteM4422` instance
realised this via the iterated-fibre route, the `(3,3,4)` anchor via the Schur frame). **This cert covers
the SINGULAR core `‖Δ·S‖²` after that transport** — the `Δ`-blow-up cover proper. The frame transport
itself (flat-entries → `(Δ,S)` normal form) is the SEPARATE `ParamsReshapeMP`/`ReducedTransport` det-1 MP
lane (`RouteMRecursion.lean:112`, banked for the value lane; reused here), NOT re-derived here. Scope kept
separate per the stage-frame discipline.

The `(3,3,4)` achiever cell core (the anchor): `‖T‖² ⊕ ‖Δ·S‖²`, `T` a clean `1×4` Morse spectator
(disjoint vars, rlct `2`), `Δ` a `2×2` residual, `S` a `2×4` free block. The singular content is the
corank-2 core `G = ‖Δ·S‖²`; everything below resolves IT.

---

## 1. THE COVER — `r²` entry-charts, complement `{Δ=0}` null (Q1 ✓, exact + Codex-CORRECT)

**The charts.** `Δ ∈ ℝ^{r×r}` is `r²` flat coords `d_{ij}`. The atlas is the `r²` entry-charts, one per
pivot `p = (i,j)`:

    chart-p  =  argmaxCellOn (univ : Finset (Fin r²)) p  =  { d | d_p ≠ 0  ∧  ∀ k, |d_k| ≤ |d_p| }
                                                            ("entry p is a max-modulus entry")

This is **verbatim** the existing `argmaxCellOn` (`S1G5Charts.lean:345`) with `active = univ`.

**The chart map.** On chart-`p`, set `a := d_p` (the scale), `R := the r×r matrix with R_p = 1,
R_k = d_k/d_p` (so `|R_k| ≤ 1`, the bounded angular matrix). Then the source map is

    φ_p (x)  =  pivotBlowupOn (univ) p x     on the r² Δ-entries   ( = a·R ),   identity on S.

i.e. `φ_p(x)_p = x_p`, `φ_p(x)_k = x_p·x_k` (`k ≠ p`) — **verbatim** `pivotBlowupOn` (`S1G5Charts.lean:384`).

**The cover-up-to-null.** `univ_ae_cover (univ) p hp` (`Case222Block.lean:41`):
`univ =ᵐ ⋃_{p∈univ} argmaxCellOn univ p`, because the complement `{∀ entry = 0} = {Δ = 0} ⊆ {d_p = 0}`,
which is `coordZero_null p`-null (`Case222Resolution.lean:663`). The omitted `{Δ=0}` is a **codim-`r²`**
null subspace; the tie loci `{|d_p| = |d_q|}` are codim-1 null hypersurfaces (`absEq_null`, already used
for `argmaxCellOn_aedisjoint`). **`coordZero_null` divides off the chart**: the coordinate that vanishes
is `d_p` (the pivot/scale `a`).

> **Verified (exact, `L32a_cover_334.py` Part A, E):** for `r = 2` (`(3,3,4)` anchor) the `4` charts
> cover `{Δ≠0}`; for `r = 3`, `9` charts. The argmax-pivot construction misses no part of any cell — every
> nonzero `d` has a max-modulus entry, and `|d_k| ≤ |d_p| ⟹ |d_k/d_p| ≤ 1`, so the bounded-ratio source
> `chartDomOn` (`{∀k≠p |R_k| ≤ 1}`) maps ONTO the full argmax cell (`pivotBlowupOn_image`, already proven).

**Codex (decorrelated, Q1) = CORRECT:** "every nonzero entry vector has a max-modulus entry; ratios lie
in `[−1,1]`; the bounded-ratio source misses no part of the argmax cell. `{Δ=0}×S` has codim `r²`, null."

---

## 2. THE PER-CHART CHANGE-OF-VARIABLES (Q2 ✓, Q4 ✓ — exact + Codex-CORRECT)

**The Jacobian.** `pivotBlowupOnDeriv_det (univ) p hp x = (x p)^(univ.card − 1) = a^{r²−1}`
(`S1G5Charts.lean:509`, `univ.card = r²`). So `|det Dφ_p| = |a|^{r²−1}`.

> **Verified (exact, `L32a_cover_334.py` Part B, E):** Jacobian `det = a³` (`r=2`), `a⁸` (`r=3`), i.e.
> `|a|^{r²−1}` — symbolic, all `r²` charts symmetric.

**The c-o-v.** Each chart-domain summand re-covers by `g5_pivotNode (univ) U (univ_ae_cover …) g`
(`S1G5Charts.lean:614`), the packaged blow-up node that discharges all six `g5_step` obligations
(`HasFDerivWithinAt`/`InjOn`-off-`{a=0}`/cover/disjoint/measurability) from the `pivotBlowupOn_*` atoms,
exactly the `NodeAchieverChart.cov` pattern (`lintegral_image_eq_lintegral_abs_det_fderiv_mul`,
`Mathlib/.../Jacobian.lean:1189`, on `V \ {a=0}` + the null-drop of `{a=0}`). **Already built.**

**The integrand after c-o-v.** `G ∘ φ_p = a²·‖R·S‖²` (degree-2 homogeneity in the scale `a`):

    |det Dφ_p|·|G∘φ_p|^{−c'}  =  |a|^{r²−1} · (a²·‖R·S‖²)^{−c'}  =  |a|^{(r²−1) − 2c'} · ‖R·S‖²^{−c'}.

> **Verified (exact, `L32a_cover_334.py` Part C, E):** `a`-degree of `G` is exactly `2`; `inner == ‖R·S‖²`
> as a polynomial identity (`r = 2, 3`). The `a`-axis is a CLEAN separate factor (a only multiplies).

**The threshold combination (Q4).** The `a`-axis is a Tonelli-separate radial factor; the chart integral
is finite iff BOTH the `a`-integral and the inner `(R,S)`-integral are finite — hence the per-chart
threshold is a **MINIMUM**:

    per-chart threshold  =  min( r²/2  [the a-divisor],  inner threshold )
    a-divisor:  ∫₀¹ |a|^{(r²−1) − 2c'} da < ∞  ⟺  (r²−1) − 2c' > −1  ⟺  c' < r²/2.

> **Verified (exact, `L32a_joint_threshold.py`):** `a`-axis finite ⟺ `c' < r²/2` (`r=2`: `2`). Codex (Q4)
> = CORRECT: "finite only if both → minimum"; "no hidden coupling between `a` and `(R,S)` except harmless
> box-bound dependence." The two Tonelli roles are kept DISTINCT: ROLE 1 (sum-integrand `(‖P‖²+W)^{−c'}`,
> rlct ADDS — `radial_morse_dominates_lt_top`/L1.1) vs ROLE 2 (product-of-separate-∫, threshold MINs).
> NO double-count.

---

## 3. THE RECURSION PLUG — nested minor-pivot cover + Schur complement (Q3 NEEDS-CARE, REFINED & closed)

This is the spec's MEDIUM-risk L2.2 + L3.2c, and the place the decorrelated Codex sharpened the design.

**Codex's refinement (Q3, exact-confirmed — adopt it).** Do **NOT** treat exact rank strata
`{rank R = j}` as integration domains: they are measure-zero, and a null locus can still control
divergence through its NEIGHBOURHOODS (`|x|^{−α}` diverges near `{x=0}` though `{x=0}` is null). Instead:

> Cover the inner `R`-space by **`j×j`-MINOR-INVERTIBLE OPEN NEIGHBOURHOODS** — a nested `argmaxCellOn`
> over the `j×j` minors of `R`, descending `j = r, r−1, …, 1`. On the neighbourhood `{minor M11 ≠ 0}`
> (a fixed invertible `j×j` block), block-Gaussian-eliminate (det-1) to the **Schur complement**
> `Sc = M22 − M21·M11⁻¹·M12`, an `(r−j)×(r−j)` matrix. The Schur determinant identity

    det R  =  det(M11) · det(Sc)                               (exact, sympy-verified r=2,3)

> makes `{det R = 0} ∩ {det M11 ≠ 0} = {det Sc = 0}` — so the residual singularity is **carried entirely
> by `Sc`**, an exact corank-`(r−j)` determinantal core. The `{all j×j minors = 0} = {rank R < j}`
> complement is the NEXT-lower level (covered at `j−1`). This is the SAME `Finset.exists_max_image` cover
> machinery, one level down — `argmaxCellOn` over minors.

**The disjoint split on the neighbourhood.** After the det-1 row/column operation,

    ‖R·S‖²  ≃  (bounded-below unit)·‖P‖²  +  ‖Sc·Q‖²            (P a jp-dim Morse block; Sc·Q the lower core)

a DISJOINT sum (Morse block ⊕ corank-`(r−j)` core), so the rlcts ADD: `jp/2 + λ_{r−j,p}`.

> **Verified (exact):** `L32a_schur_r3.py` — the `r=2` rank-1 split `‖R·S‖² = (1+v²)·‖[1,u]·S‖²`; the
> `r=3` rank-2 split `(1+α²)‖A'‖² + ((1+α²+β²)/(1+α²))‖B‖²` (positive-definite coupling Gram
> `det = 1+α²+β² > 0`); `r=3` rank-1 `‖col‖²·‖row·S‖²`. `L32a_minor_neighborhood.py` — the Schur identity
> `det R = det M11 · Sc` (`r=2,3`), the residual `(det R)²/(R00²+R10²)` corank-1 core, the nested
> minor-pivot cover. The bounded-below unit is a `positivity`/`nlinarith` fact (the `pivotF0_unit_ge_one`
> pattern, `Case222Block.lean:120`).

**The terminal leaves.** Morse blocks `‖P‖²`, `‖Q‖²`, `‖Sc·Q‖²` at corank 0 are Euclidean sum-of-squares,
discharged S2-FREE by `radial_morse_dominates_lt_top` / `sumSqND_box_lt_top` (`S1RadialMorse.lean:127,67`,
both banked sorry-free); the `a`-divisor 1-D monomial by elementary `∫ t^a dt`. **No `monomial_rlct` in the
hfin conclusion.**

**Threshold + termination (Q4, Q5 ✓).** The recursion threshold is

    λ_{r,p} = min( r²/2 ,  min_{1≤j≤r}( jp/2 + λ_{r−j,p} ) ),   λ_{0,p} = 0,

where the index `j` is the **rank-DROP** (residual corank `r−j`, NOT a stratum rank — reconciled in
`L32a_corank_reconcile.py`). `λ_{r,p} = ½·minAdm(r,r,p)` for ALL tested `(r,p)` (thread 27
`Vzero_lambda_recursion.py`, **10/10, re-confirmed here**: `(2,4)→2`, `(3,4)→4`, `(3,3)→7/2`, `(4,4)→6`,
`(2,2)→3/2`, `(2,3)→2`, `(3,2)→5/2`, …). The `(3,3,4)` cell: `‖T‖²(rlct 2) ⊕ ‖Δ·S‖²(λ_{2,4}=2)` gives
`4 = ½·minAdm(3,3,4)`. **WellFounded measure = corank `r`**, strictly decreasing (pivot `R_p = 1 ⟹
rank R ≥ 1 ⟹ r−j ≤ r−1 < r`); depth `≤ r` (`(3,3,4)`: ≤ 2). Codex (Q5) = CORRECT.

**The ambient transport (L3.2c plumbing).** Each chart's reduced core `‖Sc·Q‖²` re-enters at corank
`r−j` via the `ReducedTransport.descent` / `ParamsReshapeMP` det-1 MP reindex (`RouteMRecursion.lean:112`,
banked for the value lane) — the SAME descent carrier, here measured by corank.

**Codex (Q6) = NO fatal hole:** "the atlas-cover plus recursive Schur resolution is sound for the
upper-bound strategy. I do not see a smallest `(r,p)` where a stratum diverges below `λ_{r,p}`."

---

## 4. THE PRECISE LEAN-TARGET LEMMA STATEMENTS (for the formaliser)

The cover + per-chart c-o-v reuse EXISTING lemmas verbatim; only the integrand/recursion lemmas are new.

### (existing — reuse, do NOT rebuild)
- `univ_ae_cover (active) (p) (hp) : univ =ᵐ ⋃_{q∈active} argmaxCellOn active q` — `Case222Block.lean:41`.
- `recStep (active) (p) (hp) (L) (hL) (h) : ∫⁻_L h = ∑_{q∈active} ∫⁻_{chartDomOn active q \ pivotZeroOn q}
  |det(pivotBlowupOnDeriv active q)|·L.indicator h (pivotBlowupOn active q)` — `Case222Block.lean:56`.
- `pivotBlowupOnDeriv_det (active) (p) (hp) (x) : det = (x p)^(active.card − 1)` — `S1G5Charts.lean:509`.
- `g5_pivotNode (active) (U) (hUcov) (g) : ∫⁻_U g = ∑_{p∈active} ∫⁻_{Vp\Zp} |det φ_p'|·g(φ_p)` —
  `S1G5Charts.lean:614` (the packaged node; the `NodeAchieverChart.cov` pattern).
- `coordZero_null (p) : volume {x | x p = 0} = 0` — `Case222Resolution.lean:663`.
- `radial_morse_dominates_lt_top` / `sumSqND_box_lt_top` — `S1RadialMorse.lean:127,67` (banked, S2-free).
- Mathlib `lintegral_image_eq_lintegral_abs_det_fderiv_mul` — `Jacobian.lean:1189` (CONFIRMED exists).

### (NEW — build, in dependency order)

**N1. `radialBlowup_loss_factor` (the integrand identity, LOW risk — `ring`).** On chart-`p`, `G∘φ_p` is
`a²·‖R·S‖²`. State it as the degree-2 homogeneity of the determinantal core under the `pivotBlowupOn`
scale; proved by `ring` after expanding `‖(a·R)·S‖² = a²·‖R·S‖²` (sympy-pinned, `L32a_cover_334.py` C).
```
theorem radialDelta_loss_factor {r p : ℕ} (a : ℝ) (R : Matrix (Fin r) (Fin r) ℝ)
    (S : Matrix (Fin r) (Fin p) ℝ) :
    ‖(a • R) * S‖_F²  =  a^2 * ‖R * S‖_F²
```
*(`‖·‖_F²` = the entrywise `∑ (·)²` Frobenius square, the `frobSq` of `MatMulFibre`. Build risk LOW.)*

**N2. `schur_minorPivot_split` (the rank recursion's per-neighbourhood split, MEDIUM risk).** On the
minor-invertible neighbourhood `{det M11 ≠ 0}` (`M11` a chosen `j×j` block), the disjoint Morse ⊕
Schur-complement split. State it via the EXPLICIT block identity (NOT abstract LU), per the `(3,3,4)`
`loss_schur_blowup_factor` pattern + the Schur determinant identity:
```
theorem schur_minorPivot_split {r p : ℕ} (R : Matrix (Fin r) (Fin r) ℝ) (j : ℕ) (hj : j ≤ r)
    (M11inv : (R.minor_topLeft j).det ≠ 0) (S : Matrix (Fin r) (Fin p) ℝ) :
    ∃ (unit : ℝ) (hunit : 0 < unit) (P : Matrix (Fin j) (Fin p) ℝ)
      (Sc : Matrix (Fin (r-j)) (Fin (r-j)) ℝ) (Q : Matrix (Fin (r-j)) (Fin p) ℝ),
      ‖R * S‖_F²  =  unit * ‖P‖_F²  +  ‖Sc * Q‖_F²   ∧   R.det = (R.minor_topLeft j).det * Sc.det
```
*(The `unit` is `positivity`/`nlinarith`; the split + `det R = det M11 · Sc` are `ring`/Schur-identity,
sympy-pinned `L32a_minor_neighborhood.py`. The minor-pivot cover over `j×j` minors reuses
`argmaxCellOn`/`exists_max_image` at the minor level. Build risk MEDIUM — the matrix-algebra heart; the
`(3,3,4)` `r=2` case is `ring`-clean, `r≥3` needs the block-Gauss det-1 shift bookkeeping.)*

**N3. `radial_loss_chart_lt_top` (the per-chart finiteness, MEDIUM).** Wiring N1+the existing c-o-v+the
threshold MIN: on chart-`p`, the integral is finite for `c' < min(r²/2, inner)`. The `a`-axis 1-D monomial
(elementary) × the inner (N2 + recurse).

**N4. `routeMCore_threshold_lt_top` (the hfin conclusion = L3.1, HIGH — the assembly).** The WellFounded-
on-corank recursion (measure = corank, N2 strictly drops it) summing N3 over the `r²` charts (via
`recStep`/`g5_pivotNode`), terminating at the Morse/monomial leaves; discharges `hfin`. Mirrors
`myF222_threshold_lt_top'` at scale `r²` with depth ≤ `r`.

### Build risks (RANKED, refined)
1. **(HIGH) N4 — the depth-`r` WellFounded recursion assembly.** The corank-measured `recStep` recursion
   bookkeeping (nested minor-pivot cover at each level). Mitigation: ship the `(3,3,4)` depth-2 instance
   FIRST (corank-2, ONE nested level — the smallest binding case), then lift to general `r`. The
   `(4,4,2,2)` corank-2 leaf is the depth-≤2 warm-up (already closed via the iterated-fibre special-class
   route, S2-free — a sanity anchor, not this route).
2. **(MEDIUM) N2 — `schur_minorPivot_split` + the minor-pivot cover.** Codex's sharpest point: state it as
   OPEN minor-invertible neighbourhoods, NOT exact rank strata. The `r=2` case is `ring`-clean; the
   general block-Gauss det-1 shift is the genuine matrix algebra. Mitigation: explicit block identity
   (sympy-transcribed), Schur determinant identity for the corank-drop bookkeeping.
3. **(LOW) N1 `radialDelta_loss_factor`** — `ring`. **N3** — wiring + elementary 1-D monomial.

---

## 5. S2-hygiene (unchanged — zero new axioms)

The hfin CONCLUSION (`∫|F|^{−c'} < ⊤`) is proven **S2-FREE**: all Morse leaves
(`radial_morse_dominates_lt_top`), the `a`-divisor 1-D monomial (elementary `∫ t^a dt`), the Tonelli
factorisations, the Schur splits, the radial Jacobian dets. `monomial_rlct` (S2) enters ONLY in the
leaf-SUM side the hfin hypothesis quantifies — the SAME S2 use the headline already rides. **No NEW
citation**; `#print axioms` stays `[propext, Classical.choice, Quot.sound, monomial_rlct]`.

---

## 6. Close (the discipline trio)

- **Firmest result.** The `r²`-chart Δ-blow-up cover **closes up to null at general `r`**, IS the existing
  `argmaxCellOn`/`pivotBlowupOn` infra at the `r²` entry level, with `|det| = |a|^{r²−1}` and `G∘φ =
  a²·‖R·S‖²` (exact, `r=2,3`; `(3,3,4)` anchor full). The inner recursion is a nested minor-pivot OPEN-
  neighbourhood cover with the Schur complement carrying corank-`(r−j)` (exact Schur determinant
  identity). Threshold `λ_{r,p} = ½·minAdm` (10/10). Decorrelated Codex: cover/c-o-v/threshold/termination
  CORRECT, no fatal hole, Q3 refined.
- **Most likely to break it (the fragile step, Codex + my read).** N2 — making the rank recursion an
  ACTUAL local finite measurable cover with the uniform comparison `‖RS‖² ≃ unit·‖P‖² + ‖Sc·Q‖²` on the
  minor-invertible neighbourhood (NOT exact rank strata). The block-Gauss det-1 bookkeeping for `r ≥ 3` is
  the genuine matrix-algebra risk; the bounded-below `unit` must be `positivity`-clean on the bounded
  chart.
- **Next construction / consult to settle the open part.** Build N4 on the `(3,3,4)` depth-2 instance
  first (corank-2, one nested minor-pivot level) — it exercises the full recursion at minimal corank and
  is the direct lift of `myF222_threshold_lt_top'`. The remaining open question for a follow-up consult:
  the exact Lean shape of the **nested minor-pivot cover** (an `argmaxCellOn` over `Finset` of `j×j`
  minors) — confirm `Finset.exists_max_image` over minors discharges the second-level `univ_ae_cover`
  analog cleanly, the one piece not yet a verbatim reuse.
