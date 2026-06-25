# R1 hfin recursive-cover SPEC — build-ready lemma families for the formaliser

**Seat:** `pen-and-paper` (design). **Date:** 2026-06-24. **Thread:** `28-hfin-recStep-spec`.
**Goal:** the build-ready design of the hfin (upper-bound `cover_le`) recursive coupled cover, as three
precise Lean-target lemma families for `r1-node-bundle`, building on the existing `Case222CoverGETail`
+ `NodeAchieverChart` + `radial_ball_iff` machinery. The MATH is validated S2-only (thread 27
`Vzero-termination-cert.md`, decorrelated-Codex-survived). This is the spec, NOT the build.

**The target.** `hfin` (`routeMLayerCover_of_atoms`, `RouteMLayerCover.lean:180`): `∀ c', (leaf-sum
< ⊤) → ∫_{routeMBaseNbhd} |routeMCore M|^{−c'} < ⊤`, i.e. `c' < ½·minAdm M ⟹ ∫ |F|^{−c'} < ⊤`. The
existing `(2,2,2)` proof of the analog (`myF222_threshold_lt_top'`) is the **template**: it works by
`recStep` over the 4 A-pivot cells, each bounded; we generalise that to all `M` with the
rank-stratified resolution.

**Existing anchors (real signatures, build ON these).**
- `recStep {N} (active) (p) (hp) (L) (hL) (h) : ∫⁻_L h = ∑_{q∈active} ∫⁻_{chartDomOn active q \
  pivotZeroOn q} |det(pivotBlowupOnDeriv active q)| · L.indicator h (pivotBlowupOn active q)`
  (`Case222Block.lean:56`) — the per-pivot integral-split unit, ALREADY general-`N`, reusable.
- `radial_ball_iff (m) (R s) (hR) : IntegrableOn (‖·‖^s) (ball 0 R) ↔ −(m+1) < s`
  (`S1SmoothBlock.lean:78`) — the **S2-FREE** Euclidean Morse terminal.
- `sumSq4_box_lt_top`/`euclid4_ball_integrable` (`Case222CoverGETail.lean`) — the `(2,2,2)` instance of
  a Morse leaf bounded S2-free; the pattern to generalise to arbitrary Morse dimension.
- `NodeAchieverChart M` (`NodeAchieverChart.lean`) — the per-cell chart bundle (`phi`, pivot `p`,
  `leafH` with `leafH p = minAdm M − 1`, `Ufun`, `cov`, `leaf_integrand`); the `(4,4,2,2)` instance is
  `RouteM4422`. The hfin cover REUSES this for the per-cell TOP chart.
- S2 = `monomial_rlct (d) (k h)` (`Skeleton.lean:120`): the normal-crossing monomial threshold +
  order. The ONLY permitted cite.

---

## Lemma family 1 — the radial disjoint-sum lemma (S2-FREE; the GLUE, build FIRST)

**Mathematical content (verified, thread 27 `Vzero_threshold_tie.py` + the (2,2,2) `sumSq4` precedent).**
The recursion glues a Euclidean Morse block `‖P‖²` (disjoint variables) onto a lower core `H(z)` by
the additive rule `rlct(‖P‖² + H) = ½·dim(P) + rlct(H)`. At the integral level (what hfin needs — a
finiteness transfer, not an rlct equality), the load-bearing statement is the **finiteness form**:

### L1.1 `radial_morse_disjoint_lt_top` (the core glue lemma)
> For `P : Fin n → ℝ` (the Morse block, `n ≥ 1`) and `z : Fin m → ℝ` (disjoint), a measurable
> `H : (Fin m → ℝ) → ℝ≥0∞` (the lower-core integrand `|G(z)|^{−c'}`), a box `B_P × B_z`, and `c' ≥ 0`:
>
>     (∫⁻_{B_z} H < ⊤) ∧ (c' < n/2)  →  ∫⁻_{B_P × B_z} (‖P‖² + (G z))^{−c'} ... 
>
> — more precisely, the form the recursion produces is `(Σ_i P_i² + W(z))^{−c'}` with `W ≥ 0`; the
> clean finiteness statement is: **if `c' < n/2` then for every fixed `z`, `∫_{B_P} (‖P‖²+W)^{−c'} dP ≤
> ∫_{B_P} ‖P‖^{−2c'} dP =: K_n(c') < ⊤` (a CONSTANT independent of `z`, since `W ≥ 0` only helps), and
> Tonelli gives `∫_{B_P×B_z} (‖P‖²+W)^{−c'} ≤ K_n(c') · vol(B_z) < ⊤`.**

The cleanest Lean target (avoids needing `rlct` of the sum — pure finiteness, which is all hfin uses):

```
theorem radial_morse_dominates_lt_top {n m : ℕ} (hn : 1 ≤ n) (c' : ℝ) (hc' : c' < n/2)
    (T : ℝ) (hT : 0 < T) (W : (Fin m → ℝ) → ℝ) (hWnn : ∀ z, 0 ≤ W z) (hWmeas : Measurable W) :
    ∫⁻ p in boxT n T, ∫⁻ z in boxT m T,
      ENNReal.ofReal ((∑ i, (p i)^2 + W z) ^ (-c')) ∂vol ∂vol
    ≤ ENNReal.ofReal (Kbound n c' T) * (vol (boxT m T))
```
where `Kbound n c' T = ∫_{boxT n T} ‖p‖^{−2c'}` (finite by `radial_ball_iff`, `−2c' > −n`).

**Why S2-FREE:** the inner `∫_{B_P} (‖P‖²+W)^{−c'} dP ≤ ∫_{B_P} ‖P‖^{−2c'} dP` (monotone, `W≥0`) is a
Euclidean radial integral — `radial_ball_iff (n−1) R (−2c')`, finite iff `c' < n/2`. NO monomial / S2.

**Proof sketch (Lean):** (a) pointwise `(‖P‖²+W)^{−c'} ≤ (‖P‖²)^{−c'} = ‖P‖^{−2c'}` for `c'≥0, W≥0`
(`Real.rpow_le_rpow_of_nonpos` on the base, since `‖P‖² ≤ ‖P‖²+W`); (b) `∫_{B_P} ‖P‖^{−2c'} dP < ⊤` via
`sumSq4_box_lt_top`'s pattern generalised to dim `n` (transport to `EuclideanSpace ℝ (Fin n)`,
`PiLp.volume_preserving_toLp`, ball domination, `radial_ball_iff (n−1)`); (c) Tonelli
(`lintegral_lintegral` / `setLIntegral_prod`) factors the product, pulling the `z`-independent `Kbound`
out. **All Mathlib + the existing `sumSq4` pattern; no new analytic axiom.**

**Build risk (LOW):** generalising `sumSq4_box_lt_top` from `Fin 4` to `Fin n` is a parametric
re-proof of an existing lemma — mechanical. The Tonelli factorisation is standard. This is the
SAFEST of the three families; build it first as the reusable terminal.

---

## Lemma family 2 — the rank-stratified Schur normal form (the per-stratum reduction)

**Mathematical content (verified, thread 27 `Vzero_224_full.py`, `Vzero_rankdrop_recurse.py`).** At a
corank-`r` cell the binding core is `G = ‖Δ·S‖²` (`Δ : r×r` residual, `S : r×p` free). The resolution:
radial `Δ = a·R` (`a` scale, `R` the bounded affine-chart `r×r` with one pivot entry `= 1`, Jacobian
`|a|^{r²−1} ≠ 0` off `{a=0}`), then `G = a²·‖R·S‖²`; on the rank-`j` stratum of `R`, after a Schur
(LU/Gauss) normal form, `‖R·S‖² ≃ ‖P‖² + ‖B·Q‖²` with `P : j×p` (full-rank Morse block), `B·Q` the
corank-`(r−j)` residual core. The variable groups are DISJOINT after the (det-1) Schur shift.

### L2.1 `radialBlowup_det` (the radial Jacobian)
```
theorem radialDelta_abs_det {r : ℕ} (a : ℝ) (R : Matrix (Fin r) (Fin r) ℝ) :
    -- the map (a, R-free) ↦ (a • R) on the r×r entries, pivot entry fixed = 1
    |det (D(radialDelta r))| = |a| ^ (r^2 - 1)
```
(the `(3,3,4)` analog `phi334_abs_det = |u₀|⁷·|u₁|²` generalised; verified `det = a^{r²−1}` for
`r = 2,3` in `Vzero_general_corank.py`). Reuses the `pivotBlowupOnDeriv` det machinery
(`Case222Block`'s `tailLift_step2E_det` pattern: a codim-`(r²−1)` blow-up determinant).

### L2.2 `schur_rank_stratum_normal_form` (the Morse ⊕ lower-core split)
```
theorem schur_rank_stratum {r p : ℕ} (R : Matrix (Fin r) (Fin r) ℝ) (j : ℕ) (hj : R.rank = j)
    (S : Matrix (Fin r) (Fin p) ℝ) :
    -- after a det-1 Schur (LU) change of S-coords + the unit row/col frames,
    ∃ (P : Matrix (Fin j) (Fin p) ℝ) (B : Matrix (Fin (r-j)) (Fin (r-j)) ℝ) (Q : Matrix (Fin (r-j)) (Fin p) ℝ),
      ‖R * S‖² = (unit:bounded-below) * ‖P‖² + ‖B * Q‖²    -- the disjoint Morse ⊕ lower-core
```
Verified concretely (`Vzero_rankdrop_recurse.py`): corank-2 rank-1 → `(1+c²)·‖[1,b]S‖²` (Morse-coeff ×
1×p core); corank-3 rank-2 → corank-2 residual; rank-1 → `‖col‖²·‖row·S‖²`. The `unit` (e.g. `1+c²`,
`1/(1+v²)`) is a bounded-below polynomial on the chart (the `a²·[(1+v²)‖P'‖² + (e²/(1+v²))‖Q‖²]` form,
`Vzero_224_full.py`).

**Build risk (MEDIUM):** the Schur LU normal form on the rank-`j` stratum + tracking the det-1 shifts
is genuine matrix algebra in Lean (Mathlib has `Matrix.rank`, LU is partial). The per-stratum identity
is `ring`-provable once the block decomposition is set up (as `(3,3,4)`'s `loss_schur_blowup_factor`
was). The bounded-below unit is a `nlinarith`/`positivity` fact (the `Uval334_ge_sq` pattern).

---

## Lemma family 3 — the recStep recursion skeleton (the COVER ASSEMBLY, the long pole)

**Mathematical content.** Generalise `myF222_threshold_lt_top'`: cover `routeMBaseNbhd M` by `recStep`
over the pivot-rank cells, recurse on the reduced core, terminate at smooth/Morse leaves; depth ≤
corank (bounded). The recursion threshold `λ_{r,p} = min(r²/2, min_j(jp/2 + λ_{r−j,p}))` reproduces
`½·minAdm` exactly (thread 27 `Vzero_lambda_recursion.py`, 10/10).

### L3.1 `routeMCore_threshold_lt_top` (the general-M finiteness — the hfin conclusion)
```
theorem routeMCore_threshold_lt_top (M : Fin (L+1) → ℕ) (c' : NNReal) (hc' : (c':ℝ) < ½·minAdm M) :
    ∫⁻ x in routeMBaseNbhd M, ENNReal.ofReal (|routeMCore M x| ^ (-(c':ℝ))) < ⊤
```
This DIRECTLY discharges `hfin` (via `routeMLayerCover_of_atoms`'s `hfin` field: leaf-sum finite ⟹
`c' < ½·minAdm` by `layerCover_exists_thresholdLe_iff_half_le`-style, then this). It is the exact
general-M analog of `myF222_threshold_lt_top'`.

### L3.2 the recursion structure (the WellFounded.fix carrier)
A recursion on the corank-stratified cells, mirroring `recStep` + the `Case222CoverGETail` p-cell sum:
```
-- at a cell with core G = ‖Δ·S‖² (corank r):
-- 1. recStep over the r² pivot charts of the Δ-blow-up (g5_pivotNode / argmaxCellOn cover up to null);
-- 2. on each chart, radialDelta_det (L2.1) pulls |a|^{r²−1}; G = a²·‖R·S‖²;
-- 3. stratify by rank R = j (schur_rank_stratum, L2.2): Morse block ‖P‖² ⊕ lower core ‖B·Q‖²;
-- 4. the a-axis: ∫ |a|^{r²−1}·(a²·I)^{−c'} da < ⊤ for c' < (r²)/2 ... ≥ ½·minAdm (a-divisor never binds
--    below threshold) -- a 1-D monomial integral (abs_rpow_lintegral_Icc_lt_top, ALREADY in CoverGETail);
-- 5. the inner I = ‖P‖² ⊕ ‖B·Q‖²: radial_morse_dominates_lt_top (L1.1) peels ‖P‖² (Morse, S2-free),
--    RECURSE on ‖B·Q‖² (corank r−j < r) -- WellFounded on corank;
-- 6. terminate at corank 0 (pure Morse, radial_ball_iff) -- depth ≤ r.
```
The WellFounded measure is the **corank** (strictly decreasing, L2.2); the `chainRel_wf`/`redM_chainRel`
pattern (`RouteMRecursion.lean`) is the analog carrier (there on `ΣM`; here on corank).

**Build risk (HIGH — this IS the long pole).** The per-cell measure-theoretic assembly: (a) the `r²`-chart
cover of the Δ-blow-up up to null (generalise `univ_ae_cover` / `argmaxCellOn_cover` from the
`(2,2,2)` A-pivot to the `r×r` entry-pivot atlas — `coordZero_null` for the divisor); (b) the
change-of-variables on each chart (`lintegral_image_eq_lintegral_abs_det_fderiv_mul` + the
radialDelta det, the `NodeAchieverChart.cov` pattern); (c) the WellFounded recursion bookkeeping (the
reduced core's ambient reindex — the `ReducedTransport`/`ParamsReshapeMP` pattern, det-1 MP). The
ε-uniformity + the box-vs-ball domination (the angular `R`-chart bounded, thread 27
`Vzero_chart_bounded.py`) are the analytic plumbing the `(2,2,2)` proof already exercises at depth 2.

---

## Dependency order (build sequence for the formaliser)

1. **L1.1 `radial_morse_dominates_lt_top`** (S2-FREE, LOW risk) — the reusable terminal; generalise
   `sumSq4_box_lt_top` to `Fin n` + the `W≥0` domination + Tonelli. Build FIRST (everything else
   consumes it at the leaves).
2. **L2.1 `radialDelta_abs_det`** (LOW-MEDIUM) — the radial Jacobian `|a|^{r²−1}`; reuse the
   `pivotBlowupOnDeriv` det pattern. Banks the per-cell Jacobian.
3. **L2.2 `schur_rank_stratum`** (MEDIUM) — the Morse ⊕ lower-core split; the matrix-algebra heart.
4. **L3.2 the recursion carrier** (corank WellFounded) — the skeleton; reuse `recStep` +
   `chainRel_wf` pattern.
5. **L3.1 `routeMCore_threshold_lt_top`** (HIGH, the assembly) — wires 1–4 into the hfin conclusion,
   mirroring `myF222_threshold_lt_top'`. Discharges `hfin`.
6. **wire into `routeMLayerCover_of_atoms`** — `hfin := routeMCore_threshold_lt_top` (+ the leaf-sum ⟹
   `c' < ½·minAdm` premise reduction, the `layerCover_exists_thresholdLe_iff_half_le` analog for the
   `<` direction). Then `cover_ge_div := layerCover_hdiv` (the closed `φ_M` lower atom) closes the FULL
   `IsRouteMCover`, hence `resolution_charts`, hence the headline (S2-only).

## S2 vs S2-FREE leaf classification (the axiom hygiene)

- **S2-FREE (no `monomial_rlct`):** ALL the Morse leaves (`radial_ball_iff` / `radial_morse_dominates`),
  the a-divisor 1-D monomial finiteness (`abs_rpow_lintegral_Icc_lt_top`, elementary `∫ t^a dt`), the
  Tonelli factorisations, the disjoint-sum domination, the radial Jacobian dets, the Schur normal form.
- **S2 (`monomial_rlct`):** ONLY where a genuine product-monomial threshold is read — in the LEAF-SUM
  side (the `monomialIntegrand` model the hfin hypothesis quantifies), which is the SAME S2 use the
  headline already rides (`layerCover` value lane). The hfin CONCLUSION (`∫|F|^{−c'} < ⊤`) is proven
  **S2-FREE** by the resolution above. **No NEW citation.** (The a-divisor's threshold `r²/2 ≥ ½·minAdm`
  is an arithmetic fact, not S2 — the 1-D integral is elementary.)

So the hfin cover adds **zero** new axioms: `#print axioms` stays `[propext, Classical.choice,
Quot.sound, monomial_rlct]`.

## Load-bearing build risks (ranked) + mitigations

1. **(HIGH) The `r²`-chart Δ-blow-up cover up to null at general `r`** (L3.2a). The `(2,2,2)` proof
   covers the 4 A-pivot cells via `argmaxCellOn`; the general `r×r` entry-pivot atlas is the same idea
   at scale `r²`. Mitigation: ship `(4,4,2,2)` (corank-2 leaf, the `RouteM4422` cell) FIRST as the
   depth-≤2 instance — it exercises the full recursion at minimal corank, then lift to general `r`.
2. **(MEDIUM) The Schur LU normal form on the rank-`j` stratum** (L2.2). Mathlib's LU is partial;
   the explicit block factorisation may need a hand `ring` proof per the `(3,3,4)`
   `loss_schur_blowup_factor` pattern. Mitigation: prove it as the explicit `‖R·S‖² = unit·‖P‖² +
   ‖B·Q‖²` identity (sympy-verified, transcribe to `ring`), not via abstract LU.
3. **(MEDIUM) The WellFounded recursion on corank + the reduced-core reindex** (L3.2c). Reuse the
   `ReducedTransport` + `ParamsReshapeMP` (banked, det-1 MP) — the same descent the value lane uses.
4. **(LOW) Generalising `sumSq4_box_lt_top` to `Fin n`** (L1.1). Mechanical parametric re-proof.

## What is VALIDATED (the math) vs the BUILD (this spec)

- **Validated S2-only (thread 27, exact + Codex-survived):** the resolution terminates at monomial(S2)/
  Morse(S2-free) leaves, depth ≤ corank, threshold `λ_{r,p} = ½·minAdm(r,r,p)` (10/10), the per-cell
  upper bound holds, the bounded angular chart. NO non-S2 cite.
- **This spec:** the precise Lean targets + dependency order + risks. NOT built (no Lean here).
- **The honest residual:** the depth-`r` measure-theoretic cover assembly is the genuine remaining R1
  effort — large but BOUNDED, with the `(2,2,2)` depth-2 proof as a complete worked template and the
  `(4,4,2,2)` as the recommended first general-`L≥3` instance.
