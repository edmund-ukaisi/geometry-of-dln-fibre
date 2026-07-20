# Cert D3 — coverage-theorem design (the named hard part) (covdesign-t02)

**Seat:** pen-and-paper (obstruction-first design). **Date:** 2026-07-17.
**Map node:** `coverage-theorem` ("charts cover; no untracked chart has a smaller ratio", no `rlct=c*`).
**Method:** the paper's Cases 1(1)/1(2)/2 (worked-tex §ssec:blowup) + the banked cover→value chain
(verify-r1-135) + exact kill-condition enumeration (`/tmp/d3_coverage_killcheck.py`, Newton-LP
`battery-drafts/_rlct.py`) + one decorrelated Codex consult (`codex/coverage-design-{prompt,answer}.md`,
gpt-5.6-sol xhigh, my conclusion withheld). NO Lean, NO `rlct=c*`.

---

## VERDICT: coverage is REACHABLE (not walled). The hard part is a DILIGENT CONSTRUCTION — the general-M
## atlas WITH sharing data + a per-blow-up local covering lemma — not a missing exhaustiveness theorem.

The no-smaller-ratio (≥) leg splits ASYMMETRICALLY (verify-r1-135, re-confirmed): it is **automatic** from
`minAdm = inf_{admissible t} Mval(t)` (`inf'_le`), needing NO surjectivity. The genuine new content is the
**covering** leg — that the emitted chart family covers a neighborhood of the origin — and Codex sharpened
where its difficulty lives: NOT in the symbolic case-split (which is trivially exhaustive), but in a
**per-blow-up local covering lemma** that identifies the standard affine charts of each blow-up with the
stated 1(1)/1(2)/Case-2 children, threading the exact monomial (diag(b)) support. This matches the
predecessor certs: "the routeStep sorry is the constructive READ, not an open theorem."

---

## 1. The chart-family exhaustiveness mechanism (the controller's questions, answered)

**(a) Why branching on the b-multiplicity pattern exhausts — and the correction.** At node `(S,J)` the equal
run of `b_{J+1},…,b_{M(S)}` above `J` has some length `r`; either `r < M(S)-J` (Case 1, partial) or
`r = M(S)-J` (Case 2, full). This is a complete dichotomy **of symbolic states** — necessary but, per Codex
(decorrelated), NOT sufficient for GEOMETRIC coverage. The load-bearing step is a **local covering lemma**:
the blow-up of the center with local ideal `(g_1,…,g_d)` is covered by the standard affine charts
`U_i : g_j = g_i z_j` (`i=1..d`), and a *support-preserving* calculation must exhibit each `U_i` as exactly
one stated child — 1(1) when the `d`-block acquires an EXISTING exceptional factor `u` (divisibility **in the
local coordinate ring**, not a pointwise test), 1(2)/Case-2 when a NEW pivot coordinate is introduced.
Coverage is then: outside the center the blow-up is an isomorphism; over it the `U_i` cover the projective
exceptional fibre; induction over the finite `(S,J)` tree lifts this to a global cover of a neighborhood.

**(b) Where covering/properness comes from, per blow-up and globally.** Per blow-up: a smooth center gives a
proper modification whose standard charts `U_i` cover it (the local covering lemma). Globally: compose the
per-node covers up the finite tree; properness supplies compact preimages / finite subcovers. Properness
alone does **not** give the child formulas or their exhaustiveness — that is the support-preserving
calculation (the new content).

**(c) The residual claim at the box boundary.** Two disposals, both banked-adjacent: (i) the FAR points
(bounded away from `0`) reduce to the resolved neighborhood by the **homogeneity scaling identity**
`I_B(c') = ρ^{2Lc'-N} I_{ρB}(c')` (F degree-`2L` homogeneous; exact CoV; cf. cert-d2 §3) — no boundary chart
needed; (ii) the measure-zero chart-overlap / coordinate-hyperplane slices are disposed by the banked null
covers (`RouteMNullSliceCov`, `S1BoxAdditive`). The non-origin *singular* points inside the neighborhood are
NC-chart interior points (Codex Q3: a further blow-up of an already-NC chart gives a ratio that is a
weighted average of existing ratios + a nonnegative transverse term — never a NEW smaller ratio), so they
need no separate check once the neighborhood is NC-resolved.

## 2. The exact statement decomposition (per-blow-up covering lemma + ledger induction)

Codex's structure, which I adopt: a **per-blow-up LEDGER induction nested inside the well-founded `(S,J)`
induction**. State to carry at each node: residual reduced widths + the branch rank profile + **the exact
symbolic divisor support of every generator (which exceptional coords, with multiplicity, divide which
generator) and the sharing relations** — Aoyagi's `diag(b)`, up to unit equivalence. Per node:
1. **Local covering lemma** (NEW, load-bearing): standard charts `U_i` of the chosen blow-up ↔ stated
   children (support-preserving); union covers the node's neighborhood.
2. **Support transport** (NEW): old divisors → their strict transforms; ADD every irreducible component of
   the new exceptional divisor; the sharing relations propagate (the 1(1) exponent-merge `M'_{s,k} =
   M_{s,k} + J_1(M^{(S+1)}-J)` / the Case-2 exponent `(M(S)-J)(M^{(S+1)}-J)`).
3. **Termination** (banked/adjudicated: `monomialization-termination`): the `(S,J)` recursion ends at
   `S=L+1` in a full monomial diagonal (NC).
4. **Threshold ledger** (banked: `RouteMLayerSplit`, Lemma-3 bridge / `exponent-ledger-bridge`): each
   terminal divisor's ratio `= (ord_D Jac + 1)/ord_D F = Mval(t)/2`.
5. **Assembly given the atlas** (banked): cover + ratios ⟹ `∫_box F^{-c'} ≤ Σ_charts (chart integral) < ⊤`
   for `c' < ½ minAdm` (`resolution_value_of_atlas`, `routeM_rlctAtOn_eq_iInf`,
   `foldFamily_iInf_eq_half_minAdm`).

**Global vs per-blow-up:** the covering is PER-BLOW-UP (local lemma) + INDUCTION, not one global surjectivity
argument (Codex confirms; verify-r1-135's asymmetric split confirms the ≥-leg needs no global surjectivity).

## 3. Genuinely NEW vs banked

- **NEW (the reconstruction):** (i) the **per-blow-up local covering lemma** (charts `U_i` ↔ stated
  children, support-preserving) — the honest new content Codex isolated; (ii) the **general-M constructive
  atlas / read** (`routeStep` for arbitrary non-leaf `M`) carrying the symbolic support field
  (`support : Gen → Finset DivVar`, verify-r1-diagb-334 §3); (iii) the covering-composition up the tree
  (generalising the fully-proven `Case222RouteMCover` atoms).
- **BANKED (consume, never rebuild):** the ≥-leg no-undershoot (`minAdm_le_Mval_toNat`,
  `PivotWitness.minAdm_le`); the achiever tie (`CascadeAchiever`, `RealizesAchiever.ofAdm`); the value fold
  given an atlas (`resolution_value_of_atlas`, `routeM_rlctAtOn_eq_iInf`, `foldFamily_iInf_eq_half_minAdm`);
  the box-cover / null atoms (`S1Cover`, `RouteMCoverLemmas`, `S1BoxAdditive`, `RouteMNullSliceCov`); the
  per-node squeeze (`schur_recursion_step_squeeze`); the exponent ledger (`RouteMLayerSplit`,
  `MinAdmMono`, Lemma-3); the worked precedent (`RouteMBoxThresholdRR4`, `Case222RouteMCover`, 0-sorry).

## 4. The kill-condition for MY design, and the check (EXACT)

**Kill-condition (named):** the emitted chart family (a) fails to cover a neighborhood — a point near `0` in
no chart — OR (b) contains/invents a divisor with ratio `< ½ minAdm(M)`. By the local-covering-lemma
structure, (a) reduces to a chart `U_i` NOT matching any stated child; (b) reduces — SHARPLY, per Codex — to
**mis-tracking the sharing support** (conflating separate divisor variables, or independentising shared
ones), which invents a spurious low-ratio divisor.

**Check 1 — rank-profile exhaustiveness (no undershoot).** `/tmp/d3_coverage_killcheck.py`, EXACT integers,
on `(2,2,2)` [full], `(2,2,3)`, `(3,3,4)`, `(2,2,2,2)`: the tracked family `Adm(M)` achieves
`min codim = minAdm`; every ratio `≥ ½ minAdm`; and the RELAXED search (drop weak-decrease) finds ZERO
profiles with `codim < minAdm` — undershooting the `Mval` formula requires a negative gap factor
`(t_{j-1}-t_j) < 0`, i.e. rank INCREASING along the chain, which is impossible (product rank ≤ each factor's
rank). **Kill-condition (a)/(no-undershoot) NOT triggered.**

**Check 2 — sharing-support kill (the sharp one, Codex Q4, EXACT via Newton-LP).**
- `(2,2,1)`, corank-2 `J=0` branch, residual `(d_1 x, d_2 y)`, `b=(d_1,d_2)`, `minAdm=2`, `½minAdm=1`:
  CORRECT (separate supports) `rlct⟨d_1x,d_2y⟩ = 1 = ½minAdm`; CONFLATED (forget supports) `rlct⟨dx,dy⟩ =
  1/2 < 1` — **a spurious low-ratio divisor**. Verified exact.
- `(3,3,4)`, `t=(1,0)` binding, corank-2 `Δ`-block: TRUE (shared `Δ`) `rlct = 4 = ½minAdm`;
  independentised (per-row scalars) gives `3 < 4` — again spurious low (verify-r1-diagb-334,
  `g-coupled-binding-334`). Verified.

So mis-tracking the sharing in EITHER direction (conflate-separate `(2,2,1)` OR independentise-shared
`(3,3,4)`) invents a ratio below `½ minAdm` and kills coverage's no-smaller-ratio leg. **The diag(b) support
is load-bearing not only for the value but for coverage's ≥-leg.** (Drafted as a battery guard:
`battery-drafts/g-coverage-sharing-killcond.py`.)

## 5. Firmest result / most likely to break / next construction

- **Firmest:** coverage is reachable; the ≥-leg no-undershoot is automatic (`inf'_le`, verified no relaxed
  undershoot on 4 chains); the covering leg decomposes into a per-blow-up local covering lemma + ledger
  induction (Codex-confirmed structure); the far points reduce by homogeneity scaling; the assembly-given-
  atlas is banked. The genuine work is diligent CONSTRUCTION, not a walled theorem.
- **Most likely to break it:** the **per-blow-up local covering lemma at corank ≥ 2** — proving each standard
  chart `U_i` is *exactly one* stated child with the *correct* symbolic support. Get the support wrong and
  you invent a spurious low-ratio divisor (Check 2). This is the one place a "simplifying" transcriber
  destroys the proof (the compass's decoupling-disease warning, made precise). The 1(1) inner recursion
  (exponent-merge / divisibility in the coordinate ring) is the fiddliest sub-part.
- **Next construction (the formaliser's leaf, hand-off):** state + prove the local covering lemma on the
  `(2,2,2)` tree (3 charts by C^(1)-rank; generalise `Case222RouteMCover`), carrying `support : Gen →
  Finset DivVar`; then the `(2,2,1)`/`(3,3,4)` corank-2 charts to exercise the sharing transport; the
  covering-composition up the `(S,J)` tree is then the general-M `routeStep` read. **Before "establishing"
  coverage, run the D4 exhaustiveness hunt (cert-d4) as the gate.**

---

## ADDENDUM (2026-07-17) — two controller/architect additions, settled EXACT

### A1 (HIGH) — `region_glue`'s SEPARATED leaf integrand IS correct at corank ≥ 2; it needs NO coupled form

The architect's `monomialChartIntegral` (`Engine/EngineObligations.lean:49`) is the separated product
`∏_k u_k^{(divExp_k−1)−2c'}` (threshold `min_k divExp_k/2`); its docstring asserts "at a normal-crossing
leaf it separates to this product form." **Settled TRUE, exact.** Mechanism: Aoyagi's `b_i` satisfy a
**divisibility chain** `b_1 | b_2 | … | b_{M(L+1)}`, so the leaf loss `Σ_i b_i² = b_1²·(1 + (b_2/b_1)² + …)
= b_1²·unit` — a SINGLE dominant monomial times a unit — whose rlct is exactly `min` over `b_1`'s divisors
of `divExp/2`, the separated form. Verified (Newton-LP, `battery-drafts/g-leaf-chain-separation.py`, exit 0):
- chain leaves (`b_1|b_2`, `b_1|b_2|b_3`, `u_1²|u_1²u_2`): `NewtonLP(Σb_i²) == min divExp/2` EXACTLY;
- non-chain nodes (Morse `u_1²+u_2²`; the `(2,2,1)` residual `⟨d_1x,d_2y⟩`, rlct 1 additive): the separated
  min UNDERSHOOTS (`1/2 < 1`) — **these are NOT leaves**, they need further blow-up.

**Answer to the architect's question:** at corank ≥ 2 the leaf-level finiteness genuinely factors per-divisor
**because the divisibility chain collapses `Σb_i²` to `b_1²·unit`**; the coupling has been pushed into
*which divisors form `b_1`* and *their `divExp` values* (`= Mval` of the sharing-aware profile — set by
`StepInvariant` consulting `support`), NOT into the leaf integrand. **`region_glue` must take the SEPARATED
form and must NOT consult `support`; its load-bearing PRECONDITION is `IsFullMonomialization`** (every leaf a
genuine chain leaf). The flattening risk is therefore entirely at the tree layer (`StepInvariant` + `support`
+ `IsFullMonomialization` giving the right `divExp`), exactly as compass fork-3 (typed sharing) fences —
NOT at `region_glue`. A node declared a leaf while its `b`'s are incomparable is the kill (undershoot);
`IsFullMonomialization` rules it out.

### A2 (LOW) — Case-2 step exponent: re-derived, and the "non-binding" scope CORRECTED

`battery-drafts/g-case2-exponent.py` (exit 0): (a) the Case-2 divisor exponent re-derived from the blow-up
= codimension of the `(M(S)−J)×(M(S+1)−J)` residual block = the printed `(M(S)−J)(M(S+1)−J)` (matches on all
shapes/`J`). (b) **The coverage-relevant fact holds:** every top-level full-block exponent `M^{(i)}M^{(i+1)}
≥ minAdm(M)` (by permutation-invariance) — a Case-2 divisor NEVER undershoots `½ minAdm`, so it cannot break
coverage's ≥-leg. (c) **Scope correction (obstruction finding):** the reproduction's T-C flag "non-binding —
never attains the min" is **too strong** — the full-block (`t=0`) exponent **TIES** `minAdm` for `(2,2,3)`
pair(0,1), `(2,2,4)` pair(0,1), `(2,2,1)` pair(1,2) [3 ties vs 15 strict on the tested chains]. So a Case-2
`J=0` divisor **can be binding** and must be KEPT in the candidate set; do not discard Case-2 divisors as
"always non-binding." True load-bearing statement: **Case-2 exponents are upper bounds on `minAdm` (never
undershoot), tight for some chains.**
