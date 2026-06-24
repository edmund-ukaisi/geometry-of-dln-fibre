# Design certificate — R1 `hfin` (the cover-completeness UPPER bound, THE long pole)

**Seat:** `pen-and-paper` (CONSTRUCT, design-before-lines). **Date:** 2026-06-24.
**Gate:** `hfin` = `cover_le` = the UPPER-bound leg of the general-`M` `IsRouteMCover`
(`routeMLayerCover_of_atoms`'s `hfin` hypothesis): for `c' < ½·minAdm M`, the box integral
`∫_{(−1,1)^N} |routeMCore M|^{−c'} < ⊤`. Equivalently `rlctAtOn(routeMCore M) 0 ≥ ½·minAdm M`
("no stratum / direction beats the achiever").
**Method:** assessment of the banked `(2,2,2)` / `(3,3,4)` resolution machinery; exact symbolic peel
(sympy, the general Schur identity); calibrated Newton-polytope LP (exact rationals, against the
Morse / `⟨δx⟩` ground truth); one decorrelated `local-codex-consult` at `xhigh` (conclusion withheld;
`codex/hfin-design-{prompt,answer}.md`).
**Artefacts:** `/tmp/hfin_recursion_structure.py`, `/tmp/hfin_crux3{,b,c}.py` (the disjoint-sum crux),
`/tmp/hfin_leafbound.py` (the `Mval ≥ minAdm` enumeration), `/tmp/hfin_intermediate.py` (termination),
`/tmp/hfin_general_schur.py` (the general Schur-shear identity, sympy-exact),
`/tmp/hfin_node_codim.py`, `/tmp/hfin_branch_soundness.py`, `/tmp/hfin_codex_newton_check.py`.

---

## VERDICT: `hfin` is **BOUNDED-and-formalizable**, not a deep AG mountain — but it is genuinely large

`hfin` decomposes into three sub-obligations. Two are **bounded** and one (the per-leaf threshold
bound, corank-sensitive) is the **single hardest** — and it is **toric/monomial combinatorics, not
general determinantal-variety resolution of singularities**. The completeness primitive already
exists, sorry-free, and is null-exact. The honest magnitude is **person-weeks of focused
formalisation**, NOT person-months of new algebraic geometry — but it is **wider than the L=2 / RRR
milestone**, and the single concrete L=2 `(3,3,4)` chart still carries 3 measure-plumbing sorries
(`RouteMLayerCoverGEL2.lean`), so the general version is a real build, not a wiring exercise. The
decorrelated Codex (conclusion withheld) reached the **same** three-part decomposition, the **same**
crux, and the **same** "bounded finite-recursion + induction" magnitude verdict independently.

---

## 0. What `hfin` actually is, and what is already banked

`hfin` (`RouteMCoverLemmas.routeM_coverLe_of_finiteness`) needs: for `c' < ½·minAdm`,
`∫_{(−1,1)^N} |routeMCore M|^{−c'} < ⊤`. The mechanism (the `(2,2,2)` template, `Case222Cover` /
`Case222Block` / `Case222Resolution` / `Case222CoverGETail`): iterate `recStep` (a pivot-blow-up
argmax-cell split) until each cell is a `monomial · unit` leaf, then each leaf is finite below its
`monomialThreshold` (`monomialIntegrand_integrable_of_lt`), and the finite SUM of finite leaves is
finite.

**Already banked, sorry-free, reusable for general `M`:**
- The **completeness primitive** `argmaxCellOn_cover` (`S1G5Charts.lean:350`): the active-pivot cells
  cover `{∃ active coord ≠ 0}` **exactly**, and the uncovered slice `{all active = 0}` is
  `coordZero_null` (`Case222Resolution.lean:663`) — a **codim-≥1 null subspace**. So each `recStep` is
  a measure-EXACT cover up to a genuine null set, for ANY nonempty active set, ANY `N`. This is the
  hard half of "completeness" and it is **done**.
- `recStep` (`Case222Block.lean:56`): the reusable single recursion step, `∫_L h = Σ_{p∈active}
  ∫_{cell} |Jac|·h∘blowup`, an EXACT equality, for ANY `(active, p, L)`. Reusable at every `N`.
- `monomialIntegrand_integrable_of_lt` / `monomialThreshold_ge_of_mult` / `integrableOn_monomial_mul_unit_iff`
  — the per-leaf finiteness + the unit-invariance, abstract over `(d,k,h)`. The leaf-level analysis is
  network-free and banked.

So `hfin` is **not** "build a resolution of singularities from scratch." The cover primitive and the
recursion step exist. What is missing is the **general-`M` recursion that assembles them**.

---

## 1. The general chart family — the recursive coupled-`diag(b)` atlas (the construction)

The chart family is the **Aoyagi block-elimination recursion** realized as iterated pivot blow-ups.
Per non-leaf node `M = (M_0, …, M_L)` (all `M_s ≥ 1`):

**(a) Schur-shear node (Aoyagi Lemma 2, det-1, GENERAL corank — sympy-verified exact,
`/tmp/hfin_general_schur.py`).** Block `C^1 = [[a, b],[c, E]]` (`a` the `t×t` generic-invertible
top-left, `t` the surviving rank along the argmax pivot), `C^2⋯C^L = [[y],[S]]`. The det-1 shear
`T := y + a⁻¹bS`, `D := E − ca⁻¹b` gives the EXACT identity

      C^1·(C^2⋯C^L) = [[a·T], [c·T + D·S]].

This is `lemma2Fwd` (`Case222Resolution.lean:76`) for `(2,2,2)` and the `Schur change` of
`RouteMLayerCoverGEL2.lean` for `(3,3,4)`; the general form is one `ring` identity (verified for
`t=1, M_0=M_1=3, K=4`: `A·C = [[aT],[cT+DS]]` holds exactly, sympy).

**(b) Weighted pivot blow-up of the normal coords `(T, D)` by a pivot `u`** (`pivotBlowupOn` over the
active normal-coordinate block): `T = u·T'`, `D = u·D'`, giving the EXACT

      F ∘ Ψ = u² · U,   U = a²‖T'‖² + ‖c·T' + D'·S·(C^3⋯C^L)‖²  (u-free).

`U ≥ a²·‖T'_pivot‖² > 0` where the pivot slot is the argmax — a genuine UNIT bounded below
(`Uval334_ge_sq` in `RouteMLayerCoverGEL2.lean`). The `u`-exceptional divisor has
`(k,h) = (1, #active − 1)`; `#active = t·(width) + (M_0−t)(M_1−t)`.

**(c) Recurse on `U`.** For `L = 2` (RRR), `U` is already a unit (no deeper chain), so the node IS the
leaf: `#active = Mval(M, t)` **exactly** (verified `/tmp/hfin_node_codim.py`: `(3,3,4) t=(1,0)`,
`#active = 4 + 4 = 8 = Mval`). For `L > 2`, `U` still contains the deeper chain `C^3⋯C^L` inside the
coupled term, so `U` recurses on a sub-chain; the branch threshold telescopes to `Mval(M,t)/2`.

**The exponent data** is exactly what the combinatorial `routeLayerAtlas` already carries (the
`foldDivisors [c]` single-divisor leaves, codim `c = Mval(M,t)`); the chart family above is the
**geometric realization** the combinatorial atlas lacks (`routeLayerAtlas` is exponent data with no
chart map — `RouteMLayerCoverGE.lean` header).

---

## 2. Completeness — the proof structure (a finite chart-tree induction; the hard half banked)

Completeness is **NOT** a symmetric surjectivity statement and **NOT** a deep resolution theorem. It
is a finite-tree induction on top of the banked null-exact `recStep`:

- **Base:** each `recStep` covers its domain `L` **up to a single codim-≥1 null subspace**
  (`{all active = 0}`, `coordZero_null`). PROVEN, reusable, network-free.
- **Induction (chart-tree height):** the recursion produces a FINITE tree of cells (termination,
  below); the union of leaf charts covers `(−1,1)^N` up to a **finite union of null sets** (still
  null). Polynomial chart maps send null to null on bounded boxes. Equivalently — and this is how it
  is realized in Lean — the box integral equals the finite leaf-sum by **repeated exact application of
  `recStep`** (each step an equality, so no "covers up to null" is even argued separately at the
  integral level; the null slice contributes 0 to the integral). The `(2,2,2)` proof
  (`myF222_threshold_lt_top'`, `Case222CoverGETail.lean:1169`) is exactly this, hand-unrolled 3 deep
  into the A-pivot / E-F0-δ / block leaves.

**This is the half a naive read fears needs a global surjectivity argument; it does not** — because
`recStep` is an EXACT integral identity, the cover completeness is discharged step-by-step, never as a
monolithic "every point is in some chart." The genuine residual is **termination** (finitely many
leaves), below.

**Termination** — the right measure is **NOT total degree** (blow-ups can raise total degree after
factoring exceptional monomials; decorrelated Codex flagged this independently). The decreasing measure
is **lexicographic** `μ = (μ_mat, μ_vec, μ_mon)`:
- `μ_mat` = Σ of unresolved coupled matrix-block areas `a·b`. A Schur-pivot step on an `a×b` coupled
  block replaces it by an `(a−1)×(b−1)` block (drops by `a + b − 1 ≥ 1`).
- `μ_vec` = unresolved clean vector-norm blocks; one radial blow-up resolves a `d`-vector to a single
  radial axis (Jacobian exponent `d−1`).
- `μ_mon` = remaining incomparable monomial summands after the matrix/vector blocks are radialized —
  the monomial-principalization step (#3 below).

DLN-specifically, the branch tree is bounded by `Adm(M)` (finite, `≤ ∏(M_s+1)`), giving a
COMBINATORIAL termination that uses the product structure — NOT a general Hironaka descent. So
termination is **bounded** (a structural recursion on `(L, M)` / well-founded `μ`), and is the genuine
"general-`M` recursion" content the `(2,2,2)` fixed-3-deep unroll does not supply.

---

## 3. The CRUX — the disjoint-sum / per-leaf-threshold reconciliation (the single hardest atom)

**This is where a naive cover SILENTLY UNDERSHOOTS — the soundness-critical point.** When the loss
splits as a disjoint sum, the RLCT is **additive** (Watanabe), but a single pivot-blow-up chart sees
the SUM of two monomials and a naive "min over axes" reads the WRONG (smaller) value.

Worked exactly on the `(3,3,4)` binding branch `t=(1,0)` (`/tmp/hfin_crux3{,b,c}.py`,
Newton-LP-calibrated against Morse_n and `⟨δx_i⟩`):

- Peel `C^1` at `t=1`: `F ∼ ‖T‖² + ‖Δ·S‖²`, `T` a clean `1×4` (vars set 1), `Δ` free `2×2`, `S` free
  `2×4` (vars set 2), **disjoint**.
- `T`-block radial: `‖T‖² = r²·U_T`, `U_T ≥ 1`, Jac `r³`. **Threshold `(3+1)/2 = 2`.**
- `Δ`-block: radial `Δ = a·B` (one `B`-entry `= 1`), `‖Δ·S‖² = a²·‖B·S‖²`; `B·S` is Morse over the
  `S`-image, radialize its dominant `S`-axis `s`: `= a²·s²·U_D`, `U_D ≥ 1`, Jac `a³·s³`. **Each of `a,
  s` axis `(3+1)/2 = 2`.**
- After both blocks: `F ∼ r²·U_T + a²·s²·U_D`, Jacobian `r³·a³·s³`. **This is a SUM of two monomials,
  NOT a single monomial leaf.** Stopping here and taking `min{2, 2} = 2` proves `rlct ≥ 2` —
  **WRONG** (the truth is `4 = ½·minAdm`). The cover would **fail the upper bound**.

**The fix (the monomial-sum refinement — independently constructed by Codex via its own blow-up AND
Newton-LP, matching to the rational):** refine the sum by comparing `r` with `a·s`. On the `r`-pivot
cell (`a = r·α`): `F ∼ r²·(U_T + α²s²U_D)` with the bracket a UNIT (`U_T ≥ 1`); Jacobian accumulates to
`r⁷·α³·s³`. **Single monomial base `r²`, binding axis `r`: `(7+1)/2 = 4 = ½·minAdm`.** (Symmetric on
the `a`-pivot cell after one more `{β,s}` blow-up; both give `4`.) The Newton-LP for the 2-monomial
model `r² + a²s²` with Jacobian weights confirms `λ = 4·½ + 4·½ = 4` exactly
(`/tmp/hfin_codex_newton_check.py`, optimum `w = (½, ½, 0)`).

**Why this is sound and non-circular.** The accumulated Jacobian exponent on the dominant axis of a
terminal leaf reached along profile `t` is `Mval(M, t) − 1` (the codim-`Mval` regular-sequence
divisor), so the leaf binding axis has `h + 1 = Mval(M, t)` and threshold `Mval(M,t)/2`. Since
`minAdm = min_{t∈Adm} Mval(M,t)`, **every** leaf threshold is `Mval(M,t)/2 ≥ ½·minAdm` (enumerated
exact, 5/5 cases incl. `(3,3,4),(2,2,4),(3,3,5,4),(4,4,2,2)`, `/tmp/hfin_leafbound.py`: no admissible
`Mval` is below `minAdm`). So `min over leaves = ½·minAdm` with **no leaf below** — the upper bound is
sound. This is `monomialThreshold_ge_of_mult` (the multiplicity bound `Mval·1 ≤ h+1` per axis), already
banked at the threshold level; the missing content is the GEOMETRIC bookkeeping that the dominant axis
genuinely accumulates `Mval − 1`, INCLUDING the corank-≥2 coupled `Δ`-block.

**This corank-sensitivity is precisely the `diag(b)` obstruction** (`verify-r1-light-recursion.md`):
the per-row multiplicity model computes `3` here because it loses the shared radial `a` of the coupled
`Δ` (it sees two independent row-scalars `δ₁, δ₂`, each contributing `½`, total DS-part `1` not `2`).
The monomial-sum refinement keeps the shared `a` (one divisor over the whole `Δ`-block), and is what
raises the DS-part from `1` to `2` and the combined leaf from `2` to `4`.

**The single hardest sub-obligation** (verbatim the Codex crux, which I withheld my conclusion from):
> Given several disjoint resolved summands with known monomial thresholds, construct a finite common
> refinement on which the sum becomes monomial × nonvanishing-unit, and prove every final leaf has
> threshold = the additive value `Mval/2`.

It is **toric/monomial-principalization combinatorics** (the Newton polytope of a sum of two monomials
in disjoint variable blocks, with the Jacobian-weight transfer) — **not** deep determinantal geometry.

---

## 4. The bridge to the combinatorial `routeLayerAtlas` thresholds (per-chart ≥ ½·minAdm)

Each geometric leaf's threshold, via S2 (`monomial_rlct`, the ONLY citation), is `min_j (h_j+1)/(2k_j)`
on its monomial base. The monomial-sum refinement makes the binding axis `(k,h) = (1, Mval(M,t)−1)`, so
the leaf threshold `= Mval(M,t)/2` (S2 + `monomialThreshold_le_regularSeq` / `_ge_of_mult`, banked).
The combinatorial `routeLayerAtlas` already encodes each branch as `foldDivisors [Mval(M,t)]` (single
divisor codim `Mval`) with `monomialThreshold = Mval/2` (`routeLayerAtlas_value`, PROVEN). **The bridge
is the identification: the geometric leaf's refined binding-axis exponent `(1, Mval−1)` equals the
combinatorial `foldDivisors [Mval]` axis.** That identification is `monomialThreshold_appendDivisor`
arithmetic (banked); the geometric content is only that the refinement reaches `(1, Mval−1)`, which is
§3's accumulated-Jacobian fact. **No second citation needed** — S2 at the leaf is the sole external
input; the refinement and Jacobian bookkeeping are on our side (soundness gate respected).

---

## 5. MAGNITUDE ASSESSMENT (the operator's scope decision — data vs interpretation)

**Data (banked / verified):**
- The completeness primitive (`argmaxCellOn_cover` + `coordZero_null`) and the recursion step
  (`recStep`) are **done, sorry-free, network-free** — reusable at every `N`.
- The general Schur identity `C^1·(C^2⋯C^L) = [[aT],[cT+DS]]` is an **exact `ring` identity**
  (sympy-verified general; instances banked at `(2,2,2)`/`(3,3,4)`).
- `Mval(M,t) ≥ minAdm` for all admissible `t` is **definitional** (`minAdm = min`), exact 5/5.
- The L=2 `(3,3,4)` SINGLE geometric chart is **35KB of Lean with 3 residual sorries** — all in the
  measure-plumbing (equidimensional Jacobian change-of-variables, image containment, a.e.-positivity),
  NOT in the algebra (`RouteMLayerCoverGEL2.lean`).

**Interpretation (the magnitude verdict):**
- `hfin` is **BOUNDED and formalizable within the expedition's reach** — it is finite-recursion +
  a termination induction (lexicographic `μ`) + the monomial-sum-refinement lemma + the per-node
  measure-plumbing (the same change-of-variables already isolated at L=2). It is **toric/monomial
  combinatorics, NOT general resolution of singularities**. Decorrelated Codex reached the identical
  verdict ("bounded finite-recursion plus induction project, monomial-sum refinement the main cost").
- BUT it is **genuinely larger than the L=2 / RRR milestone**, and honestly larger than a single
  thread. The cost drivers, in order:
  1. **The monomial-sum refinement lemma** (the §3 crux, general disjoint-summand → single-monomial
     refinement with the additive-threshold proof). The single hardest atom. Person-week-scale alone,
     because it must handle the corank-≥2 coupled block correctly (where per-row multiplicity fails).
  2. **The per-node measure-plumbing** (the change-of-variables / Jacobian / a.e.-positivity for the
     general Schur-shear ∘ pivot-blow-up) — the SAME 3 sorries open at L=2 `(3,3,4)`, now needed for
     the general node and iterated. This is the recurring `(2,2,2)`/L2 friction, generalized.
  3. **The termination / chart-tree induction** (structural recursion on `(L, M)` matching the
     `routeLayerAtlas` recursion). Bounded but real (the `(2,2,2)` unroll is fixed-depth; general needs
     the genuine induction).
- **Realistic estimate:** several focused formalisation-threads (person-weeks), gated on the L=2
  measure-plumbing sorries closing first (they are the reusable per-node atom). **NOT multi-month new
  AG.** The risk is not conceptual (the math is settled and decorrelated-confirmed) but **formalisation
  surface area** — the measure-theoretic change-of-variables is the friction that already cost the L=2
  single chart 35KB-with-sorries.

**The cleanest path (recommendation).**
1. **Close the L=2 `(3,3,4)` measure-plumbing first** (the 3 `achieverChart334` sorries) — it is the
   reusable per-node change-of-variables atom; everything else iterates it. This is the highest-leverage
   move and is already in flight (task #44).
2. **Then the monomial-sum refinement lemma** as a standalone, abstract-over-`(d,k,h)` toric lemma
   (the §3 crux), tested first on the `(3,3,4)` two-monomial model `r² + a²s²`.
3. **Then the termination induction + chart-tree assembly** wiring the per-node atom up the
   `routeLayerAtlas` recursion to discharge `hfin` for general `M`.

If the operator wants to **bank the milestone instead**: the L=2 / RRR result
(`rlctAtOn(routeMCore M) 0 = ½·minAdm M` for `L = 2`, the reduced-rank-regression core, anchored to the
published Aoyagi-Watanabe formula) is a clean, citable, sound deliverable that does NOT need the general
`hfin` — the L=2 single Schur+blow-up node IS the leaf (no recursion), so it sidesteps the
monomial-sum refinement and the termination induction entirely. The general-`L` `hfin` is the
"complete the layer" extension; it is **reachable** but is the dominant remaining cost.

---

## 6. Scope, caveats, what would break this

- **Levels kept separate.** This certificate is about the **cover / chart family + the per-leaf
  threshold = ½·minAdm** (the combinatorial-core RLCT). The geometric `rlct = ½·codim` *reading* still
  rides the cited Aoyagi/Watanabe analytic bound — unchanged. S2 (`monomial_rlct`) is the ONLY external
  citation, used only at the leaf; no `rlct ≥ ½·codim` smuggled in (soundness gate respected).
- **Proved vs verified-exact vs banked vs inferred.**
  - *Banked (Lean, sorry-free):* `argmaxCellOn_cover`, `coordZero_null`, `recStep`,
    `monomialIntegrand_integrable_of_lt`, `monomialThreshold_ge_of_mult`, the value lane
    `routeLayerAtlas_value`.
  - *Verified exact (sympy / Newton-LP, calibrated):* the general Schur identity; the `(3,3,4)`
    disjoint-sum threshold `4` (both my Newton-LP and Codex's, to the rational); `Mval ≥ minAdm` 5/5.
  - *Inferred (the magnitude, the cost ordering):* clearly labelled interpretation, decorrelated-Codex-
    confirmed on the three-part decomposition + the bounded verdict.
- **The one thing most likely to break the magnitude estimate:** the per-node measure-plumbing (cost
  driver 2) is the same change-of-variables that has repeatedly proven friction-heavy (L=2 `(3,3,4)` =
  35KB-with-3-sorries; `(2,2,2)` cover = several files). If the general Schur-shear ∘ pivot-blow-up
  change-of-variables does not modularize cleanly (so each node re-pays the measure-Jacobian cost), the
  estimate slips from person-weeks toward person-month. The *math* will not break (settled + decorrelated);
  the *formalisation surface* is the risk. The monomial-sum refinement (cost driver 1) is the conceptual
  crux but is bounded toric combinatorics, low risk of blowing up.
- **What is NOT in scope and does not need general `hfin`:** the headline `rlct = ½·minAdm` for the
  RRR / L=2 core; the value-side fold (PROVEN); the lower bound `hdiv` at L=2 (the `(3,3,4)` wedge,
  integrated). `hfin` is specifically the general-`L` upper-bound completion.

---

## 6b. UNIFICATION — does ONE coupled resolution serve BOTH `hdiv` and `hfin`? (operator-decision-critical)

**Context (controller, 2026-06-24, discuss-at-close §8):** the `hdiv` lower-bound `(3,3,4)` chart
`phi334` was found DEGENERATE (drops 2 coords → Jacobian `det ≡ 0`, null image → the c-o-v field asserts
`0 = ⊤`, false). Its honest fix hits the SAME `a = 0` (pivot-vanishing / Schur-shear-singular) locus
that `hfin` faces. Question: does ONE coupled-`diag(b)` resolution discharge both legs?

**VERDICT: YES — one resolution serves both bounds. This is the standard Watanabe/Hironaka RLCT recipe,
and the unification REDUCES total work versus two separate builds.** (Exact-verified at the sharp
boundary, `/tmp/hfin_unif_sharp.py`; structural split `/tmp/hfin_unification.py`,
`/tmp/hfin_shared_split.py`.)

**The classical fact.** A SINGLE normal-crossings resolution `π : W → ℝ^N` gives, on each chart, a
monomial integral that **converges iff `c' < chart-threshold` and DIVERGES iff `c' ≥ chart-threshold`**.
So `rlct = min over charts`, and BOTH bounds read off the SAME atlas: `c' < min` ⟹ every chart converges
⟹ total finite (`hfin`); `c' ≥ min` ⟹ the binding chart diverges ⟹ total `= ⊤` (`hdiv`). There is no
"separate lower-bound resolution" in the standard recipe — the split into two charts was a banked
shortcut, not a mathematical necessity.

**The achiever leaf is LITERALLY the same chart for both legs (exact, `(3,3,4)`, `minAdm = 8`).** On the
achiever leaf the pulled-back integrand near `u = 0` is `|u²·U|^{−c'}·u^{minAdm−1} ∼ u^{minAdm−1−2c'}`
(`U` bounded above and below). The 1-D test `∫₀^ε u^{minAdm−1−2c'}`:
- `c' < minAdm/2` ⟹ exponent `> −1` ⟹ CONVERGES — this leaf's finite contribution to the `hfin` sum;
- `c' ≥ minAdm/2` ⟹ exponent `≤ −1` (sharp `u^{−1}` at `c' = 4`) ⟹ DIVERGES — this leaf IS the `hdiv`
  diverging chart.

**Why `phi334` degenerated, and why the atlas cures it for free.** The achiever curve sits ON `{a = 0}`
(the deepest point, all coords `→ 0`), exactly where the Schur shear `T = y + a⁻¹bS` is singular. A LONE
chart through `a = 0` either avoids it (misses the achiever ⟹ no divergence) or hits it (shear singular ⟹
drops coords ⟹ `det ≡ 0`, `phi334`'s failure). The pivot blow-up `a = u·â` is PRECISELY what resolves
the `a = 0` singularity: in resolved coords the achiever curve is the `u`-axis, SEPARATED from the
center, and the leaf map is an honest local diffeo (Jacobian `u^{minAdm−1} ≠ 0` off `u = 0`). **The
degeneracy was the cost of dodging the resolution with a lone chart; building the atlas removes it.**

**Precise SHARED-vs-SEPARATE (the corrected magnitude calculus).** It is neither "two hard constructions"
nor "one construction discharges everything free." It is:
- **SHARED (the single hardest atom, built ONCE):** the per-node Schur-shear ∘ weighted-pivot-blow-up
  CHART with its HONEST measure-change-of-variables (Jacobian `u^{#active−1}`, local diffeo off null,
  image containment, a.e.-positive unit) + the exact `F∘chart = u²·U` factorization. This is BOTH the
  honest replacement for the degenerate `phi334` AND the `hfin` per-leaf chart — the most load-bearing
  residual for both legs.
- **`hdiv`-specific (LIGHT, on top of the shared chart):** ONE achiever leaf, box-integral `= ⊤`
  at-and-above `minAdm/2` (the sharp `u^{−1}` via `monomialIntegrand_lintegral_box_eq_top` + the chart's
  c-o-v). NO recursion, NO tree, NO completeness.
- **`hfin`-specific (the HEAVY tail):** the full recursion (every node/branch) + termination + cover
  completeness + the monomial-sum refinement at each multi-summand leaf (§3). The dominant cost.

**Net effect on the operator's scope decision.** Building `hdiv`'s honest chart is NOT wasted work — it
IS the `hfin` per-node atom. The `phi334` detour means `hdiv` must now pay the shared-atom cost it tried
to dodge, but that cost is paid ONCE and serves `hfin` too. So: **the realistic R1 cost is ONE shared
hard atom (the per-node honest c-o-v chart) + a light `hdiv` tail + a heavy `hfin` tail — not two
independent resolution mountains.** This SHRINKS the scope-decision gap between "bank L=2/RRR" and
"pursue general-L": the L=2 milestone needs the shared atom anyway (the L=2 `(3,3,4)` honest chart =
the degenerate `phi334`'s replacement = the per-node atom at depth 1), so building it is the natural
first step of EITHER path, and the general-`L` `hfin` is then "iterate the same atom up the tree + the
refinement lemma."

**Caveat (the one place the legs could fail to share).** The two Lean FIELD SHAPES differ: `hfin` is a
SUM over all leaves finite on the box `(−1,1)^N`; `hdiv` is ONE leaf's integral `= ⊤` on every small cube
`[−ε,ε]^N`. The achiever leaf serves both, BUT the `hdiv` divergence needs the achiever chart's image to
contain a positive-measure piece of EVERY cube `[−ε,ε]^N` (the `ε`-uniformity) — a containment the
degenerate `phi334` lacked (null image). The shared honest chart fixes this (its image is full-measure
off null), so the caveat is discharged BY the shared atom — but it is the precise extra the `hdiv` leg
needs beyond "same chart," and it must be checked, not assumed. (No case found where the `hfin` cover
fails to contain the `hdiv` diverging chart — the achiever leaf is in the cover by construction.)

---

## 7. Close — for the controller's scope decision and the formaliser hand-off

- **Firmest result:** `hfin` is **bounded-and-formalizable** (finite chart-tree recursion + lexicographic
  termination + the monomial-sum-refinement lemma + the per-node measure-plumbing), **toric/monomial
  combinatorics not general AG**. The completeness primitive is banked null-exact; the upper-bound
  soundness rests on `Mval(M,t) ≥ minAdm` (definitional) + the refined per-leaf binding axis
  `(1, Mval−1)`. Decorrelated Codex independently reached the same decomposition, crux, and magnitude.
- **UNIFICATION (§6b):** ONE coupled resolution serves BOTH `hdiv` and `hfin` (the standard
  Watanabe/Hironaka recipe — `rlct = min over charts`, both bounds off the same atlas). The shared
  hardest atom is the per-node honest Schur-shear ∘ pivot-blow-up chart with its measure-c-o-v; it is
  BOTH the degenerate `phi334`'s honest replacement and the `hfin` per-leaf chart. `hdiv` then needs only
  ONE leaf on top (light); `hfin` needs the full tree (heavy). So R1 = one shared hard atom + a light
  `hdiv` tail + a heavy `hfin` tail — NOT two resolution mountains; the unification REDUCES total work.
- **Most likely to break it:** the per-node measure-theoretic change-of-variables surface area (the L=2
  `(3,3,4)` 3-sorry friction, generalized + iterated) — a formalisation-cost risk, not a math risk.
- **The cleanest next step:** close the L=2 `(3,3,4)` `achieverChart334` measure-plumbing sorries (task
  #44) — it is the reusable per-node atom; then the standalone monomial-sum-refinement toric lemma on
  the `r² + a²s²` model; then the termination/assembly induction. If banking the milestone: the L=2 / RRR
  result is clean, citable, and sidesteps the entire `hfin` recursion.
