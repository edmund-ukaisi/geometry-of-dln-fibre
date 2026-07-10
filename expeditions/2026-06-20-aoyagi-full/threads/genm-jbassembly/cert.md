# Joint-block assembly + §8 — the Lean-friendly route from `frobSq(A₀·Q)` to the banked corner endpoint

**Seat:** pen-and-paper (witness). **Task #111.** **Date:** 2026-07-10. **NO Lean.**
**Charge:** pin the exact Lean-friendly route for the two hard CoV-production pieces — (1) the
opaque-width joint-block pointwise assembly (the L-recursion + disjoint-block form) and (3) the §8
unit-boundedness / g-positivity discharge (the `g>0`-on-sphere locus + the deep-factor rank-drop
branch) — so a follow-on tide formalises them onto the banked corner endpoint
`corner_block_cube_lintegral_lt_top` (`RouteMSJRadialPolar.lean:257`) without a blind grind.
**Decorrelated:** one neutral `local-codex-consult` (xhigh, my tentative conclusions withheld —
`codex/assembly-{prompt,answer}.md`); it independently reproduced the peel algebra and converged on the
same load-bearing finding (§V).

---

## VERDICT (route pinned, with one load-bearing sharpening)

The route to the banked endpoint is **sound width-general, but ONLY on a REFINED cover where every
pivot minor is bounded below and the deepest factor is rank-generic** — NOT on the raw pivot chart
`{minor ≠ 0}`. The naive "single joint block of dim `minAdm`, pivot as a passive environment parameter,
feed the endpoint once" route **UNDERSHOOTS**: it certifies only `rlct ≥ 5/2` on `(3,3,3,4)`, not the
required `7/2` (exact witness §1b below). The pivot magnitude is a genuine resolution direction, not a
unit; where it → 0 the endpoint's uniform sphere lower bound `a ≤ g(ω)` fails, and that region is a
**separate, deeper (higher-charge, non-binding) flag branch**. This SHARPENS the vslice §8 named gap
(which named only the `A₂`-rank-drop as the degrading direction): **the small-pivot direction degrades
the cores by the same mechanism**, and both are closed by the flag stratification.

So the two `corner_block_cube` caller obligations resolve as:
- **(1b) disjointness + `dim = minAdm`:** HOLDS on each good chart (pivots bounded below, deep factor
  generic) — and the disjoint form is not even required (the banked *cross-coupled* Schur form is
  already endpoint-admissible, §1b, avoiding the det-inverse "drop-L"). It FAILS on the raw chart.
- **(§8) `a ≤ g(ω) > 0`:** this is the SINGLE load-bearing gate. It requires (3a) the deep factor
  generic AND (implicitly) the pivots bounded below; its complement is the (3b) deeper branch.

**The genuinely-hard, un-banked content is therefore the flag stratification / simultaneous resolution
chart that supplies `a ≤ g(ω)` — recon-map item 1, ~65–75% new — now with the pivot-bounded-below
sub-gate named explicitly.** Everything downstream of `a ≤ g(ω)` (the endpoint, the charge accounting,
the domain control) is banked or bounded.

---

## 0. Objects (the frame)

Leaf `sjJointResolution M hIH t ρ κ … : gammaPeelIntegral M t ρ κ c' < ⊤`
(`RouteMSJResolution.lean:797`), integrand (`:517`)

    ∫⁻ A' in paramsBoxM (tailChain M) 1,
      ∫⁻ A0 in matBox (M 0) (M 1) 1 ∩ pivotChart ρ κ,
        ofReal ( frobSq (rmatMul A0 (prod (tailChain M) A')) ^ (-c') ),   c' < minAdm M / 2.

Write `Q = prod (tailChain M) A' = A₁·A₂·…·A_{L-1}` (`M₁ × M_L`). On chart `(ρ,κ)` the `t×t` pivot
block `A` of `A₀ = [[A,B],[C,D]]` is invertible. Banked endpoint (the LANDING):

> `corner_block_cube_lintegral_lt_top` — measurable degree-2-homog `g : (Fin n → ℝ) → ℝ`
> (`g (r•x) = r²·g x`) with `a ≤ g (ofLp ω)` on the unit sphere (`a > 0`) and `c' < n/2` ⟹
> `∫⁻_{[-1,1]ⁿ} (g z)^{-c'} < ⊤`. (Ball form `corner_block_lintegral_lt_top:185` — arbitrary radius `R`.)

Per-block `hom`/`hg` discharges banked: `frobSq_rmatMul_smul`, `measurable_frobSq_rmatMul`
(`RouteMSJCornerLoss.lean`).

---

## 1. PIECE (1) — the opaque-width joint-block assembly

### 1a. The L-recursion structure

**The recursion is over the rank flag (the `(S,J)` profile), and it BUILDS ONE simultaneous-resolution
chart per branch; the endpoint is applied ONCE at the top of the chart, not leaf-by-leaf.** Concretely,
for a flag branch `T = (t₀, t₁, …, t_{L-1})` (nested pivot ranks), the peel at boundary `i` is the banked
Schur split (`frobSq_schur_block_split`, `RouteMSJChartAlgebra.lean:107`):

    frobSq(A₀·Q) = frobSq(A·Q̃_p) + frobSq(C·Q̃_p + Γ·Q_b),
      Q̃_p = Q_p + ⅟A·B·Q_b,   Γ = schurCompl A B C D = D − C·⅟A·B   (the corank block, dim q₀ = (M₀−t)(M₁−t)).

The pivot part `frobSq(A·Q̃_p)` = the loss of the reduced chain `redChain t M = (t, M₂, …, M_L)`
(arity `L−1`), which recurses; the corank block `Γ` (dim `q₀`) is peeled off. The recursion:

    peel boundary 0  →  (corank block Γ₀, charge q₀)  ⊕  reduced chain (t, M₂,…) [RECURSE]
    …
    base: deepest factor A_{L-1} is a SINGLE matrix (generic ⟹ full row rank), so the terminal
          reduced loss frobSq(v·A_{L-1}) is a CLEAN positive-definite quadratic in v — STOP.

**Induction variable (Codex-concurred):** the remaining boundary index + the incoming rank `t_{i-1}` +
the chosen flag suffix — NOT the collapsed matrix `H` of the §4a depth reduction treated as a free
generic matrix (that loses the `Γ₀` Schur block + its charge bookkeeping). The §4a depth reduction
`frobSq(A₀A₁A₂) = frobSq(H·A₂)` is an exact identity (`vslice cert §4a`) but is a *presentation* of the
composed peel, not the recursion carrier.

**On a complete GOOD branch** (every pivot `A_i` bounded below, deep factor generic) the accumulated
endpoint block is

    E_T = Γ₀ ⊕ Γ₁ ⊕ … ⊕ (terminal free block),   dim E_T = Σ_i q_i = Mval(M, T),

and the loss, as a function of `E_T` with the pivots + tail as bounded environment, is the degree-2
form `g_T(E_T) = Σ_i frobSq(Γ_i · U_i)` (`U_i` = the resolved right/tail maps). Feed `g_T` to the single
endpoint: threshold `dim E_T / 2 = Mval(T)/2`. Min over branches `= minAdm/2` (banked exhaustiveness,
§1b). **This is why the endpoint is single-block:** its ONE polar blow-up of the whole `E_T` IS the
corner blow-up that merges all the boundary divisors — the "codimensions ADD" is exactly
`dim E_T = Σ q_i` under one radius.

**hIH question (recon-map THE CRITICAL PATH), resolved.** A PLAIN-finiteness recursion is INSUFFICIENT:
prepending `Γ₀` to the accumulated block (the sum-not-min coupling) needs the reduced chain's *resolved
form* (its joint block `E'` + its unit lower bound), not merely `RouteMBoxThresholdFinite (reduced)`.
Handing a plain-finiteness reduced-chain IH is exactly the refuted front-peel (recon-map §COUPLED: the
plain IH cannot reach the deeper `{rank Q_b = q−1}` strata; it over-charges and DIVERGES). **So the
recursion must carry a RESOLVED-FORM invariant (the internal `SJState`/`SJSupport` ledger — UPDATE-668,
kept internal), and the arity-`hIH` in the leaf signature is UNUSED for the good-branch resolution**
(it may be kept for signature compatibility, as `sjJointResolution_frontPeel` does with `_hIH`). The
flag TERMINATION (not arity) drives the recursion; termination = the flag is a finite nonincreasing
integer rank-sequence (reference `remaining_lt_of_support_ssubset`, re-derive-then-adopt).

**Sum-not-min, the exact mechanism (Codex, DERIVED + numerically confirmed `codex/…` / `/tmp/jb_sumnotmin.py`).**
The one-step coupled integral

    ∫_{‖x‖≤R} (‖x‖² + h)^{-c} dx  ≲  h^{q/2 − c}   (x ∈ ℝ^q, c > q/2)   [exponent verified −1.0027 ≈ q/2−c]

shows peeling a `q`-dim block shifts the residual exponent `c ↦ c − q/2`, giving a compound threshold
`q/2 + λ_tail`, NOT `min(q/2, λ_tail)`. The banked single-block endpoint achieves the same additivity by
putting ALL blocks under one radius (`dim E_T = Σ q_i`); the banked `radial_morse_residual_power_le`
(`RadialResidualPower.lean:157`, `c' ↦ c'−½(m+1)`) is the block-by-block form of the same shift, available
if a nested formulation is preferred.

### 1b. The disjoint-block form + `dim = minAdm` (the two caller obligations)

**FINDING (the sharpening — witness of undershoot).** Treat the pivot `a` as a FREE box variable and
lower-bound each core by its generic constant: `frobSq(A₀·Q) ≳ a²·σ²‖v‖² + τ²‖Γ‖²` (`v` the boundary-1
row, dim `d_v = 3`; `Γ` the `2×2` corank block, dim `d_Γ = 4`). This crude model has RLCT **exactly
`5/2`**, NOT `7/2`:

    rlct(a²‖v‖² + ‖Γ‖²) = rlct_{(a,v)}(a²‖v‖²) + rlct_Γ(‖Γ‖²)     [Thom–Sebastiani, disjoint var-groups]
                        = 1/2 + d_Γ/2 = 1/2 + 2 = 5/2                [1D reductions exact; grid /tmp/jb_pivot.py]

because `rlct(a²‖v‖²) = min(rlct(a²), rlct(‖v‖²)) = min(1/2, d_v/2) = 1/2` (the `∫a^{-2c'}da` factor caps
at `c' < 1/2`). So **any route that admits the pivot `a` as a free variable disjointly summed into the
model cannot exceed `rlct ≥ 5/2 < minAdm/2 = 7/2`.** The pivot must be bounded below (its own branch).

**On the GOOD chart (pivot bounded below `|det A| ≥ δ`, deep factor generic), the obligations HOLD:**

- **Disjointness is not even needed — the banked CROSS-COUPLED Schur form is endpoint-admissible
  directly** (verified symbolically `/tmp/jb_crosscoupled.py`). With `Q̃_p = v·(A₂…)`, `Q_b = W·(A₂…)`:

      g_cc(Γ, v) := a²·frobSq(v·(A₂…)) + frobSq((C·v + Γ·W)·(A₂…))   [ = frobSq(A₀·Q) exactly ]

  is degree-2-homogeneous jointly in `(Γ, v)` (both scale linearly), and its ONLY sphere zero is the
  trivial `(Γ, v) = 0` when `|a| ≥ δ`, `A₂…` and `W·(A₂…)` full row rank. So `g_cc` satisfies the
  endpoint hypotheses on the good chart with **no drop-L, no det-inverse**. (The DISJOINT form
  `g_dis = a²·frobSq(v·A₂…) + frobSq(Γ·W·A₂…)` — from dropping the unit `L = [[1,0],[C/a,I]]` — is a
  cleaner alternative for the §8 block-by-block lower bound, but dropping `L` is only valid where
  `‖L⁻¹‖ = 1 + ‖C‖/|a|` is bounded, i.e. `|a| ≥ δ` — Codex-flagged, so the cross-coupled form is
  preferred to sidestep it.)

- **`dim E_T = Σ q_i = Mval(T)`, min over branches = minAdm** — banked: `sjChargeUpdate_accum`
  (`RouteMSJResolution.lean:353`, the additive charge `Mval` decomposition), `sjChargeBudget_le` (`:203`,
  `minAdm M ≤ (M₀−t)(M₁−t) + minAdm(redChain t M)` for every admissible `t` — the exhaustiveness),
  `sjChargeBudget_binding` (`:210`, the achiever), `minAdmRec_eq_minAdm` (`RouteMLayerSplit.lean:395`).
  Two-block additive threshold `(q₁+q₂)/2` (not `min`) numerically corroborated `/tmp/jb_sumnotmin.py`.

**COMPASS (det-inverse audit).** Every step's Jacobian is `1` or a bounded-below-unit coefficient:
- `Γ = D − C·⅟A·B`: the CoV `(A,B,C,D) ↦ (A,B,C,Γ)` is a `D`-translation, **Jacobian `1`**
  (`measurePreserving_shearSub`, `RouteMSJPivotChart.lean:337`); `⅟A` is a unit coefficient, not a
  Jacobian determinant. Controlled only where `A⁻¹` bounded ⟹ good chart. `⅟`→`⁻¹` for integrand use
  via `invOf_eq_nonsing_inv`.
- `A₁ ↦ A₁^♯ = U·A₁`, `U = [[1, ⅟A·B],[0,I]]` unit-triangular: **Jacobian `(det U)^{M₂} = 1`**.
- The reduced-chain collapse `v ↦ F' = A·v` (should a nested formulation use it) has Jacobian
  `det(A)^{M₂}` — a det factor, but **`det A ≥ δ^t > 0` on the good chart makes it a bounded-below unit,
  not a pole** (compass-OK). OFF the good chart it is a genuine pole ⟹ the map says "re-express" ⟹ the
  deeper flag branch. No step grows an unbounded det-inverse on a good chart.

### 1c. Opaque-width Lean tactics (from `lean/CLAUDE.md`)

- **Block reindex** `Fin (M k) ≃ Fin t ⊕ Fin (M k − t)` (`blockSplitEquiv`/`finSplit`; banked
  `matReindexEquiv`/`measurePreserving_matReindexEquiv`, `RouteMSJBlockReindex.lean:146/164`;
  `blockSplitD`/`measurePreserving_blockSplitD`, `RouteMSJChartShear.lean:86/94`) — do cast bookkeeping at
  the EQUIV level (`finCongr_refl` → `Matrix.reindex_refl_refl` via `erw`), never entrywise.
- **Dependent-width reassociation** (`A·(v·A₂)` vs `(A·v)·A₂`): `rw [mul_assoc]`/`simp`/`conv` do NOT
  match through the dependent `HMul`; use fully-applied `RouteMFrontPeel.mul_three_reassoc`, or
  `set X;set Y;exact Matrix.mul_assoc`; peel `prod`/`prodAux` by prefix-length induction
  (`prodAux_succ`).
- **`⅟`→`⁻¹`**: `blockShear_step` / `frobSq_schur_split_inv` are stated with `⅟α`; convert with
  `invOf_eq_nonsing_inv` (after `IsUnit.invertible`) for integrand-usable identities.
- **Matrix-apply at opaque widths**: `fun_prop` FAILS on abstract `Matrix.mul` over `Fin (M k)`; work
  the **Params / Pi form** `Fin a → Fin b → ℝ` (where `frobSq`, `rmatMul` live and `measurable_frobSq_rmatMul`
  already `fun_prop`s), and prove per-entry identities as `have`s at explicit `⟨_, by decide⟩` indices,
  then `exact` (Fin proof-irrelevance unifies). Binder-codepoint hazards: ASCII `Qt`/`phi`, never `Q̃`/`φ`.
- **Endpoint plumbing**: the joint block on the good chart ranges over a box **shifted by the bounded
  amount `C·⅟A·B`** (|C|,|B| ≤ 1, |⅟A| ≤ 1/δ), hence contained in a FIXED ball `closedBall 0 R`,
  `R = 1 + √(dim)/δ`. Use the BALL endpoint `corner_block_lintegral_lt_top` (arbitrary `R`) +
  `lintegral_mono_set` domination — the shifted-domain obstruction is dissolved by pivot-bounded-below
  (Codex Q2b concurs). `ofLp` transport is banked in `corner_block_cube_lintegral_lt_top` itself.

---

## 3. PIECE (3) — the §8 unit-boundedness / g-positivity discharge

The endpoint's `a ≤ g(ofLp ω)` on the unit sphere is the SINGLE load-bearing gate.

### 3a. When is `g > 0` on the sphere (the generic locus)

`g_T(ω) = Σ_i frobSq(Γ_{i,ω} · U_i)` (or the cross-coupled `g_cc`). On the joint sphere at least one
block `Γ_{i,ω} ≠ 0`, so `g_T(ω) = 0` ⟺ `Γ_{i,ω}·U_i = 0` for the nonzero block ⟺ **`U_i` fails to be
left-injective** (`Γ ↦ Γ·U_i` has a kernel). Each `U_i` is built from the deepest factor `A_{L-1}` and
the resolved intermediate layers; `U_i` left-injective ⟺ `A_{L-1}` full row rank (+ intermediate tail
maps full rank). So:

> **`g_T > 0` on the joint sphere on the `A_{L-1}`-generic locus (all `U_i` full row rank).**

The uniform positive lower bound `a = min_i σ_min(U_i)² > 0` follows by **continuity + compactness**
(joint sphere compact, `g_T` continuous, positive ⟹ positive minimum). Banked supply-technique
templates (nonzero-poly witness ⟹ `0 < U` a.e., then the positive-min): `Uval4422_ae_pos`,
`achieverUfun_ae_pos`, `cleanUfun_ae_pos` (clean-three). **This is bounded chart algebra on the
`(2,2,2)` `Case111`/`Case222` templates lifted to opaque widths + tracking which resolved row hits
which `U_i` — genuine-new (un-banked) but NOT a wall** (vslice §8; RRR-anchored; the value is certified
general-`L`).

### 3b. The deep-factor rank-drop branch (+ the small-pivot branch)

Where a `U_i` drops rank — i.e. **`A_{L-1}` rank-deficient**, OR (the sharpening) **some pivot `A_j` → 0**
— `g_T` vanishes on part of the joint sphere and (3a) fails. Route BOTH as **deeper flag branches**:

- **`A_{L-1}`-rank-drop** is the next determinantal stratum `{rank A_{L-1} ≤ r}` of the tail. Peeling it
  adds a boundary charge `q' = (s − r)(M_L − r)` (Codex Q3, DERIVED). It is a DEEPER `(S,J)` level.
- **Small-pivot** `{rank A_j < t_j}` (some pivot minor → 0) is a LOWER-rank flag branch: a smaller pivot
  rank ⟹ a BIGGER corank block `(M_a − t')(M_b − t')` ⟹ a bigger `Mval` (e.g. the `t = 0` cut =
  `{A₀ = 0}`, charge `M₀·M₁`, threshold `M₀M₁/2` — for `(3,3,3,4)`: `9/2 > 7/2`, the vslice α-branch;
  confirmed `/tmp/jb_pivot.py`).

**Closure (exhaustiveness — required, not optional).** Every such deeper branch has threshold
`½·Mval(branch) ≥ ½·minAdm` — this is precisely the banked `sjChargeBudget_le`
(`RouteMSJResolution.lean:203`): `minAdm M ≤ (M₀−t)(M₁−t) + minAdm(redChain t M)` for EVERY admissible
`t`, so no branch undershoots. **It is NOT automatic that a rank-drop branch is non-binding** (Codex Q3
caveat): it is non-binding exactly because `minAdm` is DEFINED as the min over all admissible branches
(including the rank-drop ones), so each is `≥ minAdm` by construction. **Termination:** the flag is a
finite nonincreasing sequence of integer ranks; the recursion bottoms out at the zero-product locus
(`r = 0`) or the exhausted chain (base `L = 1`, `sjBase1_freeMatrix`, `:912`). Every leaf is either a
good chart (endpoint, threshold `≥ minAdm/2`) or a strictly-deeper branch — finitely many.

---

## 7. The Lean-friendly pipeline (what feeds `sjJointResolution`)

    front-split (CLOSED)                    routeMLayerBoxIntegral_front_split (:461)
      → pivot-chart cover (CLOSED)          pivotChartCover_matBox_le_sum (:552)  [= sjBoundaryPeel plumbing]
        → REFINE: pivot bounded below       ★ GAP: {|det pivot| ≥ δ} good chart ∪ deeper branch (§3b)
          → Schur block split (BANKED)      frobSq_schur_block_split (ChartAlgebra:107)  [cross-coupled g_cc]
            → shears D↦Γ, A₁↦UA₁ (BANKED MP) measurePreserving_shearSub  [COMPASS: Jac 1]
              → accumulate Γ_i down flag     ★ GAP: simultaneous-resolution chart (recon item 1, ~65–75% new)
                → §8 lower bound a ≤ g_T(ω)  ★ GAP (3a): A_{L-1}-generic + pivots≥δ ⟹ compactness min
                  → ball domination          corner_block_lintegral_lt_top (:185) over closedBall 0 R
                    → endpoint (BANKED)       corner_block_cube_lintegral_lt_top (:257), c' < dim E_T/2
    accounting: Σ q_i = Mval ≥ minAdm (BANKED)  sjChargeBudget_le (:203), sjChargeUpdate_accum (:353)
    deeper branches non-binding (BANKED)        sjChargeBudget_le + finite flag termination

The three `★ GAP`s are the mountain; all else is banked. **They collapse to ONE statement**: *on the
refined cover (pivots bounded below, deep factor generic) the resolved loss is `g_T` on `E_T`
(`dim = Mval`) with `a ≤ g_T(ω)` on the sphere; off it, a strictly-deeper branch.* This is the vslice §8
named brick, sharpened to include the small-pivot direction.

---

## V. Codex (decorrelated, xhigh; my conclusions withheld) — CONVERGES on the finding

Codex independently derived (see `codex/assembly-answer.md`): the boundary-`i` peel
`Y_i = L_i·diag(P_i, Γ_i)·R_i` with `dim Γ_i = q_i`; the accumulated block `E_T = ⊕Γ_i`,
`dim = Σ q_i = Mval(T)`; `g_T = Σ‖Γ_i U_i‖²` with `g_T ≥ min σ_min(U_i)²·Σ‖Γ_i‖²`; the sum-not-min
one-step integral `∫(‖x‖²+h)^{-c} ≲ h^{q/2−c}`. Its **VERDICT (verbatim spirit): "A naive
single-joint-block-to-the-endpoint proof is not sound width-general. The sound route is boundary-by-
boundary peeling with an accumulated block or exponent-shift induction; the banked endpoint is a terminal
chart lemma once all pivots and tail maps are uniformly nondegenerate. The most likely failure mode is
loss of a uniform sphere lower bound — either from dropping an unbounded pivot unit as `a → 0` or from
the shared deep factor rank-drop."** Codex flagged the `Γ = D − CP⁻¹B` det-inverse (Jacobian `1` in the
`D/Γ` block, controlled only where `P⁻¹` bounded — matches my COMPASS) and confirmed the shifted-`Γ`
domain is bounded on a pivot-bounded-below chart (matches §1c ball domination). **INFERENCE preserved as
such:** Codex's "boundary-by-boundary with accumulated block" and my "flag recursion builds one chart,
one endpoint at top" are the same construction viewed as recursion-on-chart vs recursion-on-integral;
the DERIVED FACTS (charges, thresholds, the `5/2` undershoot, the one-step exponent) are the certificate.

---

## Closing

- **Firmest result.** The route lands on the banked endpoint `corner_block_cube_lintegral_lt_top` on
  each good chart (pivots bounded below, deep factor generic) via the banked cross-coupled Schur form
  `g_cc` (degree-2-homog, positive on the sphere — verified) fed directly (no drop-L, no det-inverse);
  the accumulated block `E_T` has `dim = Mval(T)`, threshold `Mval(T)/2`, min `= minAdm/2` (banked
  charge). Deeper branches (deep-factor rank-drop AND small-pivot) are non-binding by the banked
  exhaustiveness `sjChargeBudget_le`; finite-flag termination. Decorrelated-Codex concurs.
- **Most likely to break it (the ONE gate).** The §8 uniform lower bound `a ≤ g_T(ω)`: it silently
  requires BOTH the deep factor generic (3a) AND the pivots bounded below (the sharpening). Supplying it
  width-general = the simultaneous-resolution chart + the pivot-magnitude stratification of the cover
  (the raw `pivotChartCover` does NOT bound pivots below). This is bounded chart algebra on the
  `Case111/Case222` templates lifted to opaque widths, but it is genuinely un-banked and is where a
  formalisation stalls — it does NOT reopen the R1-UPPER truth (`minAdm(3,3,3,4)=7` banked; value
  RRR-anchored) but it is the real labour.
- **Next construction that settles the open part.** Formalise the refined cover
  `{|det pivot minor| ≥ δ·(scale)}` (good) ∪ (deeper branch) as a chart split feeding the endpoint on
  the `(3,3,3,4)` binding chart, with `g_cc` and the compactness lower bound (3a) — then lift to opaque
  widths. `vslice_corner.py` / the `dim E_T = 7 = minAdm` accounting is the exact target the good-chart
  endpoint call must reproduce (`c' < dim E_T / 2 = 7/2`).
