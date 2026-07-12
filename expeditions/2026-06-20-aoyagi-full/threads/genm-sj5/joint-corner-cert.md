# #5 coupled-corner JOINT ESTIMATE — design cert (`innerCorankDescent_lt_top` / peelOp-preserves core)

**Seat:** pen-and-paper (design cert BEFORE formalisation — genm-sj5-cover). **Date:** 2026-07-12. **NO
Lean.** **Charge (team-lead):** the #5 mountain — at the binding cut `minAdm M = P + minAdm(redChain)` the
freed corank block's residual exponent EXACTLY SATURATES the reduced-IH threshold, so a naive Hölder split
is infeasible. **HOW does the (S,J) double induction establish JOINT finiteness at the exact saturation?**
Generalize the banked corank-2 joint estimate to the general coupled corner; hand desc4 a Lean-friendly
coupled estimate for `innerCorankDescent_lt_top`.

**Exact algebra (mine):** `/tmp/sj5corner/{coupled_add,nested3}.py` (the corner charges-ADD; the nested
recursion; the units-dependence of the sector gate — exact + numeric). **Decorrelated:** own xhigh
`local-codex-consult`, conclusion WITHHELD (asked HOW joint finiteness holds at saturation, did not state my
answer): `codex/jointsat-{prompt,answer}.md`. **Codex earned it** — independently returned the SAME mechanism
(projective radialization `t=u₀s`) AND supplied a cleaner second route (integrate-Γ-first + black-box IH).
**Consumed:** `corank2-cert` (genm-vsastruct, the worked q=2 joint two-scale density), `stephyp-intersection-cert`
(Q1 no-collapse), dmcheck `cert` (the settled invariant, P3), `RouteMSJFreedPeel` (freedSchurLoss),
`stephyp-buildplan` (§5′ N4/N5), `peel-buildplan` (§1.3-3 deeper).

---

## ★ HEADLINE (the load-bearing finding, decorrelated-confirmed)

**The saturation is defeated by an ASYMMETRIC coupling, NOT a symmetric split.** Two equivalent routes, both
giving the charges-ADD threshold `c' < ½(P + minAdm(redChain)) = ½minAdm(M)`:

- **Route (A) — projective radialization (nested corner).** Substitute the reduced radial `t = u₀·s`
  (`s ∈ (0,1)`); the Jacobian pushes the reduced block's `R = minAdm(redChain)` worth of dimension ONTO the
  freed block's radial `u₀`: measure `u₀^{P+R−1} s^{R−1} du₀ ds dν`, loss `u₀²(U₀ + s²U_r)`. The `s`-integral
  is UNIFORMLY finite (units bounded below), leaving `∫₀¹ u₀^{P+R−1−2c'} du₀ < ∞ ⟺ c' < (P+R)/2`. All the
  charge piles onto ONE terminal divisor; the loss stays order 2. [= the corank-2 corner `u₀²(U₀+τ²U₁)`,
  generalized; exact `/tmp/sj5corner/coupled_add.py`, `nested3.py`.]
- **Route (B) — integrate-Γ-first + black-box decorated IH (CLEANER, banked).** On the units sector the loss
  admits the additive block comparison `decLoss ≥ commonDivisor(u)²·(c·‖Γ‖² + V(w))` (`Γ` the freed corank
  block, `V` the reduced-chain loss; via the Schur `loss_blockSplit` + Rayleigh `frobSq_mul_ge`). Integrate
  `Γ` FIRST (freed-block Morse, dim `P`): `∫_Γ (c‖Γ‖² + V)^{−c'} dΓ ≲ V^{P/2−c'}` for `c' > P/2`. This SHIFTS
  the exponent by exactly `P/2`, so the reduced integral is `∫_w V^{−(c'−P/2)}·(reduced jac) dw =
  D'.integral(c'−P/2)`, finite by the DECORATED IH because `c' − P/2 < ½minAdm(redChain)` STRICTLY (the shift
  is `carrierThreshold_shift`). **The IH is used as a BLACK BOX** — its internal resolved structure is NOT
  needed; only its decorated finiteness `DecoratedBoxThresholdFinite D'` (which carries the jac monomial).

**Why the naive split fails (the saturation, exact).** `½(P+R) = P/2 + R/2` sits EXACTLY at the sum of the
two individual bounds. A symmetric split (drop the reduced, or Hölder-split the exponent `c' = c_f + c_r`)
needs `c_f < P/2` AND `c_r < R/2` with `c_f + c_r = P/2 + R/2` — infeasible for strict inequalities. Dropping
the reduced gives only `P/2` (undershoot by `R/2`); the reduced's budget must be ADDED, not split away. The
ASYMMETRIC integrate-Γ-first (route B) / projective radialization (route A) shifts `c'` by `P/2` so the
reduced sits STRICTLY inside its IH range — no saturation after the shift. [Exact: `coupled_add.py` —
drop-reduced `→ 2 = a/2`, coupled `→ 7/2 = (a+b)/2`; Hölder-split at the boundary INFEASIBLE.]

---

## 1. The exact model + verification (charges ADD)

Freed corank block dim `P` (radial `u₀`, block-radial Jacobian `u₀^{P−1}`); reduced chain effective dim
`R = minAdm(redChain)`; units `U₀, U_r ≍ 1` on the sector. Coupled corner `F = u₀²(U₀ + s²U_r)` after the
projective sub `t = u₀ s`:

> **`∫₀¹∫₀¹ u₀^{P+R−1} s^{R−1} (U₀ + s² U_r)^{−c'} du₀ ds < ⊤ ⟺ c' < (P+R)/2`** — the `s`-integral finite
> (units), the `u₀`-integral binds at `(P+R)/2`. [V exact: `coupled_add.py` cases (4,3)→7/2, (1,1)→1,
> (2,2)→2, (3,5)→4; nested 3-level `nested3.py` (4,3,1)→4, (2,2,2)→3, (1,5,3)→9/2 — the recursion piles ALL
> dims onto the outer radial.]

**The corank-2 anchor recovered.** `P = ab = 4` (freed `2×2`), `R = minAdm(1,3,4) = 3` ⟹ `(4+3)/2 = 7/2` —
the banked `corank2-cert` value, via the joint two-scale density `dμ ≍ s₂²ℓ(s₂)`. The log tie is harmless
(subdominant to the power; strengthens only the excluded `η=1` boundary).

## 2. The nested double induction (the recursion structure)

Route (A) generalizes to `k` levels by iterating the projective sub (`nested3.py`): the reduced chain is
itself resolved, each successive collapsing block's scale nested onto the outer `u₀`, so `u₀` carries
`Σ_j d_j = minAdm(M)` and the threshold is `½minAdm(M)`. Route (B) makes this an INDUCTION: one peel = one
integrate-Γ-first exponent-shift `P/2 = ½peelCharge`, landing on `D'.integral(c'−½peelCharge)`; the decorated
IH recurses. **The base is the width-2 uniform leaf** (#4, `corankLeaf(Z=I)`, S2-verified uniform).
`minAdm M = peelCharge + minAdm(redChain)` (`exists_binding_cut`) is the arithmetic that makes the shift land
inside the IH range.

## 3. The units-sector gate + the rank-drop recursion (T4, dmcheck P3)

- **On the units sector** `{Q_b Q_bᵀ ≽ c·I}` (equivalently `σ_min(Z) ≥ ε` on the WHOLE deeper tail — the
  γ-lock correction; `Z = A₂···A_L`): the units `U₀, U_r ≥ c(ε) > 0`, so the `s`-integral is UNIFORMLY finite
  (route A) / the Rayleigh comparison holds (route B). This is the T4 no-collapse gate (`stephyp-cert §7-Q2`);
  the freedSchurLoss interface (pivot energy `> 0`, `Q_bQ_bᵀ` PosDef) is exactly this sector.
- **Off the sector** `{σ_min(Z) < ε}`: the units → 0, the `s→0` endpoint becomes a NEW singular direction, the
  reduction to a single `u₀`-power FAILS. This complement RECURSES (a deeper stratum, higher `Mval`, threshold
  `≥ ½minAdm` per-branch by dmcheck P3, `D_q ≤ M₀q`-at-binding). ★ **Codex Q3 caveat (fold in):** excising the
  rank-drop is legitimate ONLY via ADAPTED CHARTS that stratify and control the small-`σ` NEIGHBOURHOODS
  (including the unit's transverse vanishing) — NOT by deleting the measure-zero locus (a null set's arbitrarily
  small neighbourhoods can still contribute an infinite integral; finite measure is insufficient). This is the
  `RouteMSJSigMin` sector cover + `Core.RankLocusClosed` stratification + N3-termination (finite ranks).

## 4. What the decorated IH must carry (reconciling the "black-box" tension)

`RouteMSJFreedPeel`'s note says "the strong IH is insufficient as a black box → the (S,J) double induction."
**Reconciled (this is a scope clarification, not a contradiction):**
- The IH must be the DECORATED box finiteness `DecoratedBoxThresholdFinite D'` (it carries the jac monomial /
  the `H⁻⁴` truncated Gram weight — the Q2 reason the plain undecorated IH is dead). NECESSARY.
- But its INTERNAL resolved-radial structure is NOT needed (route B uses it as a black box after
  integrate-Γ-first). So "IH insufficient as a black box" refers NOT to the reduced integral itself, but to the
  three freedSchurLoss INTERFACE hypotheses (`Q_bQ_bᵀ` PosDef, pivot energy `> 0`, `c' > a·b/2`) which FAIL
  POINTWISE and must be supplied as a MEASURE statement (the §3 sector cover + rank-drop recursion). That
  measure-level supply — not a stronger IH — is the genuine #5 work.
- **Consequence for FaithfulSJAt (★ coercivity is NOT carried — precision fix, controller-flagged).** The
  carried `adm` is exactly **`{genuineCarrier + provenance (res=(Γ·Z_tail)_ρ) + α (pSimultaneous) + β
  (monomialThreshold≥½minAdm) + minAdm≤a·n + residualSupport≡0}`** — and every one of these is
  **z-INDEPENDENT** (a structural / combinatorial / arithmetic property of `supp`, `jac`, dims, or the
  parametrization `e`), hence holds on ALL of `dom`, as a carried invariant must. The units-sector coercivity
  (`Q_bQ_bᵀ ≽ c·I` / `σ_min(Z) ≥ ε`) is the ONE **z-DEPENDENT** fact — it FAILS POINTWISE on the rank-drop
  locus `{σ_min(Z) < ε} ⊂ dom`, so it CANNOT be a carried `adm` clause (adm must hold on the whole domain).
  It is **PER-PEEL-SUPPLIED** by the sector cover (§3): the peel restricts to `{σ_min(Z) ≥ ε}` (where route B
  fires) and the complement RECURSES. The invariant does NOT carry a resolved radial form of the whole reduced
  chain (route B uses the black-box IH). **Crisp criterion:** a clause may be carried iff it is z-independent
  (holds on all of `dom`); coercivity is z-dependent, hence per-peel/sector, not carried. [This SIMPLIFIES the
  earlier "IH must carry the resolved structure" reading and keeps the #4 carry {…+residualSupport≡0} COMPLETE
  as-is — the coercivity was never part of it.]

## 5. Lean-friendly shape (`innerCorankDescent_lt_top`) + banked-piece map

The freed triple integral (post `gammaPeelIntegral_schurShearFree_eq`, banked) `∫_{A'}∫_{x}∫_{Γ}
(freedSchurLoss)^{−c'}` closes by:
1. **Sector cover** `{σ_min(Z) ≥ ε} ⊔ {< ε}` — `RouteMSJSigMin` [ADJ] + `Core.RankLocusClosed` [BANKED].
2. **On the sector:** `freedSchurLoss_inner_peel_lt_top` [BANKED, `RouteMSJFreedPeel`] integrates `Γ`
   (route B), giving the `w^{P/2−c'}` bound (`w` = pivot energy = the reduced loss); then the DECORATED IH on
   the reduced chain at `c'−½peelCharge` [`carrierThreshold_shift` BANKED + the IH] closes it. The additive
   comparison = `loss_blockSplit` [BANKED] + `frobSq_mul_ge` Rayleigh [BANKED].
3. **Off the sector:** the rank-drop branch recurses (higher `Mval`), threshold `≥ ½minAdm` per-branch
   (dmcheck P3), N3-termination (finite ranks). [OWED small: the finite-stratum induction + adapted-chart
   neighbourhood control — Codex Q3.]
4. **`c' ≤ a·b/2` branch:** `freedSchurLoss_inner_bounded_lt_top` [BANKED] (pivot energy > 0 alone, bounded
   integrand) — no shift needed.

**The charges-ADD content lives in step 2** (the exponent-shift `½peelCharge` composing with the IH), NOT in a
symmetric split. Guard (from stephyp-cert / dmcheck): NEVER "higher codim ⟹ slack" (the `x²(x²+y^{2N})`
correction); the per-branch threshold is the joint tube estimate `½(M₀ρ + min(M₀q, D_q))`, `m=1` per direction.

---

## Firmest / most-likely-to-break / next

- **Firmest.** The saturation is defeated by the ASYMMETRIC coupling: integrate-Γ-first shifts `c'` by
  `½peelCharge`, landing the reduced integral STRICTLY inside the decorated-IH range; charges ADD to
  `½minAdm(M)`. Exact (`coupled_add.py`/`nested3.py`), decorrelated-confirmed (Codex: projective radialization
  `t=u₀s` + the integrate-Γ-first route), and route B is entirely BANKED pieces (`freedSchurLoss_inner_peel` +
  `loss_blockSplit` + Rayleigh + `carrierThreshold_shift` + the IH). Anchor `(3,3,3,4)` recovered (7/2).
- **Most likely to break.** The OFF-SECTOR recursion (§3): Codex Q3 flags that deleting the rank-drop null set
  is illegitimate — the small-`σ_min(Z)` NEIGHBOURHOODS need adapted-chart control (the unit's transverse
  vanishing), and this is where a hidden collapse would hide if some width had a rank-drop branch with
  `D/m < n₀` (dmcheck de-risked no-collapse on the sweep, but the general-width per-branch `D_q ≤ M₀q` check is
  the concrete verification). N3-termination + the per-branch `≥ ½minAdm` is the [OWED] assembly.
- **Next.** desc4 formalizes `innerCorankDescent_lt_top` via the §5 map (route B, banked-heavy) + the sector
  cover; I audit the OFF-SECTOR recursion (adapted-chart neighbourhood control, per-branch `½minAdm`, finite
  stratification) hardest — that is the residual soundness surface. The #4 audit PREEMPTS this the moment desc4
  reports the committed #4 build.
