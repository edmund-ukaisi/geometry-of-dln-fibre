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

---

## 6. ★★ OFF-SECTOR rank-drop cover (the last soundness surface) — a REAL GAP in the naive corank cover; the fix is a TRANSVERSALITY-augmented ARITY recursion

**Charge (team-lead): design the off-sector `{σ_min(Z)<ε}` recursion airtight — no null-set deletion (Codex Q3).**
Decorrelated skeptical Codex (`codex/offsector-{prompt,answer}.md`, conclusion withheld) + exact algebra
(`/tmp/sj5corner/{offsector,mgt1}.py`). **Codex CAUGHT A REAL GAP** in my first-pass corank-of-`Z`
stratification — recorded honestly, NOT papered over.

**The exact-verified per-cell finiteness (the part that IS airtight).** On the GENERIC (transverse, `m=1`)
part of corank cell `S_q`, the nested-simplex tube integral `∫_{0<s_q<…<s_1<κ} (∏s_j^{α_j})^{−c'} dμ`
(`dμ ≍ ∏s_j^{(D_j−D_{j−1})−1}`) is finite over a POSITIVE-measure neighbourhood (not the locus) at the
charges-ADD threshold `½(M₀ρ + min(M₀q, D_q))`; the inner integrals' `+1`s ADD (`offsector.py`: anchor q=2
→ 7/2, generic q=3 → the accumulated `Σ(p_j−α_j)+(q−1)>−1`). Cells GLUE at the seams (`corank2 §1` sector
boundary). `min_q = ½minAdm` (QIP, dmcheck). [FINE.]

**★ THE GAP (Codex Q2, exact-verified `mgt1.py`): `m>1` does NOT imply higher corank.** Counterexample
`Z = a·b` (scalar product): at `a=b=0`, `corank(Z)=1` but `σ_min = |ab| ≍ t²` on the diagonal (`σ_min² = t⁴
≠ dist² = t²`) — first-order vanishing FAILS, yet there is NO higher-corank stratum to catch it. So the split
"generic `S_q` (m=1) + recurse on `{corank≥q+1}`" is **INCOMPLETE**: the non-`m=1` part of `S_q` is a
**SAME-corank critical locus** of the parameter→matrix map. A corank-of-`Z` recursion MISSES it.

**The fix (honest resolution).** The `m>1` / non-transverse loci ARE the **INTERSECTION RAYS** (several product
factors degenerate coincidentally — `a=b=0` in `Z=ab`). They are NOT caught by corank-of-`Z`; they are the
**ITERATED coupled corner** (blow up the crossing: `a=u, b=uτ ⟹ ab=u²τ`, the `u₀²·unit` form — my
`stephyp-intersection-cert` Q1). So the airtight off-sector cover is a **TRANSVERSALITY-augmented recursion on
ARITY**, NOT on corank-of-`Z`:
- **GOOD tube** `{corank Z=q, parameter→Z map TRANSVERSE (uniform Jacobian bound, m=1)}`: the joint density
  gives finiteness `≥ ½minAdm`. **Requires N1 STRENGTHENED to a UNIFORM transversality bound on the tube**
  (not merely generic `m=1`) — Codex Q2.
- **BAD locus** `{corank Z=q, NON-transverse (m>1)}` = the intersection rays: handled by the iterated coupled
  corner, recursing by **peeling a deeper factor (ARITY ↓)** — the well-founded variable is ARITY (each peel
  reduces arity, bounded), NOT corank-of-`Z` (which does not decrease at the crossing). The intersection ray's
  coupled corner charges-ADD (Q1, exact `coupled_add.py`); dmcheck's QIP gives `≥½minAdm` per branch.
- **Total** (Codex Q3): finite measurable cover ⟹ subadditivity `∫_{σ_min<ε} ≤ Σ_cells ∫_{tube}`; the ARITY
  recursion is well-founded (finite) AND each level RE-VERIFIES the same estimate (loss lower bound, density,
  UNIFORM constants, bad-region containment) + a finite subcover / compact localization.

**Net (honest).** The off-sector is the DEEPEST #5 content, as flagged — and Codex's catch sharpens WHY: a
corank-of-`Z` cover alone is unsound (`m>1` gap, `Z=ab` verified). The airtight cover is the
transversality-augmented ARITY recursion: GOOD tube (uniform transversality, N1-strengthened) + intersection
rays (iterated corner, Q1) + arity well-foundedness + Codex-Q3 uniform-constant re-verification per level. This
is a GENUINE ADDITIONAL obligation beyond dmcheck's threshold-arithmetic (which is necessary — the QIP
`≥½minAdm` — but NOT sufficient for the measure-theoretic neighbourhood cover). LABOUR, not a
decorrelated-confirmed wall (arity well-foundedness + the banked iterated corner + dmcheck per-branch give the
route), but the UNIFORM transversality bound (N1-strengthened) + the finite-subcover/uniform-constant control
are the concrete owed pieces. **This supersedes §3's "rank-drop recurses (dmcheck P3)" one-liner** — the recursion
is on ARITY with a transversality gate, not a bare corank stratification.

**Owed for `innerCorankDescent_lt_top` off-sector (updated):** (1) N1 strengthened to a UNIFORM transversality/
Jacobian lower bound on the good tube [OWED, geometric — the `m=1` gate must be uniform, not generic]; (2) the
intersection-ray iterated corner = `stephyp-intersection-cert` Q1 [certified, banked-adjacent]; (3) the ARITY
recursion well-foundedness + per-level uniform-constant re-verification + finite subcover [OWED, measure
assembly]. dmcheck's no-collapse (threshold) is necessary but the measure-cover (1)+(3) is the residual work.

---

## 7. ★★★ The ARITY recursion, AIRTIGHT (the exhaustiveness PROOF) — well-founded on the product structure, bottoms out at width-2 (Eckart–Young)

**Charge (team-lead): design the off-sector arity recursion airtight — an EXHAUSTIVENESS claim, the gate is a
PROOF (does each peel STRICTLY reduce? does the base close? is the bad locus GENUINELY the intersection rays?).**
Exact: `scripts/wellfounded.py`. (Controller will run an INDEPENDENT hunt on this before formalisation.)

**The recursion (one off-sector level).** On `{σ_min(Z) < ε}` (`Z = A₂···A_L` the deeper tail), stratify by
`rank Z = ρ` (`ρ < r`; finitely many; `Core.RankLocusClosed`). Split each stratum into GOOD (transverse,
`m=1`) and BAD (non-transverse, `m>1`):
- **GOOD tube** → the iterated coupled corner + joint two-scale density, finite at `½(M₀ρ+min(M₀q,D_q)) ≥
  ½minAdm`, UNIFORM constants (compact chart + the uniform Jacobian bound, piece A).
- **BAD locus** (`m>1`) → recurse.

**★ (A) N1-STRENGTHENED — the geometric owed lemma (uniform transversality).** On the GOOD tube (the generic
part of `{rank Z=ρ}`), the `(ρ+1)`-minor map is a submersion with a UNIFORM Jacobian lower bound on each
compact sub-chart, so `σ_{ρ+1}(Z)² ≍ dist(·,{rank≤ρ})²` UNIFORMLY (`m=1`, not merely generic). `#109
normalSlice_transfer` gives the straightening CoV; this ADDS the uniform order-1 bound. [OWED, geometric — the
one concrete geometric lemma; feeds the good-tube uniform constants.]

**★ (C) WELL-FOUNDEDNESS (the exhaustiveness core — VERIFIED `wellfounded.py`).** The `m>1` bad loci arise
**ONLY from the PRODUCT structure**: a SINGLE matrix has `σ_{ρ+1}² ≍ dist²` (`m=1`) ALWAYS (Eckart–Young:
`σ_{ρ+1}` IS the distance to `{rank≤ρ}`; verified `σ₂/t ∈ [0.85, 3.8]`, order 1). `m>1` requires `≥ 2`
factors degenerating COINCIDENTALLY (`Z=ab`: `σ₂(Z) ≍ t²`, order 2 at `a=b=0`; verified). So:
- each recursion step PEELS a coincidentally-degenerating factor (arity `L → L−1`, STRICTLY ↓) or restricts to
  a factor's rank-drop stratum (Noetherian dimension STRICTLY ↓);
- it **BOTTOMS OUT at width-2** — a single matrix (no product), where Eckart–Young gives `m=1` EVERYWHERE, so
  **there is NO bad locus at the base**; the base closes (= #4, S2-uniform). **NO infinite regress.** [This is
  the clean well-foundedness: `m>1` is a product-only phenomenon that the arity descent exhausts.]

**★ (D) The BAD locus IS the intersection rays ⟹ Q1 applies (GENUINELY).** At the `m>1` crossing, `σ_min(Z)`
factors as the PRODUCT of the coincidentally-degenerating factors' contributions (`Z=ab`: `σ_min=|ab|`), i.e.
the COUPLED-CORNER monomial. Blow up the crossing (`a=u, b=uτ ⟹ ab=u²τ`): the `u₀²·unit` form, charges ADD
(`stephyp-intersection-cert` Q1, exact `coupled_add.py`). So the bad-locus estimate is EXACTLY the iterated
corner Q1 — banked-adjacent — and `dmcheck` P3 gives the per-branch `≥ ½minAdm`.

**★ (E) FINITE subcover + UNIFORM constants (Codex Q3).** `{σ_min(Z)<ε}` is covered by FINITELY many adapted
charts: the parameter box is compact, the rank/transversality stratification is Noetherian (finitely many
strata, dimension ↓), and each stratum's good tube is covered by finitely many compact sub-charts on which the
estimate constants are uniform. Subadditivity over the finite measurable cover: `∫_{σ_min<ε} H^{−c'} ≤
Σ_charts ∫_chart H^{−c'} < ∞`. Overlaps/seams are harmless (nonnegativity + measurable cover). Each recursion
level RE-VERIFIES the same four (loss lower bound, joint density, uniform constants, bad-region containment).

**Net (the airtight exhaustiveness).** The off-sector arity recursion is well-founded (product-structure
descent, VERIFIED bottoms out at width-2 via Eckart–Young), the bad locus is genuinely the intersection rays
(Q1 applies), and the cover is finite with uniform constants (compact + Noetherian). The exhaustiveness holds
as a PROOF, modulo the TWO owed builds: **(A) N1-strengthened** (uniform transversality on the good tube —
geometric) and **(E) the finite-subcover / uniform-constant / Noetherian-termination measure assembly**. The
Q1 iterated corner (D) + dmcheck per-branch are banked-adjacent; the well-foundedness (C) is verified
(product-only `m>1`, Eckart–Young base). This is LABOUR (A + E), not a wall.

**Owed for `innerCorankDescent_lt_top` off-sector (final list):**
1. **[OWED, geometric] N1-strengthened uniform transversality** `σ_{ρ+1}(Z)² ≍ dist²` uniform on the good-tube
   compact charts (order-1, banked-adjacent `normalSlice_transfer` #109).
2. **[OWED, measure] the Noetherian/arity recursion assembly** — well-foundedness (banked via Eckart–Young
   base + product-only `m>1`), finite subcover (compactness), uniform constants per chart, measurable
   good/bad split.
3. **[BANKED-ADJACENT] the bad-locus iterated corner** = Q1 (`stephyp-intersection-cert`) + dmcheck P3
   per-branch `≥½minAdm`; the good-tube joint density = `corank2 §2` generalized (`offsector.py`).

---

## 8. ★★★★ REFUTATION + PIVOT (2026-07-12) — §6/§7 naive corner SUPERSEDED; the off-sector PROOF is the coupled `diag(b)` (route B / the decorated descent), NOT the naive-corner charges-ADD

**The controller's independent obstruction hunt (`offsector-independent-hunt.md`, fresh decorrelated seat)
REFUTED §6/§7 as an airtight PROOF.** I reconcile HONESTLY (not defend). The `½·minAdm` VALUE survives; my
§7 MECHANISM is wrong. Two errors, both verified (`scripts/caterror.py`, the R1 thread):

1. **§7 (C) Eckart–Young is a CATEGORY ERROR.** `σ_min = dist(·,{rank≤ρ})` (Eckart–Young) is a MATRIX-space
   distance, true for EVERY matrix (products included) — it is NOT the PARAMETER-order the integral needs. A
   SINGLE matrix can have parameter-order `> 1`: `M(t)=[[1,t],[t,0]]` is affine+immersive yet `σ_min ≍ t²`
   (tangent to `{det=0}`; verified). So "m>1 is product-only, base bottoms out at m=1" is FALSE. The real
   hypothesis is UNIFORM TRANSVERSALITY / metric regularity (owed piece A), strictly stronger than immersion.
2. **"charges ADD to ½Σ-dims" is a UNITS-SECTOR-ONLY value.** For the scalar chain `Z=a₂···a_L`,
   `σ_min²=(∏aᵢ)²`, `∫∏|aᵢ|^{−2c}` factorizes → `lct = ½ = ½minAdm` (minAdm=1), NOT `(L−1)/2`. Each `aᵢ→0`
   is a GENUINE singular direction (a shared deep factor vanishing), so the true threshold is the **MIN**
   over binding directions, not the SUM. My `nested3.py` "½Σ = ½minAdm" is the outer-radial value UNDER the
   units assumption — correct locally, FALSE globally. The corank-≥2 SHARED-DIVISOR collapse (R1-proven:
   `d²(x²+y²)` shared → `lct=½` MIN vs `(d₁x)²+(d₂y)²` unshared → `lct=1` ADD, IDENTICAL widths) is exactly
   what a threshold-only / charges-ADD corner cannot see, and it BINDS at `(3,3,4)`.

**§6/§7 are SUPERSEDED as the off-sector proof.** Do not build from them. The reconciliation ↓ pivots to the
coupled `diag(b)`.

### §7 ↔ R1 reconciliation (`verify-r1-diagb-334.md`): where they AGREE / DISAGREE

R1's PROVEN `(3,3,4)` resolution (the genuinely-binding corank-2 witness, RLCT `4 = ½·minAdm`): peel `C¹` at
`t₁=1` → `F ∼ ‖T‖² + ‖Δ·S‖²`, `T` and `(Δ,S)` in DISJOINT variable sets ⟹ RLCTs **ADD** (Watanabe product
rule): `2 + 2 = 4`. Within `‖Δ·S‖²`: radial `Δ = a·[…]` (Jac `|a|³`, dim 4), the shared shear `e = w−vu`
couples row-2 to row-1, `‖ΔS‖²∘π ∼ a²(‖P‖² + e²‖Q‖²)`; the divisor `a` binds at `(3+1)/2 = 2`, the inner
coupled corner at `5/2`, and the value is the **MIN** `min(2, 5/2) = 2`. Threshold-only (multiplicity,
independent `δ₁,δ₂`) UNDER-counts → `3` (wrong).

- **DISAGREE — §7's Q1 "bad locus = intersection rays ⟹ charges ADD (½Σ)".** R1 shows the corank-2 block is
  **MIN** (the freed-block divisor `a` binds at `½·dim(Δ)`, BELOW the inner corner `5/2`), with DISJOINT
  blocks ADDing (Watanabe) — governed by the SHARED-DIVISOR data (the shear `e`: which divisor/coefficient
  couples which generator). A naive charges-ADD corner OVER-counts (would give `2 + 5/2 = 9/2` for `‖ΔS‖²`,
  not `2`); threshold-only UNDER-counts (`3`). Neither naive mechanism is R1's `diag(b)`. **§7's Q1 is the
  wrong mechanism.**
- **AGREE — route B (integrate-Γ-first + black-box decorated IH, §1).** Route B integrates the freed block
  `Γ=Δ` FIRST (freed Morse, threshold `½·dim(Δ) = 2`) then defers to the reduced/disjoint via the IH — which
  is EXACTLY R1's `min(a-divisor 2, inner)` + disjoint-`T` Watanabe-ADD. Route B carries the shared-divisor
  data in the DECORATION (`supp` = which exceptional divisor weights which generator; `coeff` = the shear
  coupling) — so **route B / the decorated descent IS Aoyagi's coupled `diag(b)`** (the `diag(b)` symbolic
  support = the carrier's `supp`+`coeff`). The threshold-only invariant (multiplicity only) is what R1
  refuted; the DECORATED carrier (full `supp`) carries what `diag(b)` needs. So route B AGREES with R1.

**PIVOT (the off-sector proof).** The off-sector is NOT a separate naive-corner cover (§6/§7) — it is the
DECORATED DESCENT itself (route B: binding-cut peel + freed Morse + black-box decorated IH, the IH carrying
`supp`+`coeff` = the `diag(b)` shared-divisor data). This is the R1 thread's decided route (task #122). The
correct mechanism at each binding cut is `minAdm M = peelCharge + minAdm(redChain)` (the binding-cut
identity, `exists_binding_cut`) — route B adds EXACTLY `peelCharge + minAdm(redChain) = minAdm(M)` (NOT the
naive ½Σ), and the reduced IH resolves the reduced chain's own sharing (recursively). At the binding cut
`peelCharge` can be a corank-≥2 coupled block (`(3,3,4)`: corank-2), which route B's freed Morse + the
decorated `supp` handle; the naive corank-≤1 recursion of §7 does NOT reach it.

**Net.** §6/§7 REFUTED as a proof (category error + units-only charges-ADD, missing the shared-divisor
collapse). The off-sector proof PIVOTS to route B / the decorated descent = the coupled `diag(b)` (R1, #122),
which carries the shared-divisor `supp`+`coeff` data. The `½minAdm` VALUE survives (QIP + Aoyagi + R1). Owed
piece A (uniform transversality) is STILL owed (route B's units sector needs it); the naive-corner well-
foundedness (§7-C) is DROPPED (replaced by the binding-cut arity recursion `minAdm = peelCharge + minAdm(redChain)`,
which strictly decreases arity and is the driver's own recursion — well-founded, banked).
