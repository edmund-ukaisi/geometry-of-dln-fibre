# Off-sector "il" recursion — the (□) discharge design cert (`innerCorankDescent_lt_top`)

**Seat:** pen-and-paper WITNESS (design + adversarial stress-test), genm-sj5-domination. **Date:**
2026-07-12. **NO Lean, NO build.** Exact algebra (minAdm/QIP recursion, exact rationals) + deterministic
quadrature for the analytic scalings; Monte-Carlo only as a guide. Decorrelated `local-codex-consult`
(xhigh, conclusion withheld): `codex/offsector-il-{prompt,answer}.md`. Reproducible scripts under `scripts/`.

**Consumed / read:** `codex/offsector-scoping-answer.md` (the tube computation); `genm-sj5-recon/
s0-reduced-core-fidelity-cert.md` (§S0.5 domination + the divisor `det(Q_bQ_bᵀ)^{−a/2}`);
`discuss-at-close.md` history (#118 a·b 2nd-order counterexample, #119 network-depth reconciliation);
`genm-sj5/joint-corner-cert.md` §6/§7 (refuted naive corner) + §8 (route-B pivot);
`genm-sj5/offsector-independent-hunt.md` (the §7 refutation); the banked bricks
`RouteMSJInnerDescent.freedSchurLoss_inner_peel_le` / `_bounded_le` and `RouteMSJCornerComparator.
cornerComparator_adm`; the banked convexity `RouteMSJTransversality` (`minAdm_redChain_succ_ge`).

---

## ★ VERDICT — CLOSES (labour), decorrelated-confirmed; the mechanism is SHARPENED (and one prior route corrected)

The off-sector `{σ_min(Q_b) < ε}` (the last genuine content of #5 `DecoratedStepHyp`, the route-ii native
(□) discharge, on which #108 rests) **CLOSES for `c' < carrierThreshold(M) = ½·minAdm(M)`** — no
obstruction survived the stress-test or the decorrelated Codex. It is **LABOUR, not a wall.** Two
load-bearing corrections to the prior framing, both now nailed:

1. **The single-corner atom domination is LOSSY off-sector — it must NOT be the off-sector proof.** The
   banked atom bound `∫_Γ freedSchurLoss^{−c'} ≤ det(Q_bQ_bᵀ)^{−a/2}·Cresid·(w+resid)^{−(c'−ab/2)}` (needs
   `Q_bQ_bᵀ` PosDef) **blows up as `Q_b → 0`**, whereas the TRUE freed-corner integral stays finite (the
   freed corner `Γ` couples to `Q_b` only through `Γ·Q_b → 0`, so `∫_Γ → w^{−c'}·vol`, the banked BOUNDED
   bound). Integrating the atom bound over the free corank block `A_cor` **diverges** whenever `a ≥ M₂`.
   So the off-sector is NOT "the good sector with a bigger constant"; it needs a genuinely different split.
2. **The correct off-sector proof is a TWO-BRICK split + a rank/flag stratification, reducing each stratum
   to the arity-`(L+1)` IH with charges that ADD to `½·minAdm(M)`.** `σ_min`-only splitting is TOO CRUDE for
   corank `b > 1` (it undershoots — verified `(3,3,3)`: `5/2 < 7/2`); the full singular-**flag**
   stratification closes tight.

The `½·minAdm` VALUE is untouched (it was already defended by QIP+Aoyagi in `offsector-independent-hunt`);
this cert supplies the airtight PROVING mechanism for the measure-theoretic off-sector, resolving the #118
soundness gap.

`CLOSES (labour): off-sector = two-brick split (banked atom brick where Q_bQ_bᵀ is PosDef / banked bounded
brick where it is not) + tail-rank×corank-flag stratification, each stratum → the arity-(L+1) reduced-
comparator IH with charge C_j = (a−j)(b−j)+minAdm(redChain@t+j) ≥ minAdm(M). No width undershoots (3161
binding cuts checked, 0 undershoots). #118 resolved by ARITY recursion (not rank-drop) + full-IH coverage +
Schur-normal base transversality. Owed = the uniform adapted-chart / finite-subcover MEASURE assembly
(piece A + E), LABOUR.`

---

## 1. The situation, precisely (banked pieces + the two bricks)

At a binding cut `t★` of `M` (arity `L+2`): `a = M₀−t★`, `b = M₁−t★`, `peelCharge = a·b`. The freed `a×b`
corner `Γ` is integrated by a banked Gaussian lemma; the deeper tail row-splits into `t★` pivot rows `Q_p`
and `b` corank rows `Q_b = A_cor·Z_deep`, where **`A_cor` (the `b×M₂` corank rows of the peeled layer) is a
FREE integration variable** and `Z_deep = prod(A₃…A_L)` is the even-deeper product (`M₂×M_last`). The pivot
energy is `w = frobSq(Γ'·Z_deep)`, the loss of the clean reduced comparator `D'` on `redChain = (t★,M₂,…)`
(arity `L+1`), `carrierThreshold(redChain) = ½·minAdm(redChain) = carrierThreshold(M) − ½·ab`.

Two BANKED freed-corner bounds (`RouteMSJInnerDescent`):
- **ATOM** `freedSchurLoss_inner_peel_le`: `∫_Γ (…)^{−c'} ≤ det(Q_bQ_bᵀ)^{−a/2}·Cresid·(w+resid)^{−(c'−ab/2)}`
  — **requires `Q_bQ_bᵀ` PosDef** (`hG`) and `c' > ab/2`. Value blows up as `Q_bQ_bᵀ → 0`.
- **BOUNDED** `freedSchurLoss_inner_bounded_le`: `∫_Γ (…)^{−c'} ≤ w^{−c'}·vol(box)` — needs only `w > 0`,
  `c' ≥ 0`. Value is FLAT as `Q_b → 0`.

GOOD sector `{σ_min(Q_b)² ≥ ε}` closes cheaply (atom, `det ≤ ε^{−ab/2}` constant, → `D'`-IH). **DONE.** The
open surface is the off-sector `{σ_min(Q_b) < ε}`.

## 2. The off-sector closure — the mechanism (airtight, with the owed measure pieces named)

**Split the freed-corner integral by `τ := σ_min(Q_b)` vs `√w`** (the exact interpolation point, Fact 2 in
the Codex prompt): the TRUE `∫_Γ = det(Q_bQ_bᵀ)^{−a/2}·∫_{u∈box scaled by τ}(w+‖u‖²)^{−c'}du`.
- **`τ ≥ √w`:** the atom brick is valid (`Q_bQ_bᵀ` PosDef there) and gives `≤ det^{−a/2}·w^{−(c'−ab/2)}·C`.
- **`τ < √w`:** the bounded brick gives `≤ w^{−c'}·vol` — this CAPS the would-be `det^{−a/2}` blow-up.

**Stratify the off-sector domain by (tail rank `ρ = rank Z_deep`, corank-flag level `j`)** — the number `j`
of small singular values of `Q_b` (`Core.RankLocusClosed`: finitely many closed rank strata). On each
`(ρ, j)` stratum the corank-block integral reduces to the **reduced comparator IH at cut `t★+j`**:

> `I_off,(ρ,j) ≤ C · D'_{t★+j}.integral(c' − ½·C_j)`, where `C_j = (a−j)(b−j) + minAdm(redChain@t★+j)`.

`D'_{t★+j}` is a genuine `cornerComparator`-admissible decoration on the arity-`(L+1)` chain `redChain@t★+j`
(BANKED `cornerComparator_adm`, `genuineCarrier` via `e=id`), so the arity-`(L+1)` IH closes it whenever
`c' − ½C_j < carrierThreshold(that redChain)`, i.e. `c' < ½·C_j`. **Charges ADD:** `C_j ≥ minAdm(M)` (§3), so
`c' < ½·minAdm(M) = carrierThreshold(M)` suffices for every stratum. The finitely many strata sum
(subadditivity over a measurable cover).

### 2a. The clean `b = 1` leading case (exact threshold, tight)

For `b = 1` the flag has a single level. The corank-block integral on the full-rank-tail chart is
`G(w,Z_deep) = ∫_{A_cor∈box} [freed-corner integral] dA_cor`, and **`G ≤ C·w^{−(c'−ab/2)}` with `C` UNIFORM
in `Z_deep`** on `{Z_deep: top M₂−1 singular values ≥ c₀ > 0}` — the box on `A_cor` CLIPS the anisotropic
`det^{−a/2}` singularity so no `1/∏σ` divisor appears (deterministic-quadrature verified: `G·w^{c'−ab/2}` is
BOUNDED and even decreasing as the tail singular value `σ → 0`, `scripts/G_exact.py`, `G_general.py`,
`G_mc.py`). Then `I_off ≤ C·D'.integral(c'−ab/2) < ⊤` by the arity-`(L+1)` IH for `c'−ab/2 <
carrierThreshold(redChain)`, i.e. `c' < carrierThreshold(M)` — **the full threshold, tight (zero slack).**
The two-regime bound composes as: atom part `w^{−(c'−a/2)}` (dominant, `a/2 ≤ M₂/2`), bounded part
`w^{−(c'−M₂/2)}`, both `< carrierThreshold(redChain)` in exponent at binding.

**The `a ≥ M₂` scare is a non-event at binding cuts.** The untruncated atom `∫_{A_cor}det(Q_bQ_bᵀ)^{−a/2}`
diverges iff `a ≥ M₂` — but the banked convexity forces `a ≤ M₂` at EVERY `b=1` binding cut: `R_{t+1}−R_t ≥
a` (convexity, `b=1`) and `R_{t+1}−R_t ≤ M₂` (incidence, rank `≤ M₂`) ⟹ `a ≤ M₂`. **Swept: 0 cases `a > M₂`
across 3161 binding cuts; 335 borderline `a = M₂`** (`scripts/verify_arity4.py`). At `a = M₂` the atom part
carries an extra `log(1/w)` — HARMLESS, absorbed by the strict `c' < carrierThreshold(M)` (a positive
exponent margin dominates any log). So the atom's divergence never bites a genuine peel.

### 2b. The `b > 1` case genuinely needs the FLAG (σ_min-only UNDERSHOOTS)

`σ_min`-only splitting mischarges corank `b > 1`. **Verified `M=(3,3,3)`, `t★=1`, `a=b=2`:** the
`σ_min`-only bounded charge gives `5/2 < 7/2 = ½·minAdm`. The correct switch is `det(Q_bQ_bᵀ)=∏τ_k² ≍ r^2`
(the FULL flag, not the single smallest `τ`), producing `r^{4−2c'}log(1/r)` and the tight threshold `7/2`.
The flag charges recover it exactly: `C_0 = (2)(2)+R_1 = 4+3 = 7`, `C_1 = (1)(1)+R_2 = 1+6 = 7`,
`C_2 = 0+R_3 = 9` — all `≥ 7 = minAdm(3,3,3)` (`scripts/verify_flag.py` CHECK D). So `b > 1` closes via the
singular-flag stratification (= the "coupled corner"/`corank2` two-scale density, generalized), NOT the
scalar `σ_min` split.

## 3. Charges ADD — the exact threshold arithmetic (the load-bearing check)

The flag charge `C_j = (a−j)(b−j) + minAdm(redChain@t★+j) ≥ minAdm(M)`. Proof (exact, `scripts/verify_flag.py`):
- **Convexity (banked `RouteMSJTransversality`):** at a binding cut, `R_{t+i+1}−R_{t+i} ≥ (a−i)+(b−i)−1`.
  Telescoped: `R_{t★+j} − R_{t★} ≥ (a+b)j − j²` (CHECK B: **0 violations**, 3161 cuts).
- Hence `C_j − minAdm(M) = [(a−j)(b−j) − ab] + [R_{t★+j} − R_{t★}] ≥ −(a+b)j + j² + (a+b)j − j² = 0`.
- **CHECK C: `C_j ≥ minAdm(M)` for ALL flag levels `j`, ALL 3161 binding cuts — 0 undershoots.** Every cut is
  **tight at `j=0`** (`C_0 = minAdm(M)`, zero slack — the binding identity `minAdm(M) = peelCharge +
  minAdm(redChain)`). Zero slack means the threshold is EXACTLY saturated; the log corrections (a=M₂
  borderline; the b>1 `∏τ ≍ r²` switch) are absorbed by the STRICT inequality `c' < carrierThreshold(M)`,
  not by slack.

This is exactly the joint-corner-cert §1 "saturation defeated by the asymmetric coupling": the freed corner
carries `½·peelCharge`, the reduced chain carries `½·minAdm(redChain)`, charges ADD to `½·minAdm(M)`, and the
saturating log is subdominant to the strict margin.

## 4. THE #118 GAP — RESOLVED (arity recursion, not rank-drop; full-IH coverage; Schur-normal base)

**The counterexample (reconstructed).** `Z = a·b` (two scalar factors, chain `(1,1,1)`). At `a=b=0`,
`corank(Z)=1` and `σ_min(Z)=|ab|`; on the diagonal `a=b=t`, `σ_min = t² ≠ dist = t` — a **second-order**
(`m>1`) degeneration. A **rank-drop-stratum recursion** ("recurse into `{corank Z ≥ q+1}`") is UNSOUND: `Z`
is `1×1`, `{corank ≥ 2} = ∅`, so the recursion NEVER reaches `a=b=0`'s 2nd-order structure.

**The resolution (matching #119, made airtight).** Recurse on **NETWORK DEPTH = ARITY**, not on rank-drop.
Three facts make it reach every degenerate point:
1. **`(1,1,1)` is a BASE case (arity 2).** Its integral `∫_{[0,1]²} frobSq(ab)^{−c'} = ∫a^{−2c'}∫b^{−2c'}`
   FACTORISES and converges for `c' < ½ = carrierThreshold(1,1,1)`. The 2nd-order `σ_min` is IRRELEVANT — the
   integral is closed directly, no rank-drop recursion. So the a·b point is handled AT the base.
2. **The reduced IH is FULL-coverage, not a rank-drop-specific recursion.** In a deeper chain where `a·b`
   appears as a sub-product, the arity induction peels down until it is at the front/base; at each level the
   reduced-comparator IH `D'.integral < ⊤` bounds the ENTIRE reduced parameter space — every point, every
   degeneration order (1st, 2nd, coincidental). Arity is a well-founded ℕ measure (strictly ↓, bottoms at 2),
   so the induction reaches every point. No point is "missed": the 2nd-order crossing is inside `redChain`'s
   box and covered by its finiteness.
3. **The charge already accounts for 2nd-order.** `minAdm`/QIP is the EXACT codimension of the degeneration
   locus (not a naive per-factor count), so it incorporates coincidental/2nd-order degenerations. `(1,1,1)`:
   `minAdm = 1`, threshold `½` — exactly the a·b answer. So `C_j ≥ minAdm(M)` (§3) holds INCLUDING 2nd-order
   crossings; no undershoot.

**The tangency red herring, resolved (Codex Q3).** `M(t)=[[1,t],[t,0]]` is affine+immersive yet `σ_min ~ t²`
(tangent to `{det=0}`) — but that is a CONSTRAINED curve. In the DLN integral the base matrix has FREE
entries: the normal (Schur) coordinate `S = D − C·P⁻¹·B` has `∂S/∂D = I`, so the free `D`-direction is
FIRST-order transverse (`S = D − t²` in free space, not `S = −t²` on the curve). Base transversality holds
in the normal/free direction — "order 1" means transverse-normal order, not order along every curve. This
is the owed uniform-transversality piece (piece A), realised as the Schur normal coordinate.

## 5. Adversarial stress-test (obstruction seat on my own design)

Hunted for a width/depth where the budget undershoots, the recursion fails to terminate, or a degenerate
point is missed:
- **Budget undershoot:** swept 3161 genuine decorated binding cuts (arity 3–5, widths ≤ 7). `C_j ≥ minAdm(M)`
  everywhere; 0 undershoots; 0 `a>M₂`. The one apparent risk (`a≥M₂`, atom-over-`A_cor` divergent) is
  excluded by the banked convexity (`a ≤ M₂` always). The `σ_min`-only UNDERSHOOT (`(3,3,3)`: `5/2 < 7/2`) is
  real but is a WRONG mechanism, not an obstruction — the flag closes it tight.
- **Termination:** arity strictly decreases (`redChain@t+j` is one node shorter), bounded below by 2. Finite
  rank strata (`Core.RankLocusClosed`) at each level. No infinite regress. (This REPLACES the refuted §7
  Eckart–Young "width-2 bottoming" — the correct well-founded variable is ARITY, and the base is closed by
  direct factorisation + Schur-normal transversality, not by a matrix-distance order claim.)
- **Missed point:** none — the reduced IH is full-coverage (§4.2), so every point of every stratum is bounded
  by the deeper level's finiteness.
- **Corank-`b>1` joint corner:** MC of `G·w^{c'−ab/2}` with BOTH smallest tail singulars driven to 0 stays
  bounded (`scripts/G_mc.py`), corroborating closure; but MC underestimates singular integrals, so the
  DECISIVE evidence for `b>1` is the exact flag arithmetic (§3), not the MC.

**No obstruction survived.** The residual is measure-theoretic LABOUR (§6 owed), not a wall.

## 6. Decorrelated Codex verdict + banked/owed map for the tide

**Codex (xhigh, conclusion withheld; `codex/offsector-il-answer.md`) — CONCURS: "CLOSES (labour) — for the
exact-min/singular-flag version; the literal `b>1` `σ_min`-only split does not."** It independently derived:
(Q1) the atom is lossy off-sector, `a≥M₂` ⟹ atom-over-`A_cor` divergent; (Q2) `b=1` closes with
`a ≤ M₂` from binding (`a + R_t ≤ R_{t+1} ≤ R_t + M₂`), both bricks inside the IH range, log at `a=M₂`
harmless; the `b>1` `σ_min`-only split undershoots (`(3,3,3)`: `5/2`), the flag charges `C_j =
(a−j)(b−j)+R_{t+j} ≥ minAdm(M)` close it, "no width undershoots"; (Q3) network-depth reaches the a·b point
via adapted rank charts, base transversality = Schur normal coordinate (order-1 free direction, not curve
order); (Q4) NET **CLOSES (labour)**. Its one caveat: "uniform adapted pivot charts + measure bounds; depth
decrease alone is not a proof of those estimates" — this IS the owed measure work below, not a gap in the
value or the logic. No inference of mine was fed in; the concurrence is decorrelated. Fact-check: it
corrected Fact 4's over-statement (at a binding `b=1` cut only `a = M₂`, never `a > M₂`, can occur) — which I
then verified exactly (§2a, 0 violations / 3161).

**BANKED pieces the design consumes:**
- `RouteMSJInnerDescent.freedSchurLoss_inner_peel_le` (atom brick, `τ ≥ √w` region, needs `Q_bQ_bᵀ` PosDef).
- `RouteMSJInnerDescent.freedSchurLoss_inner_bounded_le` (bounded brick, `τ < √w` region, needs `w > 0`).
- `RouteMSJCornerComparator.cornerComparator_adm` (the reduced comparator `D'_{t+j}` on `redChain@t+j`).
- `RouteMSJTransversality` convexity `minAdm_redChain_succ_ge` (`R_{t+1}−R_t ≥ a+b−1`) + `minAdm_eq_backPeel`
  + the binding identity `minAdm(M) = peelCharge + minAdm(redChain)` (`exists_binding_cut`).
- `Core.RankLocusClosed` (finite tail-rank strata) + `RouteMSJSigMin` (the `{σ_min ≷ ε}` sector cover) +
  `carrierThreshold_shift`.

**OWED (the genuinely-new pieces for the tide — LABOUR):**
1. **(b=1) corank-integrability lemma:** `G(w,Z) := ∫_{A_cor∈box}[freed-corner integral] dA_cor ≤
   C·w^{−(c'−ab/2)}·(1 + 𝟙[a=M₂]·log(1/w))`, `C` uniform over `{Z: top M₂−1 singulars ≥ c₀}`. Proof = the
   two-regime split at `τ=√w` + the box-clipping (`vol{‖A_cor Z‖ ≤ r} ≲ r^{M₂}`, NOT `/∏σ`). Consumes `a≤M₂`.
2. **(b>1) singular-flag stratification:** stratify `{det(Q_bQ_bᵀ) < ε}` by the flag level `j` (# small
   singulars), reduce each to the atom/bounded brick at cut `t+j`; charge `C_j` (banked convexity). This is
   the `corank2` two-scale density generalized to arbitrary `(a,b)`.
3. **Uniform adapted rank charts (piece A, geometric):** the Schur-normal transversality giving uniform
   constants on each good tube + a FINITE subcover of `{σ_min(Q_b)<ε}` (compact box + Noetherian rank
   stratification). This is #144-adjacent and is the residual soundness surface.

---

## Close

- **Firmest (design cert, decorrelated-confirmed).** The off-sector CLOSES for `c' < carrierThreshold(M)` via
  a **two-brick split** (atom where `Q_bQ_bᵀ` PosDef / bounded where not — both banked) over a **tail-rank ×
  corank-flag stratification**, each stratum reducing to the arity-`(L+1)` reduced-comparator IH with charge
  `C_j = (a−j)(b−j) + minAdm(redChain@t+j) ≥ minAdm(M)`. The single-corner atom domination is **lossy
  off-sector** and must NOT be the off-sector proof (it diverges over the free `A_cor` when `a ≥ M₂`); `b=1`
  never hits `a>M₂` (banked convexity), `b>1` needs the full flag (`σ_min`-only undershoots, `(3,3,3)`:
  `5/2<7/2`). Charges ADD to EXACTLY `½·minAdm(M)` (3161 cuts, 0 undershoots, tight at `j=0`); the saturating
  log is eaten by the strict inequality. **#118 is resolved by ARITY recursion (not rank-drop) + full-IH
  coverage + Schur-normal base transversality** — the a·b 2nd-order point is handled at the base case by
  direct factorisation, and `minAdm`/QIP already charges 2nd-order degenerations exactly.
- **Most likely to break (the owed residual, for the tide to green-gate).** The **uniform adapted-chart /
  finite-subcover MEASURE assembly** (owed piece 3): the good-tube uniform constants require the deeper tail's
  surviving singular values bounded below (`{top M₂−1 singulars ≥ c₀}`) — i.e. the tail rank-drop excision must
  be by ADAPTED charts (Codex Q3, the pitfall the certs already flagged: NO null-set deletion), and the
  constant `C` in the `b=1` lemma degrades if the tail collapses fully rather than dropping by one rank (that
  collapse is a DEEPER flag level / a shorter chain — the arity induction handles it, but the tide must
  stratify, not bound uniformly across all `Z`). This is LABOUR + the one place a hidden non-uniformity could
  hide; it is the same piece-A the sibling threads owe.
- **Next.** Hand this to the desc4 tide as the corrected `innerCorankDescent_lt_top` spec: (i) the two-brick
  `τ ≷ √w` split of the freed-corner integral (both bricks banked); (ii) the tail-rank×corank-flag
  stratification with `C_j` from the banked convexity; (iii) the (b=1) corank-integrability lemma and (b>1)
  flag lemma as the two new analytic obligations; (iv) piece-A uniform adapted charts. The next pen-and-paper
  check, if wanted before the build: a fully-worked `b=2` flag two-scale density at a genuine binding cut
  (e.g. `(3,3,3)@t=1` or `(3,3,4)@t=1`), to pin the per-flag uniform-constant assembly the tide will formalise
  — the exact charge arithmetic (§3) is settled, the measure assembly is the residual.
