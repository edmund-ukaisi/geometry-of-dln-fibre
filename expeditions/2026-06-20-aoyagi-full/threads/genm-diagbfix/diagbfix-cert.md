# diagbfix — the L≥1 deep-Gram "residual": the OBJECT is FINITE; the fix is the deep-stratum GATE (3a), not a comparator reshape and not object-scoping

**Seat:** pen-and-paper (design-space adjudication, decorrelated), aoyagi-full Stage 2, `genm-diagbfix`.
**Date:** 2026-07-15. **NO Lean edits, NO build.** Exact coarea/Wishart algebra + exact `ℕ` codim recursion;
Monte-Carlo as CONFIRMATION of exact-asymptotic claims only (nothing load-bearing rests on a float). Decorrelated
`local-codex-consult` (gpt-5.x, xhigh; my conclusion WITHHELD, prompt "argue whichever way"):
`codex/diagbfix-{prompt,answer}.md` — **returned; INDEPENDENTLY CONCURS on all four questions** (§5).

**Consumed / verified (signatures, not paraphrased), on `origin/genm-deepatlas` unless noted:**
`RouteMSJIncidenceAssembly.lean` (`frontChargeIntegrand` :553, `frontCharge_factor` :668,
`shellSpine_le_frontCharge` :610 with `hGae`/`hEtopae`, `coupledBoxIntegrand` :417, `freedSchurLoss_gammaPeel_le`
:493, `clsCodim_gate_genL` :723, `stratum_corner_lt_top` :767, `shellSpine_le_coupledBox` :436 with the
a-fortiori `lintegral_mono_set`), `RouteMSJChartShear.lean` (`SJOuter`, `freedSchurLoss` :146, `outerDom` :185),
`RouteMSJHeadSplitDom.lean` (`hsQ` :44 — pivot rows `= prod(redChain u M) z`, corank rows `= A_cor·Zf z`),
`RouteMSJDeepGate.lean` (**`origin/genm-sj5-stepbuild`, sorry-free**: `chargeExp` :32 = `γ_s`,
`minAdm3_add_chargeExp_le` :87, `deepGate_branch` :152, `deepGate_uρ_branch` :161),
`RouteMSJDeepCoverage.lean` (**sorry-free**: `deepCell` :69, `deepRankLE_eq_iUnion_cells` :158,
`deepRankLE_lintegral_lt_top` :177), `RouteMSJDeepAtlas.lean` (1 sorry), `RouteMSJDeepCover.lean` (1 sorry).
Cross-read: `genm-reassembly/reassembly-cert.md` §3.2/§3.3 (@a25091d35, the +∞ self-audit),
`genm-deepgate/deepgate-cert.md` (Route B, `C_k ≥ 2T1_q`), `genm-arch1probe/arch1-cert.md` §1.1–1.3.
Scans (this thread, `/tmp/`): `honest_acor.py`, `full_frontcharge.py`, `witness_check.py`, `ck_rederive.py`.

---

## ★ VERDICT

**1. THE PIVOTAL FACT — reassembly's L≥1 "`∫frontChargeIntegrand = +∞`" self-audit is REFUTED (decorrelated).**
`∫_p frontChargeIntegrand M u c' p` (over `paramsBoxM(redChain u M) 1 ×ˢ matBox(M₁−u) M₂ 1`) is **FINITE**
for every good-branch binding strict-shell cut, all `L≥1`, **including uniform width `(d,d,d,d)`** and the b=2
witness `(3,4,5,4)@u=2`, for all `c' < carrierThreshold M` (i.e. `q = c'−ab/2 < T1_q = (minAdm M − ab)/2`). The
"uncompensated deep-Gram residual `det⁺(Z_deep Z_deepᵀ)^{−b/2}`" is a **coarea UPPER-bound prefactor, not the
honest object**: the box fibre-volume `L(Z)` collapses like `det⁺(ZZᵀ)^{+b/2}` and exactly cancels it. reassembly's
divergence step needs a LOWER bound with `inf L > 0`; **`inf L = 0`** — provable from reassembly's OWN scaling
identity `I(tZ)=|t|^{−ab}I(Z)` (§1). So this is **NOT a wall, NOT an object-scoping problem** — it is a
proof-mechanism gap, and the object is fine.

**2. THE FIX — Option (3a) deep-stratum GATE (= deepgate Route B = the Arch-2 machinery). ADJUDICATED WINNER.**
Sound, non-circular, buildable. The deep rank-drops need **no separate lower-arity descent** (reassembly's (3a)
framing is heavier than needed): `frontChargeIntegrand` is ALREADY finite over them (the corank charge is INERT at
the binding stratum). (3a) = a JOINT per-stratum RLCT gate over ALL deep strata `{rank Z_deep = ρ−k}`, with
`C_k = min(uρ, u(ρ−k)+κ_k−γ_{ρ−k}) ≥ minAdm(M)−ab = 2T1_q` (the banked, sorry-free `deepGate_branch`), each
stratum radial-finite via the same `corner_block_cube_lintegral_lt_top` engine as the banked `stratum_corner_lt_top`.
Non-circular: a DIRECT per-stratum monomial-RLCT bound — no descent onto a shorter-chain `(□)`-IH; the only chain
fact used is the deep chain's GEOMETRIC codim `κ_k = CR((M₂,…,M_last), ρ−k)` (a separate recursion, `crstrat`).

**3. `hGae` was never the deep-factor mechanism, and the cornerComparator DESCENT (route α) is genuinely UNSOUND
for L≥1** (reassembly's scaling obstruction `G/comparator = |t|^{−ab} → ∞` is REAL as a refutation of the
*per-slice domination*, arch1probe's "reabsorb `det(ZZᵀ)^{−b/2}` into `decLoss`" is FALSE). But the object being
finite means the SOUND route is the direct joint stratified atlas (front gate [banked] + deep gate (3a)), which is
self-contained per cut — not the descent.

**4. LATE-15 is UN-REVERSED for L≥1:** the deep-stratum arc (deepgate `C_k` / `RouteMSJDeepGate` / crstrat `(I)` /
the deep atlas) **is load-bearing for L≥1**, exactly as the controller suspected. Its "off-path" verdict rested on
arch1probe's descent-reabsorption claim, which reassembly correctly refuted; but the correct consequence is (3a),
not a wall.

**5. Option 2 (deep-Gram-decorated comparator) is DEAD — for the RIGHT reason.** Not because the intermediate is
`+∞` (it is finite), but because it decorates the comparator to match a SPURIOUS residual, introducing an
unnecessary deep-Gram-weighted IH that does not close. Drop it. **Option (3b) (undecorated descent)** is viable
ONLY as the full Aoyagi §5 `(S,J)` recursion (charter Lane 2), **not** as a "drop the Γ-peel over-estimate"
shortcut — the charge `det(Q_bQ_bᵀ)^{−a/2}` is the EXACT Gaussian integral of the peeled corank block, intrinsic
to any front peel (§4).

---

## 1. The pivotal fact: `∫_p frontChargeIntegrand` is FINITE for L≥1 — and reassembly's exact error

**The object (Lean-exact, `frontChargeIntegrand` :553 + `frontCharge_factor` :668).** For a binding cut `u`,
`a=M₀−u`, `b=M₁−u`, `q=c'−ab/2`, deep factor `Z_deep = deeperFlagZdeep M u` (an `M₂×n` matrix, `n=M_last`):

    ∫_p frontChargeIntegrand = ∫_{z, A_cor} det(Q_b Q_bᵀ)^{−a/2} · Cresid · frontLossIntegrand(z, A_cor),
    Q_b = A_cor · Z_deep(z)   (b×n),   Q_p = prod(redChain u M) z   (u×n),   x=(P,B₁₂,C)∈outerDom.

**reassembly's mechanism (updated cert @a25091d35 §3.2–3.3):** change variables `A_cor ↦ Q̂_b = A_cor·S`
(`S` a row-space basis of `Z_deep`), pulling out the coarea prefactor `det⁺(ZZᵀ)^{−b/2}`; bound the A_cor-leaf
integral by a `Z`-independent leaf constant; conclude `∫frontCharge ≤ K·∫_{deep} det⁺(ZZᵀ)^{−b/2}·[…]` with the
residual non-integrable, then assert this is ALSO a lower bound "needing only `inf L>0` locally" ⟹ `+∞`.

**The exact error — `inf L = 0`, provable from reassembly's OWN scaling identity.** Write `L(Z) := J(Z) /
det⁺(ZZᵀ)^{−b/2}` where `J(Z) = ∫_{A_cor∈box} det(Q_bQ_bᵀ)^{−a/2} dA_cor` is the honest A_cor-box charge. Under
the ray `Z = tZ₀` (reassembly's own §2/§5 fact) `J(tZ₀) = |t|^{−ab} J(Z₀)`, while `det⁺((tZ₀)(tZ₀)ᵀ)^{−b/2} =
|t|^{−bk} det⁺(Z₀)^{−b/2}` (`k = deepTailMin`). Since **`bk > ab`** on the good branch (`k ≥ a+1` at binding
cuts, rankgen), 

    L(tZ₀) = |t|^{−ab} / |t|^{−bk} · L(Z₀) = |t|^{b(k−a)} · L(Z₀)  →  0   as  t→0.

So `inf L = 0`; the lower bound reassembly needs FAILS. The residual `det⁺(ZZᵀ)^{−b/2}` is a valid but VACUOUS
upper bound (`∫frontCharge ≤ K·(+∞)`), never a divergence proof (a non-integrable `g ≥ f ≥ 0` says nothing about
`∫f`). This is exactly the distinction reassembly's own decorrelated Codex flagged ("a separate weighted local-zeta
estimate would be needed") but the §3.3 self-audit over-read into "`+∞`".

**The honest charge is INERT at the codim-1 deep rank-drop (exact asymptotic + MC).** For a=b=1, square deep
(uniform width), `J(Z) = |det Z|^{−1} ∫_{Ω_Z}‖y‖^{−1}dy`, `Ω_Z = Zᵀ·box`. As one singular value `σ→0` (`{rank
Z=k−1}`, codim 1), `Ω_Z` is a slab of thickness `~σ`, and `∫_{Ω_Z}‖y‖^{−1}dy = Θ(σ) = Θ(|det Z|)` (`‖y‖^{−1}`
integrable in ℝ⁴). Hence **`J(Z) = Θ(1)`, bounded** — no `|det Z|^{−1}` pole. Confirmed:
- `honest_acor.py` (a=b=1, 4444): `J(A₂) → 19.4` as `σ: 1→10⁻⁴`; `J·|det| → 0` (NOT `~|det|^{−1}`).
- `witness_check.py` (a=1,b=2, `(3,4,5,4)@u=2`): `J(A₂) → 4000` bounded as `det(A₂ᵀA₂)→0`; `J·det → 0`.

**The FULL object converges, onset exactly at `q = T1_q` (`full_frontcharge.py`, 4444@u=3, binned by `|det A₂|`).**
The mean integrand per `|det A₂|`-decade **plateaus** (does NOT grow like `|det|^{−1}`) toward `det→0`, while the
measure `{|det|~δ} ~ δ` shrinks ⟹ convergent:
- `q=0.5, 2.0` (far below `T1_q=5`): plateau, comfortably finite (refutes the *q-independent* `+∞` claim outright).
- `q=4.9` (just below 5): finite, heavy tail. `q=5.5` (above): divergent. **Onset at `q=5 = T1_q`** — matches
  deepgate `C_k = 10` exactly (`2q < 10`), NOT below.

**Independent re-derivation of the gate (`ck_rederive.py`, exact ℕ):** `C_k = min(uρ, u(ρ−k)+CR(deep,ρ−k)−γ_{ρ−k})
≥ minAdm(M)−ab` — **0 violations / 5736 checks** (arities 4–6, widths 1..6; 3451 tight). `(4,4,4,4)@u=3`: binding
`k=1,2` at `C_k=10=2T1_q` (charge inert `γ=0`); `k=4` full collapse `κ_4=16, γ_0=1, C=12`. Reproduces deepgate.

> **Reconciliation of the two rigorous certs.** deepgate (Route B) computed the codim of the *honest* charge-form
> object and got `C_k ≥ 2T1_q` (finite). reassembly computed the *coarea over-estimate* and got a non-integrable
> residual. Both computations are internally correct; reassembly's error is the LEAP from "the over-estimate is
> `+∞`" to "the object is `+∞`" — the fibre volume it discarded (`L(Z)`) is precisely the compensation. The
> per-slice scaling obstruction `G/comparator = |t|^{−ab}→∞` is REAL and correctly kills the *cornerComparator
> descent*; it does not touch the *object*.

---

## 2. The adjudication: (3a) vs (3b) vs option 2

| Route | Sound? | Non-circular? | Buildable? | Verdict |
|---|---|---|---|---|
| **α** cornerComparator descent (reabsorb `det(ZZᵀ)^{−b/2}` into `decLoss`) | **NO** (per-slice domination `|t|^{−ab}→∞`; residual ≠ `decLoss`) | — | — | UNSOUND for L≥1 (reassembly right here) |
| **2** deep-Gram-decorated comparator | matches SPURIOUS residual | weighted-IH does not close | — | **DEAD** (right reason: over-estimate, not `+∞`) |
| **3a** deep-stratum GATE (deepgate Route B / Arch-2) | **YES** (`C_k ≥ 2T1_q`, 5 independent confirmations) | **YES** (direct per-stratum monomial-RLCT; no `(□)`-IH; uses geometric `CR`) | **~90% banked** (§3) | **★ WINNER** |
| **3b** undecorated descent | YES only as full Aoyagi §5 `(S,J)` | (open, = Lane 2) | Lane-2-sized rebuild | viable ALTERNATIVE, not an Arch-1 fix (§4) |

---

## 3. Option (3a) — the exact spec + banked state

**Statement (the L≥1 deep extension of `stratum_corner_lt_top`).** For a binding cut `u = t★+j` (`1≤j<r`), the
outer `∫_p frontChargeIntegrand` is resolved by a JOINT stratification indexed by `(front (ℓ,s), deep rank-drop k)`.
Each deep stratum `{rank Z_deep = ρ−k}` (`ρ = deepTailMin M`, `k = 1,…,ρ`) becomes, after the composite-rank
big-cell charts, a codim-`C_k` normal block carrying a degree-2-homogeneous loss (sphere-bounded, `hlb`) times the
corank charge; the radial integral `∫₀^δ r^{C_k−1−2q} dr < ⊤` for `q < T1_q`, because the **Nat gate**

    C_k = min( u·ρ ,  u·(ρ−k) + κ_k − γ_{ρ−k} )  ≥  minAdm(M) − a·b  =  2·T1_q,
    κ_k = CR((M₂,…,M_last), ρ−k)   (composite-rank codim),   γ_s = max_{max(0,b−s)≤h≤b} h(a+b−s−h).

**Banked pieces (consume, do not re-derive):**
- **The Nat gate — DONE, sorry-free** (`RouteMSJDeepGate.lean`, `origin/genm-sj5-stepbuild`): `deepGate_branch`
  (`minAdm(M) + γ_{ρ−k} ≤ ab + u(ρ−k) + κ_k`, `κ` abstract), `deepGate_uρ_branch` (the generic-front cap),
  `minAdm3_add_chargeExp_le`, `chargeExp = γ_s`. The `(I)` input `minAdm(M) ≤ κ_k + minAdm(M₀,M₁,ρ−k)` is
  crstrat's (`CR`/`(I)`).
- **Per-stratum finiteness — DONE, sorry-free** (`RouteMSJDeepCoverage.lean`): `deepCell`,
  `deepRankLE_eq_iUnion_cells`, `deepRankLE_lintegral_lt_top` (the deep rank-drop locus is a finite union of cells
  with finite per-cell integral).
- **The radial engine — DONE** (`corner_block_cube_lintegral_lt_top`, reused by the banked front
  `stratum_corner_lt_top`): same shape, `q < C_k/2`.
- **Remaining build obligation (~2 sorries):** `RouteMSJDeepAtlas.lean` (1 sorry — the composite-rank big-cell
  monomial-Jacobian chart / hierarchical non-comparable degeneration), `RouteMSJDeepCover.lean` (1 sorry — the
  `rankEqLocus` pivot-minor decomposition). This is the "deep analogue of incidencepp §3b's front atlas"
  (deepgate §6); it is the substantive Lean labour, but bounded (explicit determinantal big-cells), NOT a wall.

**Wiring:** replace the OLD `deeperFlag_shell_le` route-B/`headSplit_domination` (`sorry`, dead) with: `shellSpine_le_frontCharge`
(banked, `hGae`/`hEtopae`) → `frontCharge_factor` (banked) → the JOINT atlas resolving `∫_p [charge·frontLoss]` by
`clsCodim_gate_genL` (front, banked) + the deep gate above. The `hGae` a.e. Γ-peel is retained (it is sound — it
only licenses the pointwise peel; integrability is closed by the GATE, not by `hGae`).

**Non-circularity, precisely.** The deep gate is a DIRECT RLCT bound per deep stratum (monomial radial finiteness),
NOT a descent onto `cornerComparator(redChain u M).integral`. The only "chain-length-reducing" object it touches is
the deep chain's geometric codim `κ_k = CR(deep, ·)` — a fact about the deep rank locus proved by `CR`'s own
recursion, independent of the `(□)` finiteness IH. No coupling identity is asserted; no `∫frontCharge ≤
K·cornerComparator` (the FALSE `+∞ ≤ finite` step) appears.

---

## 4. Option (3b) — undecorated descent: viable only as Lane 2, not a shortcut

The controller's (3b) hope was "drop the Γ-peel over-estimate; descend the undecorated `frobSq(prod M)^{−c'}`
directly (RLCT `½minAdm`, no residual)". Two facts settle it:

1. **The charge is not a droppable over-estimate — it is the EXACT peel integral.** `freedSchurLoss_gammaPeel_le`
   (:493, via `corankBlock_morsePeel_setLE`) integrates the peeled `a×b` corank block `Γ` against
   `frobSq(C·Q̃ₚ + Γ·Q_b)`; the Gaussian/Wishart result IS `det(Q_bQ_bᵀ)^{−a/2}·Cresid` times the transverse
   Schur core. The `≤` is only the Γ-domain relaxation (genBox → ℝ^{a×b}), a valid finite over-estimate — NOT the
   source of a residual. ANY front-block peel of the undecorated object generates this charge.
2. **`RLCT(frobSq(prod M)) = ½minAdm` is the CIRCULAR off-shell bound** (bltj §3 / Aoyagi) — it assumes the
   answer; it is not a recursion. The only NON-circular route to it on the undecorated object is Aoyagi §5's
   `(S,J)` coordinate resolution (radial blow-ups on `{d_ij=0}`, monomial charts, the diag(b) ledger) — i.e. the
   charter's **Lane 2**, a full alternative build, not a modification of the Arch-1 (incidence/charge) route.

So (3b) is a viable PARALLEL route (already the charter's Lane 2) but is NOT a cheaper fix to the Arch-1 L≥1 gap.
For fixing Arch-1, (3a) is the minimal delta (mostly banked). If Lane 2 lands first, it discharges `(□)` directly
and (3a) is unneeded; both bank.

---

## 5. Decorrelated Codex (conclusion WITHHELD; prompt "argue whichever way") — INDEPENDENT CONCURRENCE

`codex/diagbfix-{prompt,answer}.md` (gpt-5.x, xhigh, no repo access, my verdict withheld; framed the disputed `+∞`
claim neutrally). Codex, decorrelated, on the SAME instance (4444@u=3):
- **Q1 [FACT]:** `∫_{Ω_Z}‖y‖^{−1}dy = Θ(σ)`, so `J(Z) = Θ(1)` bounded — "does not blow up like `|det Z|^{−1}`."
- **Q2 [FACT/INFERENCE]:** `L(tZ₀) = |t|³ L(Z₀) → 0`, so `inf L = 0`; "the colleague's lower bound is false; the
  fibre volume collapses like `t³`." (Identical to my §1, via the shared scaling identity.)
- **Q3:** "a non-integrable upper bound proves nothing about divergence"; "the determinant computation only makes
  the naive upper bound vacuous — not a divergence proof."
- **Q4 [FACT]:** `I(½) < ∞` via TWO independent estimates — the local model gives the rank-3 drop effective
  codim `C = 10` (radial `∫ρ^{9−2q}dρ`, converges `q<5`); and a global bound `integrand ≤ ‖xZ‖^{−2}·C` with
  `∫_x‖x‖^{−2} < ∞` in ℝ⁴. "The rank-three deep drop has effective codimension `C=10`, not a codim-one
  `|det Z|^{−1}` pole."
- **FINAL:** "The disputed claim is **FALSE**. Sharpest reason: the explicit finite estimate `I(½)<∞`;
  geometrically, the thin fibre volume cancels the apparent determinant pole."

No point of divergence between my exact algebra, the deepgate re-derivation, and the decorrelated consult. Codex's
global `‖xZ‖^{−2}` estimate (Q4) is a bonus clean small-`q` finiteness proof independent of the stratification.

---

## 6. Levels kept apart

- **Quiver/orbit:** untouched; consumed via `minAdm`/`redChain`/`CR` (geometric codim only).
- **Codim `(C,θ)`:** `clsCodim_gate_genL` (front, general-L, banked) + `deepGate_branch` (deep, banked) are `ℕ`
  inequalities — the exponent gates. The deep gate's `C_k ≥ 2T1_q` is exact-verified (0/5736 + deepgate 3999+ +
  Codex proof). NOT a ring-identity lift of L=0 — the deep factor is stratified, not assumed generic.
- **RLCT cap / finiteness:** this cert works at the per-shell FINITENESS / `(□)` level (is `∫_p frontChargeIntegrand
  < ⊤`?), NOT the cited Aoyagi `rlct = ½·codim` equality. `(□)` remains TRUE throughout (bltj/Aoyagi); this cert
  settles the CONSTRUCTIVE, non-circular MECHANISM for L≥1 — it is (3a), the deep-stratum gate.

---

## Close

- **Firmest result.** `∫_p frontChargeIntegrand` is **FINITE** for L≥1 good binding cuts (`q<T1_q`), uniform width
  included — five independent confirmations (exact coarea asymptotic; honest-charge MC for b=1 and b=2 witnesses;
  full-object binned MC with onset exactly at `q=T1_q=5`; independent `C_k ≥ 2T1_q` re-derivation 0/5736;
  decorrelated Codex). reassembly's "`+∞` for uniform width" self-audit is **REFUTED** — its residual
  `det⁺(ZZᵀ)^{−b/2}` is a vacuous coarea upper bound (`inf L = 0`, from its own scaling identity), not the object.
  **The L≥1 fix is Option (3a): the deep-stratum GATE** (deepgate Route B / the Arch-2 machinery) — sound,
  non-circular, ~90% banked (`deepGate_branch` + `deepRankLE_lintegral_lt_top` sorry-free; ~2 sorries in the deep
  atlas). **LATE-15 un-reversed for L≥1.** Option 2 dead (spurious residual). Option (3b) = Lane 2, not a shortcut.
  **NO WALL** (kill-condition NOT triggered).
- **Most likely to break it.** (a) If `bk ≤ ab` at some good cut (would make `inf L > 0` possible): checked FALSE —
  `k = deepTailMin ≥ a+1` at binding strict shells (rankgen `a+b ≤ ρ−1`), so `b(k−a) ≥ b ≥ 1 > 0`; the fibre
  volume always collapses. (b) The deep-atlas 2 sorries: the composite-rank big-cell atlas must genuinely EXHAUST
  hierarchical (non-comparable-singular-value) degenerations without lowering `C_k` below `2T1_q` — deepgate §6's
  open model-dependence; a pen-and-paper follow-on could pin the non-comparable case (the `CR`-recursion's last-
  layer-rank stratification IS the atlas index). This is the ONE place the arithmetic is still model-dependent.
- **Next construction/consult that would settle the open part.** (i) The formaliser wires (3a): compose
  `shellSpine_le_frontCharge → frontCharge_factor →` the JOINT atlas (front `clsCodim_gate_genL` + deep
  `deepGate_branch` + `deepRankLE_lintegral_lt_top`), discharging the 2 deep-atlas sorries. (ii) A pen-and-paper
  follow-on on the hierarchical (non-comparable) deep degeneration, to retire deepgate §6's model-dependence
  (the only residual soundness caveat in (3a)).

**Files (absolute):**
- `/home/ubuntu/workspace/geometry-of-dln-fibre/expeditions/2026-06-20-aoyagi-full/threads/genm-diagbfix/diagbfix-cert.md` (this cert)
- `…/genm-diagbfix/codex/diagbfix-{prompt,answer}.md` (decorrelated consult)
- scans: `/tmp/honest_acor.py`, `/tmp/full_frontcharge.py`, `/tmp/witness_check.py`, `/tmp/ck_rederive.py`
