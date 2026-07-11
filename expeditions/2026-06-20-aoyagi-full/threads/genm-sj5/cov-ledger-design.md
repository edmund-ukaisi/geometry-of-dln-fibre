# §5 CoV/ledger DESIGN cert — the decorated (S,J) descent that fills `innerCorankDescent_lt_top`

**Seat:** formaliser (genm-sj5-descent), pen-and-paper design BEFORE formalising (charter discipline).
**Date:** 2026-07-11. **NO Lean build.** **Route:** A (decorated (S,J) ledger) — CONFIRMED by the
decorrelated route-reconcile (`route-reconcile.md`, #139/#140: cover + Codex + `corank2-cert §4`; Route B's
disjoint-`A₂`/independent-Wishart step is FALSE). **Gate:** genm-sj5-cover audits this cert (decorrelated)
before I formalise the ledger threading.
**Consumed:** `descent-buildplan.md`, `corank2-cert.md §2/§4` (genm-vsastruct), `route-reconcile.md`,
`RouteMSJInnerDescent.lean` (my banked (b) bedrock), the banked spine (`RouteMSJFreedPeel`, `RouteMSJCorankPeel`,
`RouteMSJLedger`, `RouteMSJLinGen`, `RouteMSJDecoratedRec`/`Charge`, `RouteMSJCorankGram`, `RouteMSJProductTube`).
**Decorrelated:** own xhigh `local-codex-consult`, conclusion withheld, adversarial ("find where it's wrong"):
`codex/covledger-{prompt,answer}.md` — read folded into §7.

Tags: **[ANCHOR]** = decorrelated-verified on `(3,3,3,4)` (corank2-cert + Codex). **[DERIVED]** = my exact
algebra. **[DESIGN]** = proposed Lean route, not yet proven. **[OPEN]** = genuine residual risk.

---

## ★ HEADLINE VERDICT (the design pass did its job — read §7 + §7.5)

The design pass, instrumented with an adversarial Codex consult, **OVERTURNED the atom-first architecture I
started from**: integrating `Γ` to the FULL-SPACE atom value first (my banked `freedSchurLoss_inner_peel_le`)
destroys the bounded-`Γ`-box cutoff and produces a majorant that DIVERGES in the outer variables even where the
true integral is FINITE. Decorrelated-confirmed by a concrete binding counterexample `M=(2,2,1,2), t=1, c'=3/4`
(§7, hand-verified). **The corrected Route A is the native bounded-box `(S,J)` decorated blow-up on the PRE-atom
integral** — keep `Γ` bounded, resolve the coupled corner JOINTLY to `sjLoss_terminal`, only then hand a plain
shifted integral to `hIH(redChain)`. This is exactly the corank2-cert route-S / cover-derisk "keep the shrinking
image" recommendation; I had wrongly interposed the atom. My banked `_peel_le`/`_bounded_le` remain SOUND lemmas
but are usable ONLY on the non-degenerate core (Gram bounded away from 0), NOT on the `{w=0}`/rank-drop
neighbourhoods where the threshold binds. **This is a ROUTE redirect, not a finiteness obstruction** (the
integral is finite). §1–§6 below record the atom-first design AS PROPOSED (for the audit trail); §7.5 is the
corrected architecture that supersedes STEP 1.

---

## 0. The object and the target

The hole `innerCorankDescent_lt_top` (skeleton `RouteMSJDecoratedPeelStep.lean`), for chain
`M = (M₀,…,M_last)` (arity ≥ 3), binding cut `t` (`1 ≤ t ≤ min(M₀,M₁)`), `a = M₀−t`, `b = M₁−t`:

    I = ∫_{A'∈paramsBoxM(tailChain M)1} ∫_{x=(P,B₁₂,C)∈outerDom t a b 1} ∫_{Γ∈shearbox}
          ( freedSchurLoss x Γ Q̃(A') )^{−c'}                                        < ⊤,   c' < ½·minAdm M.

`freedSchurLoss = frobSq(P·Q̃ₚ) + frobSq(C·Q̃ₚ + Γ·Q_b)`, `Q̃ₚ = Q_p + P⁻¹·B₁₂·Q_b`, `Q̃ = prod(tailChain M) A'`
(`M₁×M_last`), rows split by `κ` into `Q_p` (`t×M_last`) / `Q_b` (`b×M_last`). `Z := A'₂···A'_{L+1}` (`M₂×M_last`)
is the deeper product; `prod(tailChain M) A' = A'₁·Z`, so `Q_p, Q_b` are row-blocks of `A'₁·Z` — they SHARE `Z`
(the irreducible coupling, route-reconcile §2).

Target threshold via the banked layer-peel recursion (`RouteMLayerSplit`):
`minAdm M = min_t [ (M₀−t)(M₁−t) + minAdm(redChain t M) ]`, `redChain t M = (t, M₂,…,M_last)`; at the binding cut
`minAdm M = peelCharge + minAdm(redChain t M)`, `peelCharge = (M₀−t)(M₁−t) = a·b`.

**Pivot-energy simplification [DERIVED, banked `pivotEnergy_inverse_free`].** `P` a unit ⟹
`P·Q̃ₚ = P·Q_p + B₁₂·Q_b` (the `P⁻¹` cancels), so the pivot energy `w = frobSq(P·Q̃ₚ) = frobSq([P|B₁₂]·Q̃)` is
BILINEAR, no inverse; `{w=0}` is a bilinear locus (input to the joint resolution §4).

---

## 1. The peel skeleton (one decorated peel, chain M → redChain t M)

    Γ-atom (banked)          → residual R(A',x) = det(Q_bQ_bᵀ)^{−a/2}·(w + frobSq(C·Q̃ₚ(I−P_{Q_b})))^{−(c'−ab/2)}
    finite chart cover (§5)  → rank-flag of Q_b; good cells (rank b) vs deficient (rank r<b)
    JOINT corner resolution  → the (S,J) blow-up of {w=0}/rank-deficiency (§3,§4) — the crux
      (§3)                      loss → monomial ∑ᵢ(∏|u_ℓ|^{e_iℓ})² (ledger SJSupport) → sjLoss_terminal
    bottom (§4/charges)      → deeper product = redChain: hIH(redChain) at c'−½peelCharge; charges ADD.

- **STEP 1 (Γ-atom, BANKED).** Integrate `Γ` per `(A',x)` via my `freedSchurLoss_inner_peel_le` (good cells:
  `c'>ab/2`, `Q_bQ_bᵀ` PosDef, `w>0`) or `freedSchurLoss_inner_bounded_le` (`c'≤ab/2` / deficient). Peels the
  front Γ-block (charge `ab = peelCharge`, threshold `ab/2`), emits `R(A',x)`.
- **STEP 2 (cover, §5).** Rank-flag of `Q_b` over the box.
- **STEP 3 (JOINT corner resolution, §3–4).** The crux — resolve `R`'s coupled `det(Q_bQ_bᵀ)^{−a/2}·(core)`
  jointly via the (S,J) corner blow-up to `sjLoss_terminal`.
- **STEP 4 (bottom, charges ADD).** Deeper product → `hIH(redChain t M)` at `c'−½peelCharge` (banked charge
  shift `half_minAdm_sub_half_peelCharge_le`); leaf → `sjLoss_terminal`.

---

## 2. The iterated-blowup chart maps (matrix-box → blow-up coords)

The resolution is Aoyagi's `(S,J)` corner. On a corank cell (`Q_b` near rank drop), the exceptional divisors are
the RADII of the collapsing blocks, coupled at the shared corner.

**[ANCHOR] (3,3,3,4), t=1, a=b=2.** Two exceptional divisors:
- `u₀` = the `2×2 = 4`-dim Γ-block / corank-block radial. Chart map: the corank block `= u₀·Δ₀`, `Δ₀` on the
  unit sphere `S³`. Jacobian `du₀-block = |u₀|^{4−1} dΔ₀ = |u₀|³ dΔ₀`.
- `u₁` = a `3`-dim boundary-row radial (the `M₂=3` boundary row of the tail degeneration). Jacobian
  `|u₁|^{3−1} = |u₁|²`.
- Coupled corner blow-up `u₁ = u₀·τ` (the load-bearing step): `|u₀|³·|u₀τ|²·|u₀| = |u₀|^{3+2+1}|τ|² = |u₀|⁶|τ|²`
  (`+1` from `du₁ = u₀ dτ`). Loss `G = u₀²·(U₀ + τ²U₁)`, `U₀,U₁ > 0` bounded on the generic-`A₂` chart, order 2.

**Chart maps, general `(a,b,t)` [DESIGN].** The Γ-block (`a×b`) radial `u₀` (Jacobian `|u₀|^{ab−1}`); the deeper
degeneration resolved by the redChain's own `(S,J)` resolution (recursion). The single peel introduces the ONE
divisor `u₀` for the front block; the deeper divisors come from `redChain`'s resolution (handled by `hIH`, or
`sjLoss_terminal` at the leaf).

**Consumed (banked):** the Γ-atom already IS the `u₀`-block integration in closed form
(`corankBlock_morsePeel_eq`: `∫_Γ = det(Q_bQ_bᵀ)^{−a/2}·Cresid·(shifted core)^{−(c'−ab/2)}`) — i.e. STEP 1 = the
`u₀` blow-up done analytically. The carrier `radialStep` (`RouteMSJLinGen`) is the ledger-level `u₀`-attach
(`loss ↦ u₀²·loss`, support gains a shared column). `gen_rowMix_const` is the det-1 unit block-elimination
(the chart's linear part).

---

## 3. Per-chart Jacobian monomials + charges-ADD to `minAdm` at `sjLoss_terminal`

**The corner monomial [ANCHOR].** After the coupled corner, the loss integrand over `u₀` is `|u₀|^{6−2c'}` (the
`|τ|²` and `U₀+τ²U₁` are bounded/harmless), so `∫₀^κ |u₀|^{6−2c'} du₀ < ∞ ⟺ 6−2c' > −1 ⟺ c' < 7/2`.
And `6+1 = 7 = minAdm(3,3,3,4)`; the `+1` is the terminal `du₀` measure exponent. Decomposition:
`6 = (4−1) + (3−1)` [the two block Jacobian powers], `+1` [`du₁=u₀dτ`], and the terminal `+1` [`∫u₀^k, k>−1`],
i.e. `(4−1)+(3−1)+1+1 = 4+3 = peelCharge + minAdm(redChain)`.

**Charges ADD, general [DESIGN, banked arithmetic].** The geometric claim: the accumulated corner Jacobian power
`= minAdm(M) − 1`, so the terminal `∫u₀^{(minAdm−1)−2c'}` gives threshold `½·minAdm`. The ARITHMETIC half is
banked exactly: `minAdm M = peelCharge + minAdm(redChain t M)` (`minAdm_le_peelCharge_add_redChain` +
`exists_binding_cut`), and the exponent shift `c' < ½minAdm ⟹ c'−½peelCharge < ½minAdm(redChain)`
(`half_minAdm_sub_half_peelCharge_le`, banked). The DESIGN claim is that the corner geometry REALISES this
arithmetic: `peelCharge` from `u₀`'s Γ-block, `minAdm(redChain)` from the deeper resolution, ADDing (not `min`-ing)
because they share the corner `{u₀=0}` — the coupling is load-bearing (§4).

**Terminal [BANKED].** The monomial endpoint is `sjLoss_terminal_lintegral_lt_top` (`RouteMSJLedger:234`): the
loss on the terminal chart is `∑ᵢ (∏_ℓ|u_ℓ|^{e(i,ℓ)})²` (the ledger `SJSupport`), and finiteness below the
`monomialThreshold` (given a dehomogenised generator) is banked. The ledger threading (`RouteMSJLinGen` carrier:
`radialStep`, `gen_rowMix_const`, `loss_blockSplit`) carries the loss to this form; `sharedDivisorExp` records
WHICH generators share `u₀` (the ADD-not-`min` datum, `RouteMSJLedger` DATA-A).

---

## 4. The joint flag-tube `{w=0}` resolution (the coupling is load-bearing)

The `{w=0}` / rank-deficiency neighbourhood is where the design is subtlest (controller sharpening: design the
JOINT density, NOT a marginal/scalar codim).

**Why marginal/scalar codim UNDERSHOOTS [ANCHOR, corank2-cert §2].** For the corank-2 cell, the front majorant is
ASYMMETRIC `g̃ ≍ max(s₂,s₃)^{−3}·min(s₂,s₃)^{−(2c'−6)}` (`s₂≥s₃` the small singular values of `P=Ã₁·A₂`). The tube
is finite for `c'<7/2` ONLY via the JOINT two-scale pushforward density
`μ{s₂≤t₂, s₃≤t₃} ≍ t₂³·t₃·log(e/t₂)` (`dμ ≍ s₂²·log ds₃ds₂`): `∫ s₂^{−3}s₃^{−η}dμ < ∞ ⟺ η<1 ⟺ c'<7/2`
(`η = 2c'−6`). The MARGINALS give `min(t₂⁴, t₃)`, closing only for `η<1/4` — insufficient. The SYMMETRIC
`∧²`-compound `(s₂s₃)^{−b}` FAILS (pointwise `b≥c'−3/2>3/2` vs integrability `b<1`, no overlap). **The joint,
asymmetric estimate is REQUIRED.**

**How Route A realises it [DESIGN, = route S corner].** The (S,J) corner blow-up (§2) is the JOINT resolution: the
coupled `u₁=u₀τ` keeps the two collapsing directions on ONE terminal divisor `{u₀=0}`, so the charges ADD
(`3+2+1=6→7/2`), NOT `min` (independent divisors give `min(2,3/2)=3/2`, the undershoot). The corner picture is the
joint density (route J) done in blow-up coordinates: `u₀ = max(s₂,s₃)`, `τ = s₃/s₂ = min/max`, and
`|u₀|⁶|τ|² du₀ dτ` is the pushforward `dμ ≍ s₂²log` re-expressed (the `log` = the `θ`-tie multiplicity, subdominant
to the power, harmless — strengthens only the excluded borderline `c'=7/2`).

**`{w=0}` is NOT deleted [DESIGN].** The inner bounds (`_peel_le`/`_bounded_le`) blow up as `w→0`, but the JOINT
integral is finite because the corank term `frobSq(C·Q̃ₚ + Γ·Q_b)` keeps the loss positive off the HIGHER-codim
`{both blocks vanish}`. The pivot energy being bilinear (`pivotEnergy_inverse_free`) makes `{w=0}` a clean bilinear
locus; the joint resolution integrates its neighbourhood via the corner, not by an a.e.-deletion.

---

## 5. The finite chart cover

**Rank-flag / pivot cover [DESIGN, #123-de-risked].** Cover the `(A',x)` box by the rank `r = rank Q_b ∈ {0,…,b}`.
- `r = b` (full row rank): `Q_bQ_bᵀ` PosDef, the Γ-atom applies (STEP 1 good cell). The det-Gram weight
  `det(Q_bQ_bᵀ)^{−a/2}` is handled as a TOOL by the Cauchy–Binet/Loewner lower bound
  `det(Q_bQ_bᵀ) ≥ det(Q_SQ_Sᵀ)` (`det_gram_le_of_submatrix_cols`, #112) → square minor → the banked Wishart
  endpoint `detGram_lintegral_lt_top` (`RouteMSJProductTube`) / `corankGram_box_lt_top` (`RouteMSJCorankGram`,
  one isolated sorry). **Cauchy–Binet is the WEIGHT tool, NOT the closer** (route-reconcile §1).
- `r < b` (deficient): do NOT assert PosDef. Integrate the `ar` ACTIVE Γ-directions (active threshold `a·r/2`),
  keep the kernel in its bounded box, and RECURSE the rank flag (the corner resolution §3 on the reduced rank).
- **Seam [ANCHOR, cover-derisk #123].** The flag partition is by indicator multiplication (no boundary term); the
  seam `{|det minor| tie}` is Lebesgue-null with transition Jacobian EXACTLY `1`; the integrand is `O(1)` there.
  **Trap to avoid:** do NOT extend the shrinking image `D_M` to a fixed box — that reintroduces a non-integrable
  `∫|det|^{r−b}` (the F2 seam); keep the coupled shrinking image.

---

## 6. Banked pieces consumed + the FRESH Lean gap

**BANKED (consume):** Γ-atom value bounds (my `freedSchurLoss_inner_peel_le`/`_bounded_le`,
`RouteMSJInnerDescent`); the domain measures (`measure_shearbox_lt_top`, `volume_genBox_lt_top`);
`pivotEnergy_inverse_free`; the corank atom `corankBlock_morsePeel_*`; the carrier steps `radialStep`,
`loss_radialStep`, `gen_rowMix_const`, `loss_blockSplit` (`RouteMSJLinGen`); the terminal
`sjLoss_terminal_lintegral_lt_top` + `sharedDivisorExp`/`SJSupport` ledger (`RouteMSJLedger`); the charge
arithmetic (`minAdm_le_peelCharge_add_redChain`, `half_minAdm_sub_half_peelCharge_le`, `exists_binding_cut`); the
outer driver (`routeMBoxThresholdFinite_of_decoratedPeel`); the Cauchy–Binet/Loewner + Wishart endpoint tools
(`det_gram_le_of_submatrix_cols` #112, `detGram_lintegral_lt_top`, `qbox_lintegral_lt_top`).

**FRESH (the build, gated on this cert's audit):**
1. **The ledger threading (§3, the centrepiece).** Transport the residual `R(A',x)` into the `SJLinGenState`
   carrier and thread the decoration (divisors, Jacobian exps, vanishing orders, shared divisors, rank/pivot chart)
   through the corner to `sjLoss_terminal`. The `frobSq → carrier loss` base connection is NOT the raw
   `freedSchurLoss` (the `P⁻¹` breaks linearity) — it is AFTER the pivot chart + corner blow-up, where generators
   are `monomial(u) · linear(active)`. **[OPEN]** the exact base-connection lemma (carrier loss of the
   corner-chart residual) is the first fresh lemma.
2. **The joint corner resolution (§4).** The coupled `u₁=u₀τ` blow-up as a measurable CoV with the ADD-not-`min`
   Jacobian, realising the joint flag-tube. **[OPEN]** general-width Jacobian count = `minAdm−1` (Q1 for Codex).
3. **The rank-flag cover assembly (§5).** The finite measurable cover + the deficient-rank recursion.
4. **Closing `corankGram_box_lt_top`** (the isolated det-Gram sorry, Cauchy–Binet #112 → Wishart) — the weight tool.

---

## 7. Decorrelated Codex read (adversarial; `codex/covledger-answer.md`) — OVERTURNS the atom-first architecture

**Codex verdict: Route A AS ARCHITECTED HERE (Γ-atom-first → Gram residual → joint corner → plain hIH) is
WRONG.** The fatal flaw is STEP 1: **the FULL-SPACE Γ-atom destroys the bounded-Γ-box cutoff**, producing a
majorant that is non-integrable in the outer variables even where the true bounded-Γ integral is finite. This is
the cover-derisk "keep the shrinking image, don't extend to a fixed box" trap — and my Γ-atom value bound
(`freedSchurLoss_inner_peel_le`, via `corankBlock_morsePeel_setLE`'s `∫_s ≤ ∫_univ`) commits exactly it.

**Concrete binding counterexample (Codex; I HAND-VERIFIED it — DERIVED, not just trusted).**
`M = (2,2,1,2)`, `t=1`, `a=b=1`, `minAdm=2`, `½minAdm=1`, take `c'=3/4 (<1)`. On a subbox (`P≍1`, `Z` bounded
away from 0), with `α = P·y + B·β`, `β` = the corank row of `A'₁`: `freedSchurLoss ≍ α² + (Γβ)²`.
- **Bounded-Γ (TRUE) integral, integrate `α` first:** `∫_{-1}^1(α²+(Γβ)²)^{−3/4}dα ≍ |Γβ|^{−1/2}` (scaling
  `α=|Γβ|u`, `∫(u²+1)^{−3/4}du<∞`), then `∫∫_{box}|Γβ|^{−1/2}dΓdβ = (∫|Γ|^{−1/2})(∫|β|^{−1/2}) < ∞`
  (exponent `−1/2 > −1`). **FINITE at `c'=3/4`.** ✓
- **Full-space Γ-atom (my `_peel_le` bound), integrate `Γ` over `ℝ` first:**
  `∫_ℝ(α²+Γ²β²)^{−3/4}dΓ = |β|^{−1}∫_ℝ(α²+s²)^{−3/4}ds ≍ |β|^{−1}|α|^{−1/2}`, then `∫_{box}|β|^{−1}dβ`
  **DIVERGES (log)** — even after deleting the exact `β=0`. ✗

So `det(Q_bQ_bᵀ)^{−a/2}` from the full-space atom is `|β|^{−1}`, but the true bounded-Γ charge on `β` is only
`|β|^{−1/2}` — the full-space atom OVER-CHARGES the `Q_b`-degeneration by exactly the Γ-box cutoff it discarded.
Codex: "Step 2's rank flag cannot repair Step 1, and Step 3 cannot make a genuinely non-integrable majorant
integrable by changing coordinates."

**The other four (ranked):**
- **Q1 (charges-ADD, general widths): incomplete, blanket equality WRONG.** DERIVED: coupled radial blocks
  `q₁,…,q_k` on the sector `u_j=u₁τ_j` give total Jacobian power `∑q_j − 1` (the anchor `3+2+1=6` is `k=2`). BUT
  the additional hypotheses (all deeper charge on the SAME divisor, `∑q_j = ab + minAdm(redChain)`) are NOT
  consequences of the banked pieces: on a rank-`r` branch Γ contributes only `ar` (not `ab`); the missing
  `a(b−r)` must come from rank-normal coordinates; on non-achieving branches the total is `Mval(T) > minAdm`.
  The correct obligation is a PER-DIVISOR terminal inequality (Jacobian exp vs loss order), not "one `u₀` with
  exponent `minAdm−1`." Cheapest check: full pullback-Jacobian on `(4,4,4,4)` charges `[4,3,4]`, every
  Case-1/Case-2 chart.
- **Q2 (joint corner vs plain hIH): wrong as written.** DERIVED: at the binding cut `c'−ab/2 ↗ ½minAdm(redChain)`,
  so plain hIH has ZERO slack for the extra Gram weight; Hölder needs `p>1` with `p(c'−ab/2)` below the reduced
  threshold — fails near the endpoint. A one-peel handoff to PLAIN hIH is possible only if the joint blow-up
  fully discharges the decoration WHILE retaining the bounded-Γ cutoff — i.e. the native decorated blow-up on the
  PRE-atom integral, NOT the post-atom residual `R`. (Repo records this: `pure-vs-atom-adj.md`.)
- **Q3 (chart cover): set-theoretically finite, analytically INCOMPLETE.** Competing pivot charts overlap on
  positive measure; the divergence lives in the punctured seam NEIGHBOURHOOD, not on the null seam; Gaussian
  elimination via `M⁻¹` introduces uncontrolled `|det M|^{−1}` as `M→singular`. A valid rank-flag needs
  quantitative sectors + explicit tubular/blow-up coords + their Jacobians + bounded overlap — "recurse the rank
  flag" alone does not supply these. Cheapest check: write the exact corank-one chart map + determinant; if an
  inverse minor appears with no radial variable compensating, the chart is unusable near the next rank drop.
- **Q4 (joint-density faithfulness): anchor sound, general UNPROVED.** The chart `u₁=u₀τ` covers only
  `|u₁|≲|u₀|`; the RECIPROCAL chart `|u₀|≲|u₁|` + all pivot/angular charts are required. The `log` is harmless
  strictly below threshold (`∫₀^ε rᵃlogᵏ(1/r)<∞`, `a>−1`), NOT at the critical exponent. The corner→joint-tube
  equivalence is credible for the anchor but needs the actual chart-cover CoV theorem, not `radialStep` + support
  bookkeeping.

---

## 7.5. CORRECTED ARCHITECTURE (the load-bearing conclusion of the design pass)

**The design pass DID ITS JOB: it overturned the atom-first architecture BEFORE any formalisation.** The corrected
Route A is the **native bounded-box `(S,J)` decorated blow-up applied to the PRE-atom integral** — keep `Γ` in its
box, resolve the coupled `(P,B₁₂,C,Γ,A')` corner JOINTLY to `sjLoss_terminal`, and only THEN (with the decoration
discharged and the cutoff retained) hand a plain shifted integral to `hIH(redChain)`. Concretely:

- **DROP STEP 1 (the full-space Γ-atom) from the descent's degeneration cells.** My banked
  `freedSchurLoss_inner_peel_le`/`_bounded_le` remain SOUND lemmas (correct upper bounds), but they are usable
  ONLY on the non-degenerate core (where `det(Q_bQ_bᵀ)` is bounded away from 0, so the full-space value is
  outer-integrable). On the `{w=0}`/rank-drop NEIGHBOURHOODS — which is where the threshold binds — the atom
  over-charges and MUST NOT be used; the native bounded-box blow-up replaces it there.
- **The corner blow-up (route S) is applied to `freedSchurLoss` WITH `Γ` bounded**, not to the post-atom residual.
  This is exactly the corank2-cert route-S recommendation ("peel `Ã₁` pivot chart, the corank block blows up
  radially, couples with the boundary row → the corner `u₀²U₀+u₁²U₁`") — I had mistakenly interposed the
  full-space atom.
- **Q1/Q3/Q4 corrections fold in:** the general charge count is a PER-DIVISOR terminal inequality (not a single
  `u₀^{minAdm−1}`); the chart cover needs quantitative sectors + BOTH coupled charts (`u₁=u₀τ` and its reciprocal)
  + explicit Jacobians; the rank-`r` branch contributes `ar` (rank-normal coords supply the rest).

This is a genuine design-level redirect (decorrelated-confirmed), NOT a finiteness obstruction — the integral IS
finite (the `(2,2,1,2)` bounded integral converges at `c'=3/4`); it is the ROUTE (atom-first) that was wrong.

---

## 8. Honest open risks (the fidelity core — base-audited-hardest)

- **[OPEN, Q1] General-width charge count.** The `3+2+1=6→7/2` is verified for `(3,3,3,4)` only. The DESIGN claim
  that the corner Jacobian power `= minAdm(M)−1` for general `(a,b,t)`+redChain rests on the arithmetic recursion
  (banked) MATCHING the geometry (not proven). If the geometric corner charge diverges from `peelCharge +
  minAdm(redChain)` at some width, the threshold is wrong. Cheapest test: a second anchor (e.g. corank-3, or a
  deeper-product chain) — check the corner Jacobian power vs `minAdm−1`.
- **[OPEN, Q2] Plain hIH vs decorated IH.** STEP 4 hands the deeper product to the PLAIN `hIH(redChain)`, but the
  Γ-atom emitted the det-Gram decoration. If that decoration is NOT fully discharged by the corner (STEP 3) before
  STEP 4, the plain hIH hits the zero-slack Hölder failure (design-cert). The design ASSERTS the corner discharges
  it; whether one peel suffices (vs a decorated IH) is the deepest risk.
- **[OPEN] Ledger base-connection.** The `freedSchurLoss → SJLinGenState.loss` connection only holds post-corner
  (the `P⁻¹` obstructs the raw form); the exact intermediate carrier state is unbuilt.
- **[ANCHOR-safe] The coupling is load-bearing.** Independent divisors give `3/2` not `7/2`; the design MUST use
  the coupled corner (not independent, not symmetric-compound, not marginal) — decorrelated-confirmed.

**If Q1/Q2 surface a genuine analytic obstruction (not labour), I isolate the minimal gap and flag it
decorrelated-confirmed (per the gate). Else it is the bounded build the buildplan predicts.**

---

## 9. POST-AUDIT (cover §7.5 PASS + Q1/Q2 resolved) — the DECORATED-IH structural lift

cover's audit (task #141): ROUTE CORRECT + WIDTH-GENERAL (Q1 POSITIVE — joint flag-tube PASS, charges-ADD
verified at 7 anchors incl `(4,4,4,4)=11 [4,3,4]`); and **Q2 RESOLVED NEGATIVE for plain-hIH — a DECORATED IH
is REQUIRED.** The front-`t=2` chart radial integration gives `∫u³(R²+u²H²)^{−c'}du ≍ R^{4−2c'}·H^{−4}`: the
peel emits `[plain reduced integrand]·[EXTRA truncated H^{−4}]`, and plain `hIH(redChain)` at the zero-slack
binding cut (`c'−ab/2 ↗ ½minAdm(redChain)`) CANNOT carry the `H^{−4}`. NOT a finiteness obstruction (`v=0` is
the equally-binding `t=3` cut, same threshold, excluded-endpoint log — the log absorbs into strict slack); a
CONSTRUCTION gap. This VINDICATES the #137 decorated-descent plan and confirms my §8 Q2 deepest-risk call.

**⇒ STRUCTURAL LIFT (flagged): the skeleton's plain IH must become the DECORATED IH the `SJDecoration`
infrastructure was built for.** The current spine (`RouteMSJResolution`/`RouteMSJDecoratedRec`):
`SJStepHyp`/`DecoratedPeelStep` take a PLAIN IH `∀M', RouteMBoxThresholdFinite M'`, base `sjBase1_freeMatrix`
(free-matrix Morse), driver `routeMBoxThresholdFinite_of_step` (arity strong-induction, PLAIN predicate). The
lift:
- **step:** `DecoratedStepHyp : ∀ M(≥3), (∀ M' one-shorter, ∀ D' : SJDecoration M', DecoratedBoxThresholdFinite D')
  → ∀ D : SJDecoration M, DecoratedBoxThresholdFinite D` — the IH is DECORATED (carries the truncated `H^{−4}`
  as the `jac` monomial + the carrier's shared-divisor structure; `DecoratedBoxThresholdFinite` already carries
  `∏|u_ℓ|^{jac_ℓ}·carrier.loss^{−c'}`).
- **base:** the DECORATED leaf — stronger than `sjBase1_freeMatrix` (trivial only); the fully-resolved members
  are `sjLoss_terminal_lintegral_lt_top` (banked).
- **driver:** replicate the arity strong-induction wrapper for the decorated `∀D` predicate, then specialise to
  `SJDecoration.trivial M` (via `decoratedBoxThresholdFinite_trivial_iff`) to recover `RouteMBoxThresholdFinite M`.
  The `L=0` vacuous base lifts cleanly (threshold `½minAdm` is decoration-INDEPENDENT).

**The subtlety to nail (the design fork):** the `∀ D : SJDecoration M` quantifier is likely TOO STRONG for a
provable base (a pathological carrier could over-charge). The faithful design restricts to the ADMISSIBLE
decorated family the peels actually produce (bounded/truncated weight, monomial carrier) — matching the
`SJDecoration` design intent (`genm-r1predicate/cert.md`, "FULLY PINNED"). Options: (A1) `∀D` (clean statement,
hard/false base); (A2) admissible-family recursion (base = `sjLoss_terminal` + Morse, needs the family def +
peel-closure) — RECOMMENDED; (B) simultaneous multi-level discharge (cover's alternative; no per-level IH).
**This changes the `(□)`-gating spine (`DecoratedPeelStep` + driver), which I authored — flagged for controller
steer before the spine rewrite.**

---

## 10. A2 DESIGN (POST-ACK) — the admissible-decoration family + the decorated base

**A2 ACK'd (controller); Q_D CERTIFIED (toric-ray-cert, both anchors, binding ray exactly ½minAdm — NOT a
wall, a construction gap); spine LANDED** (`RouteMSJDecoratedRec`: `DecoratedStepHyp`/`DecoratedBaseHyp`
`adm`-abstract + `decoratedBoxThresholdFinite_of_decoratedStep` + `DecoratedDescent` +
`routeMBoxThresholdFinite_of_decoratedDescent`, green + clean-three, aggregator 8835). This section designs the
SPECIFIC `adm` the landed abstract driver consumes. TWO CORRECTIONS folded in from the toric-ray cert.

### 10.1 The invariant = `p=0` TRANSVERSALITY (correction 1, load-bearing)

The decorated IH carries the corank-row valuation `p = ν_η(H₁)` (`H₁ = |q₁ + s·q₂|`, the mixed corank
direction) and maintains `p = 0` on the CRITICAL reduced divisor. Geometrically: **the corank block is
transverse to the deeper-pivot degeneration** — the critical divisor is the pivot-block-vanishing locus with
the shared deeper product `Z` generic full-rank, on which the corank rows `q₁,q₂` are generic units (`p=0`).
`q = ν_η(H₂)` is HARMLESS — NOT tracked (toric §2: `p=0,q=1` still certifies `7/2`; only `p>0` obstructs). This
is SHARPER than the #141 "carry `H⁻⁴`": the load-bearing datum is `p`, target `p=0`.

So the admissible predicate `adm n M D` is (informally): `D` is reachable-from-`trivial`-by-peels AND its
carrier realises `p=0` transversality on the critical reduced divisor of `M`'s deeper product — i.e. the
corank generators of the carrier are NOT divisible by the critical (pivot-vanishing) divisor (the shared
deeper `Z` enters them at full rank). The EXACT Lean encoding on `SJDecoration` (carrier `supp`/`coeff` +
deeper `Z`/`ctx`) is being co-scoped with cover's width-general `p=0`-transversality RECURSION (#144) — that
recursion IS invariant (ii) peel-closure.

### 10.2 The three invariants
- **(i) trivial ∈ family.** `SJDecoration.trivial M` has carrier `ofMatrix` (support ≡ 0, residual = product
  entries) — no exceptional divisors, so `p=0` vacuously (no critical divisor resolved yet). `adm n M (trivial
  M)` holds. [reachability base + vacuous transversality]
- **(ii) PEEL-CLOSED = `p=0` transversality preserved.** One decorated peel (radialAttach + the chart step, §5
  sectors) maps an admissible `M`-decoration to an admissible reduced-chain decoration, MAINTAINING `p=0` on
  the new critical divisor (current corank block transverse to the deeper pivot degeneration). This is cover's
  #144 width-general recursion — the substantive invariant. Feeds `DecoratedStepHyp adm`.
- **(iii) PROVABLE BASE.** The fully-resolved admissible members bottom at the banked monomial terminal
  `sjLoss_terminal_lintegral_lt_top` (d,k,h arbitrary); the arity-leaf (single free matrix) is the decorated
  Morse. See 10.3.

### 10.3 The decorated base / b>1 terminal reduction (subsumes gap (3)) — DOES reduce to `sjLoss_terminal`

**Controller's key question — answered YES (from the toric local model + `p=0`).** Via the §5 Γ=u·M sector
chart (`M=[[1,s],[t,st+v]]`, `|dΓ|=u³dudsdt dv`, `v`=det-normal RETAINED, NO inverse-det), the leaf loss pulls
back (after the bounded row op `row₂ ↦ row₂ − t·row₁`) to

    f = R² + u²(H₁² + v²H₂²),   H₁=|q₁+s q₂|,  H₂=|q₂|,  R=|P·Q_tp|.

On the transverse (`p=0`) critical divisor `H₁,H₂` are UNITS, so `f ≍ R² + u²·(unit)` — a MONOMIAL-times-unit
in the exceptional coords `(u, v, and the R-resolving reduced coords)`. Hence it bottoms at the banked
`sjLoss_terminal_lintegral_lt_top`: the generators are `∏|u_ℓ|^{e(i,ℓ)}` monomials, and the dehomogenised-
generator hypothesis `∃ i₀, e i₀ = sharedDivisorExp` is supplied by the `p=0` transversality (the corank
generator `H₁` is a unit = its residual support equals the shared-divisor min, so `i₀` = that generator). The
`a>1` rank-deficient directions are handled by the finite entrywise reciprocal charts (§5) + the `{v=0}`
rank-drop sub-chart (recurse — the deeper pivot-vanishing critical divisor, again `p=0`). **NOT a genuine new
terminal — a `sjLoss_terminal` instance** (given `p=0`). [The `b=1` case is banked B4 `RouteMSJFreeBilinear`.]

### 10.4 The corrected residual (correction 2, load-bearing)

The exact `v`-integral is `∫₀¹(H₁²+v²H₂²)^{−2}dv ≍ H₁^{−3}(H₁+H₂)^{−1}` (→ `H₁^{−4}` when `H₂≤H₁`), NOT
`H₁^{−3}H₂^{−1}` (#141/§9 — that blows up as `H₂→0` with `H₁` a unit = ARTIFICIAL divergence, over-constrains
to `3p+q=0`). The correct form needs ONLY `p=0` — exactly what transversality gives. The decoration the peel
emits + carries is thus governed by `H₁` (the `p`-tracked direction), `H₂` untracked.

### 10.5 Charges ADD (toric §5, confirms §3 Q1 — now with the correct per-divisor account)

On the coupled corner, `∫∏|u_i|^{p_i}(∑u_i²U_i)^{−c'}` converges ⟺ `c' < ½Σ(p_i+1)`, `Σ(p_i+1)=Σ(block dims)
=minAdm` (nD-homogeneous corner). BOTH coupling charts (`u₁=u₀τ` and reciprocal `u₀=u₁σ`) are needed (each
covers half, same threshold, toric §5). This is the correct PER-DIVISOR account Codex's Q1 demanded (§7):
NOT "one `u₀^{minAdm−1}`" but the homogeneous corner `½Σ(p_i+1)`, units `U_i>0` bounded below on the generic
chart (recurse where a unit vanishes = the deeper `p=0` critical divisor).

### 10.6 Status / what cover base-audits
The A2 design rests on: the LANDED abstract spine; Q_D CERTIFIED (toric); the `p=0` invariant + corrected
residual + §5 sectors (toric, decorrelated). cover base-audits: the admissible-family DEF (10.1) + its base
(10.3, does it reduce to `sjLoss_terminal`) + peel-closure (10.2 = its own #144 recursion). On PASS I build:
the specific `adm` Lean def (synced with #144) + `DecoratedBaseHyp adm` (10.3) + `DecoratedStepHyp adm` (the
decorated peel, §5 sectors + corrected residual). **[OPEN, honest]** the exact `SJDecoration`-level encoding of
`p=0` transversality (10.1) is the fidelity crux — co-scoped with #144; a wrong encoding (too loose→false base,
too tight→misses peels) is the conceptual slop the base-audit catches.
