# (D) design cert — the UNIFIED joint corank-one / rank-sector transversality resolution

**Seat:** pen-and-paper (design, decorrelated), `genm-satred`, follow-on. **Date:** 2026-07-16.
**NO Lean.** Math design only (I hand the reduction + CoV + exponent bookkeeping + banked pieces + traps;
the controller commissions the Lean build). Verified FOUR ways: my exact-`ℕ` + sublevel-volume numerics
(`scripts/{joint_corank,corner_rlct,strata_recursion,AvsDelta,kill_check}.py`); corneradj's **independent**
per-stratum derivation (`genm-corneradj`, `strata.py`); edgebrick's corank-one analysis + Codex xhigh
(`genm-edgebrick`); my own decorrelated Codex (`codex/D-{prompt}.md`, `D-run.log`, repo-grounded, 332/332).
Consumes corneradj `edge-design-cert.md`, edgebrick's handoff, couplerad `corankaxis.py`, satred `satred-cert.md`.

---

## ★ VERDICT

**(D) CONVERGES. The unified joint corank-one/rank-sector resolution REACHES `½·minAdm M` for ALL of:
the edge (`a,b≥1, a+b=ρ+1`, corank-one), the deep corank (`a,b≥1, a+b≥ρ+2`), and the saturated `A>2Δ`
(`a=0`, the front-factor dual). NO `(□)` wall. The KILL-condition is NOT triggered — verified exhaustively:
of 4039 corner shells (widths ≤6), 0 undershoot (3688 reach `minAdm`, 351 over-cover; ZERO with
joint-min < `minAdm`), and rigorously the corner `≤ RMBTF(M)|_chart` (RLCT `≥ ½minAdm`, Aoyagi).**

The single-chain / factored / pointwise / polar-angular routes DO undershoot (that is the corner over-call
pattern; corneradj's edge Part-1 was WRONG — its angular `J` re-derives the divergent charge). The **joint**
resolution — resolving the corank rank-sector and the deep factor **together**, reducing each stratum to a
*different* arity−1 chain — reaches `½·minAdm M` because its exponent count **is the `minAdm` recursion
realized geometrically**. One principle, three instances (edge corank-one, deep corank, saturated dual).

---

## 1. The unified object and the one principle

At a shell cut `u` (`a=M₀−u, b=M₁−u, ρ=tailMinWidth M = min(M₁,…,M_last)`), the honest corner is
`shellSpineIntegrand` (`RouteMSJDeeperFlagCore:444`; per-exponent target `∫_p coupledBoxIntegrand M u c' p
< ⊤`, `RouteMSJIncidenceAssembly:417`, reached by the PROVEN `shellSpine_le_coupledBox`), with
`freedSchurLoss = frobSq(P·Q̃ₚ) + frobSq(C·Q̃ₚ + Γ·Q_b)`, `Q_b = A_cor·Zf` (`b×n`, `Zf=Zdeep` rank `ρ`).

**The joint-rank-sector PRINCIPLE (one line):** *the loss's own vanishing on the JOINT low-rank locus of
`(A_cor·Zf, Γ, C)` pays the factor's density/charge singularity; the `min` over the rank strata `=
minAdm(M)`.* Three instances:
- **(A) EDGE, corank-one (`a,b≥1, a+b=ρ+1`).** `K=A_cor·Zf` rank drops `b→b−1` (a codim-`a` event). ONLY
  ranks `b`, `b−1` critical. The smallest instance — a good STARTING case.
- **(B) DEEP corank (`a,b≥1, a+b≥ρ+2`).** All ranks `r∈0..min(b,ρ)` critical.
- **(C) SATURATED (`a=0`, `A>2Δ`).** Corank term vanishes (0 rows); `z̃₀=[P|B₁₂]·[z₀;A_cor]` recombines to
  a single `frobSq(z̃₀·Zdeep)` (satred `satred-cert.md`). Rank-sector on the FRONT factor; the dual of (A)/(B).

## 2. Part 1 — convergence (the `(□)`-critical check): REACHES `½·minAdm M`, NO undershoot

**The truth (rigorous, non-numerical).** Every corner shell `≤ RouteMLayerBoxIntegral(M)|_{P-block
invertible}` — the Schur weld (`chartInner_schurWeld_eq`, measure-preserving) rewrites `freedSchurLoss` as
the front-factor chart loss; the shell/`outerDom`/`Γ`-image are a SUB-region (integrand `≥0`). So corner
RLCT `≥ ½·minAdm M`. **The corner cannot undershoot in the truth.**

**The single-chain / factored / polar routes UNDERSHOOT** (verified exact). Locking to the single chain
`redChain u M` gives per-stratum reduction (corneradj, independent; = edgebrick's codim `ab+s(s−1)` at the
edge with `s=b−r`; matches my `joint_corank.py` to the digit)

    red_r = a·r/2 + (b−r)(ρ−r)/2,   min_r red_r = ab/2 − (k−1)/2 at k=a+b−ρ≥2   (r=b top gives ab/2).

`joint_corank.py` (`S` fixed rank `ρ`): `a=2,b=1,ρ=1 → 0.494 (=1/2 ≠ ab/2=1)`; `a=3,b=1,ρ=2 → 1.00 (≠3/2)`.
The saturated dual: shortfall `A/2−Δ`, `= (k−1)/2 = 1/2` at the tight cells `(2,3,4,4)/(2,2,2,2)/(2,2,3,3)`.

**The JOINT (multi-chain) REACHES `½·minAdm M`** (verified exhaustively — `strata_recursion.py`,
`kill_check.py`). The corank rank-drop `(b−r)` rows **re-peel to a deeper effective cut** `u' = u+(b−r)`, so
stratum `r` reduces to `redChain u' M` (arity−1 IH — a *different* chain per stratum, NOT locked to
`redChain u M`). The reachable range is `u' ∈ [u+max(0,b−ρ), min(M₀,M₁)]` (r-range `0..min(b,ρ)`; if `b>ρ`
the top stratum is `r=ρ`, cut `u'=u+(b−ρ)` — a *shifted* top, not a wall). Then

    corner threshold  =  min_{u' in range} [ peelCharge(u') + minAdm(redChain u' M) ]  ≥  minAdm(M),

a `min` over a SUBSET of cuts, so it is **always `≥ minAdm(M)`** — the corner **never undershoots**.
**Exhaustive KILL scan (`kill_check.py`, widths ≤6, 4039 corner shells): 0 undershoot** (3688 reach exactly,
351 over-cover — finite beyond `½minAdm`, harmless). Tight cases reach: `(2,1,2,2)@0`, `(2,2,3,3)@0`,
`(4,2,3,4)@1`, `(2,3,4,4)@0` all `min = minAdm`. **This IS `minAdm`'s recursion realized geometrically.**

**Decorrelated Codex (repo-grounded).** Independent: joint incidence-rank resolution gives
`min_strata C_{ℓ,s}/2 = T1 (=½minAdm)` **exhaustively 332/332 in-scope binding cuts** — NOT a wall;
pointwise-in-`z` FALSE (must integrate — matches "joint not factored"); its scope `a+b≤M₂` is the FACTORED
route's (see §4).

## 3. Part 2 — the corank-one (edge) instance + the two traps (the smallest, the STARTING case)

At the edge `a+b=ρ+1`, `K=A_cor·Zf` drops `b→b−1`; sector codim at rank `b−s` is `ab+s(s−1)` — `s=0` AND
`s=1` both give the minimal `ab` (the **corank-one TIE ⟹ a LOG**); `s≥2` strictly better. So ONLY the
rank-`(b−1)` stratum needs the transversality treatment (why the edge is corank-ONE, smaller than the deep
all-rank resolution, SAME mechanism).

**TWO TRAPS — both re-derive the SAME divergent charge (do NOT route the edge through them):**
1. The banked morse-peel `corankBlock_morsePeel_setLE` (`RouteMSJCorankPeel:88`) extends `Γ` to `ℝ^{ab}`
   (`subset_univ`), producing `det(KKᵀ)^{−a/2}`; its `A_cor`-integral is the `strongBlock_unif_const_lt_top`
   boundary `a<ρ−b+1` and **log-DIVERGES at `a=ρ−b+1`** (the edge). `deeperFlag_shell_core_le` /
   `deeperFlagUnifConst_lt_top` are interior-only (need `hconv`).
2. The polar "angular front charge" `J = ∫_{A_cor}∫_{S^{ab−1}} frobSq(ΩK)^{−ab/2}` **EQUALS**
   `ω·∫ det(KKᵀ)^{−a/2}` by the sphere identity — same divergence. **corneradj `edge-design-cert.md` Part-1
   is WRONG here** (its worst-case `C₀=0` maximises the charge, dropping the saving mechanism).

**Banked-file classification (for the edge build — checked headers).** USE (edge-safe): `RouteMSJSphereBlowup`
(the KEEP-Γ-on-box polar `∫⁻` blow-up — its own header names it as NOT the det route), `RouteMSJRadialPolar`
(general degree-2-homog polar factor `r^{N−1}`), `RouteMSJDecoratedRadial` (`radialAttachFactor =
∫|u₀|^{j₀}(u₀²)^{−c'}`, the 1-D weighted radial for step 4), `RouteMSJFreeBilinear` (the b=1 leaf). BUILD
FRESH: the `u=rs` coupling (r=‖γ‖, s=‖z‖=‖τ‖; Jacobian `s^{−1}` = `sigmaLog`) + the C-shift
(`mulVec_of_surjective`). **DO NOT USE `RadialResidualPower`** — it is the dead full-space det route
(manufactures the divergent `det(Q_bQ_bᵀ)`; named as such in `RouteMSJSphereBlowup`'s header). `RouteMSJTwoBlockRadial`
(front-first coupled σ-charge majorant) and `RouteMSJProjRadial` (Cat-I) are NOT the edge route — skip.

**The HONEST mechanism (what (D) does at corank-one) — stated to bedrock (edgebrick, load-bearing).** Keep
`Γ` on the **BOX** (radial cutoff `s_max(Ω)`) AND retain the **C-integration**. Near a rank-`(b−1)` point of
`K`, let `η` be the unit vector spanning `K`'s lost row-direction; the morse residual carries
`‖Ccross·η‖² = ‖C·Q̃ₚ·η‖²`. The **enabling lemma is a NON-DEGENERACY of the MAP** (NOT a uniform bound):
`C ↦ C·Q̃ₚ·η` (`ℝ^{a×u}→ℝ^a`) is **SURJECTIVE whenever `Q̃ₚ·η ≠ 0`** (generic, `Q̃ₚ` full rank). This
surjectivity lets the **C-INTEGRATION** absorb the log — it does **NOT** remove the log pointwise-uniformly:
**`C=0` is in the box**, where `η_C=0` and no fragile direction is supplied, so there is **NO
uniform-constant / finite-constant bound**. The honest deliverable is the **δ-slack per-exponent** finiteness:
`∫_C(w+‖η_C‖²)^{−q}dC` finite via `1+log(1/τ) ≤ C_δ τ^{−δ}` + the arity-IH on the open range
`c'−ab/2+δ < ½minAdm(redChain)`. **Net: reduction `ab/2` with a LOG at the tie — NO finite-constant exact
`ab/2` peel** (scalar model `∫_{[−1,1]²}(w+x²y²)^{−p} ≍ w^{1/2−p}·log(1/w)`; `H_p(w) ≤ C_δ w^{−(p−1/2+δ)}`
only). **RLCT VALUE `= ½minAdm` intact — the log is a pole-order/multiplicity bump, NOT a threshold shift.
Claim the VALUE, never a multiplicity `m`, and NEVER "uniform C-transversality removes the log" (FALSE at
`C=0`).**

**Starting atom.** `RouteMSJFreeBilinear.lean` (b=1): `Γ·Q_b = γ⊗z` (outer product),
`frobSq(γ⊗z)^{−c'}` box integral FACTORS into two independent radial integrals (`sumSqND_box_lt_top`),
finite `c'<½·min(a+1,D+1)`. This is the `b=1` corank-one LEAF (`C_cross=0` at `b=1` IS that outer-product). For general
`b≥2`, `C_cross=0` does NOT reduce to FreeBilinear (it is the divergent det-charge — why C-integration is
essential); instead **localize at the rank-`(b−1)` stratum, factor off the full-rank `(b−1)` block**, and the
remaining 1D fragile direction is a FreeBilinear-type rank-1 outer product LOCALLY — so FreeBilinear is the
local model AFTER localization, plus the C-non-degeneracy lift.

**The (b−1)-block chart, precise (delivered to dbuild; verified `bminus1_chart.py`/`matrix_to_scalar.py`).**
The `b=1` edge IS FreeBilinear directly: `Q_b` is `1×n`, `Γ·Q_b = γ⊗Q_b` (`γ=Γ∈ℝ^a`), corank energy
`‖C·Q̃ₚ + γ⊗Q_b‖²`; after the C-shift and localizing the fragile row `z=Q_b` (∈ℝ^a effective, `ρ=a` at
`b=1` edge) the model is `(w+‖γ‖²‖z‖²)^{−c'}`. It reduces by **polar + the coupling `u=rs`** (`r=‖γ‖`,
`s=‖z‖`): `∫r^{a−1}∫s^{a−1}(w+r²s²)^{−p} = [∫s^{−1}ds=log]·[∫u^{a−1}(w+u²)^{−p}du = w^{a/2−p}B]` — i.e.
**the `|y|⁻¹=s⁻¹` (`sigmaLog`) arises from `u=rs`, NOT the chart**; the radial is `JapaneseBracket`
(`u^{a−1}` weight). For general `b≥2`: the `(b−1)`-block MINOR CHART (finite cover over which `(b−1)`-row
block `Q_R` of `Q_b` is full-rank; `q_frag = c·Q_R + τ`, `{rank=b−1}={τ=0}` codim `a`; Jacobian a **BOUNDED**
Gram-det `|det Q_R Q_Rᵀ|^{1/2}`, carried) **peels off the full-rank `(b−1)` block, leaving the `b=1`
FreeBilinear leaf** (`z=τ`, `γ=Γη`). So the whole corank-one instance is dbuild's 6-lemma kit end-to-end +
this one bounded chart — `a`-agnostic (the `u^{a−1}` radial carries `a`).

**Build-route refinement (dbuild's question — the 2D atom is REAL but FACTORS, do NOT build a monolith).**
The corank-one per-cell finiteness is NOT sidestepped by the multi-chain min-over-cuts arithmetic (that
gives the VALUE `½minAdm`; the LOG at the tie is genuine analytic content). BUT the scalar 2D model
`H_p(w)=∫_{[−1,1]²}(w+x²y²)^{−p}dx dy` **FACTORS** (verified exactly, `scripts/edge_2d_factor.py`,
`H_direct=H_factored`): substitute `u=xy` (Jacobian `|y|^{−1}` — CARRY it, it is the source of the log),
giving `∫dy |y|^{−1}·[∫(w+u²)^{−p}du] = [w^{1/2−p}·B] × [∫_τ^1|y|^{−1}dy = log(1/τ)]`. So the Lean atoms are:
polar-`Γ` (banked `s^{ab−1}`); the **1D radial `∫(w+u²)^{−p}du`** (the SAME single-sum-of-squares leaf,
`sumSqND`-type, in the ONE coupled variable `u`); an **elementary σ-log `∫_τ^1 σ^{−1}dσ = log(1/τ)`**
(`Real.log`); the **δ-fold** (`one_add_log_inv_le_rpow`); the **C-non-degeneracy** (`mulVec_of_surjective`)
setting `τ²≍w+‖η_C‖²` and giving `∫_C ln(1/‖η_C‖)dC<∞`; the arity-IH on the open range. The rank-sector
recursion (B) ORGANIZES where this atom is applied (the `r=b−1` tie stratum); the 2D model is proved by the
factorization, NOT as a monolithic 2D singular integral. Matrix→scalar: minor chart + localize at
rank-`(b−1)` (C-non-degeneracy picks the 1D fragile `σ_min` direction) reduces the matrix corank-one to
exactly this scalar model.

## 4. Part 3 — Lean-friendly design

**Object / target.** `∫_p coupledBoxIntegrand M u c' p < ⊤` per-exponent for `c' < ½·minAdm M`
(`RouteMSJIncidenceAssembly:417`, via the proven `shellSpine_le_coupledBox`).

**EDGE (`k=1`) vs DEEP (`k≥2`) — the W2 reduction differs (verified `edge_single_chain.py`, 0/377 edge
cells fail):**
- **EDGE (`k=1`, the `s=0/s=1` tie): SINGLE-chain.** The corank charge cleanly `= ab/2` (both critical
  sectors have codim `ab`), so reduce to the SINGLE chain `redChain u M` at exponent `c'−ab/2` (+ the tie
  LOG, δ-slack `→ c'−ab/2+δ`). Sufficient by cut-soundness `minAdm M ≤ ab + minAdm(redChain u M)`
  (`minAdm_le_peelCharge_add_redChain`, `RouteMSJResolution:204`): `ab/2+½minAdm(redChain u M) ≥ ½minAdm M`.
  **NO multi-chain / no `u'`-cuts** — the `s=1` sector is the LOG on the SAME `redChain u M @ c'−ab/2`
  reduction, not a second chart. (This is corneradj's Step E; only its "`J` finite" was wrong.)
- **DEEP (`k≥2`): MULTI-chain.** The single-chain corank charge `< ab/2` (the min sector-codim shifts to a
  deeper stratum, undershooting by `(k−1)/2`), so reduce stratum `s` to the DIFFERENT chain `redChain(u+s)M`
  at charge `peelCharge(u+s)/2`; `min_s = ½minAdm M` (the `u'`-cut multi-chain, §2). The `u'`-cuts are
  needed HERE only.

**The joint rank-sector reduction (atomic; carry `|det J|`).**
1. **Minor chart on `Q_b`** (`Q_b = D·[I|X]`, full-rank `min(b,ρ)`-minor; finite cover; det-P→0 benign via
   the minor supplement, cf. satred). Carry the minor Jacobian.
2. **Shear** the pivot/corank coupling (`H = P·U + B·D`, banked `RouteMSJChartShear`, measure-preserving).
3. **Stratify `rank(A_cor·Zf) = r`, `r∈0..min(b,ρ)`;** blow up each rank-`r` determinantal stratum. Carry
   `|det J|`: `Γ`-polar `s^{ab−1}` + the `A_cor` rank-`r` determinantal Jacobian (codim `(b−r)(ρ−r)`, the
   `C_{ℓ,s}` monomial exponents). **NEVER drop the Jacobian (tide-D KILL guard).** [Edge/corank-one: only
   `r=b` and `r=b−1` — the `Γ`-BOX cutoff + C-transversality of §3, NOT `corankBlock_morsePeel_setLE`.]
4. **Reduce stratum `r` to `redChain u' M`, `u'=u+(b−r)`** (arity−1 IH) at exponent `q_r`; residual deep
   integral is the comparator, finite by the arity-IH. [The `u'`-cut map is the corank (a,b≥1) instance; the
   SATURATED (`a=0`) instance uses the front-factor rank-sector via the density-order `A` (satred §4), NOT
   the `u'`-map (`u` already `=min(M₀,M₁)`). Same principle, different reduced object.]
5. **`min`/sum over strata.** `min_{u'∈range}[peelCharge(u')+minAdm(redChain u' M)] = minAdm(M)` (the
   recursion; banked `minAdm_le_peelCharge_add_redChain`, `RouteMSJResolution:204`). Corner finite for
   `c'<½minAdm M`. The corank-one tie contributes a log absorbed by the per-`c'` `δ`-slack.

**Composition with the deep resolution (couplerad, verified 0/1296).** The corank axis and the deep-rank
axis are ORTHOGONAL and stack via **ARITY** induction. `redChain u' M = (u', M₂,…,M_last)` has its deep tail
`(M₂,…,M_last)` **IDENTICAL to `M`'s and UNTOUCHED** by the corank peel (which collapses only the front
`M₀,M₁→u'=M₁−r`), so `Zf` is generic/fresh (rank `ρ`) in `redChain u' M` — a genuine FRESH arity−1 chain
whose OWN charge (and deep-rank resolution) is supplied by the arity−1 IH, with **no coupling-back / no
carried corank decoration** (this is why ARITY induction is clean where LENGTH induction compounds
decorations — `arity ≠ length`). **Double-count GUARD:** the stratum `{rank(A_cor·Zf)=r}` mixes `A_cor`- and
`Zf`-rank-drops; **attribute the drop to `A_cor`** (the corank matrix) so the deep tail stays fresh, and let
`Zf`'s own rank-drops be resolved by the arity−1 IH's deep resolution of `redChain u' M` — do NOT
double-count the `Zf`-drop between the corank axis and the deep axis.

**Banked pieces.** `freedSchurLoss`/weld/`blockSplitEquiv` (`RouteMSJChartShear`); the arity-IH
`∀M':Fin(L+1+1), RouteMBoxThresholdFinite M'` (`sjStepHyp_of_coupled`, arch1build @4dff27df1); the `minAdm`
recursion (`peelCharge`, `minAdm_le_peelCharge_add_redChain`); `RouteMSJFreeBilinear` (b=1 leaf,
`sumSqND_box_lt_top`); `uniformWenn_proj_le`/`offSector_cover_le` (shell cover). **New content:** (i) the
per-stratum determinantal blow-up + `min`-over-strata `= minAdm` recursion (the JOINT, multi-chain); (ii)
the **corank-one enabling non-degeneracy** `C ↦ C·Q̃ₚ·η` surjective (iff `Q̃ₚ·η≠0`) `⟹` the **δ-slack
per-exponent log bound** (NOT a uniform "C removes the log" — false at `C=0`; edgebrick). A transversality +
a localized singular-integral estimate; the honest form the build closes on. **Diamond guard:** raw-`Pi` instances for all matrix products/reindexes.

**Mathlib gap for the controller's build-vs-cite call.** The polar / Stiefel-sphere CoV and the
determinantal-stratum blow-up with Jacobians: this is **detail-at-scale to BUILD** (patient, decomposable —
the rank-sector of a determinantal variety, reusable radial/polar box lemmas à la `sumSqND_box_lt_top`), NOT
a monument. The one genuinely-new analytic atom is the corank-one C-transversality (ii); the rest is
chart-maps + Jacobians + per-stratum comparator ratios.

**Discipline.** Keep it JOINT (pointwise-in-`z` FALSE, Codex); MULTI-CHAIN (single-chain undershoots
`(k−1)/2` at `k≥2`); do NOT form the global corank-Gram / require `a+b≤M₂` (that is the factored route —
corneradj-confirmed artifact; the joint uses the per-stratum rank-`r` image Gram, non-degenerate by
construction); carry the r-range `0..min(b,ρ)`; do NOT route the edge through the two traps (§3); carry
`|det J|`; claim the VALUE `½minAdm`, not a multiplicity.

## 5. Scope finding (cut-selection axis — for the controller / corneradj)

The peel cut `t★` is **freely choosable** (cut-soundness `flagCharge_ge` for all cuts); shells have
`k_j = k_0 − 2j`. `k_0≤1` (all shells corank-one/interior) is achievable for **1814/2401 chains**
(widths ≤7) but **587 force `k_0≥2`**; and the saturated shell `j=r` (cut `min(M₀,M₁)`) is **unavoidable**
regardless of `t★`. So (D) is needed for: the *forced* deep corank + the saturated `A>2Δ` cells. (Refines
corneradj's open question: cut-selection prunes most but not all deep corank; the saturated corner never
prunes.)

## Close

- **Firmest result.** (D) CONVERGES — the unified joint corank-one/rank-sector resolution reaches
  `½·minAdm M` for the edge (corank-one), deep corank, and saturated `A>2Δ` corners; verified four ways +
  the rigorous `⊆ RMBTF(M)|_chart` truth; **exhaustive KILL scan: 0/4039 undershoot.** Mechanism: corank
  rank-drop `(b−r)` re-peels to cut `u'=u+(b−r)`, reducing to `redChain u' M` (arity−1 IH), and
  `min_{u'}[peelCharge(u')+minAdm(redChain u' M)] = minAdm(M)` — `minAdm`'s recursion, geometrically. The
  corank-one edge is the `s=0/1` tie (ab/2 + LOG, δ-slack). NO `(□)` wall.
- **Most likely to break the BUILD (not the math).** (i) The corank-one TWO TRAPS
  (`corankBlock_morsePeel_setLE` / interior-only `deeperFlag*`; the polar `J`) — both re-derive
  `det(KKᵀ)^{−a/2}`, log-divergent at the edge; must use the Γ-BOX + C-transversality instead. (ii)
  Single-chain lock (`redChain u M` only) undershoots `(k−1)/2` at `k≥2`; use the `u'`-cut chains. (iii)
  pointwise-in-`z` / global corank-Gram (`a+b≤M₂`) — factored artifacts. (iv) claiming a finite-constant
  exact `ab/2` peel (FALSE — δ-slack log only) or a multiplicity `m` (claim the VALUE).
- **Next construction.** The formaliser builds the per-stratum determinantal blow-up (minor chart → shear →
  rank-`r` strata → per-stratum comparator ratio → min/sum), starting from the `RouteMSJFreeBilinear` b=1
  corank-one leaf and lifting via the C-transversality. The exponent arithmetic (`min = minAdm` recursion)
  is the DONE, reusable certificate (`strata_recursion.py`, `kill_check.py`, corneradj `strata.py`, Codex
  332/332). The one genuinely-new atom: the corank-one C-transversality lemma (edgebrick consulting).

Files (absolute):
- `…/threads/genm-satred/D-cert.md` (this cert); `satred-cert.md` (the `a=0` saturated instance)
- `…/threads/genm-satred/codex/D-{prompt}.md`, `D-run.log`
- `…/threads/genm-satred/scripts/{joint_corank, corner_rlct, strata_recursion, AvsDelta, kill_check}.py`
- `…/threads/genm-corneradj/edge-design-cert.md` (per-stratum bookkeeping; Part-1 corrected here)
- `…/threads/genm-edgebrick/` (corank-one analysis + the two traps + the C-transversality; consulting)
