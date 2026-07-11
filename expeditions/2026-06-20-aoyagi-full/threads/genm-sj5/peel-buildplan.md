# §5 lane — the coupled diag(b) peel: formaliser-ready build-plan

**Seat:** pen-and-paper (design lead, the §5 lane). **Charge:** attack the coupled `diag(b)` peel DIRECTLY
via Aoyagi §5 and hand the formaliser a build-plan for `(□)` = `RouteMBoxThresholdFinite M` ∀M, whose sole
open obligation is `sjJointResolution:803` ≡ `DecoratedPeelStep`.
**Method:** source-read of Aoyagi §5 (`paper-sources/aoyagi-2023-…/aoyagi-2023-neural-networks-preprint.txt`,
lines 852–2810 = "Proof of Main Theorem"), source-read of the banked Lean scaffold (`RouteMSJ*`,
`RouteMSJDecorated*`), the banked design record (`genm-sjdecomp/carrier-skeleton.md`,
`genm-sjjoint-design/{cert,corank-adj,pure-vs-atom-adj}.md`, `genm-sjnative/step0-derisk.md`,
`r1upper-{derisk,wall-review}.md`), and ONE decorrelated Codex xhigh consult (`codex/recursion-{prompt,answer}.md`,
conclusion withheld). **NO Lean written.**

This plan does NOT re-derive lane 1 (native cover/σ_min); it is the DIRECT §5 method (radial blow-ups +
det-1 unit clears + absorption-by-renaming + `diag(b)` ledger). Where it reuses machinery shared with lane 1
(the dominant-minor cover), the WEIGHT handling is the §5 one (radial/`diag(b)` monomial ledger), flagged.

> **★ CONTROLLER CORRECTION (2026-07-11).** This plan's "opaque-width lift owed (B2/B5a′)" (§2.2 row, §4.2
> DAG "SECOND BUILDABLE") is **STALE — B5a′ is already BANKED sorry-free.** The opaque-width Schur split +
> the Γ-freeing shear landed in genm-sjcarrier6/7 (post-dating this plan's tree read): `frobSq_schur_split_inv`
> (`RouteMSJChartWeld:83`), `chartInner_schurWeld_eq_of_emb` (`:149`), `chartInner_schurShearFree_eq`
> (`RouteMSJChartShear:253`), `frobSq_rmatMul_reindex`/`chartInner_blockReindex_eq_of_emb`
> (`RouteMSJBlockReindex:71/256`) — all clean-three, wired `DLNFibre.lean:798/805/820`. **The §5 lane's SOLE
> remaining content is B5-desc** (the corank-Gram chain-length descent + legs (i)/(ii)/(iii); see BUILT-INDEX).
> Also: `corankBlock_morsePeel_setLE`'s PosDef hyp FAILS on bottleneck charts (Lean-confirmed the §2.1 atom
> adjudication). See synthesis UPDATE-890.

---

## 0. The target, exactly (re-verified against the live tree)

The whole content of the §5 lane is ONE Prop; everything above it is banked sorry-free.

- **`DecoratedPeelStep`** (`RouteMSJDecoratedRec.lean:78`):
  `∀ {L} (M : Fin (L+1+1+1) → ℕ), (∀ M' : Fin (L+1+1) → ℕ, RouteMBoxThresholdFinite M') →`
  `DecoratedBoxThresholdFinite (SJDecoration.trivial M)`.
- The driver **`routeMBoxThresholdFinite_of_decoratedPeel`** (`:99`) closes `(□)` from it (arity strong
  induction `routeMBoxThresholdFinite_of_step:863` + Morse base `sjBase1_freeMatrix` — banked).
- **`gammaPeelIntegral_lt_top_of_decoratedPeel`** (`:111`) retro-fills `sjJointResolution:803` from it (via
  `sjJointResolution_of_boxThresholdFinite`, `gammaPeel ≤ box`). **So the lane's real target is
  `DecoratedPeelStep`; `803` is obsolete once it lands.** Build `DecoratedPeelStep`, not `803` directly.

`DecoratedBoxThresholdFinite (D)` (`RouteMSJDecorated:148`) = below `carrierThreshold M = ½·minAdm M`, the
decorated integral `∫_{dom} ∫_{unitBox d} (∏_ℓ|u_ℓ|^{jac_ℓ})·(decLoss u z)^{−c'} < ⊤`. At `trivial M` (d=0)
it IS the plain box integral (`trivial_integral_eq:198`).

---

## 1. Aoyagi §5's recursion, Lean-friendly (the coupled diag(b) peel as a DOUBLE induction)

### 1.1 What §5 actually does (source, lines 1269–2340)

§5 computes the RLCT of `‖∏_{s=1}^L C^{(s)}‖²` (`C^{(s)}` free, `M^{(s)}×M^{(s+1)}`, `M^{(s)}=H^{(s)}−r`) by
a recursive coordinate blow-up carrying an inductive normal form with a **two-index state `(S,J)`**:

```
⟨∏_{s=1}^L C^{(s)}⟩ = ⟨ diag(b₁,…,b_{M(S)}) · [ E_J  O ; O  D_J ] · ∏_{s=S+1}^L C^{(s)} ⟩      (p.15)
```
- `M(S) = min{M^{(s)} : s ≤ S}` — running-min corank (the block dimension; monotone, banked
  `sjRunMin_antitone`).
- `E_J` = J×J identity (rank already resolved to units); `D_J` = residual `(M(S)−J)×(M^{(S+1)}−J)` block.
- `diag(b₁,…,b_{M(S)})` = the **diag(b) ledger**: `b_0=1`, `b_i = (∏_{t̃_{s,k}<i} u_{s,k})·b_{i−1}` — a
  monomial in the accumulated blow-up coordinates `u_{s,k}`. The blow-up Jacobian carries `∏ u^{M_{s,k}−1}`.

**One peel step** (Case 1 / Case 2, lines 1473–2340). Blow up along the named submanifold
`{d_ij = 0, u_{s,k} = 0}`; this factors a monomial `u_{s,k}` out of a row-block, so
`diag(b_{J+1},…) → u_{s,k}·diag(b'_{J+1},…)`; then a **det-1 unit transform** (the regular matrices `P`, `Q`
whose entries are the ledger ratios `b'_i/b'_{J+1}` and the residual `d''`, det = 1 — Lemma 2 / Thm 3) reduces
`D_J → [1 ⊕ D_{J+1}]` (one more pivot), ABSORBING the off-pivot residual by renaming `d''' → d`, `c' → c`,
`b' → b`. `J ↦ J+1`.
- **Case 1** (b-ladder has a proper run then a jump): two sub-branches — 1(1) (whole row-block scales,
  the extra instances), 1(2) (one pivot `d_{J+1,J+1}→1`, the row-clear).
- **Case 2** (b-ladder constant to the block end): the whole residual scales by one `u_{S,J+1}`; charge
  `M'_{S,J+1} = (M(S)−J)(M^{(S+1)}−J)`. **← the printed Case-2 TYPO lives here** (see §3.4).

When `J+1 > M(S+1) = min{M(S),M^{(S+1)}}` the block is exhausted (`D'''_J` degenerates to a row/column of
`(1,0,…,0)`); **absorb the residual into the next factor** and `S ↦ S+1`. Terminates at `S = L+1`:
`⟨∏C^{(s)}⟩ = ⟨diag(b₁,…,b_{M(L+1)})⟩`, a pure monomial ideal. Candidate RLCT (lines 2342–2359):
`½·min{M_{s,k} : t̃_{s,k}=0}`, `M_{s,k} = (M^{(1)}−t^{(1)})(M^{(2)}−t^{(1)}) + Σ_{j=2}^L (t^{(j−1)}−t^{(j)})(M^{(j+1)}−t^{(j)})`.

### 1.2 The Lean-friendly recursion — TWO nested inductions, and why it is a DOUBLE induction

**dps-instance-cert, CONFIRMED (my exact read + decorrelated Codex, `codex/recursion-answer.md` Q1).**
The peel is NOT a plain-IH single peel. After the front peel the integrand is **decorated**: the blow-up
coordinate `u₀` sits in BOTH the Jacobian `∏|u_ℓ|^{jac}` AND inside the deeper loss `decLoss` (the shared
divisor — not separable except at the terminal, `SJDecoration.integral` docstring). The plain undecorated
IH controls only `∫ F_red^{−s}`, not `∫ G·F_red^{−s}` with an unbounded correlated `G`; at the binding cut
`c' ↗ (pq+D)/2` the reduced-chain threshold `D/2` is saturated with **zero slack**, so no Hölder/nesting
absorbs `G` (finite `Lᵅ`-range vs `α→∞`). And `diag(b)` cannot be "renamed away" into the next free matrix:
`B ↦ diag(b)·B` has Jacobian `∏ b_i`-powers, **singular at `b_i=0`** — that singular Jacobian is exactly the
ledger's content. **⟹ genuinely a double induction.**

```
OUTER  =  chain ARITY L  (Aoyagi's S-loop, recast).  BANKED, well-founded.
          routeMBoxThresholdFinite_of_step:863 — strong induction on L; L=0 vacuous, L=1 Morse base,
          L≥2 = DecoratedPeelStep. Each peel descends to redChain u★ M = (u★, M₂,…,M_L), ONE fewer layer.
INNER  =  the decorated resolution WITHIN one peel.  THE HEART, unbuilt.
          resolves the front layer-pair's corank block against the deeper product, carrying the diag(b)
          ledger; returns an UNDECORATED shorter-chain integral (so the OUTER plain IH can close it),
          OR carries a decorated IH. Terminates by CHAIN-LENGTH descent (subred), NOT the literal (S,J) loop.
```

**Load-bearing design decision (mine, Codex-corroborated Q1/Q4):** the INNER induction is the subred
**chain-length descent**, not Aoyagi's literal two-index `(S,J)` loop. The literal loop needs a
lexicographic triple/pair measure `(R(S,J), E)` (Case 1(1) moves neither `S` nor `J`) + five further
prose repairs (§3.5); the chain-length descent has measure `= L : ℕ` (banked, matches
`remaining_lt_of_support_ssubset` support-strict-subset) and **all six repairs evaporate**
(`carrier-skeleton §5.3`, Codex Q4). The `diag(b)`/`SJState` ledger stays an INTERNAL invariant, never a
statement decoration (stage2-brief CARRIER discipline, UPDATE-668).

### 1.3 The peel step, precisely (what `DecoratedPeelStep`'s proof does at the binding cut)

Given the plain one-shorter IH and `c' < ½·minAdm M`:

1. **Front-split + pivot-chart cover** (BANKED): `∫ frobSq(A₀·Q)^{−c'} = ∑_{t,ρ,κ} gammaPeelIntegral`
   over pivot ranks `t` and row/col selections `(ρ,κ)` (`sjBoundaryPeel:688`, `pivotLocus_eq_iUnion`).
   Finiteness of each chart-term suffices.
2. **Pivot–Schur block split** on a `t`-pivot chart (BANKED exact, opaque-width lift owed):
   `frobSq(A₀·Q) = ‖a·Q̃_p‖² + ‖C·Q̃_p + Γ·Q_b‖²`, `Γ = D − C·a⁻¹·B` the corank block (`p×q`, `p=M₀−t`,
   `q=M₁−t`), `a⁻¹` living ONLY in det-1 shears (`frobSq_schur_block_split` `RouteMSJChartAlgebra:107`;
   `measurePreserving_shearSub` `RouteMSJPivotChart:337`). The pivot energy `‖a·Q̃_p‖²` is `Γ`-free.
   This IS Aoyagi's det-1 unit clear (Lemma 2). **Take `t = u★`** the binding cut (`exists_binding_cut`).
3. **Resolve the corank block `Γ` — RANK-ADAPTED on the `Q_b` stratification** (see §2 for the atom
   verdict). `Q_b` (`q × deeper-width`) stratifies by rank:
   - good `rank Q_b = q` / top `rank Q_b = q−1`: `corankBlock_morsePeel` (the det-Gram atom) applies —
     exact exponent shift `c' ↦ c'−pq/2`, Jacobian `det(Q_bQ_bᵀ)^{−p/2}` FINITE here.
   - **deeper `rank Q_b ≤ q−2` (binding, ~86%): the in-box RADIAL blow-up** — the blow-up center includes
     the compatible cross/divisor coordinates (Codex Q2 correction 1: radialising `Γ` ALONE does not make
     `‖Ccross+ΓQ_b‖²` a clean `u₀²·(…)`), then the det-1 unit Schur clears; the fresh shared divisor `u₀`
     enters the `diag(b)` ledger (`radialAttach`/`radialStep`), Jacobian `u₀^{pq−1}`. **NOT** the full-space
     Γ-integral (that is the atom B-trap, §2). Equivalently, recurse on the corank-Gram integral as the
     SHORTER chain `(q, M₂,…,M_last)` (subred B5-desc), threshold `min(tail)−q+1`.
4. **The threshold shift + handoff.** The peel emits charge `peelCharge M u★ = (M₀−u★)(M₁−u★) = pq` and
   lands the reduced integrand on `redChain u★ M` at threshold shifted DOWN by `½·peelCharge`
   (`carrierThreshold_shift:71`). By `exists_binding_cut`, `minAdm M = peelCharge M u★ + minAdm(redChain)`
   with zero slack, so `c' < ½·minAdm M ⟹ c'−½·peelCharge < ½·minAdm(redChain)` — the plain IH
   `RouteMBoxThresholdFinite (redChain u★ M)` closes the UNDECORATED reduced integral. The decoration was
   discharged inside step 3 (the inner resolution), NOT carried into the IH.
5. **Charges ADD via the SHARED terminal monomial / CORNER blow-up, not sequential radials** (Codex Q2
   correction 2). A single radial gives only `c' < pq/2 = ½·peelCharge`; the FULL `½·minAdm` (the SUM over
   the binding rank-path) comes from the shared terminal `diag(b)` bookkeeping — the corner `u₀=u₁=0`
   blow-up accumulating Jacobian powers additively (B5c), NOT boundary-wise-min sequential peels (which
   undershoot — `r1upper-derisk` §2: `fibre_lintegral_mul_le` caps at min single layer).

### 1.4 The terminal (Aoyagi Step 4, banked)

At the fully-resolved leaf the loss is `(unit)·∏_ℓ|u_ℓ|^{2k_ℓ}` with Jacobian `∏_ℓ|u_ℓ|^{h_ℓ}`
(`h_ℓ = M_{s,k}−1`), finite ⟺ `c' < min_ℓ (h_ℓ+1)/(2k_ℓ) = ½·min_ℓ M_{s,k} = ½·minAdm`. Banked:
`monomialIntegrand_integrable_of_lt` (`Case222Cover:59`), `terminal_monomial_mul_unit_lintegral_lt_top`
(`RouteMSJTerminal:160`), threshold `iInf_axisRatio_le_monomialThreshold` (`RouteMSJMonomialLower:276`,
S2-free), ledger terminal `sjLoss_terminal_lintegral_lt_top` (`RouteMSJLedger:234`). The `L=1` leaf of the
outer recursion is the free-matrix Morse `sjBase1_freeMatrix` — so ONE peel + IH closes each ≥3-width chain.

---

## 2. The banked-brick library map + the atom adjudication

### 2.1 VERDICT on `corankBlock_morsePeel` (the charge's explicit question)

**`corankBlock_morsePeel` (`RouteMSJCorankPeel:114`; the det-Gram atom, ATOM-1) is the native §5 atom ONLY
on the FULL-RANK `Q_b` strata (good/top). It is NOT the native atom on the BINDING deeper strata.** Three
decorrelated lines agree (my exact read; `pure-vs-atom-adj`; Codex Q2):

- It requires `hG : (Qb·Qbᵀ).PosDef` = `Q_b` full row rank. On good (`rank=q`) / top (`rank=q−1`) strata
  this holds and it delivers Aoyagi's exact shift `c'↦c'−pq/2` with a FINITE weight `det(Q_bQ_bᵀ)^{−p/2}`.
  **CONSUME it for B3/B4.**
- On the deeper stratum `{rank Q_b = r < q}` the map `Γ ↦ Γ·Q_b` has kernel dim `p(q−r) > 0`; the
  full-space integrand is CONSTANT along the kernel ⟹ the `ℝ^{p×q}` integral is `+∞`. Exact witness
  (Codex, = `pure-vs-atom-adj`/`sjj_cutoff`): `∫_{[-1,1]³}(x²+y²γ²)^{−c}` is finite for `c<1`, but
  `∫_ℝ(x²+y²γ²)^{−c}dγ = K_c·|y|^{−1}|x|^{1−2c}` whose outer `y`-integral diverges — full-space enlargement
  fails throughout the ENTIRE true box-finite range. So ATOM-1 on the deeper stratum manufactures a
  divergence the true (bounded-box) integral does not have. **Do NOT consume `corankBlock_morsePeel` on B5.**

The "det ledger" the operator brief names as §5's mechanism is the **det-1 UNIT clears (Lemma 2 /
`block_elimination` / `frobSq_schur_block_split`) + the `diag(b)` MONOMIAL ledger** — NOT `det(Q_bQ_bᵀ)`.
The native deeper-stratum atom is the **in-box radial blow-up + shared monomial ledger** (ATOM-2), or
equivalently subred's **chain-length descent** recursing on the corank-Gram integral as a shorter chain.
Note (Codex, measure hygiene): the rank strata are measure-ZERO; "resolve the deeper stratum" means resolve
on chart NEIGHBOURHOODS (the cover / blow-up charts), never integrate over the bare null set.

### 2.2 Brick → banked-piece map (from `BUILT-INDEX.md`, re-verify `file:line` at build time)

| step | brick | banked pieces consumed | status |
|---|---|---|---|
| driver root | `DecoratedPeelStep → (□)` + retro-fill 803 | `routeMBoxThresholdFinite_of_decoratedPeel:99`, `_of_step:863`, `sjBase1_freeMatrix`, `gammaPeelIntegral_lt_top_of_decoratedPeel:111` | BANKED |
| 1.3-1 front cover | pivot-chart cover | `sjBoundaryPeel:688`, `pivotChartCover_matBox_le_sum`, `pivotLocus_eq_iUnion` | BANKED |
| 1.3-2 Schur split | det-1 unit clear (Lemma 2) | `frobSq_schur_block_split` (`RouteMSJChartAlgebra:107`), `measurePreserving_shearSub` (`RouteMSJPivotChart:337`), `mulLeftₚ`/`lintegral_comp_mulLeftₚ` (`RouteMSJDecoratedPeelMeas`) | BANKED L=2; **opaque-width lift owed (B2/B5a′)** |
| 1.3-3 good/top | det-Gram atom | `corankBlock_morsePeel_lt_top:114`, `matBox_corank_residual_le` (`RouteMSJCorankResidual`), `sumSqND_box_lt_top`, `radial_morse_dominates_lt_top` | BANKED (B4 certified; B3 in flight #113) |
| 1.3-3 deeper | in-box radial + ledger | `radialAttach:242`/`radialStep`, `gen_rowMix_const`, `loss_blockSplit`, `RouteMSJSphereBlowup:82` (`lintegral_eq_polar`), `radial_morse_residual_power_le` (`RadialResidualPower:157`) | **THE HEART — new inner induction (B5)** |
| 1.3-4 charge | binding cut + shift | `exists_binding_cut:79`, `peelCharge:45`, `minAdm_le_peelCharge_add_redChain:52`, `carrierThreshold_shift:71`, `minAdmRec_eq_minAdm` | BANKED (ℕ/ℝ) |
| 1.3-5 corner | additive-charge corner CoV | `lintegral_eq_polar`, `radial_morse_residual_power_le`, `Mval_decompose`/`sjChargeUpdate_accum:353` | **corner CoV composition NEW (B5c)** |
| 1.4 terminal | monomial read-off | `monomialIntegrand_integrable_of_lt` (`Case222Cover:59`), `terminal_monomial_mul_unit_lintegral_lt_top:160`, `iInf_axisRatio_le_monomialThreshold:276`, `sjLoss_terminal_lintegral_lt_top:234` | BANKED |
| carrier | ledger IS `diag(b)` | `SJLinGenState` (`RouteMSJLinGen:100`), `SJDecoration:89`, `.trivial:157`, `decoratedBoxThresholdFinite_trivial_iff:217` | BANKED |

### 2.3 Genuinely-NEW sub-lemmas (surface, don't launder)

1. **★ The decorated inner induction (THE HEART).** A finiteness predicate on the corank-Gram / decorated
   integral (NOT the plain Frobenius box), and its **chain-length descent** `L → L−1`: the corank-Gram
   integral `∫ det(Q_bQ_bᵀ)^{−a/2} d(Y,A_{≥2})` (`Q_b = Y·A_{≥2}`) reduces to that of the SHORTER chain
   `(q, M₂,…,M_last)` via `J(A_{≥2}) = det⁺(Gram A_{≥2})^{−q/2}` on a **dominant-minor cover** of `A_{≥2}`
   (on-chart `J` a unit over the rank-`min(M₂,q)` image; deeper recursion off-chart). Math PROVEN (subred
   `verdict.md`: Gaussian/Bartlett + exact `(1,1,2)`/`(2,2,3)`, decorrelated Codex). Lean UNBUILT. **Codex
   Q2 flags this needs a NEW Gram-decorated IH — the plain Frobenius-loss IH does not cover the joint
   weighted residual; do NOT wire it as `[free-Q core] ∘ [loss IH]` (invalid factorisation, wrong already
   at `a=0`).** Consumes B2, the dominant-minor cover machinery, the `⅟→⁻¹` integrand conversion.
2. **The min-tail-width threshold ℕ-lemma (B5-desc-ℕ).** `min(M₂,…,M_last) − q + 1` composed across the
   descent equals the layer-peel `minAdm` recursion (`minAdmRec`). Analogue of `minAdm_eq_frontPeel`. Small.
3. **The corner blow-up toric CoV (B5c).** `u₁ = u₀·τ` at the corner `u₀=u₁=0`, accumulating Jacobian
   powers ADDITIVELY onto one terminal divisor (finiteness leg banked; the CoV composition is new).
4. **Bounded-below unit supply (B5d).** The resolved cores `≥ a > 0` a.e. uniformly on the compact box (the
   `hunit` the terminal endpoint consumes); technique banked (`Uval4422_ae_pos` &c.), residual = a.e.→uniform
   bridge.
5. **Center-list completion (cornrev FOLLOW-UP-2).** The incidence-center list for the deeper resolution
   needs the **proportionality locus `(x₂,p₂)∥(x₃,p₃)`** added (the `5/2` carrier in `(2,3,3,4)`) beyond
   `{A=0},{Y=0},{im A⊆ker Y}`. Actionable, not missing.

---

## 3. Soundness gates (each must be discharged, not assumed)

### 3.1 Charges ADD, not MIN, along the shared rank-drop divisor
The threshold is a SUM over the binding rank-path (`minAdm M = peelCharge M u★ + minAdm(redChain)`, exact
at `u★`), NOT a min over single boundaries. GATE: the additive coupling must come from the SHARED terminal
`diag(b)` monomial / the CORNER blow-up (B5c). Sequential boundary radials give boundary-wise MIN and
UNDERSHOOT by a factor of 2 at the monster `(3,3,3,3)` (`r1upper-{derisk,wall-review}`). Kill-condition: any
brick routing through `fibre_lintegral_mul_le` + `product_min_rlct` for the corner (they give the min).
`radialAttach` alone is MULTIPLICATIVE (the `min→3/2` caricature cross-level, `BUILT-INDEX`) — the additive
coupled corner is the fix.

### 3.2 Non-circular descent (strictly-shorter chain; keep `1 ≤ t`)
GATE: the OUTER descent must land a STRICTLY-shorter chain (`redChain u★ M`, `L→L−1`) closed by the plain
IH — never route back through `sjJointResolution`/`DecoratedPeelStep` on the SAME arity. `t = u★ ≥ 1` keeps
the pivot positive so the front factor genuinely contributes (the `t=0` whole-box term is excluded — it was
the circularity the re-scoped `gammaPeelIntegral` fixed, `RouteMSJResolution:489`). The INNER descent
(chain-length) is bounded below by 0 and strictly decreasing per subred; termination banked-supported via
`remaining_lt_of_support_ssubset` (support strict subset). Do NOT build Aoyagi's literal `(S,J)` loop
(measure `(R,E)` + five prose repairs; avoidable — §3.5).

### 3.3 Binding cut is interior at the log-borderline
GATE: `c' = pq/2` (the block Morse boundary) must be strictly EXCLUDED — `c' < ½·minAdm` is strict, and the
`c'=ab/2` log-borderline is interior only AT the binding cut (`exists_binding_cut`, e.g. `M=(4,4,2,2) t=2`;
`RouteMSJDecoratedCharge`). The good/top atom `corankBlock_morsePeel` needs `pq/2 < c'` (strict) — consistent,
since off the binding cut the reduced threshold has slack. Marginal `p = min(tail)−q+1` is LOG-divergent
(Codex Q3) — the strict `<` must be preserved through the descent-ℕ lemma.

### 3.4 The Case-2 typo (build the prefix-min form; land a fidelity card)
Aoyagi's printed Case-2 charge `M'_{S,J+1} = (M(S)−J)(M^{(S+1)}−J)` uses ACTUAL widths; the faithful form is
PREFIX-MIN `(μ_S − J)(M^{(S+1)}−J)`, `μ_S = min{M^{(s)}:s≤S}`. Discrepancy `(M(S)−μ_S)(M^{(S+1)}−J)`.
Threefold absorption (`carrier-skeleton §7`, all confirmed): (1) VALUE unaffected — the Case-2 branch never
attains the min (trusted-spine slack `2λ ≤ M^{(i)}M^{(j)}`), coarse bound suffices; (2) equal-prefix slices
(e.g. `(3,3,3,4)`) coincide; (3) width-general chains DIVERGE (incl. MONOTONE-INCREASING, e.g. `(2,4,4)`
S=2 J=0: 16 vs 8). GATE: **build the prefix-min `(μ_S−J)` form regardless** and land a named-deviation
fidelity card — the actual-width form is not just a bookkeeping overcount, it references rows ABSENT after
the bottleneck, so the coordinate construction itself is undefined in actual widths. The `normalSlice`/
descent route (reduce to the `μ`-reduced chain directly) sidesteps it.

### 3.5 (native literal-loop only — AVOID) the six measure/prose repairs
If anyone builds Aoyagi's literal inner `(S,J)` loop, these are OWED: the triple/pair measure `(R,E)`, the
Case-1(1) label-move rule, the `J=K_S` empty-residual boundary transition, the `S=1` base convention, the
Case-2-iterates clause, the comparability-preservation lemma (`carrier-skeleton §5.2`, Codex Q4). **The
recommended chain-length descent (§1.2) makes ALL SIX evaporate** — this is the decisive argument for the
descent architecture over the literal loop.

---

## 4. VERDICT + the buildable sub-lemma DAG

### 4.1 Verdict
The coupled `diag(b)` peel is **TRUE and BOUNDED** (no wall; three decorrelated lines: my exact algebra,
the banked design record, Codex xhigh). Its Lean shape is a **double induction**: OUTER = chain arity
(banked driver), INNER = the decorated resolution within one peel, terminating by CHAIN-LENGTH descent
(subred), NOT Aoyagi's literal two-index loop. The single open analytic content = **the decorated inner
induction (B5)**: the corank-Gram chain-length descent on the binding deeper strata, threshold
`min(tail)−q+1`, dominant-minor cover, `J = det⁺(Gram)^{−q/2}`. Everything else is banked or opaque-width
lift on a proven template. `corankBlock_morsePeel` is the native atom ONLY on the full-rank strata (B3/B4);
on the binding deeper strata the native mechanism is the in-box radial / chain-length descent (ATOM-1 fails
there — Codex + `pure-vs-atom-adj` exact witness).

### 4.2 The DAG (Level A = integrability `< ⊤`, feeds `(□)`; sizes S/M/L)
```
D0  DecoratedPeelStep → (□) + retro-fill 803                    [BANKED]
 └ B1  front-split + pivot cover                                [BANKED]
    └ B2  opaque-width Schur block split (det-1 unit clear)     [M, lift; L=2 banked]     ← BUILDABLE
       ├ B4  top/`b=1` stratum leaf (free-bilinear)             [S, base; CERTIFIED]      ← FIRST BUILDABLE
       ├ B3  good stratum (det-Gram atom; thr min(tail)−q+1)    [M, #113 in flight]
       └ B5  ★ deeper strata = decorated inner induction        [L, THE HEART]
            ├ B5a′ opaque-width block-shear identity            [M, lift]                 ← SECOND BUILDABLE
            ├ B5-desc  chain-length descent (Gram-decorated IH) [L, math PROVEN/subred]
            │    └ B5-desc-ℕ  min-tail-width → minAdm           [S, new ℕ-lemma]
            ├ B5b  additive charge (sum-not-min)                [S; ℕ banked]
            ├ B5c  corner blow-up toric CoV (charges ADD)       [M; finiteness banked]
            └ B5d  bounded-below unit supply (hunit)            [M; technique banked]
 B6  DecoratedPeelStep assembly (compose B2–B5 at u★)           [M, lift] consumes B2,B3,B4,B5
 B7  terminal read-off verify (Lemma-3 arithmetic)             [BANKED verify]
```
**Commission order:** (1) **B4** — the `b=1`/top-stratum leaf: banked corank/Morse inputs, no recursion,
closes an entire chart class, de-risks the pivot-Schur wiring. (2) **B5a′** in parallel — pure opaque-width
linear algebra (`L=2` banked, lift by prefix-length induction reusing `prodAux_succ`). (3) **B5-desc** on a
CONTRACTING-TAIL chart (`M₂<M_last`, e.g. `(3,3,3,4)` `q∈{1,2}` giving tail `(1,2)` ⟹ `(q,1,2)`) so the
min-tail twist is EXERCISED, not hidden by a balanced case — front-load the det-inverse dominant-minor cover
finiteness (§4.4). Then B5b/B5c/B5d/B6, B7 verify.

### 4.3 Firmest result
`DecoratedPeelStep` is the correct sole target (driver + retro-fill of `803` both banked). The recursion is
a double induction with a BANKED outer (chain arity) and a math-PROVEN inner descent (subred chain-length,
threshold `min(tail)−q+1`, Gaussian/Bartlett-exact + exact witnesses). `corankBlock_morsePeel` = native atom
on full-rank strata only. The `diag(b)` ledger, base state, both blow-up ops, block-split, value formula, and
monomial terminal are ALL banked; the missing content is the inner-induction composition + the deeper-stratum
descent + the opaque-width lifts.

### 4.4 Most likely to break
The **det-inverse dominant-minor cover boundary (§8-i)**: subred proves the MATH (the cover spends
`J=det⁺(Gram)^{−q/2}`, the shrinking-image cancellation is Gaussian/Bartlett-exact), but the Lean cover
assembly + the `⅟→⁻¹` integrand conversion + verifying **no Beta-divergence survives on the cover seam**
(the exact mechanism that sinks the atom route, `pure-vs-atom-adj §3`) is the delicate labour. Secondary:
the **contracting-tail twist silently ignored** — a formaliser using the free-`Q` threshold `q−q+1` (=1) or
`q−b+1` instead of `min(tail)−q+1` OVERESTIMATES the budget on every `M₂<M_last` chart, and
permutation-invariance puts contracting tails AT binding cuts (load-bearing, not a rare edge). Tertiary: a
build attempting the plain-IH single peel (dps-instance-cert violation) — Codex Q1 + cert.md both say it is
a category error (zero-slack, unbounded correlated weight); the decorated inner induction must be built.

### 4.5 Next construction / consult that settles the open part
Before the opaque-width lift, run a `local-codex-consult` on the **Lean cover finiteness** — specifically
that the dominant-minor cover of `A_{≥2}` leaves NO Beta-type divergence on the cover seam (the atom route's
failure mode), on the concrete contracting-tail vertical slice `(3,3,3,4) q∈{1,2}`. The single computation
that clarifies: the composed inner descent END-TO-END on that slice (front cover → Schur split → deeper
corank-Gram descent → corner blow-up → monomial terminal → accounting `=7=minAdm`) — NONE of the probes has
run the COMPOSED machine at opaque width; this vertical slice shakes out the carrier before the width-general
grind. Also add the proportionality center `(x₂,p₂)∥(x₃,p₃)` to the incidence-center list (§2.3-5) before
B5's center enumeration is fixed.

---

## Anchors
- Open obligation: `RouteMSJResolution.lean:803` (`sjJointResolution`) ≡ `RouteMSJDecoratedRec.lean:78`
  (`DecoratedPeelStep`); driver `:99`, retro-fill `:111`.
- Aoyagi §5 source: `paper-sources/aoyagi-2023-consideration-of-learning-efficiency-of-dln/…preprint.pdf`,
  "5. Proof of Main Theorem" (text lines 852–2810; recursion 1269–2340; terminal 2342–2359; counting
  Lemma 3/4/5 2596–2808).
- Authoritative brick DAG: `threads/genm-sjdecomp/carrier-skeleton.md` (subred descent, LIVE-TREE banner).
- Atom adjudications: `threads/genm-sjjoint-design/{corank-adj,pure-vs-atom-adj,cert}.md`;
  `threads/genm-sjnative/step0-derisk.md` (clear-first ordering).
- Decorrelated Codex (this thread): `threads/genm-sj5/codex/recursion-{prompt,answer}.md`.
- Banked library: `expeditions/2026-06-20-aoyagi-full/BUILT-INDEX.md`.
