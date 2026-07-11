# genm-sjendpoint-recon — recon-map: route-S corner endpoint for the (S,J) descent

**Seat:** self-recon (read-only). **Date:** 2026-07-11. **Base:** canonical HEAD `cdd0b206`
(`expedition/aoyagi-full`). **Charge:** map the banked state for closing the corank-2 corner-monomial
endpoint of the (S,J) descent (vsastruct `corank2-cert.md` route S). **No Lean edits, no builds.**
All line numbers verified against the live tree at `cdd0b206`.

---

## HEADLINE (fold into the build spec)

**The charge's named endpoint is one architecture-generation stale — correct it before speccing.**
The charge frames the target as "close `sjJointResolution` (and/or `sjBoundaryPeel`) for the corner
monomial → `monomialIntegrand_integrable_of_lt`". Against the live tree:

1. **`sjBoundaryPeel` is CLOSED** (proved sorry-free, `RouteMSJResolution.lean:688–744`). Not a gap.
   The `RouteMSJResolution:950` docstring calling it "a remaining sorry" is STALE (already flagged by
   `genm-decrecon`).
2. **`sjJointResolution` (`RouteMSJResolution.lean:797`, the lone live `sorry` at `:803`) is now
   RETRO-FILLABLE / OBSOLETE.** The `genm-decbuild` re-architecture (landed since the prior
   `genm-decrecon` recon; `RouteMSJDecoratedRec.lean`) re-gates the whole `(□)` on a single stated
   analytic `Prop` `DecoratedPeelStep` and PROVES, sorry-free, `DecoratedPeelStep → ∀M,
   RouteMBoxThresholdFinite M` (`routeMBoxThresholdFinite_of_decoratedPeel:99`) AND `DecoratedPeelStep
   → gammaPeelIntegral … < ⊤` = the exact `:803` goal (`gammaPeelIntegral_lt_top_of_decoratedPeel:111`,
   via the PROVED bridge `sjJointResolution_of_boxThresholdFinite`). So the live `(□)`-discharge core is
   **`DecoratedPeelStep` (`RouteMSJDecoratedRec.lean:78`), an UNPROVEN `Prop`** — the sole open analytic
   content of R1-UPPER. `sjJointResolution:803` is a parallel, now-superseded endpoint; closing it
   directly re-opens the circularity trap for no gain.

3. **The corner monomial the cert describes IS banked as the TERMINAL (T5) of that recursion, not a
   fresh endpoint.** `monomialIntegrand_integrable_of_lt` (`Case222Cover.lean:59`) is consumed by
   `terminal_monomial_mul_unit_lintegral_lt_top` (`RouteMSJTerminal.lean:160`) → `sjLoss_terminal_
   lintegral_lt_top` (`RouteMSJLedger.lean:234`). The corner blow-up ATOM `u₀²U₀+u₁²U₁` → single
   terminal divisor is ALSO banked as `corankBlock_morsePeel_lt_top` (`RouteMSJCorankPeel.lean:114`).
   The cert's coupling warning (independent divisors → 3/2, coupled → 7/2) is realised in this
   architecture ACROSS recursion levels (one `radialAttach` `u₀²`-peel per arity step, threshold shifts
   by `½·peelCharge`), NOT as a single 2-scale integral — so the honest gap is not "build the corner
   monomial" but **the block-split step (T4) that PRODUCES the reduced decoration the terminal lands
   on**, plus the analytic-`R` rowMix synchronisation (T2 a′).

**Net for the controller:** commission the build against `DecoratedPeelStep`, whose remaining pieces are
**T4 (block-split regime A/B — genuinely new)** and **T2 a′ (analytic-`R` rowMix `hsh`)**; the corner
blow-up atom, the terminal, the radial peel, the charge bookkeeping, and the Schur-split/shear are all
banked. Do NOT re-target `sjJointResolution:803` directly (circular-trap territory), and do NOT build
the corner monomial as a standalone `monomialIntegrand` (it is the banked T5 terminal). This map
supersedes the endpoint framing of the charge and updates `genm-decrecon` (its Tile 0 / GAP 2 driver is
now DONE).

---

## 1. The (S,J) spine sorry state (exact, verified at `cdd0b206`)

**Only ONE live `sorry` in the entire `RouteMSJ*` + `RouteMBoxThresholdFinite` family:**
`RouteMSJResolution.lean:803` (`sjJointResolution`). Confirmed by a trimmed-content sorry grep over
`DLNFibre/DLN/RLCT/Validate/` (all other "sorry" hits in these files are docstring prose).

| Declaration | file:line | status |
|---|---|---|
| `sjJointResolution` | `RouteMSJResolution.lean:797` (`sorry`@`803`) | **LIVE sorry, but RETRO-FILLABLE / obsolete** (see below) |
| `sjBoundaryPeel` | `RouteMSJResolution.lean:688` | **PROVED sorry-free** (`:694–744`); pure cover inequality |
| `sjResolutionStep_proof : SJStepHyp` | `RouteMSJResolution.lean:849` | PROVED (composes peel + `sjJointResolution`) |
| `routeMBoxThresholdFinite_of_step` (wrapper) | `RouteMSJResolution.lean:863` | PROVED, axiom-clean; strong induction on arity |
| `routeMBoxThresholdFinite_sjResolution` (`(□)`) | `RouteMSJResolution.lean:950` | PROVED **modulo** `:803` (via `sjResolutionStep_proof`) |
| `sjBase1_freeMatrix : SJBaseHyp` | `RouteMSJResolution.lean:912` | PROVED (free-matrix Morse base) |
| `SJState` / `sjRunMin` / `sjRunMin_antitone` | `RouteMSJResolution.lean:752 / 761 / 771` | **STUBS** — coarse dimensional shadow only; the matrix-valued `[E_J|D_J]` invariant is deferred/folded into `:803` |

**`sjJointResolution`'s honest statement (`:797–803`).** GIVEN the strong IH `hIH : ∀ M' : Fin(L+1+1)→ℕ,
RouteMBoxThresholdFinite M'` (box-finiteness for EVERY one-shorter chain), `t`, `ρ : Fin t ↪ Fin(M 0)`,
`κ : Fin t ↪ Fin(M 1)`, `ht : 1 ≤ t`, `ht2 : t ≤ min(M 0)(M 1)`, `c' : NNReal`, `hc' : c' <
minAdm M / 2` ⟹ `gammaPeelIntegral M t ρ κ c' < ⊤`. `gammaPeelIntegral` (`:517`) is the RAW per-chart
integral `∫_{A'∈box(tail)} ∫_{A₀∈matBox ∩ pivotChart ρ κ} frobSq(A₀·prod(tailChain M)A')^{−c'}`.

**The CIRCULAR pitfall, characterised exactly (docstring `:46–60`, `:488–499`, `:777–796`).** The OLD
peel summed pivots over `t ∈ range(min+1)`; the `t = 0` term is a `0×0` pivot, whose chart is the WHOLE
box, so `gammaPeelIntegral M 0 _ _` = `routeMLayerBoxIntegral M c' 1` = `RouteMBoxThresholdFinite M`
itself = the induction goal. Feeding `sjJointResolution M hIH 0 …` would then need the very statement
being proved. **Fix (live):** `sjBoundaryPeel` sums over `Finset.Icc 1 (min M₀ M₁)` (`:691`) and
`sjJointResolution` requires `ht : 1 ≤ t` (`:800`); `{rank = 0} = {A₀ = 0}` is volume-null so `{rank ≥ 1}`
= box a.e. **INVARIANT for any build: never instantiate `sjJointResolution`/`gammaPeelIntegral` at
`t = 0`; keep `1 ≤ t` live** — at `t ≥ 1` the pivot has positive rank and the chart reduces to STRICTLY
shorter chains (`redChain t M`, `tailChain M`), so the IH is legitimate.

**The live re-architecture that supersedes `:803` (`RouteMSJDecoratedRec.lean`).**
- `DecoratedPeelStep` (`:78`) — **UNPROVEN `Prop`** (no `theorem : DecoratedPeelStep` anywhere; verified
  by grep). For every `≥3`-width `M`, given box-finiteness of every one-shorter chain, the trivial
  decoration on `M` is finite below `carrierThreshold M = ½·minAdm M`.
- `decoratedPeelStep_imp_sjStepHyp` (`:89`), `routeMBoxThresholdFinite_of_decoratedPeel` (`:99`),
  `gammaPeelIntegral_lt_top_of_decoratedPeel` (`:111`) — all PROVED sorry-free; the last discharges the
  exact `:803` goal. **⟹ once `DecoratedPeelStep` is proved, `(□)` and `:803` both close and `:803` need
  never be touched.**

---

## 2. (a) CONSUME — banked, reuse directly (exact names + file:line)

### The endpoint chain the descent lands on (all PROVED)
- **`monomialIntegrand_integrable_of_lt`** — `Case222Cover.lean:59`.
  `(d k h : Fin d→ℕ)(c' : NNReal)(hc' : 0<c')(hlt : (c':ℝ≥0∞) < monomialThreshold d k h) ⟹
  IntegrableOn (monomialIntegrand d k h c') (unitBox d)`. THE corner-monomial integrability endpoint.
  `monomialIntegrand d k h c u = (∏|uⱼ|^{hⱼ})·(∏|uⱼ|^{2kⱼ})^{−c}` — `k` = loss-vanishing exponents,
  `h` = Jacobian-measure exponents. Its down-set companion: `monomialIntegrand_downset:30`.
- **`terminal_monomial_mul_unit_lintegral_lt_top`** — `RouteMSJTerminal.lean:160`. Lifts the above to
  `monomial × (unit bounded in [a,b], a>0)`: `∫_{unitBox} (monomialIntegrand … · |unit|^{−c'}) < ⊤`
  below `monomialThreshold`. (`terminal_monomial_mul_unit_integrable:136` is the `IntegrableOn` form.)
- **`sjLoss_terminal_lintegral_lt_top`** — `RouteMSJLedger.lean:234`. The (S,J) terminal: given a
  dehomogenised generator `∃ i₀, e i₀ = sharedDivisorExp e` (⟹ residual unit `∈ [1,#ι]`) and
  `c' < monomialThreshold d (sharedDivisorExp e) h`, `∫_{unitBox} (sjLoss e u)^{−c'}·∏|uₗ|^{hₗ} < ⊤`.
  This is **where the corner monomial actually terminates** in the decorated recursion.
- **`iInf_axisRatio_le_monomialThreshold`** — `RouteMSJMonomialLower.lean:276`. S2-FREE lower bound
  `⨅ⱼ (hⱼ+1)/(2kⱼ) ≤ monomialThreshold d k h` — discharges the `hthr`/`hlt` gate above WITHOUT the
  cited `monomial_rlct`. (Support bricks `:62/:87/:215/:260`.)

### The corner blow-up ATOM + Schur-split + shear (the vslice §5 corner, BANKED)
- **`corankBlock_morsePeel_lt_top`** — `RouteMSJCorankPeel.lean:114` (sorry-free, S2-free). The
  corank-block radial Morse peel on the atom shape `w + ‖Apiv‖² + ‖Ccross + Γ·Qb‖²`; the Lean form of
  the vslice-cert §5 corner blow-up `u₀²U₀+u₁²U₁`. (Companions `_eq:65`, `_setLE:88`.)
- **`frobSq_schur_block_split`** — `RouteMSJChartAlgebra.lean:107`. The EXACT block identity rewriting
  `frobSq(A₀·Q)` on a unit-pivot chart to `‖A·Q̃ₚ‖² + ‖C·Q̃ₚ + Γ·Q_b‖²` (`Q̃ₚ = Qₚ + A⁻¹B·Q_b`,
  `Γ = D − CA⁻¹B`) — the honest bridge `sjJointResolution`'s docstring names.
- **`measurePreserving_shearSub`** — `RouteMSJPivotChart.lean:337`. The MP shear `D ↦ Γ = D − CA⁻¹B`
  exposing `Γ` as a free variable.
- **`matBox_corank_residual_le`** — `RouteMSJCorankResidual.lean:114`. The isotropic corank-atom Gram
  residual (the `Γ ↦ Γ·Q_b` CoV output), origin `genm-sjpeel-blow`.

### Charge bookkeeping (all PROVED)
- **`Mval_decompose`** — `RouteMLayerSplit.lean:96` (used by `sjChargeUpdate_accum`,
  `RouteMSJResolution.lean:353`): `Mval M T = (M₀−T₀)(M₁−T₀) + Mval (redChain T₀ M)(tail T)`.
- **`sjChargeBudget_le`** — `RouteMSJResolution.lean:203`: `minAdm M ≤ (M₀−t)(M₁−t) + minAdm(redChain t M)`.
  Siblings: `sjChargeBudget_recursion:196`, `_binding:210`, `sjSubordination:339`
  (`a = (M₀−t*)(M₁−t*) ≤ minAdm(tailChain M)` — coupling stays ≤ threshold; NOTE its docstring flags
  strict slack is FALSE at some binding cuts, so a build must select a gentle cut, not the arbitrary
  minimiser). `minAdm_leadWidth_mono:287`, `minAdm_cons_zero:266` also banked.
- **`peelCharge`** — `RouteMSJDecoratedCharge.lean:45` (`(M₀−u)(M₁−u)`); **`minAdm_le_peelCharge_add_
  redChain`** `:52`; **`half_minAdm_sub_half_peelCharge_le`** `:67`; **`exists_binding_cut`** `:79`.
  `carrierThreshold_shift` — `RouteMSJDecorated.lean:71`.

### The decorated carrier + banked tiles (T3 fully banked)
- `SJDecoration` structure `RouteMSJDecorated.lean:89`; `.decLoss:128`, `.integral:139`,
  `DecoratedBoxThresholdFinite:148`, `.trivial:157`, `carrierThreshold:64`.
- `decoratedBoxThresholdFinite_trivial_iff` — `RouteMSJDecorated.lean:217` (PROVED: trivial decoration
  finiteness ⟺ `RouteMBoxThresholdFinite M`).
- `SJDecoration.radialAttach:242` + `radialAttach_decLoss:262` (multiply loss by `u₀²`, `d→d+1`);
  **integral-level T3 banked:** `radialAttach_integral` `RouteMSJDecoratedRadial.lean:83`,
  `radialAttachFactor_lt_top:65` (per-divisor Morse threshold `c'<(j₀+1)/2`), `radialAttach_integral_
  lt_top` `RouteMSJDecoratedRadialFin.lean:45`.
- Measurability plumbing banked: `RouteMSJDecoratedMeas` (`measurable_decLoss`, `measurable_integrand`,
  …); the matrix-space Haar-CoV diamond workaround `mulLeftₚ`/`lintegral_comp_mulLeftₚ`/
  `lintegral_box_le_absorption` in `RouteMSJDecoratedPeelMeas.lean:37/69/90` (see `lean/CLAUDE.md`
  gotcha, `genm-decbuild` 2026-07-10).
- The block-split coordinate frame (OPTIONAL plumbing, clean-three): `gammaPeelIntegral_piSplit_eq`
  (`RouteMSJTransport.lean`), `rowSplit_lintegral_eq` (`RouteMSJRowSplit.lean`); deep factor
  `sjDeepFactor` `RouteMSJDeepFactor.lean:37`, `gammaPeelIntegral_sjGoodMap_eq':81`.

### Retro-fill bridge for `:803` (if ever wanted for tidiness — PROVED)
- `gammaPeelIntegral_le_boxIntegral` `RouteMSJJointReduce.lean:55`, `sjJointResolution_of_
  boxThresholdFinite` `:68`.

---

## 3. (b) STAGED for this point vs (c) the precise GAP

### STAGED (built deliberately to be consumed here — highest-value)
- **`DecoratedPeelStep` + its driver/bridge** (`RouteMSJDecoratedRec.lean:78/99/111`) — the whole
  conditional recursion exists SO THAT the only thing left to prove is the one analytic `Prop`. This
  resolves `genm-decrecon`'s GAP 2 (driver) — now DONE.
- **The corner endpoint pieces are ALL staged** to compose in the T4→T5 handoff:
  `frobSq_schur_block_split` (split) → `measurePreserving_shearSub` (free Γ) →
  `corankBlock_morsePeel_lt_top` / `freedSchurLoss_inner_peel_lt_top` (inner Γ peel) →
  `radialAttach` (`u₀²`) → `sjLoss_terminal_lintegral_lt_top` → `monomialIntegrand_integrable_of_lt`.
- **Block-split regime A/B pattern is STAGED (conditional):** `RouteMSJFreedPeel.lean` welds the corank
  atom onto the freed loss `freedSchurLoss` (`RouteMSJChartShear.lean:146`):
  - **Regime A** `freedSchurLoss_inner_peel_lt_top` (`:114`): `∫_Γ (freedSchurLoss x Γ Q)^{−c'} < ⊤`
    for `ab/2 < c'`, given `hG` (`Q_b Q_bᵀ` PosDef) + `hpiv` (pivot energy > 0). Uses
    `corankBlock_morsePeel_lt_top`.
  - **Regime B** `freedSchurLoss_inner_bounded_lt_top` (`:156`): the atom-inapplicable branch — over ANY
    finite-measure `s`, `< ⊤` for `0 ≤ c'`, given `hpiv`. Drops the nonneg corank term.
- **rowMix (a)-half** `SJDecoration.rowMix` (`RouteMSJDecoratedRowMix.lean:56`) + `rowMix_decLoss:100`
  (mixed quadratic `∑ⱼ(∑ᵢRⱼᵢgenᵢ)²`, unconditional at CONSTANT support via `hconst`).

### THE GAP — what must be newly proven (in priority order)
1. **T4 — block-split regime A/B assembly into ONE decorated peel (the genuinely-new heart).** The
   inner-Γ finiteness (regimes A/B) is banked CONDITIONALLY; the FreedPeel header explicitly warns the
   three interface hypotheses (`hG` PosDef, `hpiv` pivot-energy > 0, `hs` finite-measure) **do NOT hold
   pointwise for a fixed `A'`** — producing them THROUGH the resolution (a.e. in `A'`, over the deep
   factor) and choosing regime by `c'` vs `peelCharge/2` (with the `c' = pq/2` log-borderline correctly
   EXCLUDED by strict `c' < ½·minAdm`) is the open construction. This is `genm-decrecon`'s Tile 4(c),
   still unbuilt (no dedicated module; grep confirms no T4 file).
2. **T2 a′ — analytic-`R` rowMix synchronisation.** `rowMix_decLoss` is proved only at CONSTANT support
   (`hconst`); the support-homogeneity `hsh` for the ACTUAL Schur matrix `R = P⁻¹B` at a NON-fresh block
   is deferred (RowMix docstring). Must discharge it and wire `rowMix_decLoss` into the peeled integrand.
3. **T5 wiring (small).** Connect the fully-resolved leaf decoration's `SJDecoration.integral` to
   `sjLoss_terminal_lintegral_lt_top` (the lemma is banked; the wiring is not).

**Is the vslice §5 corner blow-up itself banked? YES** — as `corankBlock_morsePeel_lt_top`
(`RouteMSJCorankPeel.lean:114`) + the regime-A/B FreedPeel wrappers. **The GAP is not the blow-up
integral; it is the RESOLUTION/SYNCHRONISATION that lands the raw chart integrand on the atom's
hypotheses** (T4) and mixes the analytic Schur rows (T2 a′). The coupling the cert insists on is
delivered by the per-peel `radialAttach` (`u₀²`, T3 banked) across recursion levels + the
threshold-shift bookkeeping (banked) — NOT by a bespoke 2-scale corner integral.

---

## 4. (c) traps + (d) DEAD / ruled-out routes

### Pitfalls that bite this endpoint
- **`t = 0` circularity** (§1): keep `1 ≤ t` live; never instantiate the peel/joint resolution at the
  whole-box `t = 0` pivot.
- **Do NOT close `sjJointResolution:803` directly.** It is superseded; the honest target is
  `DecoratedPeelStep`. Filling `:803` by any route other than the banked bridge re-imports the
  circularity risk and adds nothing the driver doesn't already give.
- **Do NOT build the corner as independent divisors.** Cert §1: `{u₀=0}`+`{u₁=0}` independently →
  `min(2,3/2)=3/2` UNDERSHOOT. The 7/2 needs the coupling — here via successive `radialAttach` peels +
  charge-shift, or (single-shot) via `corankBlock_morsePeel_lt_top`'s joint atom. State the loss as one
  degree-2 form on the JOINT block, not a product of divisors.
- **`c' = pq/2` borderline** (log divergence) must be EXCLUDED by strict `c' < ½·minAdm` — an
  over-clean regime statement will hide the borderline hole. (`genm-decrecon` flagged this as the most
  likely place a hole hides.)
- **Subordination is NON-strict** (`sjSubordination` docstring, `RouteMSJResolution.lean:339`): strict
  slack is FALSE at some binding cuts (e.g. `M=(1,1,1)`), so the peel must pick a gentle (minimal-`a`)
  cut, not the arbitrary `sjChargeBudget_binding` minimiser.
- **`SJState`/`sjRunMin` are STUBS** (`:752/:761`): only the coarse `sjRunMin_antitone` dimensional
  shadow is proved; do not treat them as the matrix-valued `[E_J|D_J]` invariant.

### DEAD / ruled-out (do NOT re-explore)
- **The `∧²`-compound `σ_min(∧²P)=s₂s₃` tube (the cert's WHOLE POINT of redirect).** corank2-cert §4:
  pointwise domination forces `b ≥ c'−3/2 > 3/2`, integrability forces `b < 1` — NO overlap. The
  symmetric compound weight cannot close the asymmetric corank-2 rung. Building `∧²P` as an explicit
  `3×6` minor matrix is also pointless (Mathlib has `exteriorPower` algebra, no compound-matrix API).
- **The GOOD-BRANCH / endpoint polar route does NOT close the DEEP corank-2 rung.** The corner-block
  polar machinery — `corner_block_cube_lintegral_lt_top` (`RouteMSJRadialPolar.lean:257`, threshold
  `c'<n/2` for a single joint block of dim `n`), `corner_block_lintegral_le`
  (`RouteMSJCornerBound.lean:55`), `corner_block_lt_top_of_pos` (`RouteMSJSphereLB.lean:63`),
  `exists_pos_lower_bound_on_sphere` (`RouteMSJCornerGate.lean:38`) — is BANKED and is the natural home
  of a "single joint radius over ℝ^{codim}" reading (which numerically also gives 7/2 at `n=7`). BUT
  `genm-decrecon` Q4 establishes it closes ONLY the dimensionally-cooperative branch (needs `W`, `A₂`
  both right-invertible — impossible when `M₁−t > M₂` or `M₂ > M_last`). The cert's `cell₂`
  (rank(P)≤1, the 3×4 tail near rank≤1) IS the rank-deficient DEEP branch, so this route is a trap
  here; the decorated recursion (T4) is what handles it. (Reuse these lemmas only for the good branch.)
- **Box-Morse / real-tube route — RETIRED** (needs GMT/Łojasiewicz tube bounds absent from Mathlib
  v4.29). **Naive-fibre route** (bound pivot chart by full box) — caps at `c'<M₀/2`, loses threshold in
  417 of the L=3..5 width-≤4 chains. **det(Q_bQ_bᵀ) Gram FIELD as a decoration weight — the "atom
  trap"** (a scalar weight can't express `minᵢ` over support). **Bare-inequality contract** (`gammaPeel
  ≤ ∑Cᵢ·boxIntegral(M'ᵢ)`) — CIRCULAR. (All from `genm-decrecon` Q5 + `lessons.md`; the decoration's
  shared-divisor absorption is the way past the `hIH`-as-black-box saturation obstruction.)

---

## Reflection (self-recon)

- **Most likely to advance the expedition:** re-scoping the build to `DecoratedPeelStep` (not
  `sjJointResolution:803`). With Tile 0 (the conditional driver) now landed by `genm-decbuild`, a crisp
  "prove this one `Prop`" tide is well-posed, and every supporting piece — corner atom, terminal,
  radial peel, charge bookkeeping, Schur-split/shear — is banked and named above.
- **Most likely to break:** T4 (block-split regime A/B), specifically producing the FreedPeel interface
  hypotheses (`hG`/`hpiv`/`hs`) through the resolution a.e. in `A'`, and the `c'=pq/2` borderline. This
  is the ~65–75% genuinely-new content every prior pass flags; an over-clean regime statement is where a
  hole will hide.
- **Next computation to clarify (pen-and-paper, before the build):** write ONE `DecoratedPeelStep` on
  the smallest genuine 3-layer bottleneck (`(3,3,4)` or `(1,2,2)`, where `minAdm > M₀`), tracking the
  decoration `(d, jac, carrier)` before/after and verifying the FreedPeel `hpiv`/`hG` are producible
  a.e. and the shifted threshold `carrierThreshold M − ½·peelCharge ≤ carrierThreshold(redChain u M)`
  holds — i.e. that the banked corner atom's hypotheses are exactly what the resolution can supply. If
  that closes on the instance, T4's statement is well-posed and the corner endpoint is reachable via
  banked pieces.
