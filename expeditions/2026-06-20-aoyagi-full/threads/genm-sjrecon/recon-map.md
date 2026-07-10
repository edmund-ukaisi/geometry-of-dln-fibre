# RECON-MAP — the NATIVE `(S,J)` rank-flag resolution build (self-recon, Stage 2 PIVOT)

**Seat:** self-recon (internal reconnaissance, read-only, NO Lean edits). **Target build:** close the
sole open leaf `sjJointResolution` (`RouteMSJResolution.lean:803`) via Aoyagi §5's **native `(S,J)`
simultaneous rank-flag resolution** (iterated blow-up → normal-crossing/monomial form, the `diag(b)`
ledger threading the rank-flag state) — **NOT** the front-peel `normalSlice_transfer` corollary.
**Verified against the LIVE tree** (current branch `genm-inj-injon` working dir) + banked branches
(`origin/genm-threadedshear`, `origin/genm-fpcarrier`, `origin/genm-seambuild`), not just the log.

---

## HEADLINE (fold into the build spec)

**The direct target is `sjJointResolution M hIH t ρ κ … : gammaPeelIntegral M t ρ κ c' < ⊤`
(`:797`/sorry at `:803`).** The whole spine ABOVE it is CLOSED and reusable verbatim: the arity
strong-induction wrapper `routeMBoxThresholdFinite_of_step` (`:863`), the CLOSED cover-inequality
`sjBoundaryPeel` (`:688`, NOT a sorry — the module header prose at `:69` is STALE), the `L=1` Morse
base `sjBase1_freeMatrix` (`:912`), and all of piece-6 charge combinatorics. The native route resolves
the per-`(t,ρ,κ)`-chart integral `gammaPeelIntegral` (`:517`) by blowing up the rank flag of the tail
product `P = prod (tailChain M) A'` SIMULTANEOUSLY, terminating at a monomial normal-crossing chart
whose leaf integral is the **banked terminal endpoint**. The **`diag(b)` ledger is already built on
the current branch** as the `RouteMSJLedger`/`RouteMSJLinGen` monomial-generator carrier (the
`SJSupport` shared-divisor support map + generator radial/rowMix step algebra + the terminal
finiteness endpoint). The **rank-flag transfer facts** (`blockShear_step`,
`rank_eq_q_add_of_normalForm`, det-1 unit clears) are STAGED clean-three on `origin/genm-threadedshear`.
**The genuine GAP is the change-of-variables / resolution MAP** (matrix box `∫frobSq(A₀·Q)^{−c'}` →
ledger `∫(∑bᵢ²)^{−c'}·Jac` over exceptional coords, finite chart cover, per-chart lintegral transport)
+ the `(S,J)` recursion assembling the generator step down the profile + discharging the row-mix
side-condition `hsh` at real step matrices — LinGen's own header scopes the CoV alone at **~65–75%
genuinely-new** construction. The banked machinery gets the ENDPOINTS + the per-step ALGEBRA + the
rank-flag TRANSFER facts (~30–40%); the CoV + recursion + assembly is the mountain.

---

## ⚠ CONTRADICTIONS / STALE-FLAGS (verify-against-live-tree catches)

1. **`sjBoundaryPeel` is CLOSED, not a sorry.** The `RouteMSJResolution.lean` MODULE HEADER (`:58`,
   `:69`) still calls it "the named sorry — the cover+shear measure-plumbing WALL", but the theorem at
   `:688–744` is a FULL proof (closed 2026-07-07, `genm-sjbpeel`). The **sole genuine sorry in the
   entire 25-file `RouteMSJ*` family is `sjJointResolution:803`** (every other "sorry" hit is docstring
   prose "the single named sorry, UNTOUCHED"). Spec against ONE open leaf.

2. **The `sjJointResolution` docstring (`:777–796`) describes a DEAD route.** It prescribes the Gram
   change of variables `Γ ↦ Γ·Q_b` + the isotropic corank atom `matBox_corank_residual_le`
   (`origin/genm-sjpeel-blow`). That is exactly the DECORATED/Γ-atom route the log refuted (cert §d;
   `RouteMSJFreedPeel` header: the three interface hyps FAIL pointwise on rank-deficient `Q_b`; kernel
   dim `a(b−s)` carries no decay). It even self-flags "The standing L≥3 wall (750/5440 charts …)".
   **The docstring should be REWRITTEN to the native `(S,J)` route** when the tide starts — do not
   follow it.

3. **The prior recon-map's HEADLINE recommendation (front-peel W1) is now REFUTED.** The
   `genm-sjcarrier-recon/recon-map.md` recommended wiring W1 = the front-peel `A₀↦A₀·U` carrier. The
   `genm-covdesign/cert.md` §COUPLED-PIVOT-RESOLUTION (3 decorrelated passes) then proved the
   per-corank front-peel CANNOT reach the deeper rank strata `{rank P = q−1}` (the one-corank
   whole-space Morse peel over-charges every deeper stratum; the bound DIVERGES in ~48–85% of `(M,q)`).
   **This recon is the pivot AWAY from that recommendation to the native `(S,J)` flag resolution.**

4. **`RouteMSchur.lean:429` (`routeMCore_threshold_lt_top`) is OFF-path.** The `_sjResolution`
   docstring says closing the leaf "discharges the bare sorry `routeMCore_threshold_lt_top`", but the
   headline consumes `RouteMBoxThresholdFinite` DIRECTLY as `_gen`'s `hbox`; `RouteMSchur:429` is DEAD
   alt-route (critpathmap). Do not spend on it.

---

## THE CRITICAL PATH (crisp — the leaf's exact contract)

- **Open leaf:** `sjJointResolution` (`RouteMSJResolution.lean:797`, sorry `:803`):
  ```
  theorem sjJointResolution (M : Fin (L + 1 + 1 + 1) → ℕ)
      (hIH : ∀ M' : Fin (L + 1 + 1) → ℕ, RouteMBoxThresholdFinite M')
      (t : ℕ) (ρ : Fin t ↪ Fin (M 0)) (κ : Fin t ↪ Fin (M 1))
      (ht : 1 ≤ t) (ht2 : t ≤ min (M 0) (M 1)) (c' : NNReal)
      (hc' : (c' : ℝ) < (minAdm M : ℝ) / 2) :
      gammaPeelIntegral M t ρ κ (c' : ℝ) < ⊤
  ```
- **The integrand it must bound finite** (`gammaPeelIntegral`, `:517`):
  ```
  ∫⁻ A' in paramsBoxM (tailChain M) 1,
    ∫⁻ A0 in matBox (M 0) (M 1) 1 ∩ pivotChart ρ κ,
      ENNReal.ofReal ((frobSq (rmatMul A0 (prod (tailChain M) A'))) ^ (-c'))
  ```
  On the chart the `t×t` `(ρ,κ)`-minor of `A₀` is a UNIT; `A'` ranges over the FULL tail box, so the
  singularity is driven by `P = prod (tailChain M) A'` rank-degenerating. The native resolution blows
  up the rank flag of `P` (and the coupled `A₀·P`) simultaneously.
- **Consumer chain (all sorry-free above the leaf):** `sjResolutionStep_proof : SJStepHyp` (`:849`,
  composes `sjBoundaryPeel` + `sjJointResolution`) → `routeMBoxThresholdFinite_of_step` (`:863`) →
  `routeMBoxThresholdFinite_sjResolution` (`:950`) → `aoyagi_learning_coefficient_gen`'s `hbox` →
  mint the unsuffixed `aoyagi_learning_coefficient` (task #108/#111).
- **CARRIER SHAPE (standing decision UPDATE-668, binding):** keep `sjJointResolution` a **PLAIN
  `gammaPeelIntegral < ⊤` contract**; the `SJState`/`SJSupport` ledger is an INTERNAL invariant, NEVER
  statement decoration. The native construction proves the plain goal directly.
- **THE hIH QUESTION (controller decision).** The leaf hands an **arity** IH
  (`∀ M' : Fin (L+1+1) → ℕ, RouteMBoxThresholdFinite M'` — all one-shorter-arity chains). The native
  `(S,J)` resolution terminates over the **rank FLAG / `(S,J)` profile** (the `remaining` measure), not
  chain arity — a direct blow-up chart-tree with monomial leaves may use the arity-`hIH` only at the
  reduced-tail leaves (or not at all). Decide up front whether the native route (a) consumes `hIH` at
  its leaves, or (b) is self-contained via the `(S,J)` termination kernel + the banked terminal, in
  which case `hIH` becomes an unused hypothesis (kept for signature-compatibility, as
  `sjJointResolution_frontPeel` already does with its `_hIH`). Cert §CRUX-PROOF's "total-width
  induction" is the alternative if a chain-IH is genuinely needed.

---

## (a) CONSUME — banked, PROVEN on the CURRENT branch, CALL it (exact `file:line`)

### The spine + base + cover (RouteMSJResolution.lean — all CLOSED except the one leaf)
- `routeMBoxThresholdFinite_of_step (hstep : SJStepHyp) (hbase1 : SJBaseHyp) : ∀ {L} M, …` — `:863`.
  Axiom-clean arity strong-induction WRAPPER. Reuse verbatim.
- `sjBoundaryPeel M c' hc' : routeMLayerBoxIntegral M c' 1 ≤ ∑_{t∈Icc 1 (min M₀ M₁)} ∑_{ρ,κ}
  gammaPeelIntegral M t ρ κ c'` — `:688`, **CLOSED** (pure cover inequality; `min=0` edge via
  `minAdm_cons_zero`).
- `sjResolutionStep_proof : SJStepHyp` — `:849` (composes peel + leaf; inherits the one sorry).
- `sjBase1_freeMatrix : SJBaseHyp` — `:912`, **CLOSED** (`L=1` Morse base, `morseBox_sumSq_lt_top:900`,
  `frobSq_prod_eq_flatSum:881`). `routeMBoxThresholdFinite_base0` — `:834` (`L=0` vacuous).
- `sjPivotSchurChart_rrp (r p) : RouteMBoxThresholdFinite ![r,r,p]` — `:815` (piece 2, `L=2` witness).

### Front-split plumbing (the OUTER reduction, CLOSED clean-three — reuse for the CoV setup)
- `routeMLayerBoxIntegral_front_split M c'` — `:461` (box integral = tail-outer front-factor fibre
  integral of `frobSq(A₀·prod(tailChain M)A')^{−c'}`). `eFront:371`, `measurePreserving_eFront:377`,
  `eFront_preimage_box:402`, `frobSq_prod_front:418`, `continuous_frontLoss:431`,
  `measurable_frontIntegrand:449`.
- Pivot-chart covers: `pivotChartCover_lintegral_le_sum:532`, `pivotChartCover_matBox_le_sum:552`,
  `frontBox_pivotCover_le:588` (includes the `{rank=0}={0}` null-point handling).

### Charge combinatorics (piece 6, all CLOSED sorry-free)
- `sjChargeBudget_recursion:196` (`= LayerSplit_value_eq_minAdm`), `_le:203`, `_binding:210`.
- `sjSubordination:339` (binding cut `a=(M₀−t)(M₁−t) ≤ minAdm(tailChain M)`),
  `minAdm_le_minAdm_tailChain:319`, `minAdm_leadWidth_mono:287`, `minAdm_le_minAdm_redChain_min:222`.
- `sjChargeUpdate_accum:353` (`= Mval_decompose`, the ADDITIVE charge — the accounting the ledger
  threads), `minAdm_cons_eq:254`, `minAdm_cons_zero:266`, `minAdm_two_eq:232`, `redChain_cons:242`,
  `tailChain:172`, `peelExp:191`.
- **On the current branch too** (`RouteMFrontPeelCharge.lean`): `minAdm_eq_frontPeel:158`
  (`minAdm M = min_{q≤tailMin}[M₀q + minAdm(shifted)]`), `frontCharge_ge_minAdm:310`, `tailMin:106`.

### Piece-4 invariant STUBS (the `(S,J)` state — the native route refines these)
- `structure SJState (M) { S J runMin }` — `:752`. `sjRunMin M S := min{M^(s):s≤S}` — `:761`.
  `sjRunMin_antitone:771` (running-min corank monotone — the block-dimension shadow). **These are the
  charter's `(S,J)` state; the matrix-valued `[E_J|D_J]` carrier is the deferred mountain content.**

### The `diag(b)` LEDGER — the monomial normal-form carrier (RouteMSJLedger.lean, S2-free clean-three)
**This IS the charter's `diag(b)` ledger. Highest-value banked (S,J) asset.**
- `SJSupport ι d := ι → Fin d → ℕ` (shared-divisor support map: order to which divisor `u_ℓ` divides
  generator `bᵢ`). `sharedDivisorExp e ℓ := ⨅ᵢ e(i,ℓ)` — `:87`; `genMonomial:91`, `sjLoss:102`,
  `residualSupport:98`.
- `sjLoss_factor:141` (common monomial factors out exactly). **`sjLoss_terminal_integrand:171`** (the
  terminal integrand EQUALS the banked `monomialIntegrand d (sharedDivisorExp e) h c' · |unit|^{−c'}`).
  **`sjLoss_terminal_lintegral_lt_top:234`** (terminal loss integrand `< ⊤` below the monomial
  threshold given a dehomogenised generator) — **the finiteness ENDPOINT the whole recursion lands on.**
- Case-2 radial ledger step: `prependColumn:280`, `sjLoss_prependColumn_one:324`
  (a fresh fully-shared divisor `u₀` multiplies loss by `u₀²`, sharing recorded).

### The generator-STEP algebra (RouteMSJLinGen.lean — the non-terminal carrier, S2-free)
- `structure SJLinGenState ζ ν ι d { supp coeff }` — `:100` (generator = monomial prefix × linear
  residual in active vars). `ofMatrix:138`, **`loss_ofMatrix_product:166`** (the ENTRY point:
  `frobSq(rmatMul A₀ Q)` IS the carrier loss of the fresh state at active var `x=A₀` — connects
  `gammaPeelIntegral`'s integrand to the ledger).
- **`radialStep:176` / `loss_radialStep:192`** (Case-2 single radial: prepend fresh shared divisor →
  loss ×`u₀²`, sharing recorded — the generator-level `corankStep`).
- **`gen_rowMix:232`** (block-elimination: generators linearly mixed by `R`, CONDITIONAL on the
  support-homogeneity side-condition `hsh`), `gen_rowMix_const:251` (discharges `hsh` UNCONDITIONALLY
  at a fresh common-support block — the post-radial state), `loss_blockSplit:290` (additive split over
  a sum-type generator index — the SHAPE the corank decrement lands on).

### Rank-flag TRANSFER (threaded shear) — **STAGED off-branch, see (b); the RANK facts are sound.**

### Per-step ANALYTIC bricks (current branch — the radial/corank/monomial machinery)
- Terminal endpoint: **`terminal_monomial_mul_unit_lintegral_lt_top` (`RouteMSJTerminal.lean:160`)** —
  consumes the bounded-below cores as its `hunit` hyp (`0<a≤|unit|` a.e.). `frobSq_terminal_radial:111`,
  `frobSq_terminal_radial_prefactor:121`, `monomialIntegrand_nonneg:148`.
- Monomial lower/integrability (`RouteMSJMonomialLower.lean`): `monomialIntegrand_integrableOn_of_lt_axisRatio:260`,
  `iInf_axisRatio_le_monomialThreshold:276`, `prod_rpow_lintegral_Ioo_box_lt_top:87`,
  `monomialIntegrand_lintegral_unitBox_lt_top:215`.
- Radial residual peel (`RadialResidualPower.lean`): `radial_morse_residual_power_le:157`
  (`c'↦c'−½(m+1)` exponent shift), `integral_core_ball_le:137`, `Cresid:39`/`Cresid_nonneg:56`.
  Pure-Morse: `sumSqND_box_lt_top` (`S1RadialMorse.lean:67`), `radial_morse_dominates_lt_top:127`;
  additive-core `radial_morse_dominates_absZ_lt_top` (`RouteMSchurDepth2.lean:156`).
- Corank atoms (`RouteMSJCorank*`): `corankStep:88`/`corankStep_prefactor:105`/`corankStep_sequential:118`
  + `frobSq_smul_mul:68` (`RouteMSJCorankStep`, the `u²` radial factor, Z-agnostic);
  `matBox_corank_residual_le:114`/`_fullSpace_eq:162` + `eMatFlat:59`/`frobSq_eq_flatSum:80`
  (`RouteMSJCorankResidual`); `corankBlock_morsePeel_lt_top:114` (`RouteMSJCorankPeel`);
  `matBox_corank_dominates_absZ_lt_top:87`/`matBox_corank_residual_absZ_le:130` (`RouteMSJCorankPure`).
- Corner/sphere blow-up: `lintegral_eq_polar:82`/`lintegral_eq_sphereProd:47` (`RouteMSJSphereBlowup`).
- Additive `frobSq` splits: `frobSq_col_split:69`/`frobSq_blockDiag_split:164`/`step3_blockFactor:117`
  (`RouteMSJStep3`); `frobSq_row_split:45`/`frobSq_schur_block_split:107`/`frobSq_schur_toBlocks_split:121`/
  `topRows_eq_mul_QtildeP:77`/`botRows_eq_cross:88` (`RouteMSJChartAlgebra`, the EXACT `L=2` block split).

### Chart CoV / measure-preservation (current branch)
- `pivotLocus_eq_iUnion:307`, `pivotChart:300`, `measurePreserving_shearSub:337`, `schur_cov:100`,
  `det_fromBlocks_cov:132`, `isUnit_submatrix_le_rank:289`, `exists_nonsingular_submatrix_of_le_rank:266`,
  `rank_submatrix_le':221` (`RouteMSJPivotChart`).
- `matReindexEquiv:146`/`measurePreserving_matReindexEquiv:164`, `frobSq_rmatMul_reindex:71`,
  `chartInner_blockReindex_eq_of_emb:256` (`RouteMSJBlockReindex`).
- `blockSplitD:86`/`measurePreserving_blockSplitD:94`, `schurShift:139`, `chartInner_schurShearFree_eq:253`
  (`RouteMSJChartShear`); `frobSq_schur_split_inv:83`, `chartInner_schurSplit_eq:128`,
  `chartInner_schurWeld_eq_of_emb:149` (`RouteMSJChartWeld`).
- `gammaAtom_aniso_shifted_eq:142`, `frobSq_mul_orthonormal_add:106`, `lintegral_comp_rightMulₚ:74`,
  `det_rightMulₚ:54` (`RouteMSJGammaAtom`); `exists_gram_normalizer:26` (`RouteMSJGramSqrt`).

### NEAR-MISS wiring
- `sjJointResolution_of_boxThresholdFinite (RouteMSJJointReduce.lean:68)` — closes the leaf GIVEN
  `RouteMBoxThresholdFinite M` of the SAME chain. Usable ONLY if box-finiteness is proven by an
  INDEPENDENT recursion (wiring W1); **circular through the spine** (the header flags it). The native
  route proves the leaf DIRECTLY, so this is not its closer. `gammaPeelIntegral_le_boxIntegral:55`
  (monotonicity, sorry-free).

---

## (b) STAGED — designed for exactly this point (off-branch; prevents re-derivation)

- **`RouteMSJThreadedShear.lean` (`origin/genm-threadedshear`, also on `origin/genm-cruxfinish`) —
  the DET-1 UNIT CLEARS + RANK-FLAG TRANSFER, clean-three, S2-free.** These carry over into the native
  route UNCHANGED (they are the charter's "det-1 unit clears" and the rank-flag ledger step):
  - `blockShear_step:105` — the per-factor threaded block-shear identity
    `[[1,0],[−K,1]]·[[A,B],[C,D]]·[[1,0],[Kp,1]] = [[α,B],[0,Y]]`, unit-triangular (det 1), `α=A+B·Kp`,
    `Y=D−(C+D·Kp)·⅟α·B`. The `Kp` threading is LOAD-BEARING (naive `Kp=0` independent-Schur is FALSE
    for `L≥3`). **The compass holds — `α⁻¹` appears only as a unit coefficient, no det-inverse.**
  - `rank_eq_q_add_of_normalForm:55` — `rank P = q + rank Z` under unit conjugation to block-upper form
    (built on `Core.rank_fromBlocks_invertible₁₁`, `SchurChartIff.lean:41`). `rank_eq_q_iff_reduced_zero:73`
    (`rank P = q ↔ Z = 0` — the CoV image of the stratum `{rank P = q}`). **These RANK facts are sound
    and reusable** (distinct from the LOSS-disjoint-block claim, which is the refuted part — see (d)).
  - Imports only `Core.SchurChartIff` + `RouteMSJChartAlgebra` (both on current branch) — a clean
    cherry-pick / merge.

- **`RouteMFrontPeelCarrier.lean` (`origin/genm-fpcarrier`, `origin/genm-cruxfinish`) — PARTLY
  reusable; its endpoints carry over, its CRUX is refuted.**
  - REUSABLE, PROVED: `shiftedThreshold:88` (charge accounting `c'−M₀q/2 < ½·minAdm(shifted)`),
    `outerRankCover:122` (front-split box ≤ finite sum over tail-rank strata `q=0..tailMin`),
    `prod_tailChain_rank_le_tailMin:104`, **`morseCore_residual_lt_top:170`** (the additive
    "sum-not-min" endpoint: `(m+1)`-Morse block + nonneg core, finite above `(m+1)/2` given the shifted
    core integral — reuses `radial_morse_residual_power_le`). `frontStratumIntegral:74` (per-stratum
    contribution def).
  - **REFUTED, DO NOT REUSE:** `normalSlice_transfer:222` (SORRY) — the front-peel crux. Its docstring
    claims the loss splits as disjoint blocks `‖R‖²+‖Z‖²` after the threaded shear; cert §1 proves this
    is FALSE (the exact split is `‖R̃α‖²+‖R̃B+S̃Z‖²`, cleaning needs `det(α)^{−m₀}`), and §COUPLED
    proves the per-corank peel diverges at `{rank P=q−1}`. `frontPeelStep_proof:237`,
    `routeMBoxThresholdFinite_frontPeel:248`, `sjJointResolution_frontPeel:259` all rest on this sorry
    — **NOT the closer.**

- **`(S,J)` termination kernel** — `remaining_lt_of_support_ssubset` in `BlowupBranchProgress.lean`
  (`aoyagi-rlct` worktree; commits `e7fc4ed3`, `68c00f37`). **NOT integrated anywhere in the current
  tree** (grep = 0 hits). Reference-only; take through the re-derive-then-adopt protocol. Provides ONLY
  the well-foundedness measure `remaining := #source-labels − #introduced-labels` +
  `remaining_lt_of_support_ssubset` (strict support growth ⟹ strict `remaining` decrease). Flags a
  Case-2 printed-mismatch trap. **This is the `(S,J)` double-induction's termination** — needed IF the
  native route recurses over the flag rather than deferring to the arity-`hIH`. The `SJState`/`sjRunMin`
  stubs (`RouteMSJResolution:752/761`) are its on-branch skeleton.

- **`SJDecoration` carrier (RouteMSJDecorated* — current branch, S2-free BRICKS).** The
  `SJDecoration:89` / `SJLinGenState`-adjacent decorated carrier with chart MOVES: `radialAttach:242`
  + `radialAttach_decLoss:262` (radial blow-up move), `SJDecoration.rowMix:56` (`RouteMSJDecoratedRowMix`)
  + `rowMix_decLoss:100` (row-mix move), `radialAttachFactor_lt_top:65` (`RouteMSJDecoratedRadial`),
  measurability suite `continuous_genMonomial`/`measurable_integrand`/`lintegral_unitBox_succ_cons`
  (`RouteMSJDecoratedMeas:37/94/111`), charge `minAdm_le_peelCharge_add_redChain`/`exists_binding_cut`
  (`RouteMSJDecoratedCharge:52/79`). **The decorated PREDICATE `DecoratedBoxThresholdFinite` as an
  EXTERNAL statement shape is DEAD (UPDATE-668, see (d)), but these chart-move + measurability BRICKS
  stand and are the closest banked analog of the `(S,J)` resolution moves** — mine them for the CoV
  construction, keep the external contract PLAIN.

---

## (c) LESSONS / PITFALLS that bite THIS build

- **The det-inverse COMPASS (charter + `lessons.md`).** Every refuted route grew a determinant inverse
  in a Jacobian (Gram `det(Q_bQ_bᵀ)^{−p/2}`; seam `det(A)^{−M₂}`; the front-peel loss-clean `det(α)^{−m₀}`,
  cert §1). The native `(S,J)` construction keeps every Jacobian a MONOMIAL in the exceptional divisors
  (radial blow-ups) times a det-1 unit clear (`blockShear_step`) — `α⁻¹` appears ONLY as a unit
  coefficient. **If a step grows a det-inverse, re-express (radial + unit clear + rename); the native
  form has always existed.** Reduction-to-germs must check SATISFIABILITY, not just faithful implication
  (the `Γ↦Γ·Q_b` atom was a faithful-but-dead reduction caught only at build time).
- **The FRONT-PEEL dead-end is a METHOD failure, not a wall (cert §COUPLED-PIVOT-RESOLUTION, 3
  decorrelated).** The one-corank whole-space Morse peel over-charges every DEEPER stratum: near
  `{rank P=q−1}` the loss behaves like a corank-`(q−1)` singularity, so a single-corank charge `m₀q`
  diverges (bound `∫|det B|^{−θ}`, `θ≥1` in 85% of `(M,q)`). The singularity is stratified along the
  ENTIRE rank flag; you MUST resolve `{rank≤q}⊃{rank≤q−1}⊃…` SIMULTANEOUSLY (the native iterated
  blow-up), not peel one corank then hand an undecorated reduced-chain IH. Truth is guaranteed
  (`J ≤ ∫_{full box}` = Aoyagi-finite) — this is why it is a re-selection, not an escalation.
- **"Sum, not min" — the corner is where codims ADD (vslice §5, Codex-corrected).** The local model is
  `G ≃ u₀²U₀ + u₁²U₁` (a SUM of radial terms), NOT a product `(u₀u₁)²` and NOT a boundary-wise `min`.
  Blow up the COMMON CORNER (`u₁=u₀τ`), accumulating Jacobian powers additively (`3+2+1=6` on `(3,3,3,4)`),
  to the terminal power `Σqⱼ−1`, threshold `½·Σqⱼ = ½·minAdm`. **AVOID the product/min tools**
  (`fibre_lintegral_mul_le` is exponent-PRESERVING → gives the boundary-wise `min`, the ×2 undershoot;
  `#70` dead route). The banked SUM/additive machinery is `sumSqND_box_lt_top`,
  `radial_morse_dominates_lt_top`, `radial_morse_residual_power_le`, `lintegral_eq_polar`,
  `morseCore_residual_lt_top`.
- **`frobSq` is TOO COARSE to recover the support matrix through block elimination (LinGen/Ledger
  headers, decorrelated Codex).** A sum-of-squares equality does NOT certify WHICH generators share a
  divisor. Shared-divisor faithfulness must be tracked **generator-by-generator** (the `SJSupport`
  ledger), not via `corankStep_prefactor`-style frobSq identities. This is precisely why the ledger
  carrier exists — the row-mix side-condition `hsh` (LinGen `gen_rowMix:232`) is the discipline that
  keeps the sharing faithful under block elimination; discharging `hsh` at REAL step matrices is the
  gap (it FAILS for arbitrary `R`; holds at fresh common-support blocks via `gen_rowMix_const`).
- **Opaque-width matrix-apply casts (`lean/CLAUDE.md`).** `fun_prop` FAILS on abstract `Matrix.mul`
  over `Fin (M k)`; `Matrix m n ℝ` has no norm. Work over the Pi form `Fin a → Fin b → ℝ` (`Params`
  shape); differentiate per-entry (`differentiableAt_pi`); sum-indexed intermediates `Fin t ⊕ Fin (M−t)`
  have NO norm → differentiate per-entry. Matrix-apply `simp` fires in isolation but "no progress"
  in-context at dependent widths → prove entries as `have` at explicit `⟨_,by decide⟩` indices, then
  `exact` (Fin proof-irrelevance unifies). The `Case111/Case222` unit-clear lift to OPAQUE widths is
  the un-banked residue of the block elimination (banked only for special widths).
- **Dependent-dimension reassociation (`lean/CLAUDE.md`).** `rw [mul_assoc]`/`simp`/`conv` won't match
  through dependent `HMul` — use fully-applied terms (`RouteMFrontPeel.mul_three_reassoc`) or
  `set X;set Y;exact Matrix.mul_assoc`; cast bookkeeping at the EQUIV level (`finCongr_refl` →
  `Matrix.reindex_refl_refl` via `erw`), never entrywise; peel `prod`/`prodAux` by prefix-length
  induction. `⅟`→`⁻¹` for integrand-usable identities via `invOf_eq_nonsing_inv` (bites `blockShear_step`
  which is stated with `⅟α`).
- **Binder-codepoint hazards:** combining-tilde `Q̃`, `φ` (U+03C6) are NOT valid identifiers — use ASCII
  (`Qt`, `phi`). **`0·∞=0` gotcha:** "∫ product finite ⟺ both finite" is FALSE over `ℝ≥0∞` (bites the
  corner-blow-up `u₀²·(U₀+τ²U₁)` accounting — record the positivity guard).
- **Build hygiene (`lean/CLAUDE.md`).** `scripts/lb <Module>` builds the import-closure only — MISSES
  name clashes; green-gate the FULL `lake build DLNFibre` before "integration-ready". Confirm
  sorry-free/axiom claims with force-recompiled `#print axioms` (AxCheck), never exit-0. `decide +kernel`,
  never `native_decide`. Single-writer on the carrier file; ≤2 concurrent heavy build-tides.
- **Bedrock/precision bar.** name = content (a `…_finite`/`…_resolution` result proves finiteness, not
  a codim proxy); the `rlct = ½·codim` reading rests on the CITED Aoyagi equality
  (`RlctInterface.cited_aoyagi_dln`) — the carrier proves box-finiteness / geometric codim, the
  Watanabe/Aoyagi equality stays Cited, caveat beside the claim.

---

## (d) DEAD / RULED-OUT — do not re-explore (one-line reason each)

- **Front-peel-to-`normalSlice_transfer` single-shot (`RouteMFrontPeelCarrier:222`).** DEAD as the
  CLOSER: the disjoint-block loss split `‖R‖²+‖Z‖²` is FALSE (cert §1); the per-corank peel diverges at
  `{rank P=q−1}` (cert §COUPLED, ~48–85% of `(M,q)`). Its PROVED endpoints (`shiftedThreshold`,
  `outerRankCover`, `morseCore_residual_lt_top`) are reusable (see (b)); the crux is not.
- **The Gram c.o.v. `Γ↦Γ·Q_b` / full-space `det(Q_bQ_bᵀ)^{−p/2}` atom (the DECORATED-peel route).**
  DEAD: shift `Γ↦Γ·Q_b` kernel dim `a(b−s)` carries no decay ⟹ achievable shift `a·s/2` not `ab/2`;
  full-space over-counts the null `{rank P=0}` locus → `∞`-Beta divergence on rank-deficient-`Q_b`
  strata (UPDATE-663/668/713, 3-decorrelated). `RouteMSJFreedPeel.lean` (`gammaPeelIntegral_schurShearFree_eq:78`,
  `freedSchurLoss_inner_peel_lt_top:114`) IS this route's machinery — its OWN header admits the three
  interface hyps FAIL pointwise. **The `sjJointResolution` docstring `:777–796` currently prescribes
  THIS route — ignore/rewrite it.**
- **`RouteMSJDecorated`'s `DecoratedBoxThresholdFinite` as the EXTERNAL statement shape.** Superseded
  by UPDATE-668 (plain contract, ledger internal). Its π=∅ bridge `decoratedBoxThresholdFinite_trivial_iff:217`
  + carrier scaffold are the decorated route's shell; the descent `decorated_peel_step` on it was the
  UNSOUND `ab`-shift. The measurability/chart-move BRICKS stand (banked, S2-free — mine them, see (b));
  the external contract stays PLAIN.
- **Exponent-preserving iterated-fibre front-peel (`#70`):** `prod_front_peel + fibre_lintegral_mul_le +
  SchurCore-at-leaves` is exponent-PRESERVING → no budget→exponent conversion → undershoots by ×2.
  Distinct from the (refuted-for-a-different-reason) `A₀↦A₀·U` front-peel.
- **The SEAM / det-Jacobian route (`#83`, UPDATE-771; `SeamGaugeAbsorption.lean` on
  `origin/genm-seambuild`).** GO/NO-GO = NO: the seam chart RELOCATES the coupled-det from
  `det(Q_bQ_bᵀ)` to the pivot `det(A)^{−M₂}`, does not remove it; still needs a per-pivot resolution
  chart-tree. `gaugeAbsorption:175` proves SURJECTIVITY, not TRANSVERSALITY (discuss-at-close #82/#83);
  it does NOT plug into the box-finiteness contract. `reference-notes-sj-kernel` names it as reusable —
  it is NOT for this build.
- **`RouteMSchur:429`, `RouteMRecursion:257`, `RouteMSchurGeneral:144`, `Skeleton` legacy D1 rungs, θ
  (`aoyagiTheta_eq`), `DeepestGaugeChart:357`.** All OFF the `_gen`/`hbox` critical path (critpathmap,
  import-verified). Do not chase.

---

## (e) GAP — the MISSING `(S,J)` content, precisely

**What is present (the two ends + the middle-step algebra):** the ENDPOINTS are banked (terminal
monomial finiteness `RouteMSJTerminal:160` + `RouteMSJLedger:234`; the radial/corank/sphere-blow-up
analytic bricks); the ENTRY is banked (`loss_ofMatrix_product` connects `gammaPeelIntegral`'s integrand
to the ledger); the per-STEP generator algebra is banked (`radialStep`, `rowMix`, `loss_blockSplit`);
the rank-flag TRANSFER facts are STAGED (`blockShear_step`, `rank_eq_q_add_of_normalForm`); the CHARGE
accounting is banked (piece 6 + `minAdm_eq_frontPeel`); the TERMINATION measure is reference-only
(`remaining_lt_of_support_ssubset`). **This gets ~30–40% of the way.**

**What is MISSING — the simultaneous rank-flag resolution carrying the pivot + radial charges across
the whole flag (the mountain):**

1. **THE CoV / RESOLUTION MAP (the heart, ~65–75% new — LinGen header, decorrelated Codex).** The
   explicit iterated blow-up chart maps transporting the matrix-box integral
   `∫⁻_{matBox∩pivotChart × tailBox} frobSq(A₀·Q)^{−c'}` to the ledger's exceptional-coordinate integral
   `∫⁻ (∑bᵢ²)^{−c'}·Jac` — each chart map measure-preserving up to a MONOMIAL Jacobian, a FINITE chart
   cover of the flag, per-chart `lintegral` transport. No pointwise brick shortcuts this. This is where
   Aoyagi §5's construction is unavoidable and must be built (it is a BOUNDED build — Aoyagi carries it
   out explicitly for DLN — but genuinely new in Lean). Shape: a recursion of `(radial blow-up →
   det-1 unit clear via `blockShear_step` → absorption-by-renaming into the next factor)` indexed by
   the rank flag, each level measure-preserving.

2. **THE `(S,J)` RECURSION down the profile.** Iterating the generator step (`radialStep` + the
   block-elimination `rowMix`) from the top of the flag to the terminal monomial chart, threading the
   `SJSupport` ledger (the `diag(b)` state) so the accumulated pivot + radial charges compose ADDITIVELY
   to `minAdm M` (piece-6 `sjChargeUpdate_accum`/`sjSubordination` supply the ℕ accounting; the analytic
   composition is new). Terminates via the `(S,J)` kernel `remaining_lt_of_support_ssubset` (bring in
   through re-derive-then-adopt) or a total-width measure.

3. **DISCHARGE the row-mix side-condition `hsh` at REAL step matrices.** `gen_rowMix:232` is CONDITIONAL
   on support-homogeneity; `gen_rowMix_const:251` discharges it only at fresh common-support blocks.
   Proving the ACTUAL `(S,J)` block-elimination step satisfies `hsh` (the block-elimination faithfulness
   — that each new generator combines only old generators sharing its target support) is genuine content
   (LinGen: fails for arbitrary `R`).

4. **THE OPAQUE-WIDTH LIFT of the unit clear (`Case111/Case222`).** The `Z`-independent det-1 unit
   block-elimination is banked only at special widths; the general-widths lift is a NEW brick (the
   opaque-width-cast discipline in (c) applies). `blockShear_step` supplies the identity; its
   measure-preservation at opaque widths + the reindex plumbing is the residue.

5. **THE BOUNDED-BELOW CORES (CRUX A, feeding the terminal `hunit`).** The terminal endpoint
   `terminal_monomial_mul_unit_lintegral_lt_top:160` consumes `0<a≤|unit u|` a.e. on the box; the
   carrier must SUPPLY it for the resolved cores. Banked supply-TECHNIQUE (nonzero-poly witness ⟹ `0<U`
   a.e.: `Uval4422_ae_pos`, `achieverUfun_ae_pos`, `cleanUfun_ae_pos` — all clean-three); residual =
   the UNIFORM `a≤|U|` (continuity+compactness positive-min, OR route the `A₂`-rank-drop locus as a
   deeper branch).

6. **THE ASSEMBLY into `gammaPeelIntegral M t ρ κ < ⊤`.** Composing 1–5 + the banked front-split cover
   to close `sjJointResolution:803` directly (plain contract; ledger internal). Whether the arity-`hIH`
   is consumed (at reduced-tail leaves) or unused (self-contained via the `(S,J)` kernel + terminal) is
   the controller decision flagged in THE CRITICAL PATH.

**Rough size:** multi-tide mountain. Item 1 (the CoV) is the dominant genuinely-new bulk; items 2–4 are
substantial but Aoyagi-guided; items 5–6 are bounded reuse. The banked ~30–40% is real bedrock (endpoints,
step algebra, rank transfer, charge) — it is the SCAFFOLDING and the LEAVES; the missing content is the
TREE (the resolution map + recursion + faithfulness) that connects them.

---

## Reflection (self-recon close)

- **What to reuse:** the whole CLOSED spine (`_of_step`/`sjBoundaryPeel`/`sjBase1`) + piece-6 charge +
  the front-split plumbing verbatim; the `RouteMSJLedger`/`RouteMSJLinGen` monomial ledger as the
  `diag(b)` carrier (on current branch); the terminal + radial/corank/sphere endpoints; and cherry-pick
  `RouteMSJThreadedShear` (clean-three, S2-free rank-flag transfer + det-1 unit clear).
- **What to avoid:** the `sjJointResolution` docstring's Gram route (rewrite it); the front-peel
  `normalSlice_transfer` crux (keep only its proved endpoints); the decorated EXTERNAL predicate; the
  seam route.
- **What's staged:** `blockShear_step` + `rank_eq_q_add_of_normalForm` (the unit clear + rank transfer);
  `morseCore_residual_lt_top` + `outerRankCover` + `shiftedThreshold` (the additive endpoints); the
  `(S,J)` termination kernel (reference-only, re-derive-then-adopt).
- **Most likely to advance:** an EARLY VERTICAL SLICE of the CoV on the `(3,3,3,4)` corank-2 binding
  chart (task #104's cert, now in Lean) — radial blow-up → `blockShear_step` unit clear → ledger step →
  terminal, on ONE flag branch — to shake out the resolution-map shape before the width-general grind.
- **Most likely to break:** item 1 (the CoV / resolution map) at opaque widths, and item 3 (`hsh`
  faithfulness at real step matrices) — the two decorrelated-Codex-flagged genuinely-new pieces.
- **Next computation that clarifies:** confirm on the vertical slice whether the native construction
  needs the arity-`hIH` at all, or terminates self-contained via the `(S,J)` kernel + banked terminal —
  this decides whether the leaf statement is kept plain-with-unused-`hIH` or reshaped to a flag-recursion.
