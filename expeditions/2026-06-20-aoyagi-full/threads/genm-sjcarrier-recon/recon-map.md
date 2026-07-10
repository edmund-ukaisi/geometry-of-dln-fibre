# RECON-MAP — the `(□)`-discharge carrier build (self-recon, Stage 2)

**Seat:** self-recon (internal reconnaissance, read-only). **Target build:** discharge
`(□) = RouteMBoxThresholdFinite M` ∀ nondegenerate `M` (∀ `c' < ½·minAdm M`,
`routeMLayerBoxIntegral M c' 1 < ⊤`) via the native `(S,J)` rank-flag blow-up recursion.
**Verified against the LIVE tree** (branch `expedition/aoyagi-full`), not just the log.

---

## HEADLINE (fold into the build spec)

**Reuse the whole `RouteMSJ*` spine + charge combinatorics; the carrier's ONE real deliverable is
`RouteMBoxThresholdFinite M` ∀M, and closing it makes the two open sorries corollaries.** The
descent primitive is **NOT** the Γ-atom/decorated-peel (dead: IH-saturates / `ab`-vs-`a·s` unsound) —
it is the **FRONT-PEEL `A₀↦A₀·U`** (r1substratum §C: no Schur, no `Q_b`, charge `M₀·q`, banked corank
bricks directly), whose ℕ closure `minAdm_eq_frontPeel` is **already banked** (`RouteMFrontPeelCharge`,
AxCheck-gated). The single analytic crux is the **"sum-not-min" corner blow-up** (vslice codex: the
binding zero is at the corner `u₀=u₁=0`; per-boundary charges *add* on the terminal exceptional
divisor, reaching `½·minAdm` — looking at boundaries separately undershoots). The staged crux is
**`FrontPeelStep` + the normal-slice/`Σ⁰` transfer** (paper Thm `addlongest`), unverified-but-likely.
**Avoid:** the Gram c.o.v. `Γ↦Γ·Q_b` / full-space `det(Q_bQ_bᵀ)^{−p/2}` atom, the exponent-preserving
iterated-fibre front-peel (#70), the seam/det-Jacobian route (#83), and `RouteMSchur:429`/other legacy
alt-route sorries (all off-path).

---

## ⚠ CONTRADICTIONS / STALE-BRIEF FLAGS (verify-against-live-tree catches)

1. **The brief says the carrier "closes the named sorries `sjBoundaryPeel` + `sjJointResolution`."
   `sjBoundaryPeel` IS ALREADY CLOSED** (full proof, `RouteMSJResolution.lean:688–744`, landed by
   `genm-sjbpeel`). The **sole genuine sorry** in the entire `RouteMSJ*` family is
   **`sjJointResolution` (`RouteMSJResolution.lean:803`)**. Every other "sorry" hit across the 25
   `RouteMSJ*` files is docstring prose ("the single named sorry, UNTOUCHED"). The carrier build should
   be spec'd against **one** open leaf, not two.

2. **The descent primitive named in `reference-notes-sj-kernel.md` + the charter's "`diag(b)` ledger"
   language reflects the DECORATED/Γ-atom route, which the log SUPERSEDED.** Timeline on the live tree:
   `ab`-shift (Γ↦Γ·Q_b, `decorated_peel_step`) → **UNSOUND** (UPDATE-713/sjdescent: kernel dim
   `a(b−s)` carries no decay, achievable shift is `a·s/2` not `ab/2`) → `a·s` rank-corrected
   (UPDATE-715, sound but stratum-blind) → **FRONT-PEEL `A₀↦A₀·U`** (UPDATE-716/r1substratum, the
   current recommended primitive; supersedes the rank-split). The `RouteMSJDecorated`/`RouteMSJFreedPeel`
   machinery is a **superseded route**, not the carrier's spine (details in (d)).

3. **`RouteMSchur.lean:429` (`routeMCore_threshold_lt_top`, a bare sorry) is OFF the headline path.**
   `RouteMSJResolution.lean`'s docstring says closing the peel "discharges the bare sorry
   `routeMCore_threshold_lt_top`" — but the `genm-critpathmap` map (2026-07-08, verified) lists
   `RouteMSchur:429` under **DEAD (alt-route), NOT imported by `r1_resolution_general`/
   `routeMLayerCover_hfin`**. The headline consumes `RouteMBoxThresholdFinite` **directly** as the
   `hbox` hypothesis of `_gen`. Do not spend on `RouteMSchur:429`.

4. **The `genm-critpathmap` D1-gap warning (hstep2 / Skeleton:1131,1177 / "uncovered general-L ≥-leg")
   is STALE for Stage 2.** That map is 2026-07-08; the Stage-1 S2-free milestone (2026-07-09,
   discuss-at-close #85/#88) closed the general-L D1 legs and re-assembled the headline into
   `HeadlineGenAssembly.aoyagi_learning_coefficient_gen`, whose **only** analytic hypothesis is now
   `hbox` (verified below). The old Skeleton rungs (`Skeleton:1094/1140/1197`) are the legacy D1 route,
   superseded by `_gen`. **Stage 2 = discharge `(□)` alone.**

---

## THE CRITICAL PATH (crisp — the carrier's exact contract)

- **Deliverable:** `RouteMBoxThresholdFinite M` for all nondegenerate `M : Fin (L+1) → ℕ`
  (`def` at `RouteMBoxReduction.lean:165`: `∀ c':NNReal, (c':ℝ) < minAdm M/2 →
  routeMLayerBoxIntegral M c' 1 < ⊤`).
- **Consumer:** `aoyagi_learning_coefficient_gen` (`HeadlineGenAssembly.lean:55`) takes
  `hbox : RouteMBoxThresholdFinite (fun s => H s - r)` (line 59) as its **sole analytic hypothesis**
  (rest are structural: `hB.rank=r`, `hr`, `hL/hL2`, `hpos`). Discharge `(□)` → `_gen` unconditional →
  mint the unsuffixed `aoyagi_learning_coefficient` (task #108).
- **Sole open leaf that closes it through the existing spine:** `sjJointResolution`
  (`RouteMSJResolution.lean:803`), consumed by `routeMBoxThresholdFinite_sjResolution` (:950) via the
  sorry-free wrapper `routeMBoxThresholdFinite_of_step` (:863) + the closed `sjBoundaryPeel` (:688) +
  base `sjBase1_freeMatrix` (:912).
- **TWO clean ways to wire the carrier** (controller call):
  - **(W1) Direct:** the front-peel carrier proves `RouteMBoxThresholdFinite M` ∀M by its own
    strong induction; then close `sjJointResolution` as a **corollary** via the banked
    `sjJointResolution_of_boxThresholdFinite` (`RouteMSJJointReduce.lean:68`) so no sorry dangles.
    (This bypasses `sjBoundaryPeel`/`sjResolutionStep_proof` entirely; both remain sorry-free banked.)
  - **(W2) Through the spine:** prove `sjJointResolution` directly (per-`(t,ρ,κ)` chart finiteness),
    letting the closed `sjBoundaryPeel` + wrapper assemble `RouteMBoxThresholdFinite`. This is the
    `gammaPeelIntegral`-shaped contract the spine already expects.
  - **NOTE the circularity trap on (W2):** `sjJointResolution_of_boxThresholdFinite` reduces
    `sjJointResolution M` to `RouteMBoxThresholdFinite M` **of the same chain** — that is the induction
    goal, so it is only usable in (W1) where box-finiteness is proven by an independent recursion.
    Do not "close" `sjJointResolution` by calling it (circular; `RouteMSJJointReduce` header says so).

---

## (a) CONSUME — banked, proven, CALL it (exact `file:line` + signature)

### Spine + wrapper (RouteMSJResolution.lean) — all sorry-free except `sjJointResolution`
- `routeMBoxThresholdFinite_of_step (hstep : SJStepHyp) (hbase1 : SJBaseHyp) : ∀ {L} M,
  RouteMBoxThresholdFinite M` — `:863`. The **axiom-clean strong-induction WRAPPER** (arity induction;
  `L=0` vacuous via `routeMBoxThresholdFinite_base0:834`, `L=1` base, `L≥2` step). Carries no analytic
  content. **This is the recursion skeleton to reuse verbatim** if the carrier is `SJStepHyp`-shaped.
- `sjBoundaryPeel (M) (c':NNReal) (hc') : routeMLayerBoxIntegral M c' 1 ≤ ∑_{t∈Icc 1 (min M₀ M₁)}
  ∑_{ρ,κ} gammaPeelIntegral M t ρ κ c'` — `:688`, **CLOSED**. The pure cover inequality (front-split +
  `t=1` pivot cover; `min=0` edge via `minAdm_cons_zero`).
- `sjResolutionStep_proof : SJStepHyp` — `:849`, composes `sjBoundaryPeel` + `sjJointResolution`
  (finite sum of finite terms). Currently inherits the one sorry.
- `sjBase1_freeMatrix : SJBaseHyp` — `:912`, **CLOSED** (L=1 Morse base, `morseBox_sumSq_lt_top`).
- `routeMLayerBoxIntegral_front_split (M) (c') : routeMLayerBoxIntegral M c' 1 = ∫_{A'∈box(tailChain)}
  ∫_{A₀∈matBox} ofReal(frobSq(rmatMul A₀ (prod (tailChain M) A'))^{−c'})` — `:461`, **CLOSED**
  clean-three (MP front-split `eFront:371` + integrand identity `frobSq_prod_front:418`). The
  general-`L` peel of the leading layer `A₀`. **This is the outer half the front-peel carrier builds
  on** — it already reduces the box integral to `∫_{A'} ∫_{A₀} frobSq(A₀·(prod tail A'))^{−c'}`.
- `frontBox_pivotCover_le` `:588`, `pivotChartCover_matBox_le_sum` `:552`,
  `pivotChartCover_lintegral_le_sum` `:532` — CLOSED product-level pivot-chart covers (subadditivity
  over `Fin t ↪ Fin m/n`; `{rank=0}={0}` null point handled). Reusable for the rank-`q` stratification.
- `gammaPeelIntegral (M) (t) (ρ κ) (c')` — `:517`, the per-`(t,ρ,κ)` chart contribution
  `∫_{A'} ∫_{A₀∈matBox ∩ pivotChart ρ κ} frobSq(A₀·(prod tail A'))^{−c'}`. The object `sjJointResolution`
  proves `< ⊤`.

### Charge combinatorics (all CLOSED, sorry-free)
- **`minAdm_eq_frontPeel (M) : minAdm M = (range (tailMin M+1)).inf' (frontCharge M)`** —
  `RouteMFrontPeelCharge.lean:158`. **THE front-peel identity**
  `minAdm M = min_{q≤tailMin} [M₀·q + minAdm((M₁..M_L)−q)]`. Integrated + AxCheck-gated
  (`AxCheck.lean:588`). ≥3-width domain `Fin (L+1+1+1)`; FALSE at 2 widths.
- `frontCharge_ge_minAdm (M) (q) (hq: q ≤ tailMin M) : minAdm M ≤ frontCharge M q` — `:310`.
  Per-`q` charge lower bound (every stratum charges ≥ minAdm; equality at the binding `q`, often
  sub-generic). `frontCharge M q := M₀*q + minAdm (fun i => M i.succ - q)` (`:111`);
  `tailMin M` (`:106`).
- `twoVar_min_eq (a b r)` — `:43`, the reflection keystone turning the layer-peel min into the
  front-peel min. `tailMin_split` `:136`, `inf'_univ_sub_right` `:118`, `le_tailMin_iff` `:130`.
- Layer-peel budget (RouteMSJResolution): `sjChargeBudget_recursion` `:196`, `_le` `:203`,
  `_binding` `:210`, `sjSubordination` `:339`, `minAdm_le_minAdm_tailChain` `:319`,
  `minAdm_leadWidth_mono` `:287`, `minAdm_cons_eq` `:254`, `minAdm_cons_zero` `:266`,
  `minAdm_two_eq` `:232`, `redChain_cons` `:242`. `sjChargeUpdate_accum` `:353` (= `Mval_decompose`,
  additive charge). `peelExp` `:191`.

### The banked corank/Morse bricks the FrontPeelStep charges through (r1substratum §C "brick map")
- `matBox_corank_dominates_absZ_lt_top {p q} (hp hq) …` — `RouteMSJCorankPure.lean:87`. Regime B
  (`c' < pq/2` terminal, Morse dominance).
- `matBox_corank_residual_absZ_le {p q} (hp hq) …` — `RouteMSJCorankPure.lean:130`. Regime A
  (`c' > pq/2`, residual at shifted exponent). Pair = the two regimes at block dim `M₀·q`.
- `matBox_corank_residual_le (p q) (hp hq) (c')` — `RouteMSJCorankResidual.lean:114`; isotropic
  corank atom (`∫_{matBox} ofReal((frobSq D + w)^{−c'}) ≤ …`); `_fullSpace_eq` `:162`.
  `frobSq_eq_flatSum` `:80`, `eMatFlat`/`measurePreserving_eMatFlat` `:59/:69`.
- `corankBlock_morsePeel_lt_top` — `RouteMSJCorankPeel.lean:114` (+ `_eq` `:65`, `_setLE` `:88`).
- `SchurRecStep (p) (lam)` (`RouteMSchurGeneral.lean:100`) + `core_schurGen_lt_top`
  (`:115`) — the WellFounded-on-corank recursion wrapper (abstract step ⟹ `SchurCore` finiteness);
  API-pinned at `RouteMSJResolution.lean:966`.
- `pivotLocus_eq_iUnion (t) : {A | t ≤ A.rank} = ⋃_{ρ,κ} pivotChart ρ κ` — `RouteMSJPivotChart.lean:307`
  (rank-`q` stratification of the tail product). `pivotChart` `:300`, `measurePreserving_shearSub`
  `:337`, `isUnit_submatrix_le_rank` `:289`, `exists_nonsingular_submatrix_of_le_rank` `:266`,
  `rank_submatrix_le'` `:221`.
- `prod_front_peel` (peel `A₀`), `mul_three_reassoc` — `RouteMFrontPeel.lean` (the dependent-width
  `prodAux` reassociation cast kernel; see lean/CLAUDE.md dependent-dimension note).
- `SchurCore`/L2 fibre engine: `fibre_lintegral_mul_le` (`MatMulFibre`, API-pinned
  `RouteMSJResolution.lean:959`); base case `routeMBoxThresholdFinite_rrp` (`sjPivotSchurChart_rrp:815`).
- Monomial terminal endpoint: `sumSqND_box_lt_top` (API-pinned `:975`),
  `monomialIntegrand_integrable_of_lt` / `RouteMSJMonomialLower` family
  (`monomialIntegrand_integrableOn_of_lt_axisRatio` `:260`, `iInf_axisRatio_le_monomialThreshold`
  `:276`, `prod_rpow_lintegral_Ioo_box_lt_top` `:87`).
- Corner blow-up ("sum-not-min" crux): `RouteMSJSphereBlowup.lean` — `lintegral_eq_polar` `:82`,
  `lintegral_eq_sphereProd` `:47` (spherical/polar blow-up; NeZero N). `RouteMSJCorankStep.lean`
  `corankStep` `:88`, `corankStep_prefactor` `:105`, `corankStep_sequential` `:118` (the `u²` radial
  factor), `frobSq_smul_mul` `:68`.

### Measurability / topology plumbing (RouteMSJResolution + RouteMSJDecoratedMeas)
- `paramsBoxM_volume_lt_top` `:152`, `measurableSet_paramsBoxM` (`RouteMBoxReduction:99`),
  `measurable_frontIntegrand` `:449`, `continuous_frontLoss` `:431`, the `Params` Pi instances
  `:113–132` (SecondCountable/Borel/SigmaFinite/MeasureSpace). `sjLocalComparability` `:140`
  (the L¹ comparability heart). `RouteMSJDecoratedMeas` measurability suite (`continuous_genMonomial`,
  `measurable_integrand`, `lintegral_unitBox_succ_cons`).

### NEAR-MISSES (one hypothesis / one CoV from usable by the carrier)
- **`sjJointResolution_of_boxThresholdFinite` (`RouteMSJJointReduce.lean:68`)** — closes
  `sjJointResolution` GIVEN `RouteMBoxThresholdFinite M` of the same chain. Usable ONLY in wiring (W1)
  (box-finiteness proven independently); circular through the spine (W2). `gammaPeelIntegral_le_boxIntegral`
  `:55` (monotonicity bound, sorry-free).

---

## (b) STAGED — designed to be consumed HERE (highest-value; prevents re-derivation)

- **`RouteMFrontPeelCharge.lean` (whole file) — the ℕ combinatorial gate, BANKED.**
  `minAdm_eq_frontPeel` + `frontCharge_ge_minAdm` are exactly the accounting the analytic
  `FrontPeelStep` recursion consumes to hit `½·minAdm`. Landed by `genm-r1frontcharge` (the branch this
  session started on, `genm-r1frontcharge-wt`). Fidelity anchors in-file: `(3,3,3,4)` frontCharge over
  `q=0..3` is `8,7,7,9`, min `7 = minAdm`; `(4,4,2)` binds at sub-generic `q=1`.
- **The r1substratum §C `FrontPeelStep` shape (`threads/genm-r1substratum/cert.md:150–200`) — the
  Lean-ready primitive.** `structure FrontPeelStep (M₀ q) : Prop` with `shiftA` (regime A,
  `c > M₀q/2 → A₀-integral ≤ Cresid(M₀q)·∫ tailRankLocus^{−(c−M₀q/2)}`) and `termB` (regime B,
  `c < M₀q/2 → < ⊤`). Mechanism: on `{rank P = q}` write `P = U·V` (`U:M₁×q` full-col-rank spanning
  `im P`); `frobSq(A₀·P) = frobSq((A₀·U)·V)`; `A₀↦A₀·U` is a linear surjection onto `M₀×q`, kernel dim
  `M₀·(M₁−q)` → isotropic `M₀·q` Morse block + bounded kernel box → shift `M₀·q/2`, **no Schur, no
  `Q_b`**. Recurse on `{rank P ≤ q}` = shifted `Σ⁰` of `(M₁−q,…,M_L−q)` (normal-slice iso). Brick map
  in the cert matches (a) above. **The build should START from §C, not the reference-notes-sj-kernel.**
- **The vslice (3,3,3,4) math cert (`threads/genm-vslice/codex-answer.md`, task #104 COMPLETE) — the
  analytic-mechanism worked example.** Delivers the **"Sum, Not Min" crux**: on `(3,3,3,4)` the local
  model is `G ~ u₀²U₀ + u₁²U₁` with measure `|u₀|³|u₁|²`; boundaries separately give the misleading
  `4/2`, `3/2`; the binding zero is at the **corner** `u₀=u₁=0`; blow up the corner (`u₁=u₀τ`) →
  terminal Jacobian power `6`, loss order `2`, threshold `(6+1)/2 = 7/2 = ½·minAdm = 4+3+0`. Also
  confirms: Schur complements use pivot inverses only as UNIT coefficients (Jacobian 1 unipotent
  shears), **no unavoidable det-inverse**. General pattern: `q₀=(M₀−t₀)(M₁−t₀)`,
  `qⱼ=(t_{j−1}−tⱼ)(M_{j+1}−tⱼ)`; each `qⱼ>0` → radial blow-up, Jacobian power `qⱼ−1`; common-corner
  blow-up → terminal power `Σqⱼ−1`, threshold `½·Σqⱼ`. **This is the recursion's terminal-accounting
  contract, framing-independent** — the "sum-not-min" is the same fact as the front-peel's
  normal-slice/`Σ⁰` transfer composing charges additively.
- **`(S,J)` termination kernel (`reference-notes-sj-kernel.md`) — reference-only, take through the
  re-derive-then-adopt protocol.** In the `aoyagi-rlct` worktree
  (`.claude/worktrees/aoyagi-rlct/…/BlowupBranchProgress.lean`, commits `e7fc4ed3`/`68c00f37`), NOT an
  import. Provides ONLY the well-foundedness measure (`remaining := #source labels − #introduced`,
  `remaining_lt_of_support_ssubset`). **Likely UNNEEDED** if the carrier is `SJStepHyp`-shaped — the
  banked `routeMBoxThresholdFinite_of_step` (arity strong-induction) already supplies termination
  (arity strictly drops; `t≥1`/`q≥1` forces strict reduction). Adopt the kernel only if the recursion
  needs a finer (S,J) double-induction measure than arity. Flags a Case-2 printed-mismatch trap.
- **UPDATE-668 plain-contract decision (synthesis:687):** `sjJointResolution`/carrier stays a **PLAIN
  `RouteMBoxThresholdFinite`-shaped contract**; the `SJState`/ledger is an INTERNAL invariant, NEVER
  statement decoration. (This is why `RouteMSJDecorated`'s `DecoratedBoxThresholdFinite` predicate,
  though it has a clean `_trivial_iff` bridge, is NOT the mandated external shape — see (d).)
- **`RouteMSJChartAlgebra` Schur identities — STAGED but for the (W2)/native-Schur framing only.**
  `frobSq_schur_block_split` `:107` (exact `frobSq(A₀·Q) = ‖A·Q̃_p‖² + ‖C·Q̃_p + Γ·Q_b‖²`,
  sympy-confirmed), `frobSq_schur_toBlocks_split` `:121`, `topRows_eq_mul_QtildeP` `:77`,
  `botRows_eq_cross` `:88`. **Only if the controller picks the native-Schur route** (vslice codex
  framing); the front-peel route (recommended) does NOT need these.

---

## (c) LESSONS / PITFALLS that bite THIS build

- **The det-inverse COMPASS (charter + lessons `1154`).** Every refuted route grew a determinant
  inverse in a Jacobian (Gram `det(Q_bQ_bᵀ)^{−p/2}`, seam `det(A)^{−M₂}`). The front-peel + unipotent
  shears keep every Jacobian `= 1` (pivot inverses appear only as unit coefficients — vslice §2). If a
  step grows a det-inverse, re-express (radial + unit clear + rename); the native form has always
  existed. **Reduction-to-germs must check SATISFIABILITY, not just faithful implication** — the
  `Γ↦Γ·Q_b` atom was a faithful-but-dead-route reduction caught only at build time.
- **Opaque-width matrix-apply casts (lean/CLAUDE.md + lessons `1030`).** `fun_prop` FAILS on abstract
  `Matrix.mul` over `Fin (M k)` widths; `Matrix m n ℝ` has no norm instance. **Work over the Pi form
  `Fin a → Fin b → ℝ`** (= `Params` shape, `instNormedAddCommGroupParams`): differentiate via
  `differentiableAt_pi` + `.fun_sum` + `.mul`, NO `fin_cases` on opaque rows. **Sum-indexed
  intermediates (`Fin t ⊕ Fin (M−t)`) have NO norm → differentiate PER-ENTRY** (each entry in `ℝ`).
  Banked atoms: `RouteMFrameDiff.lean`, `RouteMFactorFDeriv`. Matrix-apply `simp` fires in isolation
  but "no progress" in-context at dependent widths → prove entries as `have` at explicit `⟨_,by decide⟩`
  indices, then `exact` (Fin proof-irrelevance unifies).
- **Dependent-dimension reassociation.** `rw [Matrix.mul_assoc]`/`simp`/`conv` will NOT match through
  the dependent `HMul` (higher-order matching fails). Use fully-applied terms
  (`RouteMFrontPeel.mul_three_reassoc`) or `set X;set Y;exact Matrix.mul_assoc a X Y`. Cast bookkeeping
  at the EQUIV level, never entrywise (`finCongr_refl` → `Matrix.reindex_refl_refl` via `erw`). Peel
  layer-products by prefix-length induction reusing `prodAux_succ`.
- **`⅟`→`⁻¹` conversion for integrand-usable identities.** A banked `[Invertible M]`-stated identity
  needs `invOf_eq_nonsing_inv` (after `IsUnit.invertible`) to become the `M⁻¹` plain-function form a
  per-point integrand can use (`frobSq_schur_split_inv`, genm-sjcarrier6).
- **Binder-codepoint hazards:** combining-tilde `Q̃` and `φ` (U+03C6) are NOT valid identifiers
  (`unexpected token`) — use ASCII (`Qt`, `phi`). Bit two build cycles.
- **whnf blowups in equiv/homeomorph constructions:** `Equiv.Set.sumCompl`-based role equivs blow up
  `whnf` in `≃ₜ`/`Homeomorph` — use `Equiv.ofBijective` (lessons `1252`, geleg1). Composing theorems
  whose universe/shape mismatch masquerades as a whnf "timeout" (memory: `fibre-θ-headline-univ-zero`).
- **`decide +kernel`, never `native_decide`** (axiom hygiene; kernel cost is heartbeat-invisible).
  ℤ-matrix products by `decide` then cast to ℝ via `← Matrix.map_mul`.
- **`0·∞=0` gotcha (lessons `390`):** "∫ product finite ⟺ both finite" is FALSE over `ℝ≥0∞`; record the
  positivity guard (bites the corner-blow-up product `u₀²·(U₀+τ²U₁)` accounting).
- **Stale-olean / name-clash (lean/CLAUDE.md + lessons `939/1172`).** `scripts/lb <Module>` builds only
  the import-closure — misses name clashes with siblings the full aggregator imports (the `(2,2,2)`
  `t222` clash). Green-gate the FULL `lake build DLNFibre` before "integration-ready"; confirm
  sorry-free/axiom claims with force-recompiled `#print axioms` (AxCheck), never build exit-0.
- **Process discipline:** single-writer on the carrier contract file (lessons `458`); `scripts/lb` has a
  GLOBAL worker cap — **≤2 concurrent heavy build-tides** (lessons `1230`); the `#70` decorrelation
  lesson (`616`): a validation set sharing an unstated property (all-interior-width=r) validates the
  special case — the (3,3,3,4) vslice must EXERCISE the genuinely-coupled `L≥3`/corank-≥2 feature, not
  a collinear anchor.
- **Bedrock/precision bar:** name = content (a `…_threshold`/`…_finite` result must prove finiteness,
  not a codim proxy); the `rlct = ½·codim` reading rests on the **cited** Aoyagi equality
  (`RlctInterface.cited_aoyagi_dln`) — the carrier proves the geometric codim/box-finiteness, the
  Watanabe/Aoyagi equality stays Cited; keep the caveat beside the claim.

---

## (d) DEAD / RULED-OUT (one-line reason each — do not re-explore)

- **Gram c.o.v. `Γ↦Γ·Q_b` / full-space `det(Q_bQ_bᵀ)^{−p/2}` atom (the DECORATED-peel route).** DEAD:
  the shift `Γ↦Γ·Q_b` kernel dim `a·(b−s)` carries no decay ⟹ achievable shift `a·s/2` not `ab/2`;
  full-space enlargement over-counts the null `{rank P=0}` locus, producing a `|z|^{−1}`/∞-Beta
  divergence on the rank-deficient-`Q_b` strata (UPDATE-663/668/713, sjdescent 3-decorrelated,
  `pure-vs-atom-adj` verdict A). `RouteMSJFreedPeel.lean` (`gammaPeelIntegral_schurShearFree_eq:78`,
  `freedSchurLoss_inner_peel_lt_top:114`, `_bounded_lt_top:156`) IS this route's machinery — its own
  header admits the three interface hypotheses (`c'>a·b/2`, `Q_bQ_bᵀ` PosDef, pivot energy >0) FAIL
  POINTWISE (bottleneck charts `M₁−t>min deeper`, ≈94/480 charts `c'≤a·b/2`). Usable only on the
  full-rank slice; NOT the carrier. The `genm-sjjoint-design/cert.md` "the mountain / IH-saturates /
  Hölder-infeasible" verdict is ABOUT THIS ROUTE (the strong-IH-as-black-box on the Γ-atom).
- **`RouteMSJDecorated`'s `DecoratedBoxThresholdFinite` as the external statement shape.** Superseded by
  UPDATE-668 (plain contract, ledger internal). Its π=∅ bridge `decoratedBoxThresholdFinite_trivial_iff`
  (`:217`) + carrier (`SJDecoration`, `SJLinGenState`) are the decorated route's scaffold; the descent
  `decorated_peel_step` on it was the UNSOUND `ab`-shift. The measurability/carrier BRICKS stand
  (banked, S2-free) but the route's DESCENT SHAPE re-scoped to front-peel. Don't build the carrier as a
  decorated predicate.
- **Exponent-preserving iterated-fibre front-peel (#70).** DEAD/DISTINCT from the live FrontPeelStep:
  `prod_front_peel + fibre_lintegral_mul_le + SchurCore-at-leaves` is exponent-PRESERVING
  (`∫frobSq(X·Y)^{−c'} ≤ C·frobSq(Y)^{−c'}`, same `c'`) — no mechanism converts spent budget to a
  reduced residual exponent → undershoots `(3,3,3,3)` by ×2 (reaches `c'<3/2`, target `<3`). **The live
  FrontPeelStep `A₀↦A₀·U` (rank-stratified, charge `M₀·q` → shifted exponent) is a DIFFERENT operation
  — do not conflate.** (Charter's "#70 front-peel NO" = this dead one; the compass fix is the `A₀↦A₀·U`
  native re-expression.)
- **Seam / det-Jacobian route (#83, UPDATE-771).** GO/NO-GO = NO: the seam chart RELOCATES the
  coupled-det from `det(Q_bQ_bᵀ)` to the pivot `det(A)^{−M₂}`, does not remove it; still needs a
  per-pivot resolution chart-tree. The `gaugeAbsorption` crux (`origin/genm-seambuild`) proves
  SURJECTIVITY not TRANSVERSALITY (discuss-at-close #82/#83); it does NOT plug into the box-finiteness
  contract. `reference-notes-sj-kernel` names it as a reusable piece — it is NOT for the front-peel
  carrier.
- **Carrier-stops / carrier-can't-peel (#58→sjbuild4, #59→#60).** Descent-level subtleties already
  dissolved into the front-peel re-scope; each was an `atom`/`ab` artifact, not a wall.
- **`RouteMSchur:429`, `RouteMRecursion:257`, `RouteMSchurGeneral:144`, `RouteMLayerCoverGE:133`,
  `RouteMInteriorLDUContract` (9 sorries), `Skeleton:1094/1140/1197` (legacy D1), `Skeleton` θ
  (`aoyagiTheta_eq`), `DeepestGaugeChart:357`.** All OFF the `_gen`/`hbox` critical path (critpathmap
  DEAD list, import-verified). Do not chase.

---

## Reflection (self-recon close)

- **Most likely to advance the build:** wiring (W1) — a front-peel carrier proving
  `RouteMBoxThresholdFinite M` ∀M by its own arity strong-induction (reusing
  `routeMBoxThresholdFinite_of_step`'s shape + `routeMLayerBoxIntegral_front_split` + the banked corank
  bricks + `minAdm_eq_frontPeel`), then closing `sjJointResolution` as a corollary. The combinatorics is
  settled 3 ways and banked; the spine is one leaf.
- **Most likely to break:** the **normal-slice/`Σ⁰` transfer** — that `{rank P ≤ q}` recurses as a
  shifted `Σ⁰` of `(M₁−q,…,M_L−q)` IN LEAN (paper Thm `addlongest`; the "sum-not-min" corner
  composition). Unverified; the r1substratum cert + vslice both flag it as the sole residual analytic
  risk. Escalate only if it needs a genuine Mathlib gap.
- **Next computation that clarifies:** the (3,3,3,4) `q∈{1,2}` FrontPeelStep first milestone — the
  `A₀↦A₀·U` shift `M₀·q/2` + one recursion level, front-loading the transfer (exactly task #104's cert,
  now to be built in Lean). One decision remains for the controller: **front-peel primitive
  (r1substratum §C, recommended, no Schur) vs native-Schur+corner-blowup (vslice codex, matches the
  charter's `diag(b)` language)** — both reach `½·minAdm`; the consume-sets differ (front-peel uses
  corank bricks + `minAdm_eq_frontPeel`; Schur uses `RouteMSJChartAlgebra` + `SphereBlowup`).
