# VM rotation — resume recipe + checkpoint (2026-06-23)

Written by the controller before a VM rotation (dying box → beefier box). The operator
resumes the SAME controller session afterward. This doc is the durable recreation recipe +
state checkpoint, so recreation does not depend on memory.

## Everything is on origin — nothing unique is lost

Verified `git rev-list <branch> --not --remotes=origin --count == 0` for every local branch
that was not directly tracking origin (crux2/fold3-close, crux2/rm-atlas-bridge, fm/l2-product
are all fully reachable from other origin branches; the `agent-*` worktrees are ephemeral
scratch whose real output was pushed). All milestone + WIP commits are banked.

## Active branches (all on origin) — what each holds

| branch | HEAD (pre-rotation) | content |
|---|---|---|
| `fm/regslice-id` | 73a815e | #158 DeepestFrame wrappers + #159 RankNormalForm Core proofs (WIP) + Codex certs/recipes (fm3-coord-bridge collapse recipe, divisor-binding, pp-rstar hMono cert) + lean-search scripts |
| `fm3/routem` | dcf667b | rs-grind: hMono #149 + #143 recursion arithmetic + MinAdmMono + degenChild corollary (double-audited FAITHFUL); #146 MvalMultSum support foundation GREEN + 1 collapse sorry |
| `fm3/routem-ga` | a94fcd8 | fm3: binding spine — binding_recursion_of_step (#153) + BindingSpine binding_rlct_eq_lambdaCore_of_hstep' (#154), rv-ga GREEN, reduces binding R1 to hstep+hbase; (2,2,2) plumbing anchor (#147); case222 statement card |
| `fm2/deepest-gauge-chart-sub34` | e081228 | cobuild: #120 consolidated (transparent regResidualPack/regGaugeIdxSplit) + FOLD3 endpoint_telescoping + #80 leaf cores (dlnLoss_two_sided_of_frame, deepestEPivot_sq_sum_eq_blocks) + Codex #80 chain design |
| `fm/deriv-spec` | 469e8bf | deriv-fm: #120 def-change + regSlice_fderiv_id skeleton; #155 early-check done; #156/#157 sandwich = the remaining analytic fill |
| `fm2/split-reindex` | 9f9d6b6 | crux2: #158 frame-lane (DeepestFrame wrappers signature-green) |
| `fm-pin1-regabsorb-ift` | 6269f53 | PIN1 #82 regabsorb (likely superseded by the consolidated transparent base — verify before reuse) |

## Worktree recreation (from a fresh clone)

```bash
git clone git@github.com:edmund-ukaisi/geometry-of-dln-fibre.git
cd geometry-of-dln-fibre && git fetch origin
# one worktree per active teammate branch (paths are suggestions; any path works):
git worktree add ../deriv-spec  fm/deriv-spec
git worktree add ../dgc-sub34   fm2/deepest-gauge-chart-sub34
git worktree add ../fm3-ga      fm3/routem-ga
git worktree add ../fm3-routem  fm3/routem
git worktree add ../split-reindex fm2/split-reindex
# Mathlib cache: each worktree needs `lake exe cache get` (or shared LEAN_PATH) before building.
```
Skip the stale worktrees (atlas-value, aoyagi-rlct, case222-wrapper, crux2-*, fibre-codim,
fm2-ge, r1-cover, resolution-atlas-scaffold, semantic-audit-ci-roadmap, the `agent-*` scratch,
a2-theta) — #28 consolidation prunes them anyway.

## Resume state — the hero task (general-M aoyagi_learning_coefficient = ½·minAdm)

**Binding R1 spine = PROVEN + triple-audited** (rv-ga + decorrelated Codex): arithmetic
(MinAdmMono #152), recursion core (#153), instantiation (BindingSpine #154). Reduces the
binding R1 to EXACTLY hstep + hbase. Basepoint answered: `(fun _ => 0 : Params M)`.

- **hbase** = #70 Morse base — proven, needs wiring.
- **#104 = hstep, the geometric heart — THE one genuinely-open piece.** Owned by **fm3**
  (corrected from a mis-attribution to rs-grind): derive the general per-node blow-up cert on
  paper/sympy (the y₀^? *exceptional-divisor* Jacobian — the SOUND weighted-cover route, NOT
  the vacuous #148 MP-chart — + the ReducedTransport det-1 shear for child-reduction), then
  bounded Lean transcription, decorrelated + fidelity-reviewed first. **This is the gate
  between "audited conditional spine" and "complete binding R1."**
- **L2 leg**: #80 (cobuild — leaf cores banked, chain around framedParams_split_eq_frame_raw
  cert (b) + #158 boundary frames; core term is a COMPARABILITY not equality = expected g156
  leakage, RLCT value stays EXACT), #82 sandwich (deriv-fm #156/#157), #158 frame-bridge
  (crux2 wrappers green; 2 Core proofs = #159, left/right_normal_form_of_cols/rows_vanish).
- **#146** geometric-codim bridge (enrichment, rs-grind): foundation GREEN, collapse =
  transcription (ℤ-Icc telescope via cast-to-ℕ: Int.toNat + Finset.sum_range_sub, OR
  Int.Icc_eq_finset_map → range; `Int.induction_on` cases are `zero | succ n ih | pred n ih`).
- **D1** top assembly: waiting on R1/L2.
- **#151** cross-branch wiring (controller): merge fm3/routem (hMono) + fm3/routem-ga
  (spine), supply hMono via MinAdmMono.lambdaCore_schurStateRed_le, leaving hstep+hbase.
  Gated on #104.

## Resume actions (post-rotation)
1. Re-engage **fm3** on the #104 general-hstep cert (primary, sound-route conditions held).
2. **cobuild** → #80 chain around framedParams (b); **deriv-fm** → #82 sandwich #156/#157
   (lands on cobuild's canonical base); **rs-grind** → #146 collapse (names verified) + the
   (2,2,2) cert transcription (gated on rv-ga's RouteMNodeDescent audit); **#159 formaliser**
   → 2 Core proofs; **crux2** → #150 review + #158; **rv-ga** → audit queue.
3. Build-env was the bottleneck (4 cores/15GB/no-swap, OOM-prone) — the beefier box should
   dissolve the LAKE_JOBS/load-gating workarounds.

## Per-teammate resume briefings (copy-paste to re-brief a fresh teammate)

Today's execution context (2026-06-23) is NOT in thread.md — it's here + the task board + the
certs. Each briefing below is self-contained: branch, tasks, what's done, the open sorry, the
cert to use, the exact next step. Re-brief a fresh agent with its block; it has everything.

### fm3 — branch `fm3/routem-ga` (worktree e.g. ../fm3-ga)
- TASKS: #135 (G-b), #104 (hstep, PRIMARY), #147 ((2,2,2) anchor), #151 inputs.
- DONE + banked + rv-ga-GREEN: binding_recursion_of_step (#153), BindingSpine
  `binding_rlct_eq_lambdaCore_of_hstep'` (#154, hMono discharged → reduces binding R1 to
  hstep+hbase only); ofNodePresentation (#144); (2,2,2) PLUMBING anchor (#147,
  Case222NodeDescent.lean — GREEN but uses a PLACEHOLDER flatCore222, 3/2 is a numeric
  coincidence, NOT the genuine loss-connection). Basepoint for #151 ANSWERED: `(fun _ => 0)`.
- OPEN — #104 = THE primary, the geometric heart. DERIVE the general per-node blow-up cert on
  paper/sympy (NOT Lean yet, NOT rv-ga-gated): present dlnLoss M 0 in Schur form
  ∑Erow²+‖bcol·Erow+SΓ‖² at a general node, generalize Erow/bcol/SΓ from the m×k pivot, pin the
  y₀^? Jacobian, the ReducedTransport det-1 shear. SOUNDNESS (hard condition): y₀^? MUST be the
  blow-up exceptional-divisor power (whose contribution = nReg/2 = Σ fresh-codims), NOT a
  Jacobian-1 measure-preserving chart (= the #148 trap; that route is vacuous). Cross-check
  against the divisor-soundness witness at threads/14-r1-design/codex/divisor-binding-{prompt,
  answer}.md. Then bounded Lean transcription + a fidelity review BEFORE transcribing.
- NEXT STEP: derive the general-hstep cert (sound y₀^? route); ping controller when it's ready
  for a decorrelated fidelity check.

### cobuild — branch `fm2/deepest-gauge-chart-sub34` (worktree e.g. ../dgc-sub34)
- TASKS: #80 (PIN2 loss_squeeze), integrates #82 + #158.
- DONE + banked: #120 consolidated (transparent regResidualPack/regGaugeIdxSplit); FOLD3
  endpoint_telescoping (sorry-free + IsUnit P0∧QL); #80 leaf cores dlnLoss_two_sided_of_frame
  + deepestEPivot_sq_sum_eq_blocks (#120-value-stable summing bijection); Codex #80 chain
  design @e081228.
- OPEN — the #80 chain assembly (~120-150 LoC) around ONE geometric cert:
  `framedParams_split_eq_frame_raw` (= hconj: reindex(P0·N_w·QL) = fromBlocks (P00−1) P01 P10
  P11). This cert is cobuild's OWN (ruling (b)): it's on split/deepestRoleIndexEquiv + core +
  gauge — a DIFFERENT object from deriv-fm's #120 (reg-slice-of-deepestEPivot only), so #120
  does NOT supply it. Use deriv-fm's structured-equiv TECHNIQUE (regBoundaryEmbed) for split's
  reg-half (deriv-fm advises). Built ON #158's boundary frames (P_0→corM, Q_{L−1}→corM).
- IMPORTANT: the core term ‖Rcore‖² is a COMPARABILITY with deepestCoreF (g156 leakage,
  Schur-of-product ≠ product-of-Schur), NOT an equality — folds into c₁/c₂, RLCT value stays
  EXACT (the squeeze was always two-sided). No headline change.
- PROBE-AND-ESCALATE: if `split` (deepestRoleIndexEquiv) is NOT actually frame-conjugate
  as-defined, STOP + escalate (a #82-style false-as-stated risk) — don't force green.
- NEXT STEP: build the #80 chain route-first with framedParams as the one leading sorry; then
  integrate deriv-fm's #82 regSlice proof + #158's frames.

### deriv-fm — branch `fm/deriv-spec` (worktree e.g. ../deriv-spec)
- TASKS: #139 / #156 / #157 (the #82 PIN1 regSlice sandwich).
- DONE + banked: #120 def-change (Milestone 2, value-preserving GREEN); regSlice_fderiv_id
  SKELETON (typechecks); #155 early-check (alignment cancel reduces by rfl/simp).
- OPEN — the #91 idempotent-sandwich analytic fill (~150-250 LoC) = #156 (value-fold
  framedProd_regSlice_fderiv) + #157 (assemble deepestEPivot_regSlice_fderiv_id). The fderiv
  VALUE through prodAux at 0 = Σ_s corner·δC_s·corner → collapse to (Σ_s δX_s, δY_L, δZ_1) →
  the regPivotFinEquiv cancel = proj i. Real Leibniz-value + cast friction (#111-class). Use
  the tactic cert @d14a1f2 (the recipe). NAMING: regStraightenTotalCLM_equiv + regBlock_id —
  the total is an invertible SHEAR-CLE, the reg-BLOCK is id; do NOT claim a literal-id total
  (crux2's #150 review accepts the shear form; the consumer needs invertibility only).
- LANDS ON cobuild's canonical base (fm2/deepest-gauge-chart-sub34) — hand cobuild the
  regSlice_fderiv_id proof-diff; the lemma is identical on both branches so it applies cleanly.
- ALSO: advise cobuild on extending the regBoundaryEmbed technique to split's reg-half for its
  #80 framedParams cert.
- NEXT STEP: grind #156 then #157 via @d14a1f2; hand the proof to cobuild.

### rs-grind — branch `fm3/routem` (worktree e.g. ../fm3-routem)
- TASKS: #146 (geometric-codim bridge) + the (2,2,2) hnode cert transcription.
- DONE + banked + DOUBLE-AUDITED-FAITHFUL @c8c9d5a: hMono (#149), recursion arithmetic (#143),
  MinAdmMono (inf'_Mval_mono + lambdaCore_schurStateRed_le), degenChild corollary
  (isLeafNode_schurStateRed_of_isLeafNode — load-bearing for the #151 hdrop adapter).
- OPEN — #146 MvalMultSum.lean (@dcf667b, GREEN + ONE collapse sorry @~line168). Full support
  foundation proven (3 boundary-support closed forms: top_row/right_col/interior + eval
  helpers). The collapse = quadruple→single sum: sum_eq_single_of_mem on i=1 then v=L, rewrite
  by the 3 support lemmas, triangular reorder (sum_sigma'+sum_nbij'), then the ℤ-Icc TELESCOPE.
  ℤ-telescope route (VERIFIED names): cast-to-ℕ via Int.toNat + Finset.sum_range_sub, OR
  Int.Icc_eq_finset_map (Data/Int/Interval.lean:72) → range → sum_range_sub. Int.induction_on
  cases are `zero | succ n ih | pred n ih` (NOT hz/hp/hn). SEARCH FIX: rg ignores .lake — use
  `rg --no-ignore <pat> .lake/packages/mathlib/Mathlib/`. Codex recipe banked at
  threads/fm3-coord-bridge/codex/mval-collapse-answer.md. Statement is scope-honest (SIGNED
  ring identity, no admissibility; the geometric-codim reading = a separate diff-r≥0 corollary).
- ALSO: transcribe the (2,2,2) hnode cert (case222-hnode-schur-cert.md) → hnode + ReducedTransport
  (the y2-pivot det-1 shear via crux2's mp_schur_transvection_vec), per fm3's ofNodePresentation
  contract — GATED on rv-ga's RouteMNodeDescent audit.
- NOT rs-grind's: the GENERAL #104 geometric squeeze (that's fm3). rs-grind = numeric nReg + Mval.
- NEXT STEP: finish the #146 collapse (transcription, names verified) on fresh context.

### crux2 — branch `fm2/split-reindex` (worktree e.g. ../split-reindex)
- TASKS: #158 (frame-bridge) + RESERVED #150 (the #80/#82 cert-fidelity review).
- DONE: #158 DeepestFrame wrappers (deepestPoint_layer0_left_frame Q_0=I,
  deepestPoint_layerLast_right_frame P_{L−1}=I) — SIGNATURE-GREEN (sorry-free wrappers), so
  cobuild's telescoping wires now. The 2 Core proof sorries (left/right_normal_form_of_cols/
  rows_vanish, RankNormalForm.lean) = #159, dispatched to a formaliser (re-dispatch fresh
  post-rotation; the WIP is on fm/regslice-id @73a815e).
- RESERVED #150 (fires when cobuild's DeepestGauge goes sorry-free): the single authoritative
  cert-fidelity rubric (#44's 6-point bar + frame-exposure + PIN2 ∏S_s linchpin + g207 +
  fm3-scope-fence). KEY CHECK: confirm #80/#82 genuinely WIRE the def-swap (regResidualPack :=
  regPivotFinEquiv) so reg-slice-id closes BY the structured correspondence, NOT a green-by-
  opaque-defeq veneer. The atoms are decl-verified transparent; check the WIRING. Accept the
  shear-CLE form (not literal id). Codex was DOWN (design-consult unavailable) — solo carefully.
- NEXT STEP: hold for cobuild's sorry-free signal → fire #150; meanwhile #158 frame-lane.

### rv-ga — auditor (works in any worktree at HEAD of the branch under audit)
- DONE: #152 (MinAdmMono), #153 (binding_recursion_of_step), #154 (BindingSpine) — all GREEN +
  decorrelated Codex. The whole binding-spine arithmetic+recursion+instantiation is audited.
- QUEUED: audit the (2,2,2) anchor #147 (RouteMNodeDescent soundness — does it discharge the
  producer obligations non-vacuously) when fm3 lands it sorry-free; then crux2's self-authored
  CoreShearMP MP-helpers (the #150 carve-out crux2 can't self-review) when the L2 chain lands;
  then fm3's #104 general-hstep cert (the #148-vacuity-class lens: is the y₀^? Jacobian the
  genuine divisor power, not a measure-preserving chart).

### #159 formaliser (re-dispatch fresh)
- 2 Core proofs left_normal_form_of_cols_vanish / right_normal_form_of_rows_vanish
  (RankNormalForm.lean ~:271/289). [A|0] rank r → first r cols independent → extend to
  invertible B → P=B⁻¹ → P·D=corM (or LinearMap.exists_leftInverse_of_injective); right via
  transpose. Self-contained Core (~40-80 LoC). The WIP is banked on fm/regslice-id @73a815e.

Recurring lesson: keep SendMessage summaries pure-ASCII ≤150 chars (unicode inflates past the
200-char cap).
