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

Recurring lesson: keep SendMessage summaries pure-ASCII ≤150 chars (unicode inflates past the
200-char cap).
