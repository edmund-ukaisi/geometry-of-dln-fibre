# genm-cruxfinish — build spec: CLOSE the 3 residual sorries → carrier sorry-free → discharge `(□)`

**This is the Stage-2 FINISH LINE.** The `genm-threadedshear` tide (concluded) landed the hardest pieces
clean-three and isolated the crux into 3 precisely-scoped, all-TRUE named sorries. This tide closes them.
**READ FIRST:**
- `threads/genm-threadedshear/spec.md` (the prior spec — route, banked bricks, discipline) + this tide's
  base commit `origin/genm-threadedshear @ 620c0c13` (READ the committed `RouteMSJThreadedShear.lean` +
  `RouteMFrontPeelCarrier.lean` — the interface, the proved bricks, and the 3 sorries are all there).
- `threads/genm-vslice/normalslice-cert.md` (§2 threaded normal form, §3 unit Jacobian, §4 loss split,
  §6 the finite pivot-chart cover / local-CoV scope).
- `threads/genm-fpcarrier/codex/normalslice-decomp-answer.md` (the lemma DAG + restatement flags).

## GOAL
Close the 3 remaining sorries on `RouteMFrontPeelCarrier.lean` (branch `genm-threadedshear @ 620c0c13`)
⇒ carrier **sorry-free** ⇒ `routeMBoxThresholdFinite_frontPeel` proves `(□) = RouteMBoxThresholdFinite M`
∀M ⇒ `aoyagi_learning_coefficient_gen` unconditional. Invariant: **canonical stays 0-sorry/0-axiom —
gaps on THIS branch only**; every landing force-recompiled `#print axioms` clean-three; single-writer.

## BRANCH / OWNERSHIP
- Worktree; base on `origin/genm-threadedshear @ 620c0c13` via `git fetch origin genm-threadedshear &&
  git reset --hard origin/genm-threadedshear` (do NOT `git checkout -b` off it — that reaches the main
  checkout). Push to a NEW branch `git push origin HEAD:genm-cruxfinish` (`git ls-remote` first).
- You OWN `RouteMFrontPeelCarrier.lean` + `RouteMSJThreadedShear.lean` (genm-threadedshear concluded).

## ALREADY PROVED (on the base @ 620c0c13 — CONSUME, do NOT redo; all clean-three sorry-free)
`blockShear_step` (per-factor threaded shear `[[1,0],[−K,1]]·[[A,B],[C,D]]·[[1,0],[Kp,1]]=[[α,B],[0,Y]]`,
`α=A+B·Kp`, `Y=D−(C+D·Kp)·⅟α·B`) · `rank_eq_q_add_of_normalForm` (units conjugating `P` to `[[α,B],[0,Z]]`,
α invertible ⇒ `rank P = q + rank Z`) · `rank_eq_q_iff_reduced_zero` · `NormalSliceChartData` +
`normalSlice_transfer_of_data` (finite-chart-sum assembly) · `morse_reduced_box_lt_top` (regime dispatch,
modulo its borderline sorry) · `reducedMorseFront(_lt_top)`.

## ★ CORRECTIONS FROM genm-threadedshear (do NOT re-hit these)
1. **The block-rank lemmas are LOCAL** — `Core.RankNormalFormDim` (`rank_fromBlocks_invertible₁₁`,
   `rank_fromBlocks_zero_offdiag`, `Matrix.rank_eq_zero_iff`), NOT Mathlib. Use the local ones.
2. **The radius-1 cover is NOT safe** — the shear coefficients `K_i=γ_iα_i⁻¹` are UNBOUNDED on the open
   chart (blow up as α→singular), so the CoV image is NOT in a radius-1 box. See sorry 1(e) for the route.

## THE 3 SORRIES (routes de-risked by the controller; all TRUE)

**Sorry 1 — `normalSliceChartData` (carrier:389): the datum. THE bulk (~200–400 LoC).** Construct
`NormalSliceChartData M q` by:
   (a) **TELESCOPING**: compose `blockShear_step` across the `L−1` tail factors via `prodAux` induction +
       the backward `K_i=γ_iα_i⁻¹` recursion (`K_L=0`) ⇒ `M_1·P = [[α_1···α_{L-1}, *],[0, Y_1···Y_{L-1}]]`
       block-upper-tri (vslice §2). `blockShear_step` is the per-factor step; the induction threads `Kp`.
   (b) **rank equation**: apply `rank_eq_q_add_of_normalForm` ⇒ `rank P = q + rank(prod (redTail M q) Y)`.
   (c) **MP**: the threaded shear is measure-preserving (compose per-factor unit-triangular shears, each
       Jacobian 1; generalise `measurePreserving_shearSub`).
   (d) **loss-split**: the disjoint `‖A₀P‖² ≃ ‖R‖²+‖Z‖²` (R from A₀, Z=`prod redTail`; vslice §4).
   (e) **RADIUS ENLARGEMENT (the tide's key subtlety)**: K unbounded on the open chart ⇒ CoV image at
       radius `T>1`. **Route (controller): box-scaling HOMOGENEITY.** The layer product is degree-`(L−1)`
       homogeneous ⇒ `routeMLayerBoxIntegral R c' T = T^{dim−2(L−1)c'}·routeMLayerBoxIntegral R c' 1`, so
       finiteness is radius-INDEPENDENT: `RouteMBoxThresholdFinite R` (radius 1, the IH) ⇒ finiteness at any
       finite `T`. Prove/reuse a scaling lemma (CHECK if one is banked for `routeMLayerBoxIntegral` /
       `paramsBoxM`; the box must scale as a cube). This discharges Codex-flag-2 (`hIH` domain translation)
       WITHOUT a bounded-K sub-chart. If the scaling lemma is fiddly, fire a decorrelated codex-consult.

**Sorry 2 — `morse_reduced_box_lt_top` borderline `c'=d/2` (carrier:221): the log endpoint.** Coupled-radial
finiteness via `radial_morse_residual_power_le` (RadialResidualPower:157) + `lintegral_eq_polar`
(RouteMSJSphereBlowup:82) — finite because `minAdm(redTail) > 0` adds codim beyond the `d`-dim Morse block
(true given `hc`). NOT the pure-Morse regime brick (that log-diverges at exactly `c'=d/2`).

**Sorry 3 — `reduced_frobSq_ae_pos` (carrier:291, CRUX A): regime-A nondegeneracy.** The reduced product is
a NONZERO polynomial in Y ⇒ a.e.≠0; route: `DeepestCoreNonvanishing.dlnLoss_deepest_core_ae_ne_zero` /
`corePoly` + `MvPolynomial.ae_eval_ne_zero`, transported Params↔flat + restricted to the box. **The tide's
BLOCKER (`∀s, 1 ≤ redTail M q s`) is a CASE-SPLIT, not a missing lemma:** it holds iff `q < tailMin M`
(then every reduced width `M s.succ − q ≥ tailMin M − q ≥ 1`, chain nondegenerate, ae-pos holds); when
`q = tailMin M` a reduced width = 0 ⇒ `Z = prod redTail ≡ 0` ⇒ ae-pos is FALSE but the analysis is the
SIMPLER branch (Z≡0 ⇒ the front Morse block `M₀q` alone charges, no reduction). So **case-split
`q < tailMin M` vs `q = tailMin M`**; the `_ae_pos` lemma is used only in the former. (The `blockShear`
telescoping / rank eq also want `q ≤ tailMin` — already `hq`.)

## BANKED (name, don't re-derive)
The base bricks above · `Core.RankNormalFormDim` rank lemmas · `measurePreserving_shearSub`
(RouteMSJPivotChart:337) · `prodAux`/`prod` API · `radial_morse_residual_power_le` + `lintegral_eq_polar` ·
`DeepestCoreNonvanishing.dlnLoss_deepest_core_ae_ne_zero` + `corePoly` + `MvPolynomial.ae_eval_ne_zero` ·
`pivotLocus_eq_iUnion` + `pivotChartCover_matBox_le_sum` (the finite cover) · `frontCharge_ge_minAdm`.

## OPAQUE-WIDTH PATTERNS (the tide's gotchas — reuse, don't rediscover)
Block-split reindexing via `blockSplitEquiv`/`finSplit` (NOT entrywise casts); `mul_three_reassoc` for
dependent-dim reassoc; `⅟`→`⁻¹` via `invOf_eq_nonsing_inv` after `invertibleOfIsUnitDet`; per-entry `have`s
at explicit `⟨k, by omega⟩` indices; ASCII binders (`al_i`, `Yt`); `decide +kernel` not `native_decide`;
`0·∞=0` positivity guard.

## DISCIPLINE
- `lean/scripts/lb` ONLY (never bare `lake`); no `lake exe cache get` in the worktree.
- Green-gate the FULL `lake build DLNFibre` (via `lb`) before "ready"; AxCheck via FORCE-RECOMPILED
  `#print axioms` (clean-three), never a bare exit-0.
- **INCREMENTAL PUSH — commit + push each green brick; do NOT go >~45 min uncommitted** (a peer tide just
  crashed on an API error; a green build with named sorries is bankable on this branch). Push freely to
  origin (pre-authorized). Checkpoint + SendMessage the controller (≤180 chars) at: telescoping green,
  MP green, loss-split green, each endpoint sorry closed, and **full carrier sorry-free + AxCheck**.
- The math is fully witnessed ⇒ pure labour. Fire a decorrelated `local-codex-consult` if the scaling
  lemma (1e) or the borderline (2) is fiddly. If a brick resists: isolate a MINIMAL named sub-sorry, build
  everything above it, report — do NOT halt. Native rank-normal-form only; do NOT cite L&R `addlongest`.
- On full closure → report; the controller wires canonical (import + `sjJointResolution:803` one-liner),
  green-gates, AxCheck clean-three, and mints the unsuffixed `aoyagi_learning_coefficient`.
