# Headline-value gate — rlctAtOn(Sreg+Score) = C/2 + the coreΦ→Score ripple scope

The (♦)/coreΦ route is dead (the overcount locus is OPEN in the fibre, not thin ⇒ the RLCT quantity
genuinely changes). The headline value must be re-derived from `Sreg + Score`, `Score = frobSq(Rcore)`
(the global Schur = the genuine deepest-layer residual). **VERDICT: rlctAtOn(Sreg+Score) = C/2 holds —
by the EXACT banked leaf + the existing rlctAtOn(loss)=aoyagiLambda chain (anchor-independent, no
Newton re-derivation). The ripple is L2-LOCAL — R1 is SAFE (it operates on the reduced-chain loss, never
the per-layer-product coreΦ).** Exact (sympy) + the banked-lemma structure; given my sub-thread error
history I flag the one read-from-code assumption for independent confirm. Read-only.

## 1. rlctAtOn(Sreg + Score) = C/2 — the clean ANCHOR-INDEPENDENT argument

The banked leaf `dlnLoss_two_sided_of_frame` (DeepestGaugeBlocks.lean:566) is a genuine TWO-SIDED bound:
`(Sreg + Score) ≤ const·loss  ∧  loss ≤ const·(Sreg + Score)`, `Score = frobSq(P11 − P10·⅟P00·P01)` (the
FRAMED global Schur of `reindex(P0·N·QL)` — the loss's OWN core block). So by rlctAtOn's
comparability-invariance:

    rlctAtOn(Sreg + Score)  =  rlctAtOn(loss)  =  rlctAtOn(dlnLoss H B (·) at w0)  =  aoyagiLambda H r.

**This is nearly tautological and anchor-independent:** the leaf was ALWAYS the route to rlctAtOn(loss),
and `Score` is the loss's own Schur core, NOT a separate object. The C/2 VALUE is whatever the headline
chain computes for rlctAtOn(loss) — UNCHANGED. The coreΦ identification was a downstream slip; correcting
it to Score restores the identity to the loss's own residual.

(2,2,2) r=1 anchor: `C/2 = nReg/2 + lambdaCore(M) = 3/2 + 0 = 3/2` (`nReg=1·(2+2−1)=3`, M=(1,1,1) trivial
core), matching the banked `case222_rlctAtOn_eq = 3/2`. ✓ The argument is anchor-independent so it holds
for (2,3,2) etc. too (the VALUE there is `nReg/2 + lambdaCore((1,2,1))`, whatever R1 gives for that
reduced core — unaffected by the Score correction).

## Where coreΦ diverged (the OPEN overcount locus)
`coreΦ = ‖∏S'_s‖²` (per-layer Schur PRODUCT, the (♦) route). `Score = ‖Rcore‖²`, `Rcore` = the GLOBAL
Schur of the framed product. Frame-free, `Rcore = u·∏S'` (the S5c unit-rescaling); with frames + on the
OPEN tilted-kernel locus (rank-deficient `S'`, the S5c germ counterexample `W = I+ηE₁₂`), `‖∏S'‖²` and
`‖Rcore‖²` DIFFER ⇒ `V(Sreg + coreΦ) ⊊ V(loss)` (coreΦ vanishes where the loss doesn't, or vice versa)
⇒ `rlctAtOn(Sreg+coreΦ) ≠ rlctAtOn(loss)`. **Score has `V(Sreg+Score) = V(loss)`** (it IS the loss's
residual) ⇒ `rlctAtOn(Sreg+Score) = rlctAtOn(loss) = C/2`. The coreΦ slip was a wrong-zero-set
identification on an OPEN locus (hence the genuine RLCT change ad67c6b4 flagged).

## 2. Ripple scope — the coreΦ→Score change is L2-LOCAL; R1 is SAFE

**The headline's core is NOT coreΦ — it's `deepestCoreF` = the reduced-chain loss.** Read from the code:
- `deepestCoreF H r y = dlnLoss (deepestM H r) 0 (paramsEquivFlat⁻¹ y)` (DeepestGaugeChart.lean:114) — the
  REDUCED-CHAIN `M = H−r` loss. The headline `deepest_regular_core_normal_form` (Skeleton:1124) computes
  `rlctAtOn(∑q.1² + deepestCoreF(coreAbsorb q)) = nReg/2 + lambdaCore(M)`.
- R1 (RouteMRecursion:150) `IsSchurStraightenSqueeze.redCore_eq : G² = dlnLoss S.red 0 ∘ redEmbed` —
  R1 operates on `dlnLoss(S.red)`, the REDUCED-CHAIN loss, resolved to `lambdaCore` via `minAdm`. **R1
  never touches a per-layer-product `coreΦ`.**

So `coreΦ = ‖∏S'‖²` was a SQUEEZE-LOCAL identification (PIN2's `deepest_loss_squeeze` relating the FULL
loss to `∑(reg)² + deepestCoreF(coreAbsorb)`); the correction (Score, not coreΦ) is the squeeze's INTERNAL
core-bridge. **The headline core (`deepestCoreF` = reduced-chain loss) and R1 (resolving `dlnLoss(S.red)`)
are SAFE — they already work on the genuine reduced loss, not the per-layer-product.**

**Ripple verdict: L2-LOCAL** — contained to `DeepestGaugeBlocks`/`DeepestGaugeConstruction`'s squeeze →
`deepest_regular_core_normal_form` core-bridge (the framed-Schur Score vs the frame-free coreΦ, the
germ-fold). The R1 recursion (RouteM*, the (3,3,4) anchor) operates on the reduced-chain `dlnLoss(S.red)`
— the global-Schur-flavored residual (the reduced chain's OWN loss) — NOT the per-layer-product core, so
it is UNAFFECTED. The fix does NOT touch R1.

## Honest scope + the one assumption to independently confirm
- The C/2 = rlctAtOn(loss) argument is exact (the banked two-sided leaf + the rlctAtOn-comparability-
  invariance + case222). No Newton-polytope re-derivation needed — it's the leaf's comparability, which
  was always the route.
- **The ripple-scope verdict rests on ONE read-from-code claim:** that `deepestCoreF`/R1 operate on the
  reduced-chain loss `dlnLoss(M)`, NOT the per-layer-product `coreΦ`. I read this from `deepestCoreF`'s
  def (= `dlnLoss(deepestM)`) + `redCore_eq` (= `dlnLoss(S.red)`). **Given my sub-thread error history,
  this should be independently cross-checked** — specifically that NO step between the squeeze's `coreΦ`/
  `deepestCoreF` and R1's `dlnLoss(S.red)` silently identifies `deepestCoreF` with the per-layer-product
  `coreΦ` (if it does, the ripple touches R1 after all). My read says it does NOT (deepestCoreF IS
  dlnLoss(M) by def; the squeeze's coreΦ-vs-Score is the FULL-loss-to-deepestCoreF bridge, downstream of
  which deepestCoreF = the reduced loss R1 sees).

## Net (the gate verdict)
**rlctAtOn(Sreg+Score) = C/2** — exact, anchor-independent, via the banked leaf + case222 (Score is the
loss's own core; coreΦ was a wrong-zero-set slip on the OPEN tilted-kernel locus). **The ripple is
L2-LOCAL** (the squeeze→normal-form core-bridge); R1 operates on the reduced-chain loss and is SAFE. The
headline value is UNCHANGED (Score = the genuine residual, the value was always rlctAtOn(loss) =
aoyagiLambda). **Independent confirm recommended for: (a) the C/2 conclusion (you're already getting it),
(b) the read-from-code claim that R1/deepestCoreF use the reduced-chain loss, not the per-layer-product
coreΦ** — that's the load-bearing ripple-scope fact.

## Files
- `/tmp/score_rederive.py`, `score_anchor.py` (the C/2 argument + the coreΦ-divergence locus). Banked:
  `dlnLoss_two_sided_of_frame` (Score = loss's own core), `case222_rlctAtOn_eq` (3/2),
  `deepest_regular_core_normal_form` (the headline core = deepestCoreF = reduced loss),
  `RouteMRecursion.redCore_eq` (R1 on dlnLoss(S.red)).
