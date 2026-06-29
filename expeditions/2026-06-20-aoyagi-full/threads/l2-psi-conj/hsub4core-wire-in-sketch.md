# Wire-in sketch — discharging the conjugated `_impl`'s `hsub4core` (handoff for the L2 leg-close)

Branch `genm-l2tie` @`d8187e5c`. The piece this banks: the conjugated `hsub4core` for
`deepest_diffeo_bridge_L2_conj_impl` (and `comp_identity_L2_conj`), via the now-closed
`deepestCoreF_coreAbsorbConj_psiSplitRawL2CoreConj_eq_score_at_chart`. For genm-l2thread's leg-close.

## What `hsub4core` is (the consumer)

`deepest_diffeo_bridge_L2_conj_impl` / `comp_identity_L2_conj` take, parametrically:

    (Score : (Fin (flatDim H) → ℝ) → ℝ)
    (hsub4core : ∀ᶠ x in nhds ((paramsEquivFlat H) (deepestPoint H r B hB hr hL)),
      deepestCoreF H r (deepestCoreAbsorbConj H r B hB hr hL hDA
          (psiSplitRawL2CoreConj H r B hB hr hL hL2eq (split x))).2.1 = Score x)

with `(hsplit : ∀ w, split w = deepestSplit H r hr hL ((paramsEquivFlat H) (deepestPoint …)) w)`.
So `split x = deepestSplit w0 x` definitionally-after-`rw`, where `w0 = (paramsEquivFlat H)(deepestPoint …)`.

## What is now banked (the producer — sorry-free, clean-three)

`deepestCoreF_coreAbsorbConj_psiSplitRawL2CoreConj_eq_score_at_chart` proves, for a fixed `x` and the
producer hyps:

    deepestCoreF H r (deepestCoreAbsorbConj H r B hB hr hL hDA
        (psiSplitRawL2CoreConj H r B hB hr hL hL2eq
          (deepestSplit H r hr hL w0 x))).2.1
      = frobSq (Schur x)                        -- the (1,1)-Schur of endpointP0·(prod(decode x) − B)·endpointQL

where `Schur x = (reindex (rThr (H 0)) (pivotThr (H (last L)) J)
  (endpointP0·(prod(decode x)−B)·endpointQL)).toBlocks₂₂ − ₂₁·(₁₁+1)⁻¹·₁₂` — IDENTICAL to the wire's
`Score` lambda (`DeepestL2Wiring`'s `hScoreDef`, the `∑i∑j(Schur)²` = `frobSq(Schur)` form).

## The consumption point (the only join)

Instantiate the `_impl`'s parametric `Score` with `Score := fun x => frobSq (Schur x)`, then build `hsub4core`
by `filter_upwards` over the germ where the producer hyps hold, then `rw [hsplit]` to turn `split x` into
`deepestSplit w0 x`, then apply the banked theorem per-`x`:

    have hsub4core : ∀ᶠ x in nhds w0, deepestCoreF H r (… psiSplitRawL2CoreConj … (split x) …).2.1
        = (fun x => frobSq (Schur x)) x := by
      filter_upwards [hq_germ, hW_germ] with x hq hW   -- the inner-ball + det-Wc≠0 germs (below)
      rw [hsplit]                                       -- split x ↦ deepestSplit w0 x
      exact deepestCoreF_coreAbsorbConj_psiSplitRawL2CoreConj_eq_score_at_chart
        H r B hB hr hL hL2eq hDA J hJfront Pf Qf hPtri hQtri hP22 hQ22 x hq hW
        hS3b hP11inv hQ11inv hMid11inv (hA0inv x) (hA1inv x)

(The `Pf/Qf/J/hJfront/hPtri/hQtri/hP22/hQ22/hS3b/hP11inv/hQ11inv` are the same producer constants the bare
wire builds for `deepest_diffeo_bridge_L2_wired` — frame-independent of `x`. `hMid11inv/hA0inv/hA1inv` are
`x`-dependent invertibilities, supplied on the germ.)

## The two germs to produce (mirror the bare wire `DeepestL2Wiring:647-669`)

1. `hq_germ` — `psiSplitRawL2CoreConj … (split x) ∈ closedBall 0 (cutoffBumpConj …).rIn` near `w0`. The bare
   builds the analogue via `htend`/`hballgerm` (`psiSplitRaw…` continuous, value `0` at the basepoint, ball
   ∈ nhds). The conjugated `psiSplitRawL2CoreConj_zero` + its ContDiff/continuity (banked in this module)
   give the same.
2. `hW_germ` — `det (l2WConj … (split x)) ≠ 0` near `w0`. Bare analogue `hWdetgerm` via `ball_l2ExtraRadius_subset`;
   the conjugated `l2WConj` is `1 + Rc` with `Rc(0) = 0` (`l2RConj_zero`), so `l2WConj(0) = 1`, `det = 1 ≠ 0`,
   and `det ∘ l2WConj ∘ split` is continuous ⟹ `≠ 0` on a nbhd (`ContinuousAt` + `isOpen_ne` preimage, or
   the bare's `l2ExtraRadius` cutoff-support pattern transported to the conjugated `l2WConj`).

The `x`-dependent invertibilities `hMid11inv/hA0inv/hA1inv` (and `hq`/`hW`) all hold on the same inner-ball
germ near `w0` (the decode layers/product have unit leading blocks there — the `hDA`/cutoff-support story);
produce them in the same `filter_upwards` (the bare wire's pattern for the layer-pivot invertibilities).

## Caveat (the one non-obvious join, flagged for the leg-close + the fidelity reviewer)

`hLDUtieConjC H r B hB hr hL hL2eq x` is **defeq** (not syntactic) to the `Function.update (…) (lastLayer hL)
((1−Kc)·S1c)` tuple `C` inside `deepestCoreF_coreAbsorbConj_psiSplitRawL2CoreConj_eq_score` (at
`q = deepestSplit w0 x`). That defeq is what lets `frobSq_prod_deepestM_hLDUtieConjC_eq` discharge the
bridge's `hLDUtieConj` hypothesis directly (the `_at_chart` theorem typechecks on it; build green). If the
leg-close refactors that `C`, keep it defeq to `hLDUtieConjC` or re-prove the tie at the new shape.

## Pointers

- Producer: `lean/DLNFibre/DLN/RLCT/Validate/DeepestDiffeoBridgeL2Conj.lean`
  (`…_eq_score_at_chart`, `frobSq_prod_deepestM_hLDUtieConjC_eq`, `l2P00Conj_eq_reindex_prod_toBlocks₁₁`).
- Bare wire germ-production template: `lean/DLNFibre/DLN/RLCT/Validate/DeepestL2Wiring.lean:636-686`.
- Statement card: `statement-card-hLDUtieConj.md` (same dir).
