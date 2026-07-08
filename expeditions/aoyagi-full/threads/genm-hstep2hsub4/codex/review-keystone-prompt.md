# Independent audit: is this Lean reduction honest and non-vacuous?

You are an independent mathematician auditing a Lean 4 (Mathlib) theorem for a formalisation of deep-linear-network fibre geometry. I want your DECORRELATED read — do NOT assume it is fine; hunt for the ways it could be vacuous, laundered, or misstated. Be concrete.

## The theorem under audit (verbatim shape; some routine hyps abbreviated)

```
theorem deepestCoreF_coreAbsorbConj_psiSplitRawGen_eq_score_at_chart
    (H : Fin (L+1) → ℕ) (r : ℕ) (B : Matrix ... ℝ) (hB : B.rank = r)
    (hr : ∀ s, r ≤ H s) (hL : 1 ≤ L) (hDA : ∀ s, IsUnit (deepBlkA ... s))
    (J : Fin r ↪ Fin (H (last L))) (hJfront : J = frontEmbed ...)
    (Pf Qf : per-layer square frame matrices)
    (q : DeepestSplit ...)                       -- an ARBITRARY point in the split space
    (x : Fin (flatDim H) → ℝ)                    -- an INDEPENDENT chart coordinate
    (hq : psiSplitRawGen ... J Pf Qf q ∈ closedBall 0 (cutoffBumpConj ...).rIn)
    (hPtri hQtri hP22 hQ22 hS3b hP11inv hQ11inv hMid11inv : frame-triangularity / pivot / invertibility facts about Pf,Qf,B,J,x)
    (hC : ∀ s : Fin L,
        reindex finCongr finCongr
          ( decode((psiSplitRawGen ... q).2.1) s          -- core reads of the MOVED point q
            + schurCorrectionConj ... ((psiSplitRawGen ... q).1, (psiSplitRawGen ... q).2.2) s )
        = blockSchur (movedC (deepestChain (decode x)) (Z0edit0 ...) s))   -- moved Schur core built from x
    (hLayer : ∀ k < L, Invertible (deepestChain (decode x) k).toBlocks₁₁)
    (hPart  : ∀ k ≤ L, Invertible (partProd (deepestChain (decode x)) k).toBlocks₁₁)
    (Score : (Fin (flatDim H) → ℝ) → ℝ)
    (hScoreDef : Score = fun w => frobSqMat (<framed (1,1)-Schur integrand over reindex(endpointP0 · (prod(decode w) − B) · endpointQL)>)) :
    deepestCoreF H r (deepestCoreAbsorbConj ... (psiSplitRawGen ... J Pf Qf q)).2.1 = Score x
```

Here `decode = (paramsEquivFlat _).symm`. The whole proof is two rewrites:
1. `deepestCoreF_coreAbsorbConj_eq_prodSchur ... hq` : GIVEN `hq` (moved point in the cutoff inner ball), rewrites the LHS to `frobSqMat (prod (deepestM) (fun s => decode((psiSplitRawGen q).core) s + schurCorrectionConj(psiSplitRawGen q) s))`.
2. `prod_deepestM_eq_schur_ldu_readback_gen ... hC hLayer hPart` : GIVEN `hC` (each reindexed reduced-core layer reads back as a moved Schur core) + chain/frame invertibility, proves `prod (deepestM) C = <the Score integrand at x>`.
Then `congrArg frobSqMat` closes it, after `hScoreDef` rewrites `Score x`.

## Context you need

- `psiSplitRawGen ... J Pf Qf q` is a genuine nonlinear "joint move" of `q`: it repacks per-layer reads `psiReadBlk` (whose interior value is `movedC (deepestChain (framedParamsPivot q)) − corM`) into the gauge/core slots. It is NOT the identity.
- There is a BANKED move identity `hmove`: `deepestChain (framedParamsPivot (psiSplitRawGen q)) = movedC (deepestChain (framedParamsPivot q)) (Z0edit0 ...)`. Note this is the FRAMED chain `deepestChain (framedParamsPivot ·)`, whereas `hC`'s RHS uses the RAW chain `deepestChain (decode x)` and wraps it in `blockSchur`.
- `hC` is declared (by the authors) to be DEFERRED "new math (~300–600 lines)": the bridge from the moved point's decoded core reads (+ conjugated correction) to `blockSchur(movedC(deepestChain(decode x)))`. It is carried as an explicit hypothesis, not proved here.
- The intended eventual use ("assembly") sets `q := split x` (so `q` becomes a function of `x`), where `split` is the chart homeomorphism centred at the base with `split(base) = 0`. At `x = base`, `decode(base) = deepestPoint`, and `prod(deepestPoint) = B` (so the Score integrand at base is 0).
- An L=2 analog `..._psiSplitRawL2CoreConj_eq_score_at_chart` is already PROVED (green) end-to-end WITHOUT an `hC` hypothesis (it discharges the readback internally via a constructed `C`).

## Questions (answer each independently, hunt hard)

1. FIDELITY. Is the LHS genuinely the energy of the MOVED point `psiSplitRawGen q` (not silently the unmoved `q` or the base)? Is pinning `Score` as a free variable + `hScoreDef` a faithful way to assert "= the wire's Score integrand at x", or does it hide anything?

2. NON-VACUITY. `q` and `x` are independent, coupled only through `hC`. Could `hC ∧ hq` be JOINTLY UNSATISFIABLE (making the theorem a vacuous `False → …`)? In particular: at the natural point `q = split(base) = 0`, `x = base`, the LHS of `hC` becomes `decode(0) + schurCorrectionConj(0)`; if `psiSplitRawGen 0 = 0` this is `0`, while the RHS is `blockSchur(movedC(deepestChain(deepestPoint)) s)` per layer — which need not be 0 per layer even though the telescoped product is 0. Does this make the base point fail `hC`? If so, is there any OTHER (q,x) where all hypotheses can hold, or is the stratum empty? Reason carefully about whether the deferred `hC` is CONSISTENT (holds at some non-degenerate config) vs CONTRADICTORY.

3. LAUNDERING. Does `hC` (or any frame hyp) secretly assume the conclusion `frobSqMat(prod(deepestM) C) = frobSqMat(<integrand>)`, or assume the deferred continuity/basepoint content (`psiSplitRawGen 0 = 0`, `Tendsto`)? Is carrying `hq` as a hypothesis honest, or a smuggling of deferred Producer-1 content?

Give a per-question verdict (honest / concern / broken) with a concrete reason. Distinguish what you can PROVE from what you INFER.
