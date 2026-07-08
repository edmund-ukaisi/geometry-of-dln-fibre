# Review — Item-3 keystone (fidelity + non-vacuity), wall D1 #120

**Target:** `DLNFibre.DLN.RLCT.deepestCoreF_coreAbsorbConj_psiSplitRawGen_eq_score_at_chart`
(`lean/DLNFibre/DLN/RLCT/Validate/DeepestHsub4coreGen.lean`), canonical `@03a9f690`.
**Reviewer function:** fidelity + non-vacuity, decorrelated Codex (xhigh).
**Verdict: CLEAN PASS on all four dimensions.** The keystone is an honest conditional reduction; the
in-flight `hstep2hc` work (`hC` + invertibility germs) is NOT wasted — `hC` is the right shape,
non-contradictory, and satisfiable at the base.

## 1. FIDELITY — PASS
- **LHS is the moved-point energy.** `deepestCoreAbsorbConj` is applied to `psiSplitRawGen … q` (the moved
  point), not `q`/base; `psiSplitRawGen` is a genuine nonlinear repack (`DeepestPsiSplitRawGen.lean:165`),
  not an identity alias. `deepestCoreF H r y = dlnLoss (deepestM) 0 (decode y) = frobSqMat(prod(deepestM)(decode y))`
  (`DeepestGaugeChart.lean:115`, `frobSqMat = ∑ᵢ∑ⱼ Xᵢⱼ²`) — the genuine squared-Frobenius reduced-core energy.
- **RHS is the wire's Score.** `Score` is a free variable pinned by `hScoreDef`; its RHS (keystone
  L113–128) is **verbatim-identical** to (i) the landed L2 template RHS
  (`DeepestDiffeoBridgeL2Conj.lean:2525–2540`), (ii) the telescope output
  (`prod_deepestM_eq_schur_ldu_readback_gen`, `DeepestSchurScoreTelescopeGen.lean:273–289`), and (iii) the
  `hsub4core` integrand the actual consumer `deepest_diffeo_bridge_gen_assembled`
  (`DeepestDiffeoBridgeGenConj.lean:146`) expects (with `psiSplitRaw := psiSplitRawGen …`, `q := split x`).
  The free-var+`hScoreDef` idiom hides nothing (the proof `rw [hScoreDef]`s to the explicit formula); the
  only obligation it transfers is that the assembly supply that exact `hScoreDef` — which the L2 wire does.
- **Composition sound.** `rw [deepestCoreF_coreAbsorbConj_eq_prodSchur … hq, hScoreDef]` then
  `congrArg frobSqMat (prod_deepestM_eq_schur_ldu_readback_gen … hC …)`. The `C` brick-1 produces
  (`fun s => decode((psiSplitRawGen q).core) s + schurCorrectionConj(psiSplitRawGen q) s`) is exactly the `C`
  `hC` reads back; type-checks (green build), so the readback shape matches the telescope, not a look-alike.

## 2. NON-VACUITY — PASS (concrete in-file witness; not a vacuous `False → …`)
`q` and `x` are independent, coupled only via `hC`. The stratum is **non-empty** at the deepest-point
configuration — witness: identity frames `Pf=Qf=1`, `B` in rank-normal form `fromBlocks 1 0 0 0`, `q = 0`,
`x = base`:
- `hq`: `psiSplitRawGen … 0 = 0 ∈ closedBall 0 rIn` (`rIn > 0`). **`psiSplitRawGen_zero` is BANKED**
  (`DeepestPsiHraw0Gen.lean:167`, given `hJfront`).
- `hC` LHS `= reindex(decode(0) + schurCorrectionConj(0)) = 0`: `decode(0)=0`, and
  `schurCorrectionConj 0 = 0` under the deepest boundary (`schurCorrectionConj_zero_boundary`,
  `DeepestSchurShiftConj.lean:119`).
- `hC` RHS `= blockSchur(movedC(deepestChain(deepestPoint)) s) = 0` layerwise: the deepest chain is
  per-layer corner-form `corM = fromBlocks 1 0 0 0` (`deepestChain_corner_eq_corM`,
  `movedC_eq_self_of_toBlocks₂₁_zero`), and `blockSchur(corM) = corM₂₂ − corM₂₁·pivot·corM₁₂ = 0`
  (all off-diagonal blocks of `corM` are 0). So per-layer cores vanish, not merely the product.
- frame/invertibility hyps hold (identity frames, corner `toBlocks₁₁ = 1`).

No internal contradiction among the hypotheses; consistent in a nbhd of base. The base-point objection
(does `hC` at `q=0` force a nonzero RHS?) **fails** — RHS is 0 layerwise at the corner config.
Independent Codex (xhigh) reached the same witness independently.

**Residual (property of the deferred work, not a keystone defect):** the *useful local* statement — `hC`
for all nearby `x` with `q = split x` — is exactly the deferred ~300–600L `hC` readback (framed-move →
raw-decode-chain + `blockSchur`). Carried honestly as a hypothesis.

## 3. LAUNDERING — PASS (honest reduction)
- `hC` does **not** assume the conclusion `frobSqMat(prod C) = frobSqMat(integrand)`; it is a strictly
  weaker per-layer readback that the telescope turns into the product-level Score. It is a visibly-carried
  hypothesis (the deferred algebra), not smuggled.
- Frame hyps are endpoint triangularity/normalization/invertibility — not Frobenius-energy equalities, not
  Producer-1 content.
- `hq` is honest for a **pointwise** theorem (it is exactly what the cutoff-strip lemma
  `deepestCoreF_coreAbsorbConj_eq_prodSchur` needs). Peeling `hq` over a neighbourhood is Producer-1
  (continuity) — deferred, not claimed here. Using the keystone as if the germ were already closed *would*
  be laundering; the keystone itself does not.

## 4. BUILD — PASS (forced clean-three, 0 sorry)
Force-recompiled in an isolated worktree (`/home/ubuntu/workspace/review-hsub4-keystone`, hardlinked deps):
target `.olean` deleted → **re-elaborated from source** (`Built …DeepestHsub4coreGen (4.5s)`), then
`#print axioms`:
```
depends on axioms: [propext, Classical.choice, Quot.sound]
```
No `sorryAx`. Matches the card's claim. (Stale-olean masking is impossible — the olean was deleted first.)

## Minor precision findings (report-only; no soundness impact)
1. **Keystone docstring is STALE** re `psiSplitRawGen 0 = 0`: lines 40–42 say "only building blocks toward
   `psiSplitRawGen 0 = 0` exist, in `DeepestPsiTripleGen`". It is in fact **fully proved** as
   `psiSplitRawGen_zero` (`DeepestPsiHraw0Gen.lean:167`). The docstring's *conclusion* (full germ sequences
   after Producer 1) still holds — the remaining Producer-1 blocker is **continuity** at base, not the
   basepoint value. Recommend correcting the parenthetical.
2. A dependency carries a pre-existing style warning (`DeepestSchurScoreTelescopeGen.lean:155`: `show`
   changed the goal, should be `change`). Cosmetic, not in the keystone.
