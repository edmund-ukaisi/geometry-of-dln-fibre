# Statement card — `hLDUtieConj` CLOSED (the L2 readback-tie, Steps B-E)

Thread `genm-l2tie` (branch `genm-l2tie` @`00c325a1`), follow-on to `genm-l2psi`.
Module: `lean/DLNFibre/DLN/RLCT/Validate/DeepestDiffeoBridgeL2Conj.lean`.
Closes the gap the `genm-l2psi` card marked **Deferred** ("the `hLDUtieConj` full discharge — chart-alignment
+ Fin-3 subst, follow-on"). First full application of the banked `prod_deepestM_eq_schur_ldu_readback` —
what the bare route never could (its `hsub4core` is a permanent W-a-false gap).

> **Claim (the conjugated LDU readback-tie + the in-file `hsub4core` discharge).** At the deepest-split
> chart point `q = deepestSplit w0 x`, the cleaned conjugated core tuple
> `C = update (decode q + corrConj q) last ((1−Kc)·S1c)` has `prod (deepestM) C` equal to the Score
> `(1,1)`-Schur integrand of the framed reindexed product; hence the conjugated absorbed-core energy of
> the moved chart point equals that Score's Frobenius energy — with NO `hLDUtieConj` hypothesis remaining.
>
> - **Lean (all sorry-free, axiom-clean `[propext, Classical.choice, Quot.sound]`, forced `#print axioms`
>   after olean delete):**
>   - `l2P00Conj_eq_reindex_prod_toBlocks₁₁` — **Step B.** `l2P00Conj (split x) = (reindex(prod x)).toBlocks₁₁`.
>     `prod = L0·L1` (`prodDecode_eq_two_of_L2` + finCongr collapse) → `reindex_mul_fromBlocks` `(1,1)` =
>     `A0c·A1c + Y0c·Z1c` matched via the Step-A reads (`reindex_decode_split_toBlocks`) + the
>     `midWidth_eq_of_L2` `finCongr_refl` cast collapse. Needs `hJfront` (`pivotThr J = rThr` so the column
>     equiv matches the layer factor).
>   - `hLDUtieConjC` — the cleaned tuple `C` at `q = deepestSplit w0 x` (def; defeq to the bridge's `C`).
>   - `frobSq_prod_deepestM_hLDUtieConjC_eq` — **the tie itself (Steps B-E).**
>     `frobSq (prod (deepestM) C) = frobSq (Score-Schur)` via `congrArg frobSq` ∘
>     `prod_deepestM_eq_schur_ldu_readback` (Fin 3, after `subst hL2eq` at the spine), with `hC0`/`hC1`:
>     - `hC0` (**Step C**, layer 0): `C 0 = decode q.core_0 + corrConj_0` (`update_of_ne`) = the layer-0
>       Schur core, EXACTLY `absorbedCoreConj_eq_schurCore` at `s=0` (`hT = deepBlkT_layer0_zero`).
>     - `hC1` (**Step C**, last layer): `C 1 = (1−Kc)·S1c` (`update_self`, defeq `1 = lastLayer`) matched
>       block-by-block to the readback's `(1 − Z1·Mid₁₁⁻¹·Y0)·(layer-1 Schur)` via the Step-A reads at both
>       layers, Step B (`hP00`), the `Y0c` cast collapse, the `hJfront` pivot reconcile, then `congr 1`.
>   - `deepestCoreF_coreAbsorbConj_psiSplitRawL2CoreConj_eq_score_at_chart` — **the in-file `hsub4core`
>     discharge.** Instantiates the existing bridge `deepestCoreF_coreAbsorbConj_psiSplitRawL2CoreConj_eq_score`
>     at `q = deepestSplit w0 x` with `Score := frobSq(Score-Schur)` and `hLDUtieConj :=
>     frobSq_prod_deepestM_hLDUtieConjC_eq …`. No `hLDUtieConj` hypothesis remains — `hLDUtieConjC` is defeq
>     to the bridge's internal `C`, so the readback-tie discharges the hypothesis directly. This is what the
>     conjugated wire's `hsub4core` consumes.
> - **Assumed (the wire's producer contract, passed as hypotheses — not new math).** The endpoint frames
>   `Pf`/`Qf`, `J = frontEmbed` (`hJfront`), the frame triangularity `hPtri`/`hQtri`/`hP22`/`hQ22`, the
>   corner split `hS3b`, and the 5 invertibilities `hP11inv`/`hQ11inv`/`hMid11inv`/`hA0inv`/`hA1inv`
>   (the readback's hypotheses; the bare wire builds these at `DeepestL2Wiring`). `hDA`, `hq` (inner-ball),
>   `hW` (`det Wc ≠ 0`) — the bridge's contract.
> - **Cited.** none new. Reuses the banked `prod_deepestM_eq_schur_ldu_readback`,
>   `absorbedCoreConj_eq_schurCore`, `reindex_decode_split_toBlocks` (Step A, banked),
>   `l2P00Conj_eq_reindex_prod_toBlocks₁₁` (Step B, this card), `reindex_mul_fromBlocks`,
>   `prodDecode_eq_two_of_L2`, `pivotThresholdSplit_frontEmbed`, `deepBlkT_{layer0,layerLast}_zero`.
> - **Deferred.** The wire rewire `hstep2 = Step Θ ∘ Step Ψ_conj` (single-writer `DeepestL2Wiring.lean`,
>   the controller's) — the chart-discharge `…_eq_score_at_chart` is the piece the conjugated wire's
>   `hsub4core` plugs into.
> - **Build.** Module green (`scripts/lb DLNFibre.DLN.RLCT.Validate.DeepestDiffeoBridgeL2Conj`, forced clean
>   recompile, 2744 jobs). Not yet in the aggregator `DLNFibre.lean` closure (the L2 family is wired by the
>   controller). All four new top-level names globally unique (no sibling clash).
> - **Status.** sorry-free, axiom-clean — fidelity review pending.
