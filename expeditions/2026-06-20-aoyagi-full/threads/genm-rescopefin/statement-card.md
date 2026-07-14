# Statement card — head-split (a)/hstrict per-shell finiteness (subset route, T1)

Thread `genm-rescopefin`, branch `genm-sj5-rescopefin`, module
`lean/DLNFibre/DLN/RLCT/Validate/RouteMSJShellSubset.lean`.

---

> **Claim (subset bound).** For a legal cut `u = t★+j ≤ M 0` and ANY flag level (`ε, r, jf` free), the
> head-split spine integrand is bounded by the bare full-chain layer-product box — a pure subset argument,
> no domination constant.
>
> - **Lean:** `DLNFibre.DLN.RLCT.shellSpineIntegrand_le_layerBox`
>   (`lean/DLNFibre/DLN/RLCT/Validate/RouteMSJShellSubset.lean` @ `e7b759ad6`)
> - **Gloss.** `shellSpineIntegrand M u κ ε r jf c' ≤ routeMLayerBoxIntegral M c' 1`, with
>   `routeMLayerBoxIntegral M c' 1 = ∫_{A ∈ paramsBoxM M 1} frobSq(prod M A)^(−c')` the full-chain box.
>   Hypotheses: `u ≤ M 0` (to place the `u` pivot rows via `Fin.castLEEmb : Fin u ↪ Fin (M 0)`).
> - **Proved.** The inequality in `ℝ≥0∞` for every real `c'`, threshold-independent. Route (all banked):
>   un-free the Schur loss (`chartInner_schurShearFree_eq` + `frobSq_schur_split_inv`), block-reindex the
>   front box to the raw factor over `matBox ∩ pivotChart` (`chartInner_blockReindex_eq_of_emb`), drop the
>   pivot chart (`IsUnit P`) and the shell (both monotone, nonneg integrand), reassemble `(A₀,A')` to
>   `Params M` (`paramsHeadSplit` MP + `prod_headSplit`).
> - **Assumed.** `u ≤ M 0` only. No shell/threshold assumption (the bound is unconditional in `c'`).
> - **Cited.** none.
> - **Deferred.** none (this inequality is complete).
> - **Status.** sorry-free; axiom-clean `[propext, Classical.choice, Quot.sound]` (forced `#print axioms`).

---

> **Claim (finiteness at T1, general M — CONDITIONAL).** For `0 ≤ c' < carrierThreshold M = ½·minAdm M`
> and the full-chain box finiteness `RouteMBoxThresholdFinite M`, the head-split spine integrand is finite.
>
> - **Lean:** `DLNFibre.DLN.RLCT.shellSpineIntegrand_lt_top_of_box` (@ `e7b759ad6`)
> - **Gloss.** `(hu : u ≤ M 0) (hc0 : 0 ≤ c') (hc' : c' < carrierThreshold M)
>   (hbox : RouteMBoxThresholdFinite M) → shellSpineIntegrand M u κ ε r jf c' < ⊤`.
> - **Proved.** finiteness for `c' < T1`, GIVEN `hbox` — via the subset bound + `hbox ⟨c',hc0⟩`.
> - **Assumed.** `RouteMBoxThresholdFinite M` — the named full-chain analytic gap:
>   `∀ c' < ½·minAdm M, routeMLayerBoxIntegral M c' 1 < ⊤`. For `L ≥ 1` this is the recursion's own
>   top-level goal (the paper's codim result), NOT independently banked in-repo. It is a carried
>   hypothesis, named here, not buried.
> - **Cited.** none.
> - **Deferred.** the L≥1 discharge of `RouteMBoxThresholdFinite M` (the capstone induction / cited Aoyagi
>   codim). Also NOT delivered: the reduced-comparator DOMINATION form (`deeperFlag_shell_le` / Brick D)
>   that the capstone's L≥1 recursion needs — this subset bound is circular for that induction (see caveat).
> - **Status.** sorry-free; axiom-clean.

---

> **Claim (finiteness at T1, L=0 leaf — UNCONDITIONAL).** For a 3-width chain `M = (M 0, M 1, M 2)` and
> `0 ≤ c' < ½·minAdm M`, the head-split spine integrand is finite.
>
> - **Lean:** `DLNFibre.DLN.RLCT.shellSpineIntegrand_lt_top_leaf` (@ `e7b759ad6`)
> - **Gloss.** `(M : Fin (0+1+1+1) → ℕ) … (hc' : c' < carrierThreshold M) → shellSpineIntegrand … < ⊤`,
>   with the full-chain box finiteness discharged by the banked `routeMBoxThresholdFinite_mnp`.
> - **Proved.** UNCONDITIONAL finiteness at the 3-width leaf for `c' < T1` (`M = ![M 0, M 1, M 2]` by
>   `funext; fin_cases`, then `routeMBoxThresholdFinite_mnp (M 0) (M 1) (M 2)`).
> - **Assumed.** none beyond `u ≤ M 0`, `0 ≤ c'`.
> - **Cited.** none (`routeMBoxThresholdFinite_mnp` is proved in-repo, `RouteMSchurRectCapB`).
> - **Deferred.** none for L=0.
> - **Status.** sorry-free; axiom-clean.

---

## Structure & ideas observed (pen-and-paper + decorrelated Codex)

- **Un-free = frobSq of a block.** `freedSchurLoss x Γ Q = frobSq(B'·Q)` for the reconstructed front block
  `B' = [[P,B₁₂],[C,Γ+C·P⁻¹B₁₂]]` (banked `schurLoss_of_blockSplitD_symm_shift`). So the whole decorated
  spine object un-frees, per `A'`, to `∫_{B ∈ block box ∩ IsUnit P} frobSq(B·Q_sub)^(−c')` — exactly
  shelljhunt's `I_j`. This is the banked `chartInner_schurShearFree_eq` (EQUALITY, any `Q`).
- **Dropping `IsUnit P` is sound at T1** (a null-set enlargement; `det P = 0` is a hypersurface). The prior
  wall's divergence came from dropping the SHELL while chasing `T2`, not from dropping `IsUnit`
  (thresholdhunt + shelljhunt, decorrelated; own Codex xhigh `codex/rescope-answer.md` concurs on all
  load-bearing points).
- **Circularity (LOAD-BEARING caveat, next to the claim).** The subset bound reduces `shellSpineIntegrand(M)`
  to `routeMLayerBoxIntegral M` = the chain-`M` box. Summed over the shell cover this is vacuous
  (`box ≤ Σ_j shell ≤ (r+1)·box`), so it does **NOT** advance the box-finiteness induction and does **NOT**
  supply the reduced-comparator domination the capstone's L≥1 recursion needs. It closes the STATED
  per-shell finiteness target (L=0 unconditional; L≥1 conditional on the named gap); the capstone's L≥1
  reduced-comparator domination remains the strong-minor stratification (Brick D `headSplit_domination`).

## Route (formaliser)

Compose banked atomic reductions per `A'` (`shellSpine_inner_le_matBox`), then drop the shell and
reassemble the bare box (`tailFront_box_eq_layerBox`), then instantiate finiteness from
`RouteMBoxThresholdFinite` (general / mnp-leaf). No new analytic content — measure/matrix plumbing only.
