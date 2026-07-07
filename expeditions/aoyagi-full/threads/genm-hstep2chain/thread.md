# genm-hstep2chain — the #120 `hstep2` chain-lock

Branch `genm-hstep2chain` off `genm-hstep2conj` (@83f7bbb0). Task: lock the general-`L` framed chain
`C`, prove `blockSchur (partProd C L) = ScoreSchur`, `Kcoup C 0 = 0`, then discharge the two germs
(`huntwist`/`hreginv`) that the banked `deepest_diffeo_bridge_gen_impl` reduces `hstep2` to.

## VERDICT — the chain SNAGS at the BRIDGE level (STOP-and-report, per task instruction)

**The banked `deepest_diffeo_bridge_gen_impl` reduces `hstep2` to a germ `huntwist` that is FALSE
(unsatisfiable) as stated.** The reduction is a *faithful implication* (huntwist + hreginv ⟹ hstep2 —
machine-verified by the reduction reviewer), but it is a *sufficient* condition that cannot be met,
because `hstep2`'s RHS (the wiring's `Φcore`) is built on the **NAIVE** `deepestCoreAbsorb`, and no
admissible single per-layer left-shear `Ψ` can carry the naive cores to the Score.

### The exact obstruction

- `hstep2:1060` (L≥3 arm) target RHS: `rlctAtOn (Sreg + deepestCoreF (coreAbsorb (split x)).2.1)`,
  with `coreAbsorb = deepestCoreAbsorb` — the NAIVE cutoff Schur shear (`DeepestGaugeConstruction:812`
  binds `set coreAbsorb := deepestCoreAbsorb`).
- `deepestCoreAbsorb = coreShearHomeo schurCutoffShift`, and `schurCutoffShift = χ·schurShiftRaw` uses
  the **naive** `schurCorrection = −Z_s·(1+X_s)⁻¹·Y_s` (pivot `1+X_s`). So (banked lemma
  `deepestCoreF_coreAbsorb_eq_prodSchur`, `DeepestGaugeConstruction:1945`):
  `deepestCoreF (coreAbsorb q).2.1 = frobSq(prod_s (S^naive_s))`, `S^naive_s = t_s − Z_s(1+X_s)⁻¹Y_s`.
- The banked bridge's `Ψ = deepestPsiCoreShear K` (`DeepestPsi:42`) applies a per-layer LEFT shear
  `S_s ↦ (1−K_s)·S_s`. So `huntwist ⟺ frobSq(prod_s ((1−K_s)·S^naive_s)) = Score x`.
- `Score x = frobSq(blockSchur(reindex(prod(decode x))))` = `frobSq(prod_s ((1−K̂_s)·S^conj_s))`
  (banked `schur_product_ldu_rec` on the HONEST chain `Ĉ_s = reindex(decode_s)`, pivot
  `deepBlkA_s + X_s`, cores `S^conj_s = T̄_s − Ẑ_s(deepBlkA_s+X_s)⁻¹Ŷ_s`).
- **`S^naive_s ≠ S^conj_s`** (pivot `1+X_s` vs `deepBlkA_s+X_s`, `deepBlkA_s ≠ 1` at the boundary —
  discriminator `deepBlkA=3`), and they differ at **first order in the reads**
  (`Ẑ_s deepBlkA_s⁻¹ Ŷ_s − Z_s Y_s ≈ (deepBlkZ_s deepBlkA_s⁻¹ − Z_s)Y_s = O(read)`, deepBlk O(1)).
- A continuous `K` with `K_s(0)=0` has `(1−K_s)=1+o(1)`, so it CANNOT change the leading homogeneous
  term of the product germ. Hence `frobSq(prod((1−K)S^naive))` and `Score` have different leading
  quadratic parts near `wstar` ⟹ `huntwist` fails in every neighborhood, for EVERY admissible `K`
  (whether `Kcoup(honest chain)`, `Kcoup(naive chain)`, or any free coupling).

### Triple confirmation

1. **Numerical** (`codex/chain_lock_check.py`, L=2, r=1, scalar cores, `deepBlkA_0=3, deepBlkA_1=2`):
   - `schur_product_ldu_rec` (honest chain): `coreProd == ScoreSchur` — **True** (banked recursion is sound).
   - `prod((1−K̂)·S^naive)` (honest `Kcoup` + naive cores) = **0.1816 ≠ Score 0.0651**.
   - naive chain `blockSchur(∏ fromBlocks(1+X,Y,Z,t))` = **0.2119 ≠ 0.0651** (the W-a falsity, reproduced).
2. **Repo's own L2 docstring** (`DeepestSchurShiftConj:33-43`): *"the bare `psiSplitRawL2` is tuned to
   the bare pivot `1 + gaugeReadX` (numerically verified: bare-ψ + conj-absorb ≠ Score), so Step Ψ needs
   a CONJUGATED joint move"* — the L2 proof is `hstep2 = Step Θ ∘ Step Ψ_conj`, using
   `deepestCoreAbsorbConj` (honest pivot) in Ψ and a separate Step Θ.
3. **Decorrelated Codex xhigh** (`codex/huntwist-satisfiability-{prompt,answer}.md`): VERDICT NO,
   confidence 0.9, matrix-general germ argument; AGREES the fix is conjugate-core Ψ + Step Θ.

## The correct route (what the general bridge MUST mirror — the L2 template)

`hstep2` for L≥3 needs the SAME two-step the L2 arm uses (`DeepestDiffeoBridgeL2Conj`):
- **Step Θ (general)** — `rlctAtOn(Sreg + coreF∘bareAbsorb) = rlctAtOn(Sreg + coreF∘conjAbsorb)`, the
  general analog of `rlctAtOn_coreF_bareAbsorb_eq_conjAbsorb` (`DeepestSchurShiftConj:439`). CHAIN-FREE:
  the MP core-shear `Θ = coreShearHomeo(schurCutoffShiftConj − schurCutoffShift)` (det-1,
  basepoint/reg-fixing; `rlctAtOn_comp_homeomorph`, NO derivative). `schurCutoffShiftConj`,
  `deepestCoreAbsorbConj` already exist (L2 files); needs a general-`L` continuity+basepoint (the L2
  `contDiff_schurCutoffShiftConj` is L2-scoped but the MP route needs only continuity).
- **Step Ψ_conj (general)** — `rlctAtOn(Sreg + coreF∘conjAbsorb) = rlctAtOn Φscore`, the CONJUGATE
  per-layer shear on the honest cores `S^conj`. **This is where the chain-lock lives**:
  `blockSchur(partProd Ĉ L) = ScoreSchur` with `Ĉ_s = reindex(decode_s)` — TRUE via
  `schur_product_ldu_rec` + `reindex_mul_split` telescoping (confirmed numerically, check #1).

So `deepest_diffeo_bridge_gen_impl` as banked is structurally insufficient: it does a single Ψ step with
the WRONG (naive) coreAbsorb and no Step Θ. **Controller decision needed** (boundary move): either
(a) re-cut `deepest_diffeo_bridge_gen_impl` to use `deepestCoreAbsorbConj` in `huntwist` + add a general
Step Θ, or (b) build a fresh general two-step bridge. The chain-lock (`blockSchur(partProd Ĉ L) =
ScoreSchur`) is the honest input to (the Ψ_conj part of) either.

## LOCKED CHAIN (the key deliverable)

The chain that wins: **`Ĉ_s = reindex_{eR_s, eR_{s+1}}(decode layer s)`** — the reindexed decode layers,
`(1,1)`-pivot the HONEST `deepBlkA_s + gaugeReadX_s` (NOT the naive `1 + gaugeReadX_s`). Its
Schur-product identity `blockSchur (partProd Ĉ L) = ScoreSchur` (unframed Schur of `reindex(prod decode)`)
holds by the banked `schur_product_ldu_rec` + `reindex_mul_split`; the frame-strip/corner to the framed
`Score` are the banked general `schur_frame_transform` + `rcore_eq_schur_of_corner_split`. It is consumed
by the Ψ_conj (conjugate-core) step, NOT by the banked naive-core bridge.

## Delivered (Lean, sorry-free)

- `Kcoup_zero : Kcoup C 0 = 0` + helper `toBlocks₁₂_one` — `DeepestSchurRecursion.lean` (the abstract
  chain algebra; reusable by any chain route, naive or conjugate). Makes the `coreProd` front factor
  `1 − Kcoup C 0 = 1`, so `∏_s (1−K_s)·S_s` telescopes to `coreProd C L`. Built green (module builds,
  5.7s), `scripts/sorries` = 0 in the file.

NOT done (correctly deferred — building on the false germ was declined per the task's STOP instruction):
the full DLN chain definition + `partProd Ĉ L = reindex(prod decode)` (the `Fin L↔ℕ` cast work), pieces 4
(`K`), 5a (`huntwist`), 5b (`hreginv`), the wire. `hstep2:1060` sorry left UNTOUCHED (not laundered).
