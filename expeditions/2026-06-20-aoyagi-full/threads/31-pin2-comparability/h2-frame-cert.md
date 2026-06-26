# h2 frame adjudication — the formaliser is RIGHT: a REAL frame obligation (my h1-cert erred)

The h2 formaliser found a frame subtlety I under-addressed. **Adjudication: the formaliser is correct —
there IS a real frame obligation. My h1-cert's "work frame-free post-hconj" was an ERROR.** Decorrelated
Codex (xhigh) + my exact/numeric checks agree. This is an honest correction, not a paper-over. Read-only.

## The error in my h1-cert
I claimed: "`hS2_front` strips the frames ⇒ work frame-free; the cores are the rThr-blocks of raw
`(symm w)_s`." **That conflates two things.** `hS2_front`/`hconj` strip the frames from the PRODUCT
(`prod F = P0·prod(A)·QL`), but the producer's `Rcore = P11 − P10·⅟P00·P01` is the Schur of the FRAMED
`Mw = reindex(P0·(prod(A)−B)·QL)` (the `P00,P01,P10,P11` ARE the framed-product blocks from `hconj`,
`DeepestGaugeConstruction` line ~2655). **The Schur is NOT frame-invariant** — stripping the frames from
the product does NOT strip them from the Schur.

## The exact obstruction (verified)
- General gauge frames P0,QL do NOT preserve the global Schur: `Schur(P0·N·QL) ≠ Schur(N)`, even for
  block-diagonal P0,QL (the pivot inverse `M11⁻¹` transforms non-equivariantly). Verified numeric:
  `max|Schur(P0 N QL) − Schur(N)| ≫ 0` for ALL block structures (diag/lower/upper/general).
- Even the deepest-point block-triangular frames (P0 upper-tri from `deepestPoint_layer0_cols_vanish`,
  QL lower-tri from `_layerLast_rows_vanish`) do NOT give bounded comparability: `frobSq(Schur(P0 N QL))
  / frobSq(Schur(N))` is UNBOUNDED (`~5e7`) in the germ regime. So the framed `Rcore` is NOT comparable
  to the frame-free `S'_0(1−K)S'_1` via the frames.

So `schur_product_ldu` (frame-free) does NOT directly close the framed `Rcore`. **h2 has a real
obligation.** Codex: "if `Rcore` remains the framed Schur, there is a real missing obligation: prove a
frame-strip/cancellation lemma; medium, not cosmetic."

## The sound resolution (the route the producer MUST take)
The fix is NOT to relate the framed Schur to the frame-free Schur (they're incomparable). It is to
**apply the LDU to the FRAMED layers directly** — `schur_product_ldu`'s `C_s` should be `reindex(F_s)`
(the FRAMED layer blocks), NOT the raw `(symm A_s)` blocks. Then:
- `M̂w = reindex(prod F) = reindex(F_0)·reindex(F_1)` (reindex_mul), with `reindex(F_s) = fromBlocks
  Â_s Ŷ_s Ẑ_s T̂_s` the FRAMED layer's r⊕M blocks (`Â_s = (Pf_s·(corM+reads)·Qf_s)` reindexed, (1,1)-block).
- `schur_product_ldu` applied to these gives `Rcore = Ŝ_0·(1−K̂)·Ŝ_1` with the FRAMED per-layer Schurs
  `Ŝ_s = T̂_s − Ẑ_s·⅟Â_s·Ŷ_s`.
- **THE NEW OBLIGATION (h2'): `coreΦ = frobSq(Ŝ_0·Ŝ_1)`, NOT `frobSq(S'_0·S'_1)`.** I.e. lemma-1's cores
  must be the FRAMED Schurs `Ŝ_s`, not the frame-free `S'_s`. Check whether `deepestCoreAbsorb`/lemma-1
  use the framed or frame-free reads:
  - lemma-1's `schurCorrection_s = −readZ_s·(1+readX_s)⁻¹·readY_s` uses the RAW reads `readX/Y/Z` (the
    gauge-slot reads, frame-FREE — they're `regGaugeSlotEquiv` coordinates, NOT frame-conjugated).
  - h1's `Ŝ_s` (if reading `reindex(F_s)` framed blocks) uses the FRAME-CONJUGATED blocks `Â_s,Ŷ_s,…`.
  **So the cores MISMATCH: lemma-1 frame-free `S'_s` vs h1-framed `Ŝ_s`.** This is the real h2 gap.

## Two routes to close h2' (the controller's call)
**Route P (preferred — make `Rcore` frame-free):** the producer should NOT take the Schur of the framed
`Mw`. Instead: since `hS2_front` gives `prod F = P0·prod(A)·QL`, and the LOSS is `frobSq(reindex(P0·N·QL))`
which the leaf lemma `dlnLoss_two_sided_of_frame` ALREADY reduces to `Sreg + Score` with the FRAMED blocks
— BUT for the CORE identification, redefine the comparison so `Rcore` is the Schur of the FRAME-FREE
`reindex(prod(A)−B)` (apply LDU to the raw `(symm A_s)` layers, frame-free cores `S'_s` = lemma-1's
cores). Then h2 is clean. **The catch:** the leaf lemma's `hconj` produces FRAMED blocks; relating the
frame-free Schur to the framed `Score` the leaf lemma uses needs... the SAME frame-cancellation. So
Route P moves the obligation, doesn't remove it.

**Route Q (the honest obligation — a framed-Schur core lemma):** prove `frobSq(Ŝ_0·Ŝ_1) ≍
frobSq(S'_0·S'_1)` (framed vs frame-free per-layer Schur PRODUCTS, in-sum with Sreg) OR re-point lemma-1's
`deepestCoreAbsorb` to use the FRAMED reads `Ŝ_s`. The framed per-layer Schur `Ŝ_s = Schur(Pf_s·(corM+reads)
·Qf_s)` — is the PER-LAYER Schur frame-invariant? UNLIKE the global Schur, the per-layer frames Pf_s,Qf_s
act on a SINGLE layer, and the per-layer Schur MIGHT be frame-covariant in a cleaner way (the deepest
per-layer frame brings the layer to corM, a rank-r normal form). **This is the precise unresolved point —
I could NOT settle whether the per-layer framed Schur Ŝ_s relates cleanly to the frame-free S'_s.**

## HONEST EFFORT READ — h2 is HEAVIER than my cert said
- My cert: "h2 CLEAN." **WRONG.** h2 has a real frame obligation (framed vs frame-free Schur cores).
- Codex: "medium, not cosmetic; needs explicit block formulas + hypotheses on P0,QL."
- The genuine sub-question (per-layer framed Schur Ŝ_s vs frame-free S'_s) is NOT settled — it needs
  either the per-layer frame structure (does Pf_s,Qf_s preserve the per-layer Schur up to the corM
  normal form?) or a re-pointing of `deepestCoreAbsorb` to the framed reads.

**Estimate: MEDIUM (not cosmetic, not a wall) — ~1-2 tides for the framed-vs-frame-free per-layer Schur
reconciliation, IF the per-layer frame structure is clean; potentially more if it needs a new
frame-covariance lemma.** I recommend a FOCUSED follow-on: adjudicate the per-layer framed Schur `Ŝ_s`
vs `S'_s` (the deepest per-layer frame is the rank-r normal-form frame — does it preserve the per-layer
Schur?). That is the load-bearing unresolved point.

## What I CAN confirm (the parts of my prior cert that STAND)
- h1's `reindex_mul` + `fromBlocks_multiply` + `schur_product_ldu` structure is correct — it gives
  `Rcore = Ŝ_0(1−K̂)Ŝ_1` for the FRAMED layer blocks. (The LDU itself is frame-agnostic — it just needs
  Â_s invertible.)
- The `⅟Â_s` in the LDU IS the (1,1)-block inverse of the framed layer — and lemma-1's `⅟(1+readX_s)`
  is the FRAME-FREE one. **These DIFFER** (this is the correction: my "⅟A_s match" was for the frame-free
  case; with framed Â_s ≠ 1+readX_s, they don't match without the frame reconciliation).

## Net (honest)
**The formaliser is right; h2 is NOT clean.** My h1-cert erred in claiming the frames strip from the
Schur. The real obligation: reconcile the FRAMED per-layer Schur `Ŝ_s` (from h1's `reindex(F_s)` LDU)
with the FRAME-FREE `S'_s` (lemma-1/`deepestCoreAbsorb`). The global Schur is NOT frame-comparable
(unbounded), so the reconciliation MUST be at the per-layer level (where the deepest frame is the rank-r
normal-form frame — possibly clean, NOT verified). **Recommend: pause the h2 core-match build; a focused
adjudication of the per-layer framed-vs-frame-free Schur is the next step** (I can take it). NOT a wall,
but a real MEDIUM obligation my prior cert missed.

## Files
- `/tmp/h2_frame.py` (global Schur NOT frame-invariant), `frame_blocktri.py`/`frame_correct.py` (the
  block-tri frames don't give bounded comparability — unbounded ratio). `codex/h2-frame-{prompt,answer}.md`
  + `/tmp/h2frame_codex/answer.md` (Codex: real obligation, medium).
