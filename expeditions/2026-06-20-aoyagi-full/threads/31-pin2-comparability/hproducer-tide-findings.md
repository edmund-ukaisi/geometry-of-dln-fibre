# hproducer tide — landed atoms + the verified (b)-gap structure

Tide on `aoyagi-full` (lean-formaliser). Target: complete `hproducer` (the last L2 body piece of
`framedParams_split_eq_frame_raw`). Outcome: **two sound banked atoms; `hproducer` itself NOT closed**
(its centerpiece is genuinely-open design work — see below). No fabrication, base stays green.

## Landed (NEW module `lean/DLNFibre/DLN/RLCT/Validate/DeepestEFullSregComparability.lean`)

All axiom-clean `[propext, Classical.choice, Quot.sound]` (NO `sorryAx`):

- `eventually_isUnit_of_continuous_eq_one` — **S5a abstract core** (network-free): a continuous
  matrix map `= 1` at a basepoint is `IsUnit` on a 𝓝. `Continuous.matrix_det` + `ContinuousAt.eventually_ne`
  + `Matrix.isUnit_iff_isUnit_det`.
- `continuous_block₁₁_map` — `w ↦ (reindex e₁ e₂ (P0·(prod((paramsEquivFlat).symm w)−B)·QL)).toBlocks₁₁ + 1`
  is continuous (CLE `symm` + a local copy of `continuous_prodAux` — the `LossContinuity` public copy
  is UNIMPORTABLE here: same-namespace `continuous_dlnLoss` collides with `DeepestGaugeChart`'s).
- `eventually_P00_invertible` — **S5a concrete**: the producer's `P00 := this block` is invertible on a
  𝓝 w0. At w0 `prod((symm) w0) = prod(deepestPoint) = B`, residual `= 0`, block `= 0`, `+1 = 1`.

**Controller action needed:** wire `import DLNFibre.DLN.RLCT.Validate.DeepestEFullSregComparability`
into `DLNFibre.lean` (single-writer; I did not touch it).

## The (b)-gap, structurally pinned (the input the next tide needs)

Codex `xhigh` (decorrelated, `codex/hproducer-route-{prompt,answer}.md`) flagged the load-bearing
unknown: are the gauge "reads" in `framedParamsPivot(split w)` last layer exactly the framed-raw last-
matrix entries in pivot order, or recomputed from core/gauge coords differently? **Verified from the
banked decode lemmas (`DeepestFrameRaw.readX/Y/Z_deepestSplit_raw` + `readT_deepestSplit_raw`):** ALL
FOUR reads (X, Y, Z, AND the T-core) decode to the SAME raw deviation `(paramsEquivFlat).symm (w − w0) s`,
placed at the four block positions. So the last-layer reconstruction is
`framedParamsPivot(split w) last = reindex(rThr.symm, pivotThr.symm)(fromBlocks reads)·Qf_last + corner`,
with the reads = the raw deviation reindexed by the PIVOT column split on the output side. Concretely the
corrected telescope is

    prod(framedParamsPivot(split w)) = P0 · prod(A w) · QL · Pπ,   Pπ a FIXED output column permutation

(NOT `P0·prod(A w)·QL` — `hS1'` refuted that; `Pπ` is the pivot-vs-threshold column relabel on the last
factor). This makes Codex's pointwise route **structurally plausible** (the `Pπ` is a fixed right-multiply
after the product, w-independent), CONTINGENT on the FACT2 identity
`reindex(rThr, pivotThr J)(M · Pπ) = reindex(rThr, rThr)(M)` applied to the DEVIATION ONLY (corner stays
in pivot convention — the soundness-critical trap).

## Why `hproducer` is NOT closeable this tide (honest)

The producer's conjunct (b) `δ₁·Sreg ≤ ∑deepestEFull² ≤ δ₂·Sreg` needs, IN LEAN:
1. the corrected telescope `prod(framedParamsPivot(split w)) = P0·prod(A w)·QL·Pπ` — **UNBUILT** (the
   only general-`w` framed-product lemmas banked are the `T=0`/zero-core prefix ones; the clean
   `endpoint_telescoping_eq` requires `C s = P s·A s·Q s` per layer, FALSE on the last layer here);
2. the FACT2 reindex identity — **UNBUILT** (asserted "VERIFIED" in the cert, but pen-and-paper only);
3. then it composes the BANKED `dlnLoss_two_sided_of_frame` / `conjugation_frobenius_comparable` /
   `frobenius_sq_eq_blocks` machinery (DeepestGaugeBlocks) — those ARE in place.

(1)+(2) are each several-hundred-LoC of new geometric work + the soundness-critical corner handling the
cert itself says to "verify BEFORE re-stating." Beyond a responsible single tide without fabrication.

The OTHER conjuncts are tractable but also new work: (c) leak (`eventually_leak`, bounded ⅟P00 +
`P01,P10→0`, ~100-180 LoC); (d)/(e) core folding (built S5c atom `schur_core_germ_comparability` +
`|∑Rcore²−coreΦ| ≤ C·Sreg` charge). (a) block-decomp is `fromBlocks_toBlocks` (free); invertibility is
now `eventually_P00_invertible` (banked).

## Recommended next-tide order
1. Build the corrected telescope (1) + FACT2 (2) — verify FACT2 numerically FIRST (Codex's L=2 test:
   H=(1,2,2), r=1, J0=1, two factorisations of B=[0,1], check `∑deepestEFull²` agree).
2. (b)-atom via the banked `conjugation_frobenius_comparable` on the two fixed reindexings.
3. `eventually_leak` (c); core folding (d)/(e); then assemble `U := ⋂` (finite ∩ of 𝓝).
The banked S5a (`eventually_P00_invertible`) + the loss-squeeze machinery (DeepestGaugeBlocks) are ready.
