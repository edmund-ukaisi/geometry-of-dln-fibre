# Item-3 SPEC — the general-M interior chart det route + the dependent-Fin-cast design (spec-first gate)

Branch `genm-interior` @bf6d22f6 (sub-tide 1 landed/pushed). This is the spec-first report on item-3 (THE
bottleneck) BEFORE deep-fill, with the architecture fork + the exact place the (3,3,3,3) pattern fails over
opaque widths. Decorrelated: Codex xhigh (`codex/interior-item3-arch-{prompt,answer}.md`).

## THE ARCHITECTURE FORK (resolved: Route A FUSED, B was the earlier composeFold plan — a bet I'd have lost)

The two banked worked instances use DIFFERENT det architectures, and this changes the item-3 plan from my
sub-tide-1 spec:
- **(4,4,2,2)** [pure-radial, trivial K-cores]: `phi4422 = Q4422 ∘ pb4422`, `pb4422 = pivotBlowupOn {0,1,2,3} 0`.
  A CLEAN 2-factor `composeFold`; det FREE via `composeFold_abs_det`. This is the only instance that fits the
  banked factor API.
- **(3,3,3,3)** [the ONLY t≥2 K-core instance]: `phi3333 = Q3333CLM ∘ Frame3333 ∘ Kparam3333`. NOT a fold:
  - `Q3333CLM` LINEAR (measure-preserving reshape, |det|=1);
  - `Kparam3333` the LDU lens (identity except free `(x1,x2,x3,x4) ↦ K-core `[x1,x1x2,x1x3,x1x2x3+x4]`;
    |det|=(x1)²; does NOT touch radial x0);
  - `Frame3333` a SINGLE FUSED bilinear map: the radial x0 is DISTRIBUTED across its output entries (ADDED in
    one diagonal `z0+bilinear`, MULTIPLIED into others `z0·z13`, `z0·z24`, …), fusing Schur + B/C chain +
    radial into one map. |det DFrame3333| = |z0|^5·|z9|^3·|z1z4−z2z3|^2 via a BLOCK-TRIANGULAR det
    (`BlockTriangular.det` over an SCC grading), NOT a telescope.
  Det via `LinearMap.det_comp`: |det Dφ3333| = 1·(z0^5 z9^3 (z1z4−z2z3)^2)·(x1)^2 → monomial after Kparam subst.

**Codex (xhigh) ranks A > B.** Route B (the composeFold-of-block-factors I brick-validated in sub-tide-1) is a
BET that the banked factor API describes a chart I do NOT have — the (3,3,3,3) chart fuses the radial into
Frame, so B needs a prior "radial-extraction" theorem (separate x0 into a pivotBlowupOn prefactor, make Frame
x0-free → a clean 4-fold). That separability is UNDECIDABLE abstractly; it requires verifying the x0-active-set
is consistent (no coord sometimes-scaled-sometimes-not, no bilinear needing x0 before an LDU/Schur subst).

**DECISION: Route A (FUSED), the honest generalization of the only nontrivial instance:**
`phiFlatLDU` (sub-tide 1, decoder-agnostic rate already banked for ANY reparam) is `phiGen (x p) (genBlk(reparam x))`,
which IS `paramsEquivFlat ∘ chartParamsGen` — the Q ∘ (structural) form. The det route:
  |det Dφ| = |det D(paramsEquivFlat)| · |det D(chartParamsGen∘reparam)|, the first = 1 (measure-preserving,
  generalize `Q3333CLM_abs_det`), the second = the general Frame_M ∘ Kparam_M block-triangular det.

## WHERE THE (3,3,3,3) PATTERN FAILS OVER OPAQUE WIDTHS (the exact dependent-Fin-cast hazard)

VERIFIED: the (3,3,3,3) chart NEVER touches `chartIdxEquiv` — `grep -c chartIdxEquiv RouteM3333*.lean = 0`. It
is built from literal `![…]` coordinate maps with `Fin 27` LITERAL indices; every step is `rfl` / `fin_cases` /
`ring`-decidable. The general decoder `genBlkFlatStruct` reads each block (K/X/N/E/W) through
`chartIdxEquiv.symm ∘ frameSplitEquiv.symm ∘ finProdFinEquiv`, and `chartIdxEquiv := finCongr … ∘
(Fintype.equivFin (ChartIdx)).symm` is **Classical.choice-based — NOT rfl-reducible** (RouteMChartIdxEquiv:82).

So: the (3,3,3,3) det reads K-entries by `rfl` from `Frame3333`'s literal `z 1, z 2, z 3, z 4`. The general
det must read K-entries through the OPAQUE `chartIdxEquiv` round-trip, computable ONLY by
`Equiv.apply_symm_apply` cancellation (the witness file's `readK_wInt` pattern: compose the chart's forward
read with the decoder's symm read so the round-trip cancels). The hazard: any det/fderiv computation that the
(3,3,3,3) instance does by `fin_cases`+`ring` becomes, at opaque width, a heterogeneous `Fin.cast` chain
through boundary-dependent block sizes (`Text(k+2)`, `Wext(k+1)−Text(k+2)`, …) that holds only
PROPOSITIONALLY after `frameSplitEquiv`/`finProdFinEquiv` `apply_symm_apply` + `Fin.cast` rewrites.

## THE BLOCK-TRIANGULAR DET ∀M (Codex-confirmed reachable; the cleaner grading)

`Matrix.BlockTriangular.det` IS abstract over an arbitrary finite index type + grading `b : m → α` (no
Fin-literal block sizes) — confirmed reachable for opaque widths. The hard obstruction is NOT the theorem; it
is (i) proving the opaque-width Jacobian's OFF-block entries vanish, and (ii) identifying each
`toSquareBlock b a` with the intended `Wext/Text k` block det. **Codex's cleaner route: a LAYER FILTRATION —
per-chain-layer diagonal-block det lemmas multiplied, block-triangular ONLY over the chain-LAYER grading (b =
which chain layer a coord belongs to), NOT a fine SCC grading.** This matches the chain's natural structure
(`Cgen`/`Agen` per-layer) and sidesteps the (3,3,3,3) bespoke SCC.

## SUB-TIDE PLAN (revised under Route A)
- **2a (item-1, the LDU reparam ∀M)**: define `reparam = kLDU` on the K-slots — read the K-slot coords (l,q,u)
  via `frameSplitEquiv`'s K sub-block and emit the LDU matrix `(1+lowMat l)·diag q·(1+upMat u)`, identity on
  non-K slots (incl. the pivot). The opaque-width generalization of `Kparam3333`. Its det = ∏_s ∏_i q_{s,i}^{…}
  (the LDU monomial per boundary). The dependent-Fin work: the K-slot index round-trip.
- **2b (item-3 core, the Frame_M structural map + its block-triangular det ∀M)**: `chartParamsGen` IS the
  structural map (no need to re-define Frame — `chartParamsGen` already assembles the chain layers). Prove
  `|det D(chartParamsGen ∘ kLDU)|` = the monomial via the LAYER-FILTRATION block-triangular det. THE bottleneck.
- **2c (Q det = 1)**: generalize `Q3333CLM_abs_det` — `paramsEquivFlat` is measure-preserving (banked
  `measurePreserving_paramsPack…`), so its det is 1. Cheap.
- **2d (cov)**: assemble |det Dφ| = monomial, injOn off the weighted-axis planes, n-fold null-slice add-back.
- **2e**: re-derive the interior witness for the kLDU decoder + the 4 fields + the new `interiorContractLDU`.

## RECOMMENDATION
The earlier composeFold plan (Route B, brick-validated in sub-tide 1) is SUPERSEDED for the t≥2 case: it needs
a radial-extraction that the fused (3,3,3,3) chart does not obviously admit. Route A (fused, generalize
phi3333 via chartParamsGen + the layer-filtration block-triangular det) is the honest route. The genuine
remaining bottleneck is 2b (the opaque-width block-triangular det of the chain's Jacobian). Recommend I
SPEC-FIRST 2b's layer-filtration grading + the off-block-vanishing in more detail (one more design pass /
possibly a pen-and-paper or Codex check on the exact grading) BEFORE deep-filling — it is the heaviest piece
and the (3,3,3,3) SCC grading does not transport. Confirm before I open 2b.
