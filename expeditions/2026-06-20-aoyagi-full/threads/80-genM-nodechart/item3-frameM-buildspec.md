# Frame_M BUILD-SPEC — the fused frame + DFrame_M + block-tri det (Route b, for the gate)

Branch genm-interior @ff6344fc; capstone on origin/genm-routeb (RouteMLayerGrade, b-0(i) PROVEN
sorry-free: Agen_genBlkFlatStruct_reads_le = the off-block-vanishing, LOWER-triangular under bLayer).
This specs the under-scoped substantial piece: Frame_M / DFrame_M + its block-tri det ∀M, for genm-mapeq.

## THE KEY DESIGN MOVE (avoid re-writing Frame3333's bilinear entries at opaque widths)
The (3,3,3,3) precedent is `phi3333 = Q3333 ∘ T3333`, `T3333 = Frame3333 ∘ Kparam3333` a HAND-WRITTEN
flat bilinear map `Fin 27 → Fin 27 → ℝ` with explicit entries — does NOT transport to opaque widths.
INSTEAD, define Frame_M ABSTRACTLY as the flat structural map, NOT entrywise:
  **Frame_M x := paramsPack.symm (chartParamsGen (x p₀) (decoder x) hle)**  : (Fin N → ℝ) → (Fin N → ℝ)
where paramsPack : (Fin N → ℝ) ≃ Params M is the reshape (the pack3333 generalization, banked as part of
paramsEquivFlat = paramsPack composed with the layer-flatten). Equivalently the chart is
  phiFlatLiveR1 ∘ kLDU = paramsEquivFlat ∘ chartParamsGen(decoder) = Q_M ∘ Frame_M ∘ (kLDU absorbed in decoder),
with Q_M = paramsEquivFlat ∘ paramsPack (LINEAR, measure-preserving ⟹ |det Q_M| = 1, generalize
measurePreserving_Q3333CLM). DFrame_M := fderiv ℝ Frame_M. NO hand-written entries.

## DFrame_M BLOCK-TRIANGULARITY INHERITS THE PROVEN b-0 LOCALITY (the crux — no entry-by-entry re-proof)
The block-tri off-block-vanishing of DFrame_M is NOT re-derived entrywise; it FOLLOWS from
Agen_genBlkFlatStruct_reads_le (capstone) by the calculus fact "a function constant in x_q has
∂/∂x_q = 0":
- bLayer (RouteMLayerGrade): the grading; the chart's output coord at flat-slot q' has layer bLayer q'.
- Frame_M's output coord at layer s (= a flattened Agen s entry) is INVARIANT under changing x at layers
  > s (Agen_genBlkFlatStruct_reads_le: Agen s reads only layers ≤ s). [Note: must lift Agen-locality
  through paramsPack.symm — paramsPack is a fixed reshape, so the flat-output coord at layer s = a fixed
  Agen-s entry; the reshape is layer-preserving by construction (chartIdxEquiv/pack share the boundary
  index). Spec a `paramsPack_layer` lemma: pack-slot ↔ chartIdxEquiv-slot preserves bLayer.]
- ⟹ the partial derivative ∂(Frame_M output, layer s)/∂(x_q, layer > s) = 0 — the off-block-vanishing,
  LOWER-triangular under bLayer (toDual): bLayer q > s ⟹ DFrame_M entry (output s, input q) = 0.
  Lean: `HasFDerivAt.congr`/`fderiv` of a locally-constant-in-x_q function is 0 in that coord — or, since
  Frame_M is a polynomial map, the fderiv entry = the partial, and locality ⟹ the partial is 0. The
  cleanest: prove `DFrame_M`'s toMatrix' is BlockTriangular bLayer (toDual) by: entry (i,j) with
  bLayer j > bLayer i is ∂(output_i)/∂(x_j), and output_i (layer bLayer i) is constant in x_j (layer
  bLayer j > bLayer i) by the capstone ⟹ the entry is 0.

## THE DIAGONAL BLOCKS (b-2: VERIFY-2, per-layer det = |det K_s|^{r+c} · radial)
The toSquareBlock at layer s = DFrame_M restricted to (output layer s, input layer s) = the within-layer
Schur frame derivative (C(s+1) FROZEN — the off-diagonal coupling is the layer-(s+1) input, excluded from
the layer-s diagonal block). Its det:
- the Schur-frame block: |det K_s|^{r_s+c_s} (banked schurFrame_abs_det), K_s read at boundary-s's frame
  slot ALONE (VERIFY-2 ✓, K_s single-layer — the capstone's reader-locality confirms).
- the LDU pivots (from kLDU, the lduChartFactor diagonal monomial) + the radial pivot (the pivotBlowupOn /
  radialFactor exponent, active.card−1 = minAdm−1 at the pivot's layer).
  [The radial u-scaling threads via u·Rmat across layers (genm-budget's affine-in-u); its degree minAdm−1
  is the card-bridge (RouteMCardBridge, banked). The leafH = the per-layer diagonal dets assembled.]

## b-3: ASSEMBLE via Matrix.BlockTriangular.det + the det_comp telescope
- |det DFrame_M| = ∏_{s ∈ image bLayer} det(toSquareBlock bLayer s)  [Matrix.BlockTriangular.det, toDual]
  = ∏_s (|det K_s|^{r+c}·LDU/radial) = ∏_j |u_j|^{leafH j} (the leafH bookkeeping, leafH_prod_eq-style).
- |det Dphi| = |det Q_M| · |det DFrame_M| · |det DKparam| = 1 · (monomial) · (LDU monomial), via the banked
  listProd_clm_abs_det / general_composed_clm_abs_det telescope (full-ambient, no casts) on the det_comp
  chain Q_M ∘ Frame_M ∘ Kparam (or kLDU absorbed). Feeds interiorDet_of_factored-style → the cov field.

## THE OPAQUE-WIDTH toSquareBlock REINDEX (b-1, the cast surface)
`Fin (blockSize_s) ≃ {i // bLayer i = s}` via Finset.card_equiv / the pivotBlowupOnDeriv_det Equiv.swap+
card pattern (NOT literal e_k). blockSize_s = #(layer-s slots) = schurDim s + (s+1<L? liftDim s : 0)
(the chartIdxEquiv per-boundary slot count, banked card_chartIdx-shape). This is the one genuine
cast-surface piece; the locality (b-0) + the diagonal dets (b-2, banked) are cast-light.

## THE LIVE-DECODER FLAG (genm-mapeq's scope note — carry the locality to genBlkFlatLiveR1)
The capstone is for genBlkFlatStruct. The live decoder genBlkFlatLiveR1 differs by (i) the Rmat-pivot
Function.update at FIXED layer p* (det-preserving — overrides one slot at a fixed layer, same locality),
(ii) the Rfin leaf at FIXED layer L−1 (the live leaf, fixed layer). BOTH are at FIXED layers, so the
SAME locality (Agen reads layers ≤ s) carries: prove `Agen_genBlkFlatLiveR1_reads_le` by the SAME block-
locality lemmas (genBlkFlatLiveR1's Bmat/Nblk/Wblk = genBlkFlatStruct's; Rmat differs only at the fixed
p* via Function.update_of_ne for s ≠ p*, and AT p* the fixed pivot is layer-p* local; Rfin at L−1 fixed).
The capstone's structure transfers verbatim with the Function.update/Rfin-fixed-layer handling.

## BUILD ORDER (gate this) + RISK
b-FrameM-1: Frame_M / Q_M defs + Q_M det = 1 (generalize measurePreserving_Q3333CLM) + the paramsPack_layer
  lemma (reshape preserves bLayer). [cast-light, banked-pattern]
b-FrameM-2: DFrame_M = fderiv Frame_M + HasFDerivAt (Frame_M is a polynomial map — fun_prop / the
  chartParamsGen entrywise polynomial; the (3,3,3,3) T3333_hasFDerivAt pattern). [moderate]
b-FrameM-3: DFrame_M block-tri (toDual bLayer) INHERITING Agen_genBlkFlatStruct_reads_le (+ the live
  version). [the locality is PROVEN; this lifts it to the fderiv — the off-block-vanishing of a
  locally-constant coord]
b-FrameM-4: the toSquareBlock reindex (b-1) + the diagonal dets (b-2) + assemble (b-3).
RISK: b-FrameM-3 (lifting Agen-locality to the fderiv block-tri — the "constant-coord ⟹ zero-partial"
  step over opaque Fin (Wext k)) + b-FrameM-1's paramsPack_layer (the reshape-preserves-layer lemma). Both
  cast-light-ish (the hard soundness — the off-block-vanishing — is ALREADY PROVEN at the value level).
  The genuine cast-surface is b-1 (toSquareBlock reindex). Frame_M-as-abstract (not entrywise) is the key
  cast-avoiding move — do NOT hand-write Frame_M's bilinear entries.
