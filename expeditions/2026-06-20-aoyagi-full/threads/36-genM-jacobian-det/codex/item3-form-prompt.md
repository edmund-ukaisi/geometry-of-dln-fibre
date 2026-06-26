# Lean 4 / Mathlib — the CLEANEST formulation of an item-3 map equality (avoid an intractable entry-match)

GOAL: prove `phiFlat_abs_det : |det (fderiv φ_flat u)| = ∏_j |u_j|^{leafH j}`. I have BANKED sorry-free:
- `phiFlat_abs_det_of_factored`: given `composeFold fs = φ_flat` (item-3) + per-factor det product =
  leafH monomial (item-4), concludes the det. (composeFold = foldr (F.f ∘ ·) over ChartFactors.)
- the structured decoder `genBlkFlatStruct : GenBlk M t` (reads K/X/N/E/W from DISJOINT flat slots via
  chartIdxEquiv; derives Bmat=[K;XK], Rmat=[[0,0],[0,E]] so C_s = Schur frame; Bmat 0=I).
- `phiFlatStruct u = paramsEquivFlat M (chartParamsGen u M t genBlkFlatStruct hle)` + its UNCONDITIONAL
  rate `routeMCore(phiFlatStruct u) = u²·V` ∀M.
- item-2 ChartFactors: radialFactor, lduChartFactor E, schurChartFactor E, chainChartFactor N E —
  each = conjBlockFactor E (block map) (block fderiv), abs-det = banked monomial at (E u).1, for any
  CLE E : (Fin N → ℝ) ≃L[ℝ] Block × Rest.

STRUCTURES (opaque dependent widths):
- chartParamsGen u M t B hle : Params M, layer s:Fin L = reindex (chainOfMt.A s.val), where
  A k = chainA(N_k)(W_k)(C(k+1)), C k = Bmat k · chainQ(N_k) + u·Rmat k (interior), C L = u·Rfin L.
  chainA(h:t+c=M')(N)(W)(C) : Matrix(Fin M')(Fin m') = reindex(finSplit) of [C - N·W ; W] (rows
  t ⊕ (M'-t)). chainQ(h)(N) : Matrix(Fin t)(Fin M') = reindex of [I | N].
- paramsEquivFlat M : Params M ≃ᵐ (Fin (flatDim M) → ℝ) — a pure reshape/reindex (2× piCurry +
  funCongrLeft), measure-preserving, |det|=1.

THE CORE WORRY. composeFold fs is a COMPOSITION of full-ambient flat maps (each factor reads its block
from flat slots, acts, writes back). chartParamsGen is reindex of chainA-LAYERS. For `composeFold fs =
phiFlatStruct` I'd match the composed flat-factor output to paramsEquivFlat(chainA-layers) ENTRY-WISE.
But the factors (Schur/LDU) produce the GenBlk block DATA, while chartParamsGen ADDITIONALLY applies
chainA/chainQ to assemble layers. So composeFold would need a factor that performs the chainA assembly
too (the chainChartFactor?). I'm unsure the composition genuinely reconstructs the chainA layers, vs
just the block data.

QUESTIONS (be concrete, skeptical, pick the LEAST-painful route):
1. Is the honest item-3 target `composeFold fs = phiFlatStruct` provable as stated, or should I instead
   DEFINE φ_flat := composeFold fs from the start (make the chart BE the factored product) and prove its
   RATE via a separate decoder, rather than match two independently-defined maps? I already have the
   rate for phiFlatStruct (the chartParamsGen one). If I redefine the chart as composeFold fs, I'd need
   to re-derive the rate for IT — is that easier or harder than matching composeFold fs = phiFlatStruct?
2. Does composeFold of (radial, LDU_s, Schur_s, chain_s) ACTUALLY reconstruct paramsEquivFlat(chainA
   layers)? Specifically: the chainA layer A_k = reindex[C_{k+1} - N_k W_k ; W_k]. Which factor produces
   this? The chainChartFactor is (W,C) ↦ (W, C - N·W) — that's the [C-NW; W] assembly. But the OUTPUT
   layout (paramsEquivFlat's flat order) must match. Is the factor-composition → paramsEquivFlat-order
   correspondence the REAL content, and is it a clean per-layer reindex or a genuine permutation-matching
   nightmare?
3. Given I have the rate for phiFlatStruct ALREADY, is there a route to phiFlat_abs_det that DOESN'T need
   the full composeFold = phiFlatStruct, e.g.: compute fderiv(phiFlatStruct) directly as a product of
   per-layer CLMs (differentiating chartParamsGen ∘ genBlkFlatStruct layer-by-layer through chainA/chainQ
   — is chainA's fderiv tractable since it's affine-linear in the block data?) then det-telescope? chainA
   is LINEAR in (C, W) and chainQ is CONSTANT in N... so maybe fderiv(chartParamsGen ∘ genBlkFlatStruct)
   IS a clean product without the full factored-chart detour. Assess this "route a-prime".

Recommend the single least-painful route to phiFlat_abs_det. I value not starting a multi-week
entry-match if route a-prime (direct layer-wise fderiv of the structured chart) is cleaner.
