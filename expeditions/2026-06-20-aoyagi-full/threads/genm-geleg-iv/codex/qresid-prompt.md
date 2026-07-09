<task>
Lean 4 / Mathlib v4.29, DLNFibre. I am porting the L=2 "residual qₑ" of a Schur corner-elimination
chart to general L. I need the cleanest DEFINITION of `qResidGen` and the proof STRUCTURE of its
slice value. I already have the reindex/measure foundation (roleEquivGen, splitMPGen, coreParamsGen,
bChart_slice_reg_zero_gen) green.

## L=2 reference (proven)

- `qBlock C₀ py := blockFlatEquiv_L2 (splitHomeoL2.symm py) + C₀`  (a 2-layer block point).
- `qResidMat C₀ Br022 G py := Q.1.toBlocks₂₁ * G Q.2.toBlocks₁₁ * Q.2.toBlocks₁₂
       + Q.1.toBlocks₂₂ * Q.2.toBlocks₂₂ - Br022`   where Q = qBlock C₀ py.
   (= the ₂₂ corner of `recoverProduct Q − Br`, with `G` a bump-globalised `(·)⁻¹`.)
- `qResid ... := fun py => (EuclideanSpace.equiv _ _).symm (fun i => qResidMat py (finProdFinEquiv.symm i).1 (finProdFinEquiv.symm i).2)`.
- SLICE VALUE (`p=0`): `qResidMat C₀ Br022 G ((0), t) = prod (H-r) (coreParams(split.symm((0),t)) + coreShiftParam C₀)`.
  Proof: at the slice the 3 regular blocks of `blockFlatEquiv_L2(split.symm((0),t))` vanish
  (bChart_slice_reg_zero), so Q's reg corners = C₀'s; `G(C₀₁₁)=C₀₁₁⁻¹` (hGeval); the target rank-r
  Schur-zero `Br₂₂ = Br₂₁·Br₁₁⁻¹·Br₁₂` (hschur) cancels the Schur term, leaving the ₂₂-product
  `A0red·A1red = prod (H-r) (...)` via `prod_two_factor_L2`.

## My banked general-L pieces (all green, in `D1GeChart` / `D1GeBlockProd`)

- `schurChartRawGen C L : (s:ℕ) → Matrix (Fin r ⊕ Fin (n s)) (Fin r ⊕ Fin (n (s+1))) ℝ` — the packed
  Schur chart of an ℕ-indexed block chain `C` (`n s = H_s - r`). Its `.toBlocks₁₁/₁₂` at slot s are
  `(partProd C (s+1))₁₁/₁₂`; `.toBlocks₂₂ s = redFactorGen C s`; `.toBlocks₂₁` at 0 is `(partProd C L)₂₁`.
- `recoverProductGen Q last := fromBlocks (Q last)₁₁ (Q last)₁₂ (Q 0)₂₁
      ((Q 0)₂₁ * (Q last)₁₁⁻¹ * (Q last)₁₂ + blockDiagProd Q (last+1))`.
- `blockDiagProd Q k := (Q 0)₂₂ * … * (Q (k-1))₂₂` (ordered ₂₂-corner product; `=1` at k=0).
- `blockDiagProd_schurChartRawGen : blockDiagProd (schurChartRawGen C L) k = redProd C k`.
- `blockSchur_partProd_asym_fold C (last+1) hPart : blockSchur (partProd C (last+1)) = redProd C (last+1)`
  (the asymmetric telescope; `blockSchur M = M₂₂ − M₂₁·(Ring.inverse M₁₁)·M₁₂`).
- `recoverProductGen_schurChartRawGen : recoverProductGen (schurChartRawGen C (last+1)) last
      = partProd C (last+1)` (given all prefix pivots invertible).
- genChain bridge (`D1GeBlockProd`): `genChain H r hr ι hι v : (s:ℕ) → Matrix (Fin r ⊕ Fin (dcw s − r)) …`
  is the ℕ-block-chain of `v : Params H`; `reindex_prod_eq_genPartProd : reindex … (prod H v) = partProd (genChain …) L`;
  `genPartProd_toBlocks₁₁ : (partProd (genChain …) k)₁₁ = (prodAux H v k).submatrix (ι 0) (ι ⟨k,·⟩)`.
- `coreParamsGen x s = (blockFlatEquivGen H r ι hι x s).toBlocks₂₂` (per-layer ₂₂), and
  `prod (H-r) (coreParamsGen x)` is the ordered product of those ₂₂ corners.

## The question

I must define `qResidGen (ι hι hL) (C₀ : block-chain-base) (Br022) (G) : (reg×(core×spec)) → EuclideanSpace ℝ (Fin ((H 0 - r)*(H (last L) - r)))`,
its `ContDiff ℝ 1` (given `ContDiff ℝ 1 G`), and prove the SLICE VALUE
`qResidMatGen ((0),t) = prod (H-r) (coreParamsGen(split.symm((0),t)) + coreShiftParamGen C₀)`.
The residual is the ₂₂ of `recoverProductGen (chart of the block chain of split.symm py + C₀) − Br`,
with `G` for the pivot inverse.

<output_contract>
1. The DEFINITION of `qBlockGen`/`qResidMatGen` for general L: what exactly is the block chain fed to
   the chart (blockFlatEquivGen point + C₀, bridged to the ℕ-chain how?), and is `qResidMatGen` best
   written as `(Q 0)₂₁·G((Q last)₁₁)·(Q last)₁₂ + blockDiagProd Q (last+1) − Br022` with
   `Q = schurChartRawGen (chainOf py) L`, OR directly `blockDiagProd (chainOf py) L + [Schur term] − Br`
   without the chart wrapper? Which minimizes the ContDiff + slice proofs? Give the exact def.
2. The `ContDiff ℝ 1` structure: which factors are `C^∞` (chart entries) vs `C¹` (G∘pivot), and the
   key point — is `blockDiagProd Q (last+1)` (an L-fold matrix product of chart ₂₂ entries) `C^∞`
   entrywise by induction on `last`? Sketch the induction.
3. The SLICE-VALUE proof: at p=0, how does `blockDiagProd (chainOf ((0),t)) (last+1)` become
   `prod (H-r) (coreParamsGen + shift)`? Is it a direct `blockDiagProd = prod`-telescope induction
   (chart ₂₂ = layer ₂₂ = coreParams+shift at the slice), and does the Schur term cancel `Br` exactly
   as in L=2? Name the general-L analogue of `prod_two_factor_L2` (does a `blockDiagProd = prod` lemma
   exist, or must I prove `prod (H-r) A = blockDiagProd (chain-of A) L` by induction)?
4. The single biggest risk/trap in the general-L version vs L=2 (the ℕ-chain ↔ Fin L bridge casts?
   the `last = L-1` vs `L` indexing in recoverProductGen? the invertibility hypotheses for the chart?).
</output_contract>

<grounding_rules>
Flag any lemma name you are unsure exists in v4.29 as "verify". Distinguish defeq from needs-a-lemma.
Do not invent lemmas; if the general-L `blockDiagProd = prod` telescope doesn't obviously exist in my
banked list, say so and give the induction to prove it.
</grounding_rules>
</task>
