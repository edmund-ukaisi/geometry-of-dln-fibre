<task>
Lean 4 / Mathlib v4.29. Follow-up to a prior consult (architecture A′ confirmed sound; my discriminating
check PASSED: with codomain pivot-twist eJ, toBlocks₁₂ of reindex eR eJ ((reindex eR.symm eJ.symm
(fromBlocks 0 Y 0 0)) * Q) = Y * (reindex eJ eJ Q).toBlocks₂₂). Now I need the LOCALIZATION decision
that determines whether the API migration is ~200 or ~600 LoC. Do NOT write Lean — design judgement only.

## The objects
- `framedLayer H r hr s P Q X Y Z T : Matrix (Fin (H s.castSucc)) (Fin (H s.succ)) ℝ`
    := reindex (rThresholdSplit r (H s.castSucc)).symm (rThresholdSplit r (H s.succ)).symm (fromBlocks 1 0 0 0)
       + P * reindex (rThresholdSplit r (H s.castSucc)).symm (rThresholdSplit r (H s.succ)).symm (fromBlocks X Y Z T) * Q
- `framedParamsReg ... p : Params H` := fun s => framedLayer ... (readX p s) (readY p s) (readZ p s) 0
- `deepestEPivot ... Pf Qf p : Fin nReg → ℝ` reads the 3 residual blocks of
    P := reindex (rThresholdSplit r (H 0)) (rThresholdSplit r (H last)) (prod H (framedParamsReg ... p))
  packed via regResidualPack (FROZEN). last = Fin.last L; H last.succ for the lastLayer = H (Fin.last L).
- The product `prod H (framedParamsReg p)` columns come entirely from the LAST layer's `.succ` columns
  (matrix product (A·B) columns = B columns). So the final product's H-last column index = the last
  layer's H-last.succ column index.

## The localization question
The pivot twist must reach BOTH (a) deepestEPivot's final-read codomain split (the H-last side) AND
(b) the last-layer's `.succ`-side split inside framedLayer (else the block is mixed reindex threshold eJ,
not the certified reindex eJ eJ). Two ways to do (b):

OPTION L1 (GLOBAL framedLayer change): add a column-split-equiv parameter to framedLayer/framedParamsReg
  (or a per-layer `eCol : (s : Fin L) → Fin (H s.succ) ≃ Fin r ⊕ Fin (H s.succ - r)` family). Then PIN2's
  banked reg-slice lemmas (framedParamsReg_regSlice_{first,last,interior}, in DeepestRegSliceFderiv) all
  need pivot variants. ~600 LoC, touches a banked sorry-free file.

OPTION L2 (LOCALIZED to deepestEPivot): keep framedLayer/framedParamsReg producing STANDARD
  rThresholdSplit-shaped layers. Change ONLY deepestEPivot's final-read codomain split to
  pivotThresholdSplit r (H last) J. Then the final product P's columns are STILL in standard layout
  (the last layer used rThresholdSplit), and reindexing P's columns by pivotThresholdSplit is a pure
  column PERMUTATION of an already-rThreshold-split matrix.
  QUESTION: in L2, is the toBlocks₁₂ of the pivot-read of P equal to (standard-Y) * (something with a
  CLEAN pivot ₂₂ block), OR does the standard inner split make it the MIXED form (reindex threshold eJ)
  that breaks F-invertibility? i.e. does L2 reproduce the discriminating-check identity, or only L1?

  My reasoning: in the discriminating check, the INNER deviation used eJ.symm (pivot) and OUTER used eJ
  (pivot) — SAME split, they cancelled to fromBlocks * (reindex eJ eJ Q). In L2 the inner last-layer Y
  sits in rThresholdSplit columns but the outer read is pivotThresholdSplit. The middle index of the
  product split would then be MIXED (rThreshold on the inner-matrix side, pivot on the read side), which
  is exactly Codex's earlier "mixed reindex threshold eJ" failure mode. So L2 seems UNSOUND and I need L1.
  CONFIRM OR REFUTE this reasoning.

## What I actually need decided
1. Is L2 sound (localized, ~200 LoC) or must I do L1 (global framedLayer pivot variant, ~600 LoC)?
2. If L1: is the cleanest parameterization a single last-layer column equiv (since only the last layer's
   `.succ` side needs the twist — interiors and first layer keep rThresholdSplit), or a uniform per-layer
   family? The interior/first reg-slice lemmas only ever produce the CORNER (fromBlocks 1 0 0 0) on their
   `.succ` side at the gauge-zero slice — does a last-layer-only twist keep those banked lemmas usable
   (their `.succ`-side reindex would still be rThresholdSplit, matching the interior corner), so only
   framedParamsReg_regSlice_LAST needs a pivot variant?
3. Given the realistic budget (one tide), confirm: API migration + PIN1 green + PIN2 statement updated to
   the pivot split but left as honest sorry is the right scope, vs attempting both green.
</task>

<output_contract>
1. L1 vs L2 verdict (decisive, one paragraph + the reason my L2-unsound reasoning is right or wrong).
2. If L1: the cleanest parameterization (last-layer-only twist vs uniform), and WHICH banked reg-slice
   lemmas survive unchanged vs need pivot variants. Be specific about the `.succ`-side reindex.
3. Scope confirmation for one tide (PIN1 green + PIN2 honest-sorry), or a better split.
</output_contract>

<grounding_rules>
Flag inference vs known-fact. The key uncertain Lean behavior: whether reindexing the columns of an
already-rThresholdSplit-shaped product matrix by pivotThresholdSplit produces a clean pivot ₂₂ block or
a mixed one. Reason from the matrix algebra (a column reindex of M = M.submatrix id eCol.symm; toBlocks
of that vs toBlocks of M).
</grounding_rules>
