# Codex verdict (PATH B viability) — 2026-06-26

PATH B is NOT a genuine shortcut. routeMCore reads via (paramsEquivFlat).symm, so the rate of
composeFold fs requires identifying (paramsEquivFlat).symm (composeFold fs u)'s Params-layers = the
bridge. PATH C (det of phiFlatStruct directly) is MORE work (rebuilds the per-factor derivative
decomposition + extra calculus). 

CLEAN RECONCILIATION = PATH A′: prove the unflattened/layer bridge ONCE at the Params level:
  (paramsEquivFlat M).symm (composeFold fs u) = chartParamsGen u M t (genBlkFlatStruct u) hle
Then BOTH NodeAchieverChart fields land on one map phi := composeFold fs:
  - rate: transport routeMCore_phiFlatStruct through the bridge;
  - det: composeFold_abs_det_leafH (free).
The bridge "only exists if the factor fold is represented as producing the chainA layers SEMANTICALLY,
not merely as ambient flat self-maps" — so DESIGN fs so the bridge is near-definitional.
