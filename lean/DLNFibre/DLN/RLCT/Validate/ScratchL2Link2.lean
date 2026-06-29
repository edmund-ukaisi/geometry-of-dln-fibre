import DLNFibre.DLN.RLCT.Validate.DeepestL2ConjSub4

/-! # Scratch: LINK-2 (route-b close) — RELOCATED.

The LINK-2 pieces (`link2_thetaPeel_half`, `regAbsorbPeel_conj`/`_bare`, `regAbsorb_conj`/`_bare`,
`link2_at_zero_gaugeReg`, `link2_at_wstar_gaugeReg`) and the assembled bridge
`deepest_diffeo_bridge_L2_assembled` have been MOVED to the wire-importable leaf
`DLNFibre.DLN.RLCT.Validate.DeepestL2ConjSub4` (which does NOT import `DeepestL2Wiring`), so the wire's
`deepest_gauge_construction` can consume the assembled bridge directly. This file is now a thin forward
kept only so the old import path resolves; all the content lives in `DeepestL2ConjSub4`. -/
