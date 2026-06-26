import DLNFibre.DLN.RLCT.Validate.FrontPivotProducer

/-!
# `DLNFibre.DLN.RLCT.Validate.DeepestEFullSregComparability` — the L2-PIN2 producer atoms

The S5a invertibility atoms (`eventually_isUnit_of_continuous_eq_one`, `continuous_block₁₁_map`,
`eventually_P00_invertible`) that this module originally banked have been **moved upstream** to
`DLNFibre.DLN.RLCT.Validate.FrontPivotProducer`. They are consumed by the front-pivot producer body
inside `framedParams_split_eq_frame_raw` (in `DeepestGaugeConstruction`), so they must live UPSTREAM
of the cert, not downstream of it. This module imported `DeepestGaugeConstruction` (downstream), which
made the lemmas unusable inside the cert (a circular import); the move fixes that. This file is kept
as a thin re-export so any existing reference to the module name still resolves.

Design cert: `expeditions/2026-06-20-aoyagi-full/threads/31-pin2-comparability/b-wlog-spec.md`
(+ `hproducer-decomp-cert.md`).
-/

namespace DLNFibre.DLN.RLCT
end DLNFibre.DLN.RLCT
