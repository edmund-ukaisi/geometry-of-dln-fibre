import DLNFibre.DLN.RLCT.Validate.Case111
import DLNFibre.DLN.RLCT.Validate.Case212
import DLNFibre.DLN.RLCT.Foundations.S1ProductMin
import DLNFibre.DLN.RLCT.Validate.Case222Algebra

/-!
# Axiom-hygiene check

Emits `#print axioms` for the load-bearing results on every build (imported by the `DLNFibre`
aggregator), so axiom regressions are caught by the standard green-gate rather than only by an
ad-hoc check.

Reading the output:
* **clean** = `[propext, Classical.choice, Quot.sound]` — fully proven, no citation, no `sorry`.
* `+ monomial_rlct` — the single permitted S2 citation (the bare weighted-monomial-integral fact).
* `sorryAx` — an unproven rung underneath. **Expected** on `aoyagi_learning_coefficient` until the
  5 Skeleton rungs (L2 `product_reduction`, D1 `deepest_point_reduction`-≥, R1 `resolution_charts`,
  A1 ×2) are proven; it must **not** appear on any result below that claims to be proven.

This file is `#print`-only — it adds no definitions and no axioms of its own.
-/

open DLNFibre.DLN.RLCT

-- (1,1,1) + (2,1,2) validate showcases — must stay axiom-free.
#print axioms case111_rlct
#print axioms resolution_charts_case111
#print axioms case212_rlct

-- S1 substrate (the heaviest analytic rung) + product-MIN engine — must stay clean.
#print axioms rlct_additive_smooth_block
#print axioms product_min_rlct
#print axioms product_min_rlct_of_ne

-- (2,2,2) loss-identity seam (#83) — pure matrix algebra (`prod_two_layer` + flat coords + `ring`).
-- Must stay clean: NO `monomial_rlct` (the seam's S2-dependence is downstream in the cover), NO `sorryAx`.
#print axioms dlnLoss222_eq_myF222

-- (2,2,2) ≤-direction cover headline (#80, the hard half) — carries `monomial_rlct`, the PERMITTED S2
-- citation (the threshold value rests on S2 via the box-divergence atom). Must be
-- [propext, Classical.choice, Quot.sound, monomial_rlct] — NO `sorryAx`. (Contrast dlnLoss222 above,
-- which must stay monomial_rlct-FREE: the S2-dependence enters here, in the singular cover.)
#print axioms rlctAtOn_myF222_le

-- (2,2,2) ≥-direction cover headline (#86, route R) — the box-local threshold-finiteness lower bound.
-- Must stay CLEAN: [propext, Classical.choice, Quot.sound], NO `monomial_rlct`, NO `sorryAx` (the ≥
-- half is pure measure theory + coordinate-conjugation symmetry, S2-FREE).
#print axioms rlctAtOn_myF222_ge'

-- (2,2,2) RLCT value (#80, the `=` half) — `le_antisymm` of the two halves. Carries `monomial_rlct`
-- ONLY (via the ≤-half), NO `sorryAx`.
#print axioms rlctAtOn_myF222_eq

-- (2,2,2) headline value + resolution-charts wrapper (#76, third ladder rung) — transports the cover
-- value along `e222`. Carries `monomial_rlct` ONLY (via the value), NO `sorryAx`.
#print axioms case222_rlct
#print axioms resolution_charts_case222

-- Headline — sorryAx expected (5 rungs pending); tracked here so the day it goes clean is visible.
#print axioms aoyagi_learning_coefficient
