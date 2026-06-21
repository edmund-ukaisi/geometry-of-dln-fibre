import DLNFibre.DLN.RLCT.Validate.Case111
import DLNFibre.DLN.RLCT.Foundations.S1ProductMin

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

-- (1,1,1) validate showcase — must stay axiom-free.
#print axioms case111_rlct
#print axioms resolution_charts_case111

-- S1 substrate (the heaviest analytic rung) + product-MIN engine — must stay clean.
#print axioms rlct_additive_smooth_block
#print axioms product_min_rlct
#print axioms product_min_rlct_of_ne

-- Headline — sorryAx expected (5 rungs pending); tracked here so the day it goes clean is visible.
#print axioms aoyagi_learning_coefficient
