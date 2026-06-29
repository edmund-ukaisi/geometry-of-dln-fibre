1. TRUTH-VALUE — FRAGILE/ENUMERATION-DEPENDENT.  
FACT: `structPivot = ⟨0,_⟩` has no semantic link to `ChartIdx`; `chartIdxEquiv` is an arbitrary finite equivalence. Under a different valid enumeration, slot `0` could map to one of the five reader tags or to a non-reader tag. INFERENCE: the current Mathlib instance has a definite value, but it is not a mathematical fact of the construction.

2. ROUTE (i) reachable? — NO.  
Tag injectivity only proves `chartIdxEquiv.symm tag_i ≠ chartIdxEquiv.symm tag_j` after both sides are tagged. Here one side is bare `⟨0,_⟩`; rewriting it as `chartIdxEquiv.symm (chartIdxEquiv ⟨0,_⟩)` leaves the opaque unknown tag `chartIdxEquiv ⟨0,_⟩`. Without reducing or otherwise specifying that tag, role-structure gives no contradiction.

3. ROUTE (ii) restructure — FEASIBLE.  
FACT: `routeMCore_phiGen` is scalar-parametric; it proves the rate for any scalar `u`, so instantiating `u := x p` for a chosen fixed pivot `p` preserves the rate, assuming no hidden proof uses `p.val = 0`. The determinant headline should also be preserved: it needs a fixed pivot coordinate distinct from reader/leaf slots, not specifically slot `0`; the change is an API/local wiring change, best as a pivot parameter plus a complement-chosen instantiation. Cardinality needed: for pivot only, `readerSet.card < routeMAmbient M`; for the current M222 pivot plus two leaf slots, `readerSet.card + 3 ≤ routeMAmbient M222`.

4. ∀M — route (ii) is robust; route (i) is not.  
FACT: the exact pivot-only invariant is `∃ p, p ∉ readerSet`, equivalently `readerSet.card + 1 ≤ flatDim M`. For the full active-slot construction, the sharper invariant is `readerSet.card + activeBudget M ≤ flatDim M`, with `activeBudget = 1 +` number of additional non-reader live/leaf slots; in the intended R1 form this should be `activeBudget = minAdm M`. INFERENCE: this holds for M222; for all `M` it is a separate budget/cardinality theorem, not a consequence of `chartIdxEquiv` alone.

5. RECOMMENDATION — use route (ii): parameterize the pivot and choose it from the non-reader complement; the sharp kill-condition is failure of `readerSet.card + activeBudget M ≤ flatDim M` for the exact general reader set.