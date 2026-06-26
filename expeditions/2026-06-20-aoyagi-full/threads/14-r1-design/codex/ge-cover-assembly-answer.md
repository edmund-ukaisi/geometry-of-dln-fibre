**1. PROBE (a) Verdict**

Sound, if you use the ae-union API directly. Observed local Mathlib chain:

`setLIntegral_congr hcover` for `U =ᵐ[μ] ⋃ i∈s, leaf i`, then `lintegral_biUnion_finset₀` for the finite ae-disjoint sum. Internally this goes through `lintegral_biUnion₀` → `lintegral_iUnion₀` → `Measure.restrict_iUnion_ae` + `lintegral_sum_measure`.

So genuine disjointness is not required; `AEDisjoint` + `NullMeasurableSet` is enough.

Nested-tree warning: do not try to prove final 24 original-space leaf images are ae-disjoint by “pushing forward” ae-disjoint source cells through charts. That does not follow from the cited signatures. Either prove a null-image theorem for the chart maps, or better, assemble recursively in the current chart coordinates. Repo-local `g5_step` / `g5_pivotNode` already have the safer shape.

**2. PROBE (b) Verdict**

Cover up to null is sufficient, even if the omitted locus is where the informal integrand “blows up.” For `ℝ≥0∞` lintegrals, a null restricted measure contributes zero for any integrand, including one taking `⊤`. Observed local tools: `setLIntegral_congr`, `setLIntegral_measure_zero`, and coordinate hyperplane nullness via product-measure facts such as `Measure.pi_hyperplane`.

But the 24-leaf cover does not follow merely from saying “finite union of coordinate hyperplanes” unless the null statement is made in the measure space where the deletion happens. If a deleted source hyperplane is later mapped into target space and you formulate the cover in target space, you must prove that image is null. Cheapest fix: delete null exceptional sets before/inside each pullback step, or prove the exact target `U =ᵐ ⋃ leafImages`.

Also note: your exact Lean integrand uses `ENNReal.ofReal (Real.rpow ...)`, so its zero-set convention is not literally `⊤`; the null-set argument is robust either way.

**3. Most Likely Silent Hole**

The likely hole is flattening the nested tree too early: asserting one global `U =ᵐ ⋃ 24 leafImages` while forgetting parent-domain restrictions or unproved nullness of exceptional images.

Cheapest Lean probe: before any monomial or threshold work, prove the exact `hcov` needed by `cover_integral_lt_top_iff` for an opaque arbitrary `g`. No `myF222`, no `c'`, no units. If that equality does not go through cleanly, the cover assembly is the problem.

**4. Safer Reordering**

First prove the null-deletion and exact 24-leaf `hcov` equality for arbitrary `g`.

Then instantiate `g = ENNReal.ofReal (|myF222 x| ^ (-(c' : ℝ)))`.

Then prove each pulled-back leaf integral is finite using the monomial/unit bounds.

Only then call `cover_integral_lt_top_iff`, followed by `rlctAtOn_ge_of_integral_lt`.