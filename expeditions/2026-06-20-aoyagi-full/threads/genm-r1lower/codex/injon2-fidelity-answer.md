**Q1**

VERDICT: SOUND. ASSUMPTION: `readK` is exactly the pure coordinate projection you state, and `matrixSplit`’s middle component is definitionally the raw diagonal `K i i`. Under those assumptions, the needed factor is a single coordinate of `pbo x₀`, not a lensed/LDU expression. It is legitimate to prove post-`kLDU` determinant nonzero via the theorem `readK_kLDU_det`, since that equality identifies it with the product of pre-`kLDU` diagonal pivots.

**Q2**

VERDICT: SOUND. The domain `{u | u p ≠ 0 ∧ ∀ j ∈ univ, u j ≠ 0}` is not empty for a finite coordinate space over `ℝ`; even in dimension `0`, `∀ j` is vacuous and the separate pivot condition only exists if such a pivot index exists. There is no apparent vacuity trap in the stated InjOn domain. Yes, the change-of-variables/image integral theorem genuinely needs injectivity on the domain to avoid multiplicity in the image integral.

**Q3**

VERDICT: SOUND. ASSUMPTION: `StairProd (eihdV M) 2` is nested as `V0 × (V1 × PUnit)`, with `V1 = (Wfun, Lfun)`. Then `Prod.ext ?V0 (Prod.ext ?V1 ?PUnit)` is exactly exhaustive: first component, second-stage pair, and terminal unit. Since `eIn` is a `LinearEquiv`, equality of all codomain components gives equality of inputs by injectivity.

Overall: PASS.