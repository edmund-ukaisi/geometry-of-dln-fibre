1. **TRUE — OBSERVED-in-file.** With `p ∈ S`, `jacDet_blockBlowupMap` proves exactly  
   `jacDet = w_p^(|S|−1)`; hence the absolute determinant is `|w_p|^(|S|−1)`.

2. **PARTIAL — OBSERVED + INFERENCE.** The chain-product formula is correct, and deeper-pivot preservation is sufficient for the naive sum. It is not “iff”: only the product equality is necessary; signs, zero exponents, or compensating factors can violate coordinatewise preservation without changing the product.

3. **FALSE — OBSERVED-in-file.** Shrinking centers protect old pivots from the deeper blow-up, but not from its shear. The rendered step is actually `blockBlowupMap ∘ edgeShear`; `hshear_pivot` fixes only the current pivot, and `IsRealBranch` leaves `shearφ` unconstrained. Reason C itself is correct. Additionally, `canonCenterOf case11` omits the reused birth pivot despite `canonPivotOf case11` selecting it.

4. **PARTIAL — INFERENCE.** The seat’s exact reversed-center example is unreal, but its conclusion survives: current hypotheses do not support an accumulation lemma. A statement must require preservation of all earlier positive-exponent pivots, or directly certify the accumulated Jacobian. No boost-aware exponent change is indicated.

5. **TRUE — formally admitted counterexample.** Take `d=(2,2)`, so `D=4`. Canonical clears give `S₁=all four`, pivot `p=(0,0)`, then `S₂={(1,1)}`, pivot `q=(1,1)`. Let the deeper determinant-one shear send `u_p ↦ u_p+u_q` and fix `u_q`. Then  
   `|jacDet g|=|u_p+u_q|³`, while the naive weight is `|u_p|³`; no nonvanishing unit near `0` can reconcile them.

BOTTOM LINE: hjac_tie defective (needs statement touch)