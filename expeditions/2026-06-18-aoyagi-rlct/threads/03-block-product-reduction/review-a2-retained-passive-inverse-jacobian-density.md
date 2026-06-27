# Review: A2 retained-passive inverse Jacobian density

Reviewer: Raman the 4th, xhigh read-only review.

## Verdict

Accepted after one documentation repair.

## Findings

1. The Lean module docstring still said the file did not construct an inverse
   Jacobian density, but the new slice defines
   `topologyTupleEdgeRawOrderInverseJacobianDensity`.  The docstring was
   updated to say that the file constructs the pointwise inverse density and a
   conditional inverse-density pushforward theorem, while not proving an
   explicit determinant formula, determinant-density continuity or
   measurability, source-prior transport, normal crossings, pole order, or
   RLCT.

2. The inverse-density algebra is sound.  With
   `K(y)=J(topologyTupleEdgeRawOrderInverse y)⁻¹`, the inverse law gives
   `K(f z)=J(z)⁻¹` on the determinant chart, and positivity of `J(z)` gives the
   `ENNReal.ofReal` cancellation.

3. The conditional unweighted pushforward is sound and explicit about its
   assumptions.  The theorem assumes a.e.-measurability of the forward density,
   inverse density, and composed inverse density; it does not infer these from
   differentiability or from the weighted change-of-variables theorem.

4. The artifact is Aoyagi-only and does not invoke quiver geometry, normal
   crossings, pole order, or RLCT.

## Required Fixes

All required fixes were limited to the Lean module docstring and have been
applied.
