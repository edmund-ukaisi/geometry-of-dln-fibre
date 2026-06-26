<task>
Independent read on whether ONE resolution-of-singularities construction discharges BOTH the upper
and lower RLCT bound for a real-analytic function, given a specific architecture.

SETUP. F = ||C^1 ... C^L||_Frobenius^2 (deep linear network loss), a polynomial on R^N, F(0)=0.
Established: the RLCT (learning coefficient) lambda of F at 0 equals (1/2) minAdm, where minAdm is a
combinatorial minimum over rank profiles. We want to formalize lambda = (1/2) minAdm via a
measure-theoretic cover, split into TWO Lean obligations:
 - UPPER (cover_le / "hfin"): for c' < (1/2)minAdm, int over box (-1,1)^N of |F|^{-c'} < infinity.
 - LOWER (cover_ge_div / "hdiv"): for c' >= (1/2)minAdm, int over every small cube [-eps,eps]^N of
   |F|^{-c'} = +infinity.

We have a per-node mechanism (verified exact): a Schur shear (det 1, T = y + a^{-1} b S, the inverse
a^{-1} of a generic-invertible top-left block) followed by a weighted pivot blow-up of the normal
coordinates by a pivot u, giving EXACTLY F(chart) = u^2 * U with U a positive unit, Jacobian
u^{#active - 1}, #active = Mval(M,t) = the codim of the stratum.

A FAILED ATTEMPT for the LOWER bound: a single hand-built chart "phi334" through the achiever curve
(the deepest-point curve where all coords -> 0) was DEGENERATE -- it dropped 2 coordinates, so its
Jacobian determinant was identically 0, its image was a null set, and the change-of-variables it
needed asserted 0 = infinity (false). The diagnosis: the achiever curve passes through the blow-up
center {a = 0} where the Schur shear a^{-1} is singular; a lone chart through that locus cannot be a
local diffeomorphism.

<output_contract>
1. Is it a THEOREM (Hironaka/Watanabe standard) that a SINGLE normal-crossings resolution gives BOTH
   the upper bound (all charts converge below the min threshold) AND the lower bound (the binding
   chart diverges at-and-above the min threshold)? State the standard recipe in 3-4 lines.
2. Does the {a=0} shear singularity that degenerated the lone lower-bound chart get RESOLVED by the
   blow-up that the upper-bound cover already performs (i.e. in resolved coords a = u*a_hat, is the
   achiever leaf an HONEST chart with nonzero Jacobian off u=0)? Or is there a reason the lower-bound
   chart needs something the upper-bound cover does not build?
3. Precisely SHARED vs SEPARATE: once the per-node honest blow-up chart (with its measure
   change-of-variables) is built, what does the LOWER bound need on top (beyond the shared chart),
   and what does the UPPER bound need on top? Is the shared per-node chart the single hardest atom
   for both?
4. NET: does ONE coupled resolution serve BOTH bounds, reducing the total formalization work versus
   two independent constructions? One-paragraph honest verdict.
</output_contract>

<grounding_rules>
- Distinguish the standard THEOREM (resolution gives both bounds) from any architecture-specific
  inference about this particular Lean split.
- Be concrete about WHY a lone chart through the blow-up center degenerates and why the blow-up cures
  it -- do not hand-wave "the resolution handles it."
- If there is a case where the upper-bound cover would NOT contain the lower-bound diverging chart,
  flag it.
