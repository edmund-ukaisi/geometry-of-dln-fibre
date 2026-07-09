**Verdict**

My read: the Gram determinant wall is **route-induced**, not intrinsic to the DLN RLCT. The intrinsic feature is the **shared exceptional-divisor coupling** at product-rank-deficient branches. Aoyagi’s native recursion handles that coupling by keeping the whole product ideal alive and tracking `diag(b)`; it does **not** manufacture `det(Q_b Q_bᵀ)`.

So for the formalisation fork: **build Aoyagi-native or cite Aoyagi. Do not continue the Gram-integrate-out route as the main proof.**

**Answers**

1. **`det(Q_b Q_bᵀ)` is an artefact of the Gamma-integration peel.**

The rank-deficient intermediate strata are real, and some bind. What is not intrinsic is the inverse Gram factor. It appears because the proof first frees/integrates `Γ` and then normalises an anisotropic quadratic form. In the native recursion, `Γ` is not integrated out as a standalone Gaussian block; the product ideal is transformed directly, and the shared divisors remain in the `b_i` ledger.

The local paper reproduction has exactly the native invariant:
`<prod C^s> = <diag(b) [E_J 0; 0 D_J] prod tail>`, with `b_i` monomials in prior exceptional variables, and Cases 1/2 blow up coordinate residual blocks plus existing `u` variables [aoyagi-2023-worked.tex](/home/ubuntu/workspace/geometry-of-dln-fibre/theory/aoyagi-2023-reproduction/aoyagi-2023-worked.tex:475). The freed-`Γ` route, by contrast, explicitly exposes `Q_b Q_bᵀ` positivity as an extra hypothesis and notes it fails on bottleneck/rank-drop charts [RouteMSJFreedPeel.lean](/home/ubuntu/workspace/geometry-of-dln-fibre/lean/DLNFibre/DLN/RLCT/Validate/RouteMSJFreedPeel.lean:25).

2. **The “non-coordinate center forced by dense-torus witness” does not survive against Aoyagi-native.**

It may be a correct obstruction to **principalising the Gram determinant of a matrix product**. But that is not the same object as resolving the zero locus of `||prod C||²`.

If the witness is a positive-loss point, it is off `{prod C = 0}`. Then it is not a singular point of the original RLCT integrand; any pole there comes from the marginalised Gram density. That pole has to be handled if one insists on the Gram route, but it is not evidence that the original DLN loss requires a non-coordinate blow-up.

Reconciliation: Aoyagi’s centers are coordinate in the evolving chart coordinates, after unit row/column operations. They need not principalise every determinantal rank-drop locus of every intermediate tail product. They only need to principalise the product ideal at the deepest zero point, and the `diag(b)` ledger records the shared divisors that a Gram marginalisation tries to rediscover through determinants.

3. **Lean gap classification: (a), with a route warning.**

For the Aoyagi-native proof, this is **(a): formalise the explicit coordinate-chart recursion**, large but bounded, citing only the monomial normal-crossing integrability endpoint if desired.

For the Gram-integrated route, the same phenomenon looks like **(c)** because that route creates a determinantal principalisation problem. But that is a self-inflicted route wall, not an intrinsic DLN wall.

The cleanest formal target is: encode Aoyagi’s `(S,J)` recursion, Cases 1/2, shared `b_i` monomial ledger, coordinate blow-up charts, and terminal monomial read-off. The repo’s own later notes make this same distinction: the product-Gram principalisation is an avoidable trap, while the native R-blow-up route never forms the Gram determinant [discuss-at-close.md](/home/ubuntu/workspace/geometry-of-dln-fibre/expeditions/2026-06-20-aoyagi-full/discuss-at-close.md:2180).

4. **Dominant difficulty: (i) the carrier data structure.**

The hard part is not “inventing resolution of singularities.” It is designing the Lean state so it is strong enough:

- current layer `S`, pivot count `J`, running minimum `M(S)`;
- residual block dimensions;
- branch/rank-profile data;
- per-generator support map: which exceptional variables divide which generators;
- sharing identity: the same `u` must be known to divide multiple generators.

A per-row multiplicity is too weak. The `(3,3,4)` witness shows this sharply: true `rlct = 4`, but threshold-only/per-row tracking gives `3`; the missing information is exactly shared `diag(b)` support [verify-r1-diagb-334.md](/home/ubuntu/workspace/geometry-of-dln-fibre/theory/aoyagi-2023-reproduction/verify-r1-diagb-334.md:19). The minimal data structure is basically `support : Gen → Finset DivVar`, plus accumulated exponents [verify-r1-diagb-4422.md](/home/ubuntu/workspace/geometry-of-dln-fibre/theory/aoyagi-2023-reproduction/verify-r1-diagb-4422.md:146).

**Size tier:** not a quick fill. With the repo’s existing infrastructure, I would budget **6-12 person-weeks** for a serious Aoyagi-native core recursion, more like **10-16** if the integral plumbing and finite chart cover are included cleanly. From scratch, higher. Top risk is building a carrier that is still too weak and discovering late that another sharing relation is missing. Chart algebra is large but more mechanical; termination/covering is finite/lexicographic once the state is right.

**Practical call:** If the goal is a fully from-scratch Lean RLCT proof, build Aoyagi-native. If the goal is the DLN fibre theorem with controlled citation footprint, cite Aoyagi’s exact RLCT. Do not spend effort principalising `det(Q_b Q_bᵀ)` unless the project explicitly chooses the Gram route.
