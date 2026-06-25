I’ll ground this in the local repo and the pinned Mathlib shape rather than answering from memory. I’m going to read the project notes and search for the dimension/trdeg/Jacobian lemmas you mentioned so the route recommendation matches the engine you actually have.

----

The repo already has more of the ambient algebraic-geometry bridge than the prompt lists: orbit image/range infrastructure, Jacobian-trdeg machinery, and affine-domain dimension files. I’m narrowing now to what would actually shorten the rank-variety equality rather than rebuilding general determinantal CA.

----

A key constraint is visible in the existing `JacobianTrdeg` file: the differential criterion is deliberately one-sided. So a “compute generic Jacobian rank and call it trdeg” route would need a new opposite inequality theorem, not just a matrix-rank calculation.

----

For the exact equality, the cleanest lower bound probably should not use the `u·v` parametrisation directly. The existing orbit machinery can make rank-exact locus a single orbit, and orbit tangent rank gives a lower-dimensional witness once the normal form is chosen. I’m checking whether that is already concrete enough to avoid a stabilizer-dimension theory.

----

There is also a stronger route hiding in the repo: for `N = 1`, the existing type-A orbit-closure/codimension engine specializes exactly to the classical rank-≤r determinantal variety. If you accept that specialization, it avoids proving a standalone determinantal-ring dimension theorem.

----

At this point I would not recommend the block-inverse transcendence-basis route as the first Lean route. It is mathematically standard, but in this codebase it fights Mathlib’s rational-function and localization bookkeeping while duplicating geometry the repo already has.