<task>
Setting (exact algebra; resolution of singularities for a learning-coefficient computation).
We have an iterated blow-up resolution g of the zero-locus of a matrix product ideal ⟨∏C⟩ at the
origin, built as a FINITE ROOTED TREE (Aoyagi's Cases 1&2 recursion). Each internal node performs a
blow-up of a COORDINATE SUBSPACE (a determinantal sub-block {d_ij = 0}); between blow-up levels there
are UNIPOTENT polynomial Schur shears (e.g. Δ = C22 − C21·C12), which are det-1 polynomial bijections
with polynomial inverses. Each terminal leaf p carries a composed map g_p : ℝ^N → ℝ^N (source =
resolved coords, target = original matrix entries u). We must produce, per leaf, a COMPACT source
domain dom_p ⊆ ℝ^N such that the images g_p '' dom_p a.e.-cover a neighbourhood of 0 in the target:

    ∃ ρ > 0,  volume( ball(0,ρ)  \  ⋃_p  g_p '' dom_p ) = 0.

This is the `hcover` field of a `Resolution` record we must inhabit in Lean (no cite allowed — must be
built). Dimension-preserving (source and target both ℝ^N).

Facts established (exact, reproduced by two independent batteries):
1. The single-block blow-up ATOM is the max-modulus (argmax) chart cover: for x in cube [-R,R]^d,
   pick pivot i = argmax_k |x_k|; the pivot chart β_i(w)_k = (w_i if k=i else w_i·w_k) reaches x from
   w with w_i = x_i (|w_i| ≤ R), w_k = x_k/x_i (|w_k| ≤ 1). This is a FULL cover of the cube by the d
   charts, with source domain [-R,R]_i × [-1,1]^{d-1}. (Already proven sorry-free in Lean for the
   maximal-ideal origin blow-up, all d.)
2. Blowing up a coordinate SUBSPACE = (origin blow-up on the block) × (identity on spectators). So the
   atom is (argmax on the block) × (spectator passthrough); the block-cube × spectator-cube is a box.
3. The unipotent Schur shears are polynomial bijections, det 1; the shear inverse (target→source lift)
   is a well-defined polynomial (e.g. Δ = C22 − C21·C12), so lifting through a shear is deterministic.
4. Composed 2-level lift (argmax level-1 → shear-inverse → argmax level-2) reconstructs the target
   EXACTLY on a rational grid, and the lifted resolved point lies in a bounded box; verified on the
   (3,3,4) coupled instance including the join step (radial C1 → Schur Δ → radial Δ / join divisor E,
   |E| ≤ 2), and on a general 2-level toy with a spectator coordinate.
5. Naive raw-coordinate box inflation R_{k+1} = R_k + R_k^2 diverges super-exponentially; but with
   NORMALIZED-coordinate shears (residual = pivot·ratio, ratios ≤ 1) the scale grows by a bounded
   factor ≤ (1+R) per level, so the box bound is R·(1+R)^m for tree depth m (finite; the tree depth is
   bounded for a fixed core).

There is an existing (retired, but kernel-checked and sorry-free) Lean development of a related cover:
a max-modulus tree cover `flatCube_subset_leafPathImages` / `geoAtlas_imageCover` that covers the flat
unit cube [-1,1]^N at radius R=1 by the tree's leaf-path images, with per-node `qNodeOf`-conjugated
pivot charts (center × spectator product split), spectators handled by the product cube. But that
development uses PURE (gauge = id) charts — the Schur shears are NOT present in that cover proof; the
shear is meant to be absorbed via a "source reparameterization" identity β̃ ∘ (α '' D) = β '' D (the
`reparam_image` single-node atom, proven), but the tree FOLD with real shears is not landed.

My sub-questions (answer independently; do NOT rubber-stamp):
</task>

<output_contract>
Answer these, each in ≤ 8 lines, no preamble:

Q1. Is this a.e.-cover CONSTRUCTIBLE from the max-modulus atom + shear-bijection lifting, WITHOUT
    invoking Hironaka properness? If yes, give the cleanest construction of dom_p and the covering
    argument. If no, name the exact obstruction.

Q2. Is the cover FULL (empty escape) or only a.e. (genuine null escape)? Enumerate precisely which
    measure-zero set, if any, escapes ⋃_p g_p '' dom_p — distinguish pivot-tie loci, exceptional /
    pivot-zero loci, and any set arising from the shears.

Q3. The SPECTATOR problem: at each level the untouched coordinates must stay bounded so dom_p is
    compact. Does the argmax routing + shear-bijection lifting confine the spectators to a bounded box?
    Or is a specific compactification of the source domain needed (which one)?

Q4. The box-inflation / depth interaction (fact 5): does the per-level factor growth threaten the
    cover, or is "finite bound for finite tree depth (shrink ρ if needed)" the correct and sufficient
    reading? Any hidden pitfall where the shear-inflated box fails to be covered by the next level?

Q5. For the LEAN statement of `hcover` = `volume(ball(0,ρ) \ ⋃_p g_p '' dom_p) = 0`: what is the
    right quantifier shape and the right DATA STRUCTURE for dom_p — a per-chart compact BOX in SOURCE
    (resolved) coordinates, or an image-side / preimage description? What is the single biggest Lean
    risk in folding the per-node cover over the recursion tree with real (non-identity) shears?

Q6. The single most likely thing that BREAKS this cover being "detail-at-scale" (i.e. that would make
    it a genuine new-math frontier / monument), and the cheapest test to settle it.
</output_contract>

<grounding_rules>
- Exact algebra only for load-bearing claims; a numeric spot-check is a guide, not a proof.
- A closure/cover claim must rule out ALL escaping strata, not just one — be exhaustive in Q2.
- Do not assume the answer is "yes constructible"; if you find an obstruction, say exactly where.
- Keep inference separate from fact: flag anything you are inferring vs. deriving.
</grounding_rules>
