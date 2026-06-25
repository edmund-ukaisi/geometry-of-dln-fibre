# Codex consult (xhigh, decorrelated) — routes to the deep fibre-codim / radicality residual

## Context

Formalising (Lean 4 / Mathlib v4.29) the geometry of LR Lemma 4.6 for deep linear networks. The
multiplication map is `mult(A₁,…,A_N) = A_N···A₁ : Rep_d → Mat_{d_N × d_0}`, where `A_i : Mat_{d_i × d_{i-1}}`.
We want `codim(mult⁻¹(B)) = C + δ` in `Rep_d`, where `B` has rank `r`, `C = codim Σ̄^r`
(`Σ̄^r = {rank(mult A) ≤ r}`, the product-rank locus), and `δ = r(d_0 + d_N − r)`.

By a landed normal-form reduction we may take `B = E = diag(I_r, 0)`. The codim is `height(vanishingIdeal(fibre))`.
Everything reduces to ONE residual, certified TRUE pen-and-paper (Singular primary decomposition on 11
cases + the type-A rank-locus reducedness theorem of Buch–Fulton / Kinser–Rajchgot): the deep fibre ideal
`I_E = (mult(Ã) − E)` (degree-N polynomial equations cutting `mult⁻¹(E)`) is **radical**, equivalently
`F_E = k[Ã]/I_E` is **reduced**, for all `N ≥ 1`.

A previous planned route built a product trivialization `e : O(Σ̄^r ∩ chart) ≃ base ⊗_k F_E` and
DESCENDED reducedness `Sred reduced ⟹ F_E reduced`. It WALLED on a certified circularity: any genuine
construction of `e` proves the radicality as a byproduct (`e` exists ⟹ `R ⊗ F_E` reduced ⟹ `F_E`
reduced), so `e` is *equivalent to* the radicality, not a path to it. DO NOT re-propose building `e`.

## What I computed (anchor `(2,2,2), r=1`)

The Jacobian of `mult`, `d(mult)(X₁,X₂) = X₂A₁ + A₂X₁ : k⁸ → k⁴`, at fibre points:
- on the generic strata (one factor full-rank): rank(d mult) = **4 = dim Mat** (submersion ONTO all of Mat),
  fibre smooth there, local dim 4 = codim 4 = C+δ.
- on the deep `(1,1)` stratum (both factors rank-1): rank drops to **3**, tangent jumps to dim 5. This
  stratum is dim 3 (codim 1 in the 4-dim components) — the locus where the 2 reduced components meet.
- So `mult⁻¹(E)` is SINGULAR (along `(1,1)`); `mult` is NOT a submersion at every fibre point.
- The pivot chart `{(mult A)₀₀ ≠ 0}` contains the WHOLE fibre (since `mult A = E` on it), so it does NOT
  excise the singular stratum.

## The questions (rank the routes; be concrete and honest)

1. **Submersion route.** `mult` is a submersion onto Mat on a dense open of the fibre, hence the fibre is
   generically reduced and its top components have codim `C+δ`. To upgrade "generically reduced" to
   "reduced" (= radical `I_E`), I need NO embedded primes / an `(S₁)`+`(R₀)` (Serre reducedness) argument.
   (a) Is there a route to `I_E` radical via generic-smoothness + `(S₁)`/unmixedness that does NOT route
   through the (circular) flat product trivialization, and is it formalisable at Mathlib v4.29 (which has
   essentially no CM/Serre-condition/depth library)? (b) Crucially: does the codim claim
   `codim(fibre) = C+δ` actually NEED radicality at all, or only the *dimension* of the fibre (which is
   radical-insensitive: `height(I) = height(radical I) = dim`-codim)? If codim needs only the dimension,
   can we get the dimension of `mult⁻¹(E)` directly (fibre-dimension semicontinuity / Chevalley upper
   bound + a lower bound), bypassing reducedness entirely?

2. **Type-A rank-locus reducedness route.** Prove the deep determinantal/rank locus `Z_r = {rank(mult A) ≤ r}`
   reduced directly (Buch–Fulton / Kinser–Rajchgot: these loci are reduced, normal, CM, with rational
   singularities). What is the cleanest SELF-CONTAINED argument (Gröbner / standard monomial basis / a
   degeneration to a reduced monomial ideal / CM + generically reduced)? How much of this is realistic to
   build from scratch in Lean v4.29 (no Gröbner-basis-for-determinantal-ideals, no CM library)? Does
   reducedness of `Z_r` even GIVE the fibre reducedness, or is that a separate descent?

3. **Other routes.** (a) The fibre/orbit as a homogeneous space under a group action ⟹ smooth ⟹ reduced —
   does some group act transitively on (a dense open of) `mult⁻¹(E)` making it a quotient/orbit, hence
   smooth? (b) A regular-sequence / complete-intersection argument — is `mult⁻¹(E)` a complete intersection
   (the `δ` or `d_N·d_0` equations a regular sequence)? (Note: we already KNOW `mult⁻¹(0)` is NOT a CI —
   `codim ≠ #generators`.) (c) A direct dimension count of `mult⁻¹(E)` via the stratification by
   intermediate ranks (rank patterns) — sum of stratum dimensions, take the max?

4. **THE key strategic question.** Of all routes, which most plausibly (i) closes `codim = C+δ` and (ii) is
   buildable in Lean v4.29 from the engine's substrate (it carries: `mult` over any CommRing, the generic
   product polynomials `multPoly`, `fibreGenIdeal`, the comorphism `multComap`, the codim engine
   `cCodim`/`Ideal.height`/catenary bridges, the going-down height-additivity lemma
   `height_eq_height_add_of_liesOver_of_hasGoingDown`, the N=1 determinantal Schur presentation, the
   endpoint gauge `gaugeEquiv`)? Is there a route that gets the CODIM (dimension) WITHOUT the radicality,
   making the whole reducedness question a red herring for the codim claim?

Give a ranked recommendation with the precise statement to formalise, the key sub-lemmas, the difficulty,
and explicit kill-conditions for each route.
