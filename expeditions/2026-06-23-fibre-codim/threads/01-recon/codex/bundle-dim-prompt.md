# Frame

Setting: Lean 4 + Mathlib v4.29.0 (toolchain leanprover/lean4:v4.29.0). We work over a fixed
algebraically closed field k of characteristic 0. Affine varieties are represented as Zariski-closed
subsets Z ⊆ (σ → k) for a finite index σ (i.e. closed subsets of affine space A^|σ|), and geometric
dimension is `varietyDim Z := (ringKrullDim (MvPolynomial σ k ⧸ vanishingIdeal k Z)).unbotD 0`,
geometric codimension is `Ideal.height (vanishingIdeal k Z)`. We already have, for an IRREDUCIBLE
variety (vanishingIdeal Z prime): `height (vanishingIdeal Z) + varietyDim Z = Nat.card σ` (the
catenary complement), proved via Mathlib's `height_add_ringKrullDim_quotient_eq` for MvPolynomial
rings. We also have a transcendence-degree / Kähler-differential ("generic Jacobian rank") route for
the dimension of the IMAGE of an explicit polynomial parametrisation map μ : G → A^n (used to compute
the dimension of an algebraic-group orbit as the image of the group under an orbit map).

# Question

Suppose I have a dominant morphism of affine varieties f : X → Y over k, where Y is a single orbit
of a connected algebraic group G acting on affine space (so Y is smooth, irreducible, homogeneous),
and f is G-equivariant for a G-action on X covering the G-action on Y. Classically this makes
f : X → Y a Zariski-locally-trivial fibre bundle, so dim X = dim Y + dim(f⁻¹(y)) for any y ∈ Y, and
in particular codim_{A^N} f⁻¹(y) = codim_{A^N} X + dim Y.

In Lean 4 + Mathlib v4.29 affine-variety terms (heights of ideals in MvPolynomial rings, ringKrullDim,
Algebra.trdeg, the StandardSmooth/etale relative-dimension API, the Krull-dimension polynomial lemmas
like `MvPolynomial.ringKrullDim_of_isNoetherianRing : ringKrullDim (MvPolynomial ι R) = ringKrullDim R
+ Nat.card ι`):

1. What does it actually take to prove `dim X = dim Y + dim (fibre f y)` for such a homogeneous-base
   locally-trivial bundle? Itemise the intermediate lemmas/theorems needed, and for each say whether
   Mathlib v4.29 has it, has a close cousin, or lacks it entirely.

2. Is there a SHORTER route that avoids building "locally trivial bundle" as a first-class object —
   e.g. a purely commutative-algebra fibre-dimension statement (dim of a fibre ring of a flat or
   smooth or just dominant finite-type morphism), or an equidimensionality / going-down argument, or
   reduction to `MvPolynomial.ringKrullDim_of_isNoetherianRing` via a global trivialisation? If so,
   what are its hypotheses and which Mathlib pieces does it rest on?

3. What is the single hardest missing piece — the one theorem whose absence is the real obstruction —
   and roughly how much from-scratch development (in module-count terms) would it be at this Mathlib
   pin?

Be concrete about Mathlib v4.29 API names where you can. If you believe the clean general statement is
simply not reachable without a substantial from-scratch dimension-theory-of-morphisms build, say so
plainly and characterise that build.
