# Decorrelated design review: feasibility of an ∀-L box-integral finiteness via a recursive monomial blow-up

You are a decorrelated second opinion. Answer FROM SCRATCH; do not assume my conclusion (I have withheld it). Report your own verdict FIRST, then reasoning.

## The exact target (a single Lean 4 + Mathlib statement)

For a "width vector" `M : Fin (L+1) → ℕ` with every `M s > 0`, and matrices `A^(s)` of size `M(s) × M(s+1)` for `s = 0..L-1`, define the box `B = { (A^(0),...,A^(L-1)) : every entry of every A^(s) ∈ [-1,1] }` (a product of closed intervals, finite Lebesgue measure). Let `P(A) = A^(0)·A^(1)···A^(L-1)` (an `M(0)×M(L)` real matrix) and `frobSq(P) = Σ_{ij} P_{ij}^2`.

We want to prove, for every real `c'` with `0 < c' < (1/2)·minAdm(M)`:

    ∫_{A ∈ B} frobSq(P(A))^{-c'} dA  <  ∞.

Here `minAdm(M)` is a positive integer defined by the layer-peeling recursion
    `minAdm(M_0,...,M_L) = min_{0 ≤ t ≤ min(M_0,M_1)} [ (M_0 - t)(M_1 - t) + minAdm(t, M_2, ..., M_L) ]`,
with base `minAdm(M_0,M_1) = M_0·M_1`. (This is the codimension of the rank-deficient locus / the true log-canonical-threshold-times-2 of `frobSq(P)` at the origin, in the deep-linear-network literature.)

## What is already DONE in Lean (banked, sorry-free)

1. **The matching lower bound / divergence** (the OTHER direction of the RLCT): for `c' ≥ (1/2)·minAdm(M)` the integral over any box neighbourhood of 0 is `+∞`. This is proved ∀L via a SINGLE-pivot rational chart `φ` with `frobSq(P)∘φ = z²·U`, `U` bounded and a.e. positive, `|det Dφ| = |z|^{minAdm-1}·(spectator monomial)`, reducing to `∫₀^ε z^{(minAdm-1) - 2c'} dz = ∞` at the boundary exponent. (One binding axis; no additive-over-boundaries structure.)

2. **The L=2 finiteness** (`L=2`, product `= A^(0)·A^(1)`, a single two-matrix product): proved by a "corank recursion" — a WellFounded recursion on the corank of the square factor, with a per-step radial change-of-variables + a minor-pivot Schur split + a Morse-block peel. This recursion's measure is the corank of ONE square factor; the number of layers is not an index of it. At L=2 the product IS a single two-matrix product `Δ·S`, so it applies verbatim.

3. All the surrounding wiring: a value lane (`⨅ over a chart family of per-leaf monomial thresholds = (1/2)·minAdm(M)`), a cover→RLCT bridge, and a measure-preserving reduction of the flat-coordinate integral to exactly the box integral above — all ∀L, sorry-free. So the box-integral finiteness above is the SINGLE remaining open input to the ∀-L result.

## The known difficulty at L ≥ 3

For `L ≥ 3` the target threshold `(1/2)·minAdm(M)` is a SUM over ≥2 rank-drop boundaries for a large fraction of width vectors (e.g. `M=(2,2,2,2)`: minAdm=3, achieved by dropping rank 2→1 at one boundary (codim 1) then 1→0 at another (codim 2), summing to 3). The two-matrix corank recursion of (2) caps at the SINGLE most-binding boundary (peeling one factor off the product caps the exponent at that layer's width/2 and preserves the exponent on the residual), so it undershoots the sum; and collapsing the chain to a single two-matrix core at one boundary either overshoots the value or changes the measure (the product-constrained box is not a free two-matrix box for L≥3). So the L=2 machinery provably does not reach the L≥3 threshold.

## The candidate route to lift it (the thing to adjudicate)

There is a classical proof (Aoyagi 2024, "learning coefficients of deep linear networks") that computes the exact RLCT of `frobSq(P)` at the origin via a **recursive monomial blow-up**: a double-indexed induction on `(S, J)` where `S ∈ {0,...,L}` counts how many factors have been absorbed into a diagonal block `diag(b_1,...,b_{M(S)})` (with `M(S) = min{M(s) : s ≤ S}`), and `J` counts diagonal entries already "peeled" in the current block. Each step is an explicit blow-up along a named coordinate submanifold `{d_ij = 0, u_{s,k} = 0}` with an explicit monomial coordinate substitution (`d = u·d'`) and an explicit monomial Jacobian `∏ u_{s,k}^{M_{s,k}-1}`. The induction maintains an invariant that the exponent vectors `T_{s,k} ∈ ℤ^L` are TOTALLY ORDERED (`T ≤ T'` or `T ≥ T'` componentwise for every pair), and splits into two cases (a maximal run of equal diagonal `b`-values that either stops internally, "Case 1", or reaches the end of the block, "Case 2"). It terminates (`S = L+1`) in a diagonal monomial ideal `⟨P⟩ = ⟨diag(b_1,...,b_{M(L+1)})⟩` — a NORMAL-CROSSING form — from which the RLCT is read off the monomial exponents. The termination measure is the lexicographic `(S, J, #{u : some index})`.

## The questions (answer each explicitly)

Q1. **Feasibility verdict.** Is lifting the FINITENESS (∫ < ∞ for c' < ½·minAdm) to general L via a Lean recursion mirroring this `(S,J)` monomial blow-up a BOUNDED (large-but-mechanical) build, or is there a genuine research-level obstruction (a non-existent-in-Mathlib analytic theorem, or a step that is false / not actually uniform in L and M)? Give your own verdict before reasoning.

Q2. **Recursion structure.** For the FINITENESS ONLY (not the full ideal equality / not the exact RLCT value), what is the cleanest Lean recursion? Specifically: (i) what should the induction measure / termination be — arity `L`, the lex `(S,J,·)`, or something else; (ii) what is the per-step operation on the integral — a change-of-variables producing a Tonelli/Fubini split of the box integral into a monomial factor times a lower-state box integral; (iii) where does the finiteness "compose additively across boundaries" (the thing the two-matrix corank recursion fails to do)?

Q3. **What can be avoided.** The full Aoyagi argument proves an exact ideal equality and reads off both the RLCT value and the multiplicity θ. For FINITENESS ALONE, which parts are unnecessary? In particular: (a) do we need the total-chain invariant on the `T_{s,k}`, or only enough of it to make each blow-up chart well-defined; (b) do we need the exact monomial exponents, or only that each leaf's threshold is `≥ ½·minAdm` (an inequality, giving finiteness below threshold); (c) can the "finite cover of the box" be organized as a finite Finset.sum of chart integrals with change-of-variables Jacobians, avoiding any germ-level/pointwise-at-origin subtlety?

Q4. **The main risks.** What are the 2–3 things most likely to turn this from bounded into a wall, or to hide a subtle error? Consider especially: (a) the finite-cover-of-the-box bookkeeping (the blow-up chart family must be FINITE and its charts must cover the whole box with unit factors uniformly bounded away from 0 and ∞, so the transported integral is a finite sum — not merely a germ at the origin); (b) whether each blow-up step's change-of-variables is a genuine diffeomorphism/measurable-embedding on the relevant chart domain (Mathlib's `MeasureTheory` change-of-variables / `lintegral_image_eq` availability for these explicit monomial maps); (c) whether the case split (Case 1 / Case 2) is genuinely exhaustive and uniform in M for all L, or hides an M-dependent sub-case.

Q5. **Alternative.** Is there a fundamentally simpler route to the FINITENESS ALONE that sidesteps the full `(S,J)` blow-up — e.g. an induction directly on the arity `L` peeling one factor at a time with an exponent that shifts correctly across boundaries, or a Hölder/Loomis-Whitney/Brascamp-Lieb-type integral inequality on the product box, or reducing to a determinant/Gram-matrix formulation? If such a route exists, sketch it and say whether it is more or less Lean-tractable than the blow-up.

Keep the answer focused on the mathematics and the Lean-tractability; you do not have the repo. Be concrete about the recursion and the risks.
