# Codex decorrelated review — P2.4 transpose-H1 honesty

You are a decorrelated second-model reviewer auditing a Lean 4 / Mathlib formalisation refactor.
Answer the SHARP question below; do not rubber-stamp. Flag circularity, vacuity, hidden hypotheses,
name≠content.

## Context

We are lifting an orbit-dimension "submersion bound" (call it A4.3) from a concrete model (deep linear
networks, encoded as matrix tuples) onto an abstract carrier, as a reusable DLN-free engine.

The intended mathematics of A4.3: for an algebraic group acting on an affine space with orbit map μ,
the **generic differential rank of the orbit-coordinate family** is at most the **dimension of the
orbit tangent image** (the range of the deformation coboundary δ⁰ : C⁰ → C¹, the Maurer–Cartan / Lie
algebra "infinitesimal action" map). Geometrically: dμ factors through the infinitesimal action, so
the rank of the orbit coordinates' Jacobian is bounded by dim(im δ⁰).

## The abstract carrier and bound (committed Lean)

```lean
structure AffineGVarietyDeformation (k) [Field k] extends AffineGVariety k where
  (C0 C1 : Type u) [AddCommGroup C0] [Module k C0] [FiniteDimensional k C0]
  [AddCommGroup C1] [Module k C1] [FiniteDimensional k C1]
  (δ : C0 →ₗ[k] C1)
-- inherited from AffineGVariety: ρ (finite coord index), R (a k-domain), fρ : ρ → R (orbit coords)

-- K = Frac R, Ω = Ω[K⁄k] the Kähler differentials.
def DifferentialFactors (δAdj : C1 →ₗ[k] C0) (L : (K ⊗[k] C0) →ₗ[K] Ω) : Prop :=
  span_K { D_k(algebraMap (fρ x)) : x : ρ } ≤ range (L.comp (δAdj.baseChange K))

theorem genericRankBound [Fintype ρ]
    (δAdj : C1 →ₗ[k] C0) (L : (K ⊗[k] C0) →ₗ[K] Ω)
    (hMC : DifferentialFactors δAdj L)
    (hRank : finrank k (range δAdj) = finrank k (range δ)) :
    genericDifferentialRank k R fρ ≤ finrank k (range δ)
```

`genericDifferentialRank k R fρ := finrank_K (span_K { D_k(algebraMap (fρ x)) })`.

The PROOF chain (sorry-free, axiom-clean):
`genericDifferentialRank = finrank_K(span_K{D f_x}) ≤[hMC, finrank_mono] finrank_K(range(L∘δAdj.bc))`
`≤[range_comp + finrank_map_le] finrank_K(range(δAdj.bc)) =[finrank_range_baseChange] finrank_k(range δAdj)`
`=[hRank] finrank_k(range δ)`.

So the whole bound is driven against `range δAdj`, and `δ` enters ONLY through `hRank` at the last step.

## Why the transpose pivot

The formaliser first tried the FORWARD hypothesis `span_K {D f_x} ≤ range(L ∘ δ.baseChange K)` with the
SAME `δ : C0 → C1`. This is **undischargeable** by the DLN model. Reason given: `range(L ∘ δ.bc) =
L(range(δ.bc)) = L(K ⊗ range δ)`, so a single `L` only ever sees the *coboundary image* `range δ ⊊ C1`;
but the orbit-coordinate differentials `D(f_x)` equal pairings of the Maurer–Cartan bracket against
**single C¹ entries** (a basis of all of C¹), which are not in `range δ`. So no `L` recovers them from
`range(δ.bc)`.

The transpose form instead carries an abstract adjoint `δAdj : C1 → C0` (in the DLN model, the
trace-transpose `δ⁰ᵀ` of δ⁰) plus the rank-tie `finrank(range δAdj) = finrank(range δ)`. The DLN model
discharges: `δAdj := deltaT M` (the entrywise trace transpose), `L := pairMC.liftBaseChange K` (pair
against the Maurer–Cartan family Θ), rank-tie `= finrank_range_deltaT` which is PROVED in the DLN file
as `finrank(range deltaT) = finrank(range δ⁰)` via the trace self-dualities `traceEquiv` on C⁰ and C¹
transporting Mathlib's `finrank_range_dualMap_eq_finrank_range` (i.e. rank A = rank Aᵀ). The
self-duality / `deltaT` are confined to the DLN file, never in the abstract engine signature.

## THE SHARP QUESTIONS

1. **Is the transpose `δAdj` + rank-tie H1 the honest abstract form of A4.3?** Or does carrying *both*
   `δ` and `δAdj` plus the rank-tie `finrank(range δAdj) = finrank(range δ)` smuggle the conclusion /
   make the theorem circular or vacuous? Specifically: is the rank-tie a legitimate abstract *input*
   (a genuine self-duality fact — rank of a map equals rank of its transpose-adjoint — that any model
   with a nondegenerate pairing supplies), or is it begging the question?

2. Is `δ` even needed in the carrier, given B1's body only uses `δAdj` and `finrank(range δ)` via the
   rank-tie? (i.e. is there a cleaner shape, or is keeping `δ` as the "canonical" object — with `δAdj`
   its adjoint — the right call for name=content, since the headline bound is stated about `range δ`,
   the true orbit-tangent image?)

3. **Is the forward-fails diagnosis mathematically correct?** Is it true that the forward
   `span ≤ range(L ∘ δ.bc)` cannot hold because `range(L ∘ δ.bc) ⊆ L(K ⊗ range δ)` and the orbit
   differentials genuinely require all of C¹ (single entries outside range δ)? Or is the forward form
   actually dischargeable with a cleverer `L`, meaning the transpose pivot was unnecessary?

4. Any vacuity / hidden-hypothesis / name≠content concern with the abstract engine as stated?

Be concrete and adversarial. Give a verdict per question.
