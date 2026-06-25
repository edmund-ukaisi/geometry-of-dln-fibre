# Codex consult — G2-3 total-space presentation + flatness (decorrelated design review)

You are a decorrelated second opinion for a Lean 4 + Mathlib (v4.29) formalisation of
Lehalleur–Rimányi (2024) "Geometry of the fibers of the multiplication map of deep linear
networks", Lemma 4.6. I want you to red-team a proposed route and propose a cheaper one if you see it.

## The setup (precise objects)

- Dimension vector `d = (d_0,...,d_N)`. `Rep_d = ∏_{i=1}^N Mat_{d_i × d_{i-1}}(k)` (k alg-closed, char 0).
- `mult : Rep_d → Mat_{d_N × d_0}`, `(A_1,...,A_N) ↦ A_N···A_1`.
- `Σ̄^r = {A ∈ Rep_d : rank(mult A) ≤ r}` (closed product-rank locus).
- `fibre(B) = mult⁻¹(B)` for `B` of exact rank `r`.
- Coordinate ring of `Rep_d` = `MvPolynomial (factor entries) k` (the variables are the entries of
  the `A_i`, NOT the product entries).

## What is ALREADY formalised (reuse, do not rebuild)

1. **Brick A**: `codim_{Rep_d}(Σ̄^r) = C = cCodim d r` (combinatorial codim), proved, general r,
   via orbit-closure / Kostant-partition machinery.
2. **G2-2 (the BASE presentation)**: for a SINGLE matrix `Mat^{rk≤r}_{q×p}` (the TARGET matrix
   space, treated as `dStratum` = the N=1 case), localized at the pivot r×r minor `detΔ`:
   `A_loc / Iad ≅ₐ[k] Sd` where `Sd = Localization.Away detSchurS` is regular of dimension
   `δ = r(p+q−r)`, and `height Iad = C = (p−r)(q−r)`. This works because the target entries ARE
   coordinate variables, so the bottom-right `B22` block is forced by the Schur complement
   `B22 = B21 Δ⁻¹ B12`, and the rank ideal localizes to a graph ideal `J = graphIdeal forcedB22`.
3. **Graph-ideal height engine** (general): for finite σ,τ and any `c : σ → MvPolynomial τ k`
   (or to a localization `Sd`), `height(graphIdeal c) = #σ`. Network-free.
4. **Bordered Schur minor identity** (any comm ring): `det[[Δ,u],[v,d]] = d·detΔ − v·adj(Δ)·u`.
5. **Going-down height-additivity** (LANDED in Mathlib v4.29):
   `Ideal.height_eq_height_add_of_liesOver_of_hasGoingDown p P` :
   `height_S P = height_R p + height_{S/pS}(P/pS)` for `R → S` with `HasGoingDown` (flat ⟹ this).
6. **Flat-quasi-finite height** brick: flat + quasi-finite-at-Q ⟹ `height_S Q = height_R (Q∩R)`.
7. The fibre comorphism `multComap : MvPoly[target entries] →ₐ[k] MvPoly[factor entries]`,
   `X_{rc} ↦ multPoly d r c = (mult d genericTuple)_{rc}` (degree-N polynomials), and
   `fibreGenIdeal d B = map multComap (maxIdealOfPoint B)`.

## The TARGET to discharge

`codim_{Rep_d}(fibre B) = C + δ` (as ℕ∞ ideal heights), i.e. `codim_{Σ̄^r}(fibre) = δ`.

## My proposed CHART chain (red-team this)

Localize `Rep_d` at the pulled-back pivot `Δ_tot = multComap(detΔ)` = the product-pivot minor.
- `R := Sd` = O(target rank locus chart), regular dim δ (= G2-2's output ring).
- `S := B_loc` = O(Σ̄^r ∩ chart), a `Sd`-algebra via the localized comorphism.
- Claim local-triviality: `S ≅ₐ[Sd] Sd ⊗_k F_E` (free over Sd), where `F_E` = O(fibre over the
  normal form `E = diag(I_r,0)`) — a "zero-product-type" ring, reducible (e.g. anchor `(2,2,2),r=1`:
  `F_E = k[u,v,X,Z,ℓ,m]/(uX+vZ−1, ℓm)`).
- Free ⟹ flat ⟹ HasGoingDown. Take `P` a minimal prime of the fibre in `S`, lying over the maximal
  ideal `m_B` of the point `B` in `R` (height δ since R regular dim δ, m_B maximal). `P` minimal in
  the fibre ring `F_E` ⟹ relative height 0. So `height_S P = δ + 0 = δ`. Min over components ⟹
  `codim_{Σ̄^r}(fibre) = δ`. Add C (Brick A, chart-localization preserves height) ⟹ `C + δ`.

## What I found (the wall)

The total rank ideal in `Rep_d` FACTORS: for `(2,2,2),r=1`, `det(A_2 A_1) = detA_1 · detA_2`
(reducible, 2 components), whereas the base target rank ideal `det(B) = B00 B11 − B01 B10` is
irreducible. So the B22-elimination/graph-ideal trick of G2-2 does NOT port: product entries are
not coordinate variables. The trivialization `S ≅ Sd ⊗_k F_E` is the genuine object and seems to be
a substantial new build (an explicit polynomial section of `mult` over the chart + the tensor
decomposition AlgEquiv).

## QUESTIONS

**Q1 (total presentation).** On the pivot chart, is `S ≅ₐ[Sd] Sd ⊗_k F_E` the right object?
What are the free vs forced FACTOR coordinates on the chart? Is there an EXPLICIT polynomial
section `Mat^{rk≤r}_chart → Rep_d` (e.g. for N=2: given B with pivot block invertible, a canonical
factorization `B = A_2 A_1`) that exhibits the trivialization? For general N (product of N matrices),
how does the section generalize — is it "put N−1 factors in normal position, one carries B"?
Is the tensor-decomposition AlgEquiv reachable, or is there a cheaper route (e.g. compute
`height_S(I_fibre)` directly via explicit C+δ coordinate equations on the chart, bypassing flatness)?

**Q2 (flatness / going-down).** Is `free ⟹ flat ⟹ HasGoingDown ⟹ height_eq_height_add_…` the right
chain, and is the "P minimal prime of fibre ⟹ relative height 0 in F_E" step sound? Or is the
flat-quasi-finite brick (`height_eq_under_of_flat_quasiFiniteAt`, fibre height 0) cleaner — does
quasi-finiteness HOLD here (the fibre F_E is dim 4, NOT finite, so quasi-finite-at-Q FAILS unless Q
is isolated in its fibre — but the fibre is positive-dimensional, so going-down + minimal-prime is
needed, not quasi-finite)? Pin the exact lemma chain. Is there a subtlety in `m_B` having height
exactly δ (R regular dim δ ⟹ every maximal ideal height δ — but is `R = Sd` actually a finitely-
generated k-algebra domain that's equidimensional, so all maximal ideals have height δ? Sd is a
localization of a polynomial ring, so YES, but confirm)?

**Q3 (reserve route).** Evaluate the "explicit coordinate equations" reserve: instead of flatness,
exhibit the fibre `mult⁻¹(B) ∩ chart` as cut by exactly `C + δ` equations whose Jacobian has full
rank `C+δ` at a smooth point (a complete-intersection / regular-sequence argument giving height
`C+δ` directly via Krull + a lower bound). Is THIS cleaner in Lean than the trivialization, given
that `det(product)` factors and the fibre is reducible?

Be concrete and adversarial. If the trivialization is the only honest route and it's a big build,
say so and estimate its size; if there's a shortcut, name it precisely. Cite Mathlib v4.29 API where
relevant (HasGoingDown, Module.Flat, IsLocalization, TensorProduct.Free, minimalPrimes, Ideal.height).
