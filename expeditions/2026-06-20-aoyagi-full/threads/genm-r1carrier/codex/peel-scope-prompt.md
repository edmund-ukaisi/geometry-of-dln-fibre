<task>
Adjudicate ONE truth-value about a formalisation step in a resolution-of-singularities / RLCT
computation (Watanabe singular learning theory; Aoyagi's deep-linear-network log-canonical threshold).
Withhold nothing about the math; reason from scratch. I am NOT telling you my current leaning.

## The concrete setting

We compute the real log-canonical threshold of the squared loss of a deep linear network by resolving
the singularities of a "layer-product" loss. After a front-layer pivot chart and a Schur block split,
the loss on one chart is (matrix norms; `‖·‖` = Frobenius):

    L = ‖A·Qp‖²  +  ‖C·Qp + Γ·Qb‖²

where:
- `Γ` (the "freed corank block") is a `p×q` matrix, `p = M0−t`, `q = M1−t`, `t` the pivot rank;
- `Qp` = the pivot (top-t) rows of the deeper tail product `Q = A_1 · A_2 · … · A_{L-1}`;
- `Qb` = the NON-pivot (bottom `q'`) rows of `Q`, so `Qb = A_{1,b} · A_2 · … · A_{L-1}` is a
  MATRIX PRODUCT (for chain length L≥3 the tail is a genuine product of ≥2 free matrices);
- `A`, `C` are further blocks of the front layer.

We integrate `∫ L^{-c'}` (an ℝ≥0∞ Lebesgue integral) over a box of all free parameters, and want
finiteness for every real `c' < ½·minAdm`, where `minAdm` is an explicit integer (the codimension).

## The banked "regime atoms" (what is already proved and available)

Two isotropic corank-block Morse lemmas, over an arbitrary outer measurable parameter `z ∈ Z`, with a
NON-NEGATIVE ADDITIVE core `W(z)` (`Δ` is a free `p×q` box matrix, `frobSq Δ = ‖Δ‖²`):

  (A) high-exponent shift  (c' > pq/2, W>0 strictly):
        ∫_Z ∫_{Δ∈box} (‖Δ‖² + W(z))^{-c'} dΔ dz  ≤  Cresid(pq,c') · ∫_Z W(z)^{-(c'-pq/2)} dz
  (B) block dominance      (c' < pq/2, W≥0):
        ∫_Z ∫_{Δ∈box} (‖Δ‖² + W(z))^{-c'} dΔ dz  <  ∞

Also banked: a "radialAttach" op (prepend a fresh fully-shared radial divisor u0, multiplying the loss
pointwise by u0²), and a "rowMix" op (linearly mix the sum-of-squares generators by a matrix R at
constant monomial support). Both keep the deeper parameter space Z FIXED and are pointwise-loss
identities. Also banked: a shared-divisor "support ledger" tracking which generators share which
exceptional divisor, and a terminal monomial finiteness endpoint (`∫ (Σ monomials²)^{-c'} · Jacobian`
finite below a per-axis threshold).

## The step in question ("peelZBlock")

To run the induction we need ONE operation that takes the loss above and, in one peel:
  (i)   maps a "z-block" of Z (the leading matrix factor of the tail product) into fresh exceptional
        `u`-coordinates via a single-radial blow-up change of variables,
  (ii)  integrates out the freed corank block `Γ` via regime atom (A) or (B),
  (iii) descends to a strictly-shorter tail product (one fewer layer),
so that after finitely many peels the loss becomes a z-INDEPENDENT sum of monomials (the terminal).

## The precise obstruction I want you to weigh

The regime atoms (A)/(B) require the block to enter ISOTROPICALLY as `‖Δ‖²` plus an ADDITIVE core
`W(z)`. But in `L` the corank block enters ANISOTROPICALLY and COUPLED: `‖C·Qp + Γ·Qb‖²`, i.e. `Γ`
is multiplied by `Qb` on the right (a right-anisotropy) with a cross term `C·Qp`. Turning
`‖…+ Γ·Qb‖²` into `‖Δ‖² + W(z)` requires a change of variables `Δ = Γ·(something built from Qb)`
that removes the right factor `Qb`. The naive Gram change of variables `Γ ↦ Γ·Qb` has Jacobian
`det(Qb Qbᵀ)^{-p/2}`, which introduces a Gram determinant of the PRODUCT `Qb = A_{1,b}·A_2·…`.
`det(Qb Qbᵀ) = ‖∧^q Qb‖²` (sum of squares of the maximal minors / Plücker coordinates of the product).

## The specific instance to adjudicate

Chain widths `M = (3,3,3,4)`, front pivot rank `t = 1`, so `p = q = 2` (corank-2). After the front
peel the tail is `Z = A_1 · A_2` with `A_1` 3×3, `A_2` 3×4; `Qb = A_{1,b}·A_2` is a 2×4 PRODUCT
(`A_{1,b}` = bottom 2 rows of `A_1`, a 2×3 matrix). So `det(Qb Qbᵀ) = ‖∧²(A_{1,b}·A_2)‖²`, the
squared 2×2 minors of a 2×4 matrix product.

</task>

<output_contract>
Answer these, in order, tersely, each with the reasoning that forces it:

Q1. Is the map from `‖C·Qp + Γ·Qb‖²` (anisotropic, product `Qb`) to the isotropic `‖Δ‖² + W(z)`
    shape required by regime atoms (A)/(B) something you can build by COMPOSING the banked pieces
    (radialAttach + rowMix + a finite coordinate/chart cover + atoms (A)/(B)), or does it require a
    genuinely-new construction those pieces do not contain? Name what is missing if so.

Q2. For the corank-2 PRODUCT `Qb = A_{1,b}·A_2` at the concrete widths above: is monomializing
    `det(Qb Qbᵀ) = ‖∧²(A_{1,b}·A_2)‖²` (to a normal-crossing "monomial × unit" on a finite chart
    cover) achievable by a SEQUENCE of coordinate/toric single-radial blow-ups (centers = coordinate
    subspaces, i.e. inside already-existing exceptional divisors), OR does it force a blow-up whose
    center is a NON-coordinate (e.g. determinantal / minor / Plücker) locus? Give the reason (e.g.
    Cauchy–Binet structure, Plücker relations, whether the minor ideal is monomial in toric charts).

Q3. VERDICT, one of:
      BOUNDED — peelZBlock is a large-but-buildable composition of the banked atoms + a finite chart
                cover + bounded chart algebra (no new resolution-of-singularities theorem); OR
      RESEARCH-GRADE — peelZBlock needs a genuinely-new principalisation / resolution result that the
                measure-theoretic atoms do not reach and that a Mathlib-based formalisation currently
                lacks.
    If RESEARCH-GRADE, state EXACTLY what theorem would have to be either built or CITED
    (name the mathematical object: principalisation of the minor ideal of a matrix product, etc.).

Q4. The single cheapest exact-algebra check that would DISCRIMINATE your Q2/Q3 answer from its
    opposite (something I can run in sympy/sage in a few minutes).
</output_contract>

<grounding_rules>
- Distinguish clearly what you assert as mathematical FACT vs INFERENCE/judgement.
- Do not assume the answer I want; I have deliberately not told you my leaning.
- "Bounded but very large" and "needs a genuinely new theorem" are DIFFERENT verdicts — pick one and
  defend it; do not hedge into "it depends" without saying what it depends on.
- Cauchy–Binet: minors of a product `AB` are bilinear in (minors of A, minors of B). Use this.
- The pure route (keep Γ a chart coordinate, blow up its radial in the box, resolve Qb via the deeper
  layers) and the atom route (integrate Γ out over full space → Gram det) may differ; say whether the
  pure route escapes the Gram-det principalisation or merely relocates it.
</grounding_rules>
