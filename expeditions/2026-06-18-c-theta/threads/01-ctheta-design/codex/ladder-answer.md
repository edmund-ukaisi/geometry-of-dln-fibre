**Bottom line:** the canonical mathematics is “complete the square, then solve a closest lattice point problem in an active coordinate simplex.” For Lean, do not formalize Conway-Sloane as a black-box lattice theorem. Prove the special rounding lemma directly by integer exchange.

1. **Quadratic form to explicit formula**

Yes, the paper’s standard route is exactly canonical: complete the square, identify the QIP with a closest-point problem in the simplex, truncate to the active prefix, then solve the affine `A_{m-1}` lattice rounding problem. The paper explicitly frames Section 7 this way and cites Conway-Sloane for the closest-point step. ([arxiv.org](https://arxiv.org/pdf/2411.19920))

The Lean-amenable derivation is more elementary:

- complete the square over `ℤ`;
- prove the active-prefix lemma by exchange: coordinates after `m` are zero in every optimum;
- reduce to minimizing `∑ (x_i - p_i)^2` over integer `x_i` with fixed sum;
- prove the rounding correction lemma: round all coordinates, then add/subtract `1` in exactly `|δ|` coordinates;
- count those choices by `Nat.choose`.

This avoids formalizing Voronoi cells, root lattices, or Conway-Sloane.

2. **Hard step in Theorem 6.1**

The substitution identity is not the hard step. You already have the easy half: `e ↦ m(e)` is valid and gives `codim = G`.

The hard load-bearing step is the converse for minimizers: every codimension minimizer is in the horizontal-lace/e-image normal form. In the arXiv v2 numbering, the paper proves horizontal representatives for weakly increasing `d` as Lemma 6.4, then uses the top-dimensional/minimality argument to force exactly one missing edge in each top row and all possible edges below, giving the `e_i, f_i` form. ([arxiv.org](https://arxiv.org/pdf/2411.19920))

In Lean this is medium-hard to hard finite combinatorics, not algebraic geometry, if recast as:

- define lace rows combinatorially;
- prove horizontal representatives for sorted `d`;
- prove a local merge/add-edge operation preserves the rank-zero condition when a row still has a gap;
- prove non-normal rows strictly improve codimension, preferably directly from your proven codim formula rather than via orbit closure.

Expect this to be the first serious proof-engineering wall: lots of interval bookkeeping and strict inequality lemmas.

3. **Theorem 7.10**

The explicit formula is reachable on top of QIP, but it is its own substantial arithmetic project. It is easier than the horizontal-lace theorem conceptually, but longer in floor/division bookkeeping.

Needed Mathlib-style ingredients:

- `Finset` sums over finite indices;
- `Int`/`Nat` division and modulo;
- `Nat.choose` and cardinality of fixed-size subsets;
- elementary square inequalities like `(a+1)^2 + (b-1)^2 < a^2 + b^2`;
- custom lemmas for “round half up” via integer division.

Genuinely absent, in the sense you should not rely on it: a ready-made Conway-Sloane closest vector theorem, lattice-point enumeration in simplices, or a packaged affine `A_n` closest-point solver.

Also: I would treat the literal rank-`r` Theorem 7.10 statement as conditionally correct at best. Lemma 4.5 reduces rank `r` to rank `0` for `d-r`, so the active prefix `m` should be recomputed after subtracting `r`. ([arxiv.org](https://arxiv.org/pdf/2411.19920)) The printed theorem defines `m` from the original sorted `d'` and then uses `S̃ = S-(m+1)r`; that is valid only when the active prefix does not change. Your enumeration evidence is exactly what the rank-reduction logic predicts.

4. **Permutation Invariance Without Poincaré**

There is a plausible independent route, but I would not call it established:

- prove adjacent-swap invariance directly on the finite KP optimization;
- for each adjacent transposition of `d`, construct a local transformation on interval multisets/lace diagrams preserving rank and top codimension;
- prove it induces a bijection only on minimizers, not on all KPs.

Where it can fail: the KP sets for `d` and `σ(d)` do not have the same size, so there is no global bijection to lean on. The paper explicitly notes this and says it does not know a proof relying only on the KP codimension combinatorics. ([arxiv.org](https://arxiv.org/pdf/2411.19920))

A safer non-Poincaré route is: prove directly that `C(d,r)` and `θ(d,r)` equal the explicit formula applied to `sort(d-r)`. Then permutation invariance is immediate. But that direct theorem is essentially the missing combinatorial invariance proof in another form.

5. **Recommended Lean Ordering**

1. Define KPs, rank, codim, `C`, `θ` as finite `Finset` minimization.
2. Prove rank shift: `C(d,r)=C(d-r,0)` and same `θ`, by adding/removing `r` copies of `[0,N]`.
3. Prove sorted rank-zero QIP:
   - e-image construction and codim identity;
   - **hardest critical step:** minimizers are exactly horizontal-lace/e-image KPs.
4. Prove explicit QIP minimizer theorem by custom rounding/exchange lemmas.
5. Derive closed `C` and `θ = Nat.choose m |δ|` for sorted `d-r`.
6. Only then attempt independent permutation invariance, as a separate capstone. Avoid formalizing the Poincaré series unless the combinatorial invariance route stalls.