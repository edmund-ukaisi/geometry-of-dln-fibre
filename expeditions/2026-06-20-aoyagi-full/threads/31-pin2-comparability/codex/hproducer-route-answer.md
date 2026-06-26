**Verdict**

I would treat (b) as **pointwise-true, medium-high confidence**, but only after proving one exact product lemma. The load-bearing reason is simple for `L = 2`: if the last pivot factor is

```lean
(Pf last * (A w) last * Qf last) * Pπ
```

with fixed `Pπ`, then

```lean
(Pf 0 * (A w) 0 * Qf 0) *
((Pf last * (A w) last * Qf last) * Pπ)
=
P0 * ((A w) 0 * (A w) 1) * QL * Pπ
```

using the fixed frame telescope. The product’s nonlinear dependence on `w` does not matter, because the permutation is a fixed right multiplication after the product.

The one assumption I cannot derive from your description is that the “gauge reads” in `framedParamsPivot (split w)` are exactly the entries of that framed raw last matrix, merely written in pivot order. If those reads recompute last-layer entries using core/gauge coordinates in a way not equal to framed raw parameters, the fixed-map route fails and you need the Taylor/germ route.

**Cheapest Test**

Use `L = 2`, `H = (1,2,2)`, `r = 1`, pivot `J(0) = 1`, target

```text
B = [0, 1]
```

Take two factorizations with the same product:

```text
A0  = [1, 0]
A1  = [[1/5, 1],
       [0,   0]]

A0' = [11/10, 0]
A1' = [[2/11, 10/11],
       [0,    0]]
```

Both satisfy:

```text
A0 * A1 = A0' * A1' = [1/5, 1].
```

Now compute:

```lean
∑ i, deepestEFull ... (split (flat A0 A1)) i ^ 2
∑ i, deepestEFull ... (split (flat A0' A1')) i ^ 2
```

If the values differ, `deepestEFull` is not a fixed function of the residual, so the pointwise proof route is unsound. If they agree, especially with the exact reindexed block matrices agreeing after the `Pπ`/FACT2 correction, the pointwise route is strongly supported.

**Module Placement**

Prove the `deepestEFull`-specific (b)-atom inline after `deepestEFull` in `DeepestGaugeConstruction.lean`; extract only generic finite-dimensional Frobenius/quadratic-form lemmas to `DeepestSchurComparability`.

**Risk Ranking**

1. **(i) (b)-atom**: 200-450 LoC, highest risk. The sink point is not analysis, it is the exact telescope plus FACT2 permutation/reindex proof.
2. **(iii) leak bound**: 100-180 LoC, medium risk. Needs bounded inverse, finite Frobenius inequalities, and `Sreg → 0`.
3. **(ii) eventual `P00` invertible**: 40-90 LoC, low-medium risk. Standard determinant continuity, `det = 1` at `w0`.
4. **(iv) wiring built core atom**: 30-80 LoC, low risk unless its statement’s block conventions differ.
5. **(v) neighborhood assembly**: 30-70 LoC, low risk. Finite intersections and extracting witnesses.

If the test fails, leave the honest atom as the sorry, not the fixed-map claim:

```lean
lemma deepestEFull_split_sq_sum_eventually_comparable_Sreg :
  ∃ δ₁ δ₂ : ℝ, 0 < δ₁ ∧ 0 < δ₂ ∧
    ∀ᶠ w in 𝓝 w0,
      δ₁ * Sreg w ≤ (∑ i, deepestEFull ... (split w) i ^ 2) ∧
      (∑ i, deepestEFull ... (split w) i ^ 2) ≤ δ₂ * Sreg w := by
  sorry
```