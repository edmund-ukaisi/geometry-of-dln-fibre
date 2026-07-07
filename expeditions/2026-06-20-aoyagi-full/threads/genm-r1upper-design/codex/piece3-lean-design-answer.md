1. **VERDICT on (P2)**

The `t = 0` collapse is algebraically real, but using it to prove `sjBoundaryPeel` makes the theorem vacuous as a peel theorem: it proves the bound by including the original integral unchanged. That is acceptable only as temporary plumbing for API wiring, not as a faithful formalisation of Piece 3. Since `sjJointResolution` for `t = 0` is then exactly the original finiteness problem, the combined proof becomes circular unless the final argument excludes or separately handles that term.

Recommendation: **must do genuine cover+schur** for the real theorem; keep the `t = 0` identity only as a diagnostic or temporary lemma.

2. **VERDICT on (P1)**

Use option **(a)**, per-chart. The sum-over-`t` signature does **not** honestly survive unless you prove a nontrivial permutation/canonicalization comparison. A single canonical first-`t` `gammaPeelIntegral M t c'` is not chart-independent because `κ` selects different rows of `Q = prod (tailChain M) A'`; that changes `Q_p/Q_b`, not just dummy coordinates.

Lean-ish shape:

```lean
gammaPeelIntegralChart
  (M : Fin (L+3) -> Nat) (t : Nat)
  (rho : Fin t ↪ Fin (M 0)) (kappa : Fin t ↪ Fin (M 1))
  (c' : ℝ) : ENNReal :=
∫⁻ A' in paramsBoxM (tailChain M) 1,
∫⁻ A in {A : Matrix (Fin t) (Fin t) ℝ | IsUnit A.det ∧ A in inducedBox},
∫⁻ B in inducedBox,
∫⁻ C in inducedBox,
∫⁻ Gamma in inducedBox,
  ENNReal.ofReal
    ((frobSq (A ⬝ Qtilde_p)
      + frobSq (C ⬝ Qtilde_p + Gamma ⬝ Q_b)) ^ (-c'))
```

where `Q_p,Q_b` are obtained from `Q` using `kappa` and its complement, and `Qtilde_p = Q_p + A⁻¹ ⬝ B ⬝ Q_b`. The variable `A` is over the invertible pivot chart plus the block image of the original box, not over all invertible matrices unless you enlarge the domain and pay for that explicitly. Then the honest theorem is:

```lean
routeMLayerBoxIntegral M c' 1 ≤
  ∑ t in range (min (M 0) (M 1) + 1),
    ∑ rho, ∑ kappa,
      C * gammaPeelIntegralChart M t rho kappa c'
```

3. **Genuine cover+schur route**

Load-bearing lemmas:

1. `frontBox_block_equiv`: reindex `A0 : matBox (M 0) (M 1) 1` into blocks `(A,B,C,D)` for fixed `(rho,kappa)` with measure-preserving coordinate permutation and the correct induced box domains.

2. `chart_block_integral`: restrict the previous block integral to `IsUnit A` and match it with `pivotChart rho kappa`.

3. `schur_shear_integral`: apply `measurePreserving_shearSub` with `Gamma = D - C ⬝ A⁻¹ ⬝ B`, preserving volume and rewriting the integrand using `schur_cov` plus the exact cross-coupled block identity.

4. `chart_bound_by_gammaPeelIntegralChart`: absorb domain equalities/enlargements into the per-chart gamma integral.

Hardest: **the block reindex-to-product measure plumbing**, especially carrying the original `matBox` through arbitrary row/column embeddings and complements. I am guessing Mathlib has enough `MeasurableEquiv`/finite product volume API to do this, but the exact matrix-block API is likely brittle.

Reachability: per-chart design is bounded plumbing but still substantial. A single tide can plausibly get the definitions and theorem skeleton with 3-5 focused lemmas stated. Fully proving all measure/block-reindex lemmas is likely a multi-hundred-line wall.

4. **Biggest correctness trap**

Do not silently enlarge or replace the post-shear domain as if `Gamma` were independently box-bounded. After `Gamma = D - C A⁻¹ B`, the image of the original box in `(A,B,C,Gamma)` is not generally a product box. Any product-domain `gammaPeelIntegralChart` must be justified by an explicit domination/enlargement lemma, otherwise the integral no longer faithfully represents the chart.