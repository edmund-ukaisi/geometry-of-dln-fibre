**Verdict:** Ship the concrete `(3,3,4)` lemma first. Inference: with one tide and a “never leave the build broken / stop on thrash” rule, the general `(M0,M1,M2)` proof is too exposed to opaque minimizer, `FlatIdx` enumeration, and dependent matrix bookkeeping; `(3,3,4)` proves the headline obstruction and gives you a proof-shaped artifact to generalize from.

**Concrete Module Skeleton**

1. `M334_defs`: define `M334`, `flatDim = 21`, `minAdm = 8`, achiever `t = 1`.  
   Cheap: `native_decide` / `decide` / `norm_num`.

2. `routeM334_chart_coords`: name the flat coordinates used for `u`, `Dbar`, `Tbar`, `S`, spectators, and prove per-entry reconstruction under `paramsEquivFlat.symm`.  
   Real weight: this is where opaque flattening can bite, but in `(3,3,4)` it should be `fin_cases`-driven.

3. `M334_active_card`: active coordinate set has card `8`, pivot belongs to active, spectators are disjoint.  
   Cheap if active is explicit Finset; `decide`.

4. `M334_blowup_apply`: expand `pivotBlowupOn active pivot x` on pivot, active non-pivot, and spectator coordinates.  
   Mostly cheap, assuming existing API exposes the gated map cleanly.

5. `M334_product_factor`: after the chart, `(A·C) i j = u * Q i j`, with `Q` independent of `u`, and `Q 0 0 = 1`.  
   Real proof weight: matrix multiplication plus flat-coordinate unfolding; likely `fin_cases`, `simp`, `ring`.

6. `M334_loss_factor`: `routeMCore M334 (φ x) = u^2 * U x`, where `U = Σ i j (Q i j)^2`.  
   Moderate: follows from previous lemma, Frobenius double sum, `ring_nf`.

7. `M334_U_ge_one`: `1 ≤ U x`.  
   Cheap after `Q 0 0 = 1`; use nonnegativity of squares and Finset sum lower-bound lemmas. Exact lemma names uncertain.

8. `M334_det_blowup`: Jacobian determinant of the chart is `u^(8 - 1) = u^7`.  
   Mostly existing-API proof; card lemma plus determinant formula. Real risk only if determinant statement has side conditions.

9. `M334_chart_image_subset_box`: for a small source box, `φ(sourceBox) ⊆ cubeBox 21 ε`, with the right positivity assumptions.  
   Real proof weight: inequalities and ensuring the gated blow-up does not leave the target box.

10. `M334_cov_lower_bound_integrand`: after change of variables, bound the pulled-back integrand below by the monomial leaf integrand in `u`, using `U` bounded above on the source box, not merely `U ≥ 1`.  
   Real proof weight and easy to get directionally wrong.

11. `M334_leaf_integral_top`: instantiate `monomialIntegrand_lintegral_box_eq_top` with exponent `-1` at `c' = 4`, or with exponent `7 - 2c' ≤ -1` for `c' ≥ 4` if the leaf supports monotonicity.  
   Moderate: exponent-vector matching may be annoying but concrete.

12. `routeM334_box_diverges`: assemble image subset, change-of-variables, lower bound, and leaf divergence.  
   Real proof weight: mostly measure-theory plumbing.

Most likely wall: `M334_product_factor`, because it touches all three hard interfaces at once: `paramsEquivFlat.symm`, dependent `Matrix.mul`, and the exact coordinate choices. If that lemma is clean, the rest is more about existing API alignment.

**Two Soundness Traps**

You already named the first: for a lower bound on `|u^2 U|^{-c'}`, you need an upper bound `U ≤ C` on the chart domain, not just `U ≥ 1`.

The other trap specific to the single blow-up: do not accidentally use the `(2,2,2)` composite-chart measure factor or domain logic. For one `pivotBlowupOn`, the Jacobian contributes exactly `u^(card active - 1)` once; there is no Lemma-2 splice, no chained gauge determinant, and no extra image restriction silently shrinking/reshaping the binding axis. A duplicated or missing determinant factor changes the threshold.

**Deferred General Lift**

Factor out one structural lemma:

`singlePivotAchieverChart_factorization`:

Given explicit index embeddings for the rank-`t` pivot block, residual `Dbar`, top block `Tbar`, bottom block `S`, and an active set whose card is  
`(M0 - t) * (M1 - t) + t * M2`, the single `pivotBlowupOn` chart satisfies

```lean
routeMCore M (φ x) = u^2 * U x
∧ 1 ≤ U x
∧ jacobian φ x = u^(card active - 1)
∧ card active = (M0 - t) * (M1 - t) + t * M2
```

with all flat-coordinate facts supplied as hypotheses.

That isolates the general problem correctly: the later lift only has to provide the achiever `t`, the active-set cardinality, and the flat-index embeddings. The algebra and measure atom then become re-instantiation instead of being entangled with `Finset.range` minimization and opaque `equivFin` enumeration.