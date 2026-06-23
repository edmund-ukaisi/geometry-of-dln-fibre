**Verdict: NO-GO for the proposed F2 sandwich.** The exact codim identity is not reachable from F1 + Brick A + bare Krull/equidimensionality. The route has a sign error: Krull gives `height ≤ #generators`, i.e. an **upper** bound on codimension, not the needed lower bound.

For `H = height(vanishingIdeal(fibre))`, `C = codim Σ̄^r`, `δ = r(d₀+d_N-r)`:

- `fibre ⊆ Σ̄^r` gives only `H ≥ C`.
- Krull, even on a rank-`r` chart with `δ` base parameters, gives at best `H ≤ C + δ`.
- Using full `R_target`, the point ideal has `d_N*d₀` generators/height, not `δ`; the shift `δ` only appears after quotienting/localizing to the exact-rank determinantal chart.
- Affine-domain equidimensionality converts known dimension bounds into height bounds; it does not supply the missing no-jump/fibre-dimension upper bound.

So the sandwich cannot prove equality.

**A. Viable Algebraic Route**
There is a believable algebraic route, but it is a new local-trivialization/flatness build, not the current sandwich:

1. Reduce rank-`r` `B` to canonical `E = diag(I_r,0)` by endpoint base-change; transport codim by the induced ambient algebra equivalence.
2. Choose a rank-`r` pivot chart `U = D(Δ)` in `Mat^{rk≤r}` containing `E`; prove its coordinate ring is a localization of a polynomial ring of dimension `δ`.
3. Build the explicit section on the chart. For block matrix `Y = [[A,B],[C,D]]` with `A` invertible and rank `≤ r`, use `D = C A⁻¹ B` and matrices sending `E` to `Y`.
4. Use equivariance to prove `mult⁻¹(U) ∩ Σ̄^r ≅ U × fibre(E)` as affine varieties/rings.
5. Apply `Module.Flat`/`Algebra.HasGoingDown.of_flat` and `Ideal.height_eq_height_add_of_liesOver_of_hasGoingDown` per component.
6. Use landed catenary/equidimensionality and Brick A’s minimal-prime/orbit-component machinery to take the minimum over top components.

Steps 2-4 and the component correspondence are the missing work. Mathlib has the flat/going-down API; it does not have this chart trivialization for your map.

**B. Going-Down Per Component**
Not globally. `multComap : R_target → R_total` is not flat; over `Mat^{rk≤r}` fibres jump at lower ranks. For example, in `(2,2,2), r=1`, the generic rank-one fibre has expected dimension `4`, while the zero fibre has dimension `5`.

Per top component, going-down becomes applicable only after restricting to the exact-rank chart and proving the local product/trivialization. Orbit structure suggests this is true, but does not give a Lean lemma for free.

**C. r ≤ 1**
`r=0` is the only fully clean case already landed: `fibre(0)=Σ̄^0`.

General `r=1` is still nontrivial. The pivot chart formulas simplify because the invertible block is `1×1`, but the same issues remain: exact-rank chart, flat/local product proof, and fibre-component bookkeeping. Specific witnesses like `(2,2,2), r=1` can be checked directly; arbitrary `r=1` is not elementary from current infrastructure.

**D. Recommendation**
Do not grind the current F2 sandwich. Either:

- keep `BundleShiftInterface` cited for now, or
- pivot to an explicit `RankChartTrivialization` build and make that the next gating theorem.

The minimal honest partial landing is a checkpoint documenting this NO-GO plus a precise new target: standard rank-chart local trivialization of `mult` and the induced componentwise height shift.